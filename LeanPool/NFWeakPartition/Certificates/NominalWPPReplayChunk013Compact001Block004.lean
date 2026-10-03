/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_clos1induct (x : Var) (z : Var) (C : Class) (R : Class) (S : Class)
    (V : Class) (X : Class) (dv_C_x : x ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_z : z ∉ R.fv) (dv_X_x : x ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_x_z : x ≠ z)
    (hyp_clos1induct_1 : Nominal.NPrf (.classMem S (syn_cvv)))
    (hyp_clos1induct_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_clos1induct_3 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem X V) (syn_wss S X) (syn_wral x C (.all z
              (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
                (.classMem (.cv z) X))))) (syn_wss C X)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ z } : Finset Var) ∪ C.fv ∪ R.fv ∪ S.fv ∪ V.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_z,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cin X C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          dv_X_x, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_z, dv_X_x, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cima R (syn_cin X C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, dv_R_z,
          dv_X_z, dv_C_z, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cin X C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          dv_X_z, dv_C_z, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0008 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0009 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0010 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_cin X C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_a_not_X, fresh_a_not_C, or_false, not_false_eq_true])
  have dv_cache_0012 :
    a ∉
      ((syn_wa (syn_wss S (syn_cin X C))
          (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
          fresh_a_not_S, fresh_a_not_X, fresh_a_not_C, fresh_a_not_R, or_false,
          not_false_eq_true])
  have p0000 := @g_clos1ex R S hyp_clos1induct_1 hyp_clos1induct_2
  have p0001 := @g_eqeltri C (syn_cclos1 S R) (syn_cvv) hyp_clos1induct_3 p0000
  have p0002 := @g_inexg X C V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem X V) (.classMem C (syn_cvv)) (.classMem (syn_cin X C) (syn_cvv))
      p0001 p0002
  have p0004 := @g_clos1base C R S hyp_clos1induct_3
  have p0005 := @g_ssin S X C
  have p0006 :=
    @g_biimpi (syn_wa (syn_wss S X) (syn_wss S C)) (syn_wss S (syn_cin X C)) p0005
  have p0007 := @g_mpan2 (syn_wss S X) (syn_wss S C) (syn_wss S (syn_cin X C)) p0004 p0006
  have p0008 :=
    @g_elima2 x (.cv z) R (syn_cin X C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 := @g_elin (.cv z) X C
  have p0010 :=
    @g_imbi12i (.classMem (.cv z) (syn_cima R (syn_cin X C)))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))))
      (.classMem (.cv z) (syn_cin X C))
      (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0008 p0009
  have p0011 :=
    (Nominal.biimpRefl (syn_wral x C
        (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X))))
  have p0012 :=
    @g_impexp (.classMem (.cv x) C)
      (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)
  have p0013 := @g_clos1conn (.cv x) (.cv z) C R S hyp_clos1induct_3
  have p0014 :=
    @g_biantrud (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv z)))
      (.classMem (.cv z) C) (.classMem (.cv z) X) p0013
  have p0015 :=
    @g_adantrl (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv z))
      (syn_wb (.classMem (.cv z) X) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      (.classMem (.cv x) X) p0014
  have p0016 :=
    @g_pm5_74i
      (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
      (.classMem (.cv z) X) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0015
  have p0017 :=
    @g_bitr3i
      (.imp (.classMem (.cv x) C)
        (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))
      (.imp (syn_wa (.classMem (.cv x) C)
          (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (.classMem (.cv z) X))
      (.imp (syn_wa (.classMem (.cv x) C)
          (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
        (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      p0012 p0016
  have p0018 :=
    @g_albii
      (.imp (.classMem (.cv x) C)
        (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))
      (.imp (syn_wa (.classMem (.cv x) C)
          (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
        (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      x p0017
  have p0019 :=
    @g_bitri
      (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      (.all x (.imp (.classMem (.cv x) C)
          (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      (.all x (.imp (syn_wa (.classMem (.cv x) C)
            (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
          (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))))
      p0011 p0018
  have p0020 := @g_elin (.cv x) X C
  have p0021 := @g_ancom (.classMem (.cv x) X) (.classMem (.cv x) C)
  have p0022 :=
    @g_bitri (.classMem (.cv x) (syn_cin X C))
      (syn_wa (.classMem (.cv x) X) (.classMem (.cv x) C))
      (syn_wa (.classMem (.cv x) C) (.classMem (.cv x) X)) p0020 p0021
  have p0023 :=
    @g_anbi1i (.classMem (.cv x) (syn_cin X C))
      (syn_wa (.classMem (.cv x) C) (.classMem (.cv x) X)) (syn_wbr (.cv x) R (.cv z))
      p0022
  have p0024 :=
    @g_anass (.classMem (.cv x) C) (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))
  have p0025 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))
      (syn_wa (syn_wa (.classMem (.cv x) C) (.classMem (.cv x) X)) (syn_wbr (.cv x) R (.cv z)))
      (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
      p0023 p0024
  have p0026 :=
    @g_imbi1i (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))
      (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
      (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0025
  have p0027 :=
    @g_albii
      (.imp (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))
        (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      (.imp (syn_wa (.classMem (.cv x) C)
          (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
        (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      x p0026
  have p0028 :=
    @g_n_19_23v (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))
      (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) x dv_cache_0004
  have p0029 :=
    @g_n_3bitr2i
      (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      (.all x (.imp (syn_wa (.classMem (.cv x) C)
            (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))))
          (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))))
      (.all x (.imp (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))
          (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))))
      (.imp (syn_wex x (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))))
        (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      p0019 p0027 p0028
  have p0030 :=
    @g_bitr4i
      (.imp (.classMem (.cv z) (syn_cima R (syn_cin X C))) (.classMem (.cv z) (syn_cin X C)))
      (.imp (syn_wex x (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))))
        (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      p0010 p0029
  have p0031 :=
    @g_albii
      (.imp (.classMem (.cv z) (syn_cima R (syn_cin X C))) (.classMem (.cv z) (syn_cin X C)))
      (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      z p0030
  have p0032 :=
    @g_dfss2 z (syn_cima R (syn_cin X C)) (syn_cin X C) dv_cache_0005 dv_cache_0006
  have p0033 :=
    @g_ralcom4
      (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))
      x z C dv_cache_0007 dv_cache_0008
  have p0034 :=
    @g_n_3bitr4i
      (.all z (.imp (.classMem (.cv z) (syn_cima R (syn_cin X C)))
          (.classMem (.cv z) (syn_cin X C))))
      (.all z (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))
      (syn_wral x C (.all z (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      p0031 p0032 p0033
  have p0035 :=
    @g_biimpri (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))
      (syn_wral x C (.all z (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      p0034
  have p0036 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a
      dv_cache_0009 dv_cache_0010
  have p0037 :=
    @g_eqtri C (syn_cclos1 S R)
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      hyp_clos1induct_3 p0036
  have p0038 := @g_sseq2 (.cv a) (syn_cin X C) S
  have p0039 := @g_imaeq2 (.cv a) (syn_cin X C) R
  have p0040 := @g_id (.classEq (.cv a) (syn_cin X C))
  have p0041 :=
    @g_sseq12d (.classEq (.cv a) (syn_cin X C)) (syn_cima R (.cv a))
      (syn_cima R (syn_cin X C)) (.cv a) (syn_cin X C) p0039 p0040
  have p0042 :=
    @g_anbi12d (.classEq (.cv a) (syn_cin X C)) (syn_wss S (.cv a))
      (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (.cv a)) (.cv a))
      (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)) p0038 p0041
  have p0043 :=
    @g_elabg (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
      (syn_wa (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)))
      a (syn_cin X C) (syn_cvv) dv_cache_0011 dv_cache_0012 p0042
  have p0044 :=
    @g_biimprd (.classMem (syn_cin X C) (syn_cvv))
      (.classMem (syn_cin X C)
        (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (syn_wa (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)))
      p0043
  have p0045 :=
    @g_n_3impib (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C))
      (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))
      (.classMem (syn_cin X C)
        (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      p0044
  have p0046 :=
    @g_intss1 (syn_cin X C)
      (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
  have p0047 :=
    @g_syl
      (syn_w3a (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C))
        (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)))
      (.classMem (syn_cin X C)
        (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (syn_wss (syn_cint
          (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
        (syn_cin X C))
      p0045 p0046
  have p0048 :=
    @g_syl5eqss
      (syn_w3a (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C))
        (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)))
      C
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (syn_cin X C) p0037 p0047
  have p0049 := @g_inss1 X C
  have p0050 :=
    @g_syl6ss
      (syn_w3a (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C))
        (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)))
      C (syn_cin X C) X p0048 p0049
  have p0051 :=
    @g_syl3an (.classMem X V) (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S X)
      (syn_wss S (syn_cin X C))
      (syn_wral x C (.all z (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)) (syn_wss C X) p0003 p0007 p0035
      p0050
  exact p0051

@[expose]
noncomputable def g_clos1is (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (y : Var) (z : Var) (A : Class) (C : Class) (R : Class) (S : Class)
    (dv_A_x : x ∉ A.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_R_y : y ∉ R.fv)
    (dv_R_z : z ∉ R.fv) (dv_S_x : x ∉ S.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_clos1is_1 : Nominal.NPrf (.classMem S (syn_cvv)))
    (hyp_clos1is_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_clos1is_3 : Nominal.NPrf (.classEq C (syn_cclos1 S R)))
    (hyp_clos1is_4 : Nominal.NPrf (.classMem (.cab x ph) (syn_cvv)))
    (hyp_clos1is_5 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps)))
    (hyp_clos1is_6 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ph ch)))
    (hyp_clos1is_7 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph th)))
    (hyp_clos1is_8 : Nominal.NPrf (.imp (.classMem (.cv x) S) ph))
    (hyp_clos1is_9 : Nominal.NPrf
        (.imp (syn_w3a (.classMem (.cv y) C) (syn_wbr (.cv y) R (.cv z)) ps) ch)) :
    Nominal.NPrf (.imp (.classMem A C) th) :=
  by
  have dv_cache_0001 : x ∉ (S).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_z,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_x, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.classMem (.cv y) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_y_z), dv_C_z, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0009 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0010 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cab x ph)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_erase, dv_ph_y,
          and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Class.cab x ph)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_erase, dv_ph_z,
          and_false, not_false_eq_true])
  have dv_cache_0013 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0014 : x ∉ (A).fv :=
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
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0015 : x ∉ (th).fv :=
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
        simp only [dv_th_x, not_false_eq_true])
  have p0000 := @g_ssab ph x S dv_cache_0001
  have p0001 :=
    @g_mpgbir (syn_wss S (.cab x ph)) (.imp (.classMem (.cv x) S) ph) x p0000
      hyp_clos1is_8
  have p0002 :=
    @g_n_3expib (.classMem (.cv y) C) (syn_wbr (.cv y) R (.cv z)) ps ch hyp_clos1is_9
  have p0003 := @g_vex y
  have p0004_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_clos1is_5
  have p0004 :=
    @g_elab ph ps x (.cv y) dv_cache_0002 dv_cache_0003 p0003 p0004_e01_recanon
  have p0005 :=
    @g_anbi1i (.classMem (.cv y) (.cab x ph)) ps (syn_wbr (.cv y) R (.cv z)) p0004
  have p0006 := @g_ancom ps (syn_wbr (.cv y) R (.cv z))
  have p0007 :=
    @g_bitri (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wa ps (syn_wbr (.cv y) R (.cv z))) (syn_wa (syn_wbr (.cv y) R (.cv z)) ps)
      p0005 p0006
  have p0008 := @g_vex z
  have p0009_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_clos1is_6
  have p0009 :=
    @g_elab ph ch x (.cv z) dv_cache_0004 dv_cache_0005 p0008 p0009_e01_recanon
  have p0010 :=
    @g_n_3imtr4g (.classMem (.cv y) C) (syn_wa (syn_wbr (.cv y) R (.cv z)) ps) ch
      (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z)))
      (.classMem (.cv z) (.cab x ph)) p0002 p0007 p0009
  have p0011 :=
    @g_alrimiv (.classMem (.cv y) C)
      (.imp (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z)))
        (.classMem (.cv z) (.cab x ph)))
      z dv_cache_0006 p0010
  have p0012 :=
    @g_rgen
      (.all z (.imp (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z)))
          (.classMem (.cv z) (.cab x ph))))
      y C p0011
  have p0013 :=
    @g_clos1induct y z C R S (syn_cvv) (.cab x ph) dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 hyp_clos1is_1
      hyp_clos1is_2 hyp_clos1is_3
  have p0014 :=
    @g_mp3an (.classMem (.cab x ph) (syn_cvv)) (syn_wss S (.cab x ph))
      (syn_wral y C (.all z
          (.imp (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z)))
            (.classMem (.cv z) (.cab x ph)))))
      (syn_wss C (.cab x ph)) hyp_clos1is_4 p0001 p0012 p0013
  have p0015 := @g_sseli C (.cab x ph) A p0014
  have p0016 := @g_elabg ph th x A C dv_cache_0014 dv_cache_0015 hyp_clos1is_7
  have p0017 := @g_mpbid (.classMem A C) (.classMem A (.cab x ph)) th p0015 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part017`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_clos1basesuc (x : Var) (A : Class) (C : Class) (R : Class) (S : Class)
    (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_R_x : x ∉ R.fv)
    (hyp_clos1basesuc_1 : Nominal.NPrf (.classMem S (syn_cvv)))
    (hyp_clos1basesuc_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_clos1basesuc_3 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf
      (syn_wb (.classMem A C) (syn_wo (.classMem A S) (syn_wrex x C (syn_wbr (.cv x) R A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ C.fv ∪ R.fv ∪ S.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
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
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : y ∉ (S).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0007 : x ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.objEq y w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classEq (.cv y) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wbr (.cv z) R (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((Wff.imp (syn_wbr (.cv z) R (.cv w)) (syn_wrex y C (syn_wbr (.cv y) R (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, dv_R_x,
          dv_C_x, fresh_x_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_wbr (.cv x) R (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_w, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wbr (.cv y) R (.cv w))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_w, dv_R_x, or_false,
          not_false_eq_true])
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0016 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0017 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0018 : z ∉ (R).fv :=
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
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0019 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0020 :
    y ∉ ((syn_wo (.classMem (.cv w) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv w))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_w, fresh_y_not_S,
          fresh_y_not_C, fresh_y_ne_x, fresh_y_not_R, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0021 :
    z ∉ ((syn_wo (.classMem (.cv y) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_S,
          fresh_z_not_C, fresh_z_ne_x, fresh_z_not_R, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0022 :
    w ∉ ((syn_wo (.classMem (.cv y) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_S,
          fresh_w_not_C, fresh_w_ne_x, fresh_w_not_R, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0023 :
    y ∉ ((syn_wo (.classMem (.cv z) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_S,
          fresh_y_not_C, fresh_y_ne_x, fresh_y_not_R, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0024 :
    y ∉ ((syn_wo (.classMem A S) (syn_wrex x C (syn_wbr (.cv x) R A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_S, fresh_y_not_C, fresh_y_ne_x,
          fresh_y_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0025 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0026 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0027 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0028 : x ∉ ((Wff.classMem A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_A_x,
          dv_C_x, or_false, not_false_eq_true])
  have p0000 := @g_abid2 y S dv_cache_0001
  have p0001 := @g_eqcomi (.cab y (.classMem (.cv y) S)) S p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x R C
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @g_uneq12i S (.cab y (.classMem (.cv y) S)) (syn_cima R C)
      (.cab y (syn_wrex x C (syn_wbr (.cv x) R (.cv y)))) p0001 p0002
  have p0004 := @g_unab (.classMem (.cv y) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv y))) y
  have p0005 :=
    @g_eqtri (syn_cun S (syn_cima R C))
      (syn_cun (.cab y (.classMem (.cv y) S))
        (.cab y (syn_wrex x C (syn_wbr (.cv x) R (.cv y)))))
      (.cab y (syn_wo (.classMem (.cv y) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv y)))))
      p0003 p0004
  have p0006 := @g_clos1ex R S hyp_clos1basesuc_1 hyp_clos1basesuc_2
  have p0007 := @g_eqeltri C (syn_cclos1 S R) (syn_cvv) hyp_clos1basesuc_3 p0006
  have p0008 := @g_imaex R C hyp_clos1basesuc_2 p0007
  have p0009 := @g_unex S (syn_cima R C) hyp_clos1basesuc_1 p0008
  have p0010 :=
    @g_eqeltrri (syn_cun S (syn_cima R C))
      (.cab y (syn_wo (.classMem (.cv y) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv y)))))
      (syn_cvv) p0005 p0009
  have p0011 := @g_eleq1 (.cv y) (.cv z) S
  have p0012 := @g_breq2 (.cv y) (.cv z) (.cv x) R
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @g_rexbidv (.objEq y z) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv z)) x C
      dv_cache_0007 p0013_e00_recanon
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (syn_wb (.classMem (.cv y) S) (.classMem (.cv z) S))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0014 :=
    @g_orbi12d (.objEq y z) (.classMem (.cv y) S) (.classMem (.cv z) S)
      (syn_wrex x C (syn_wbr (.cv x) R (.cv y)))
      (syn_wrex x C (syn_wbr (.cv x) R (.cv z))) p0014_e00_recanon p0013
  have p0015 := @g_eleq1 (.cv y) (.cv w) S
  have p0016 := @g_breq2 (.cv y) (.cv w) (.cv x) R
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @g_rexbidv (.objEq y w) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv w)) x C
      dv_cache_0008 p0017_e00_recanon
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (syn_wb (.classMem (.cv y) S) (.classMem (.cv w) S))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0018 :=
    @g_orbi12d (.objEq y w) (.classMem (.cv y) S) (.classMem (.cv w) S)
      (syn_wrex x C (syn_wbr (.cv x) R (.cv y)))
      (syn_wrex x C (syn_wbr (.cv x) R (.cv w))) p0018_e00_recanon p0017
  have p0019 := @g_eleq1 (.cv y) A S
  have p0020 := @g_breq2 (.cv y) A (.cv x) R
  have p0021 :=
    @g_rexbidv (.classEq (.cv y) A) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R A) x C
      dv_cache_0009 p0020
  have p0022 :=
    @g_orbi12d (.classEq (.cv y) A) (.classMem (.cv y) S) (.classMem A S)
      (syn_wrex x C (syn_wbr (.cv x) R (.cv y))) (syn_wrex x C (syn_wbr (.cv x) R A))
      p0019 p0021
  have p0023 := @g_orc (.classMem (.cv y) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv y)))
  have p0024 := @g_clos1base C R S hyp_clos1basesuc_3
  have p0025 := @g_sseli S C (.cv z) p0024
  have p0026 := @g_breq1 (.cv y) (.cv z) (.cv w) R
  have p0027 :=
    @g_rspcev (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv z) R (.cv w)) y (.cv z) C
      dv_cache_0010 dv_cache_0004 dv_cache_0011 p0026
  have p0028 :=
    @g_ex (.classMem (.cv z) C) (syn_wbr (.cv z) R (.cv w))
      (syn_wrex y C (syn_wbr (.cv y) R (.cv w))) p0027
  have p0029 :=
    @g_syl (.classMem (.cv z) S) (.classMem (.cv z) C)
      (.imp (syn_wbr (.cv z) R (.cv w)) (syn_wrex y C (syn_wbr (.cv y) R (.cv w)))) p0025
      p0028
  have p0030 := @g_clos1conn (.cv x) (.cv z) C R S hyp_clos1basesuc_3
  have p0031 :=
    @g_syl (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv z)))
      (.classMem (.cv z) C)
      (.imp (syn_wbr (.cv z) R (.cv w)) (syn_wrex y C (syn_wbr (.cv y) R (.cv w)))) p0030
      p0028
  have p0032 :=
    @g_rexlimiva (syn_wbr (.cv x) R (.cv z))
      (.imp (syn_wbr (.cv z) R (.cv w)) (syn_wrex y C (syn_wbr (.cv y) R (.cv w)))) x C
      dv_cache_0012 p0031
  have p0033 :=
    @g_jaoi (.classMem (.cv z) S)
      (.imp (syn_wbr (.cv z) R (.cv w)) (syn_wrex y C (syn_wbr (.cv y) R (.cv w))))
      (syn_wrex x C (syn_wbr (.cv x) R (.cv z))) p0029 p0032
  have p0034 :=
    @g_impcom (syn_wo (.classMem (.cv z) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv z))))
      (syn_wbr (.cv z) R (.cv w)) (syn_wrex y C (syn_wbr (.cv y) R (.cv w))) p0033
  have p0035 := @g_breq1 (.cv x) (.cv y) (.cv w) R
  have p0036_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (syn_wbr (.cv x) R (.cv w)) (syn_wbr (.cv y) R (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0036 :=
    @g_cbvrexv (syn_wbr (.cv x) R (.cv w)) (syn_wbr (.cv y) R (.cv w)) x y C dv_cache_0005
      dv_cache_0004 dv_cache_0013 dv_cache_0014 p0036_e00_recanon
  have p0037 :=
    @g_sylibr
      (syn_wa (syn_wbr (.cv z) R (.cv w))
        (syn_wo (.classMem (.cv z) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv z)))))
      (syn_wrex y C (syn_wbr (.cv y) R (.cv w)))
      (syn_wrex x C (syn_wbr (.cv x) R (.cv w))) p0034 p0036
  have p0038 :=
    @g_olcd
      (syn_wa (syn_wbr (.cv z) R (.cv w))
        (syn_wo (.classMem (.cv z) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv z)))))
      (syn_wrex x C (syn_wbr (.cv x) R (.cv w))) (.classMem (.cv w) S) p0037
  have p0039 :=
    @g_n_3adant1 (syn_wbr (.cv z) R (.cv w))
      (syn_wo (.classMem (.cv z) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv z))))
      (syn_wo (.classMem (.cv w) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv w))))
      (.classMem (.cv z) C) p0038
  have p0040 :=
    @g_clos1is (syn_wo (.classMem (.cv y) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv y))))
      (syn_wo (.classMem (.cv z) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv z))))
      (syn_wo (.classMem (.cv w) S) (syn_wrex x C (syn_wbr (.cv x) R (.cv w))))
      (syn_wo (.classMem A S) (syn_wrex x C (syn_wbr (.cv x) R A))) y z w A C R S
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0001
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 hyp_clos1basesuc_1 hyp_clos1basesuc_2 hyp_clos1basesuc_3
      p0010 p0014 p0018 p0022 p0023 p0039
  have p0041 := @g_sseli S C A p0024
  have p0042 := @g_clos1conn (.cv x) A C R S hyp_clos1basesuc_3
  have p0043 := @g_rexlimiva (syn_wbr (.cv x) R A) (.classMem A C) x C dv_cache_0028 p0042
  have p0044 :=
    @g_jaoi (.classMem A S) (.classMem A C) (syn_wrex x C (syn_wbr (.cv x) R A)) p0041
      p0043
  have p0045 :=
    @g_impbii (.classMem A C)
      (syn_wo (.classMem A S) (syn_wrex x C (syn_wbr (.cv x) R A))) p0040 p0044
  exact p0045

@[expose]
noncomputable def g_clos1baseima (C : Class) (R : Class) (S : Class)
    (hyp_clos1basesuc_1 : Nominal.NPrf (.classMem S (syn_cvv)))
    (hyp_clos1basesuc_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_clos1basesuc_3 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf (.classEq C (syn_cun S (syn_cima R C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0003 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cun S (syn_cima R C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
          fresh_x_not_S, fresh_x_not_R, fresh_x_not_C, or_false, not_false_eq_true])
  have p0000 := @g_elima y (.cv x) R C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_orbi2i (.classMem (.cv x) (syn_cima R C))
      (syn_wrex y C (syn_wbr (.cv y) R (.cv x))) (.classMem (.cv x) S) p0000
  have p0002 := @g_elun (.cv x) S (syn_cima R C)
  have p0003 :=
    @g_clos1basesuc y (.cv x) C R S dv_cache_0001 dv_cache_0003 dv_cache_0002
      hyp_clos1basesuc_1 hyp_clos1basesuc_2 hyp_clos1basesuc_3
  have p0004 :=
    @g_n_3bitr4ri (syn_wo (.classMem (.cv x) S) (.classMem (.cv x) (syn_cima R C)))
      (syn_wo (.classMem (.cv x) S) (syn_wrex y C (syn_wbr (.cv y) R (.cv x))))
      (.classMem (.cv x) (syn_cun S (syn_cima R C))) (.classMem (.cv x) C) p0001 p0002
      p0003
  have p0005 := @g_eqriv x C (syn_cun S (syn_cima R C)) dv_cache_0004 dv_cache_0005 p0004
  exact p0005

@[expose]
noncomputable def g_clos1basesucg (x : Var) (A : Class) (C : Class) (R : Class)
    (S : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv)
    (dv_R_x : x ∉ R.fv) (dv_S_x : x ∉ S.fv)
    (hyp_clos1basesucg_1 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem S V) (.classMem R W)) (syn_wb (.classMem A C)
          (syn_wo (.classMem A S) (syn_wrex x C (syn_wbr (.cv x) R A))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ A.fv ∪ C.fv ∪ R.fv ∪ S.fv ∪ V.fv ∪ W.fv
  let s : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_s : x ≠ s := Ne.symm fresh_s_ne_x
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_s_not_S : s ∉ S.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_ne_r : s ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cclos1 (.cv s) (.cv r))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_s, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cclos1 S (.cv r))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, dv_S_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cclos1 S R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          Finset.mem_union, dv_R_x, dv_S_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, dv_R_x, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_r, not_false_eq_true])
  have dv_cache_0007 : s ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_S, not_false_eq_true])
  have dv_cache_0008 : r ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_S, not_false_eq_true])
  have dv_cache_0009 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0010 :
    r ∉
      ((syn_wb (.classMem A (syn_cclos1 S R)) (syn_wo (.classMem A S)
            (syn_wrex x (syn_cclos1 S R) (syn_wbr (.cv x) R A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_not_R, fresh_r_not_S, fresh_r_ne_x,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    s ∉
      ((syn_wb (.classMem A (syn_cclos1 S (.cv r))) (syn_wo (.classMem A S)
            (syn_wrex x (syn_cclos1 S (.cv r)) (syn_wbr (.cv x) (.cv r) A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_s_not_A, fresh_s_ne_r,
          fresh_s_not_S, fresh_s_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have p0000 := @g_clos1eq1 (.cv r) (.cv s) S
  have p0001 :=
    @g_eleq2d (.classEq (.cv s) S) (syn_cclos1 (.cv s) (.cv r)) (syn_cclos1 S (.cv r)) A
      p0000
  have p0002 := @g_eleq2 (.cv s) S A
  have p0003 :=
    @g_rexeqdv (.classEq (.cv s) S) (syn_wbr (.cv x) (.cv r) A) x
      (syn_cclos1 (.cv s) (.cv r)) (syn_cclos1 S (.cv r)) dv_cache_0001 dv_cache_0002
      p0000
  have p0004 :=
    @g_orbi12d (.classEq (.cv s) S) (.classMem A (.cv s)) (.classMem A S)
      (syn_wrex x (syn_cclos1 (.cv s) (.cv r)) (syn_wbr (.cv x) (.cv r) A))
      (syn_wrex x (syn_cclos1 S (.cv r)) (syn_wbr (.cv x) (.cv r) A)) p0002 p0003
  have p0005 :=
    @g_bibi12d (.classEq (.cv s) S) (.classMem A (syn_cclos1 (.cv s) (.cv r)))
      (.classMem A (syn_cclos1 S (.cv r)))
      (syn_wo (.classMem A (.cv s))
        (syn_wrex x (syn_cclos1 (.cv s) (.cv r)) (syn_wbr (.cv x) (.cv r) A)))
      (syn_wo (.classMem A S) (syn_wrex x (syn_cclos1 S (.cv r)) (syn_wbr (.cv x) (.cv r) A)))
      p0001 p0004
  have p0006 := @g_clos1eq2 (.cv r) S R
  have p0007 :=
    @g_eleq2d (.classEq (.cv r) R) (syn_cclos1 S (.cv r)) (syn_cclos1 S R) A p0006
  have p0008 := @g_breq (.cv x) A (.cv r) R
  have p0009 :=
    @g_rexeqbidv (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) A) (syn_wbr (.cv x) R A) x
      (syn_cclos1 S (.cv r)) (syn_cclos1 S R) dv_cache_0002 dv_cache_0003 dv_cache_0004
      p0006 p0008
  have p0010 :=
    @g_orbi2d (.classEq (.cv r) R)
      (syn_wrex x (syn_cclos1 S (.cv r)) (syn_wbr (.cv x) (.cv r) A))
      (syn_wrex x (syn_cclos1 S R) (syn_wbr (.cv x) R A)) (.classMem A S) p0009
  have p0011 :=
    @g_bibi12d (.classEq (.cv r) R) (.classMem A (syn_cclos1 S (.cv r)))
      (.classMem A (syn_cclos1 S R))
      (syn_wo (.classMem A S) (syn_wrex x (syn_cclos1 S (.cv r)) (syn_wbr (.cv x) (.cv r) A)))
      (syn_wo (.classMem A S) (syn_wrex x (syn_cclos1 S R) (syn_wbr (.cv x) R A))) p0007
      p0010
  have p0012 := @g_vex s
  have p0013 := @g_vex r
  have p0014 := @g_eqid (syn_cclos1 (.cv s) (.cv r))
  have p0015 :=
    @g_clos1basesuc x A (syn_cclos1 (.cv s) (.cv r)) (.cv r) (.cv s) dv_cache_0005
      dv_cache_0001 dv_cache_0006 p0012 p0013 p0014
  have p0016 :=
    @g_vtocl2g
      (syn_wb (.classMem A (syn_cclos1 (.cv s) (.cv r))) (syn_wo (.classMem A (.cv s))
          (syn_wrex x (syn_cclos1 (.cv s) (.cv r)) (syn_wbr (.cv x) (.cv r) A))))
      (syn_wb (.classMem A (syn_cclos1 S (.cv r))) (syn_wo (.classMem A S)
          (syn_wrex x (syn_cclos1 S (.cv r)) (syn_wbr (.cv x) (.cv r) A))))
      (syn_wb (.classMem A (syn_cclos1 S R))
        (syn_wo (.classMem A S) (syn_wrex x (syn_cclos1 S R) (syn_wbr (.cv x) R A))))
      s r S R V W dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      p0005 p0011 p0015
  have p0017 := @g_eleq2i C (syn_cclos1 S R) A hyp_clos1basesucg_1
  have p0018 :=
    @g_rexeqi (syn_wbr (.cv x) R A) x C (syn_cclos1 S R) dv_cache_0012 dv_cache_0003
      hyp_clos1basesucg_1
  have p0019 :=
    @g_orbi2i (syn_wrex x C (syn_wbr (.cv x) R A))
      (syn_wrex x (syn_cclos1 S R) (syn_wbr (.cv x) R A)) (.classMem A S) p0018
  have p0020 :=
    @g_n_3bitr4g (syn_wa (.classMem S V) (.classMem R W)) (.classMem A (syn_cclos1 S R))
      (syn_wo (.classMem A S) (syn_wrex x (syn_cclos1 S R) (syn_wbr (.cv x) R A)))
      (.classMem A C) (syn_wo (.classMem A S) (syn_wrex x C (syn_wbr (.cv x) R A))) p0016
      p0017 p0019
  exact p0020

@[expose]
noncomputable def g_clos10 (C : Class) (R : Class)
    (hyp_clos10_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_clos10_2 : Nominal.NPrf (.classEq C (syn_cclos1 (syn_c0) R))) :
    Nominal.NPrf (.classEq C (syn_c0)) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_n_0ex
  have p0001 := @g_n_0ss (syn_c0)
  have p0002 := @g_noel (.cv x)
  have p0003 := @g_pm2_21i (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) (syn_c0)) p0002
  have p0004 :=
    @g_adantr (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) (syn_c0))
      (syn_wbr (.cv x) R (.cv y)) p0003
  have p0005 := Nominal.gen p0004 y
  have p0006 :=
    @g_rgenw
      (.all y (.imp (syn_wa (.classMem (.cv x) (syn_c0)) (syn_wbr (.cv x) R (.cv y)))
          (.classMem (.cv y) (syn_c0))))
      x C p0005
  have p0008 :=
    @g_clos1induct x y C R (syn_c0) (syn_cvv) (syn_c0) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000
      hyp_clos10_1 hyp_clos10_2
  have p0009 :=
    @g_mp3an (.classMem (syn_c0) (syn_cvv)) (syn_wss (syn_c0) (syn_c0))
      (syn_wral x C (.all y
          (.imp (syn_wa (.classMem (.cv x) (syn_c0)) (syn_wbr (.cv x) R (.cv y)))
            (.classMem (.cv y) (syn_c0)))))
      (syn_wss C (syn_c0)) p0000 p0001 p0006 p0008
  have p0010 := @g_n_0ss C
  have p0011 := @g_eqssi C (syn_c0) p0009 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_transex : Nominal.NPrf (.classMem (syn_ctrans) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let q : Var := freshVar proofSupport 5
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_r_ne_z : r ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_r : z ≠ r := Ne.symm fresh_r_ne_z
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have fresh_r_ne_q : r ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_q_ne_r : q ≠ r := Ne.symm fresh_r_ne_q
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have fresh_a_ne_q : a ≠ q :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_q_ne_a : q ≠ a := Ne.symm fresh_a_ne_q
  have dv_cache_0001 : a ≠ r := by exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0005 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0006 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0007 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : y ∉ ((syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_r, fresh_y_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    y ∉
      ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                  (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                (syn_cins2 (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    z ∉
      ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_ne_r, fresh_z_ne_a,
          or_false, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
              (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
            (syn_cins2 (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    z ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    z ∉
      ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((Class.cv r)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_r, not_false_eq_true])
  have dv_cache_0019 :
    q ∉
      ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_y, fresh_q_ne_x, fresh_q_ne_r,
          fresh_q_ne_a, or_false, not_false_eq_true])
  have dv_cache_0020 :
    q ∉
      ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_cop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_y, fresh_q_ne_z, or_false, not_false_eq_true])
  have dv_cache_0022 : q ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_r, not_false_eq_true])
  have dv_cache_0023 :
    y ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, fresh_y_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0024 :
    y ∉
      ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((syn_cop (.cv x) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_r, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((syn_cop (.cv r) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, or_false, not_false_eq_true])
  have dv_cache_0028 :
    x ∉
      ((syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif
                    (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                        (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
            (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 :
    r ∉
      ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                    (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                          (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                  (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                            (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
                (syn_c1c))) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 :
    a ∉
      ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                    (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                          (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                  (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                            (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
                (syn_c1c))) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x y z r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @g_vex r
  have p0002 := @g_vex a
  have p0003 := @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a))
      (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                      (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                        (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
            (syn_c1c))) (syn_c1c))
      p0003
  have p0005 :=
    @g_elin (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                  (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                (syn_cins2 (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
        (syn_c1c))
  have p0006 := @g_otelins2 (syn_csn (.cv x)) (.cv r) (.cv a) (syn_csset) p0001
  have p0007 := @g_vex x
  have p0008 := @g_opelssetsn (.cv x) (.cv a) p0007 p0002
  have p0009_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a)) :=
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
      p0008
  have p0009 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a) p0006
      p0009_e01_recanon
  have p0010 :=
    @g_elima1c y (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
              (syn_cins2 (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
      dv_cache_0011 dv_cache_0012
  have p0011 :=
    @g_elin
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
      (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
              (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
            (syn_cins2 (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))
  have p0012 := @g_snex (.cv x)
  have p0013 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))
      (syn_cins2 (syn_csset)) p0012
  have p0014 := @g_otelins2 (syn_csn (.cv y)) (.cv r) (.cv a) (syn_csset) p0001
  have p0015 := @g_vex y
  have p0016 := @g_opelssetsn (.cv y) (.cv a) p0015 p0002
  have p0017_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a)) :=
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
      p0016
  have p0017 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a) p0013
      p0014 p0017_e02_recanon
  have p0018 :=
    @g_elima1c z
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
      (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
            (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
          (syn_cins2 (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      dv_cache_0013 dv_cache_0014
  have p0019 :=
    @g_elin
      (syn_cop (syn_csn (.cv z))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
        (syn_cins2 (syn_cins4 (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
  have p0020 := @g_snex (.cv y)
  have p0021 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y))
      (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
      (syn_cins2 (syn_cins2 (syn_csset))) p0020
  have p0022 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))
      (syn_cins2 (syn_csset)) p0012
  have p0023 := @g_otelins2 (syn_csn (.cv z)) (.cv r) (.cv a) (syn_csset) p0001
  have p0024 := @g_vex z
  have p0025 := @g_opelssetsn (.cv z) (.cv a) p0024 p0002
  have p0026_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv a)) (syn_csset)) (.objMem z a)) :=
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
      p0025
  have p0026 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv a)) (syn_csset)) (.objMem z a) p0023
      p0026_e01_recanon
  have p0027 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
      (.classMem
        (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.objMem z a) p0021 p0022 p0026
  have p0028 :=
    @g_eldif
      (syn_cop (syn_csn (.cv z))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
      (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
      (syn_cins2 (syn_cins4 (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
  have p0029 :=
    @g_elin
      (syn_cop (syn_csn (.cv z))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
      (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))
  have p0030 := @g_snex (.cv z)
  have p0031 :=
    @g_opelxp (syn_csn (.cv z))
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
      (syn_cvv)
      (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
  have p0032 :=
    @g_mpbiran
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv)
          (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      (.classMem (syn_csn (.cv z)) (syn_cvv))
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
      p0030 p0031
  have p0033 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (.cv a)
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))
      p0002
  have p0034 :=
    @g_elin
      (syn_cop (syn_csn (.cv z))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
      (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_cins2 (syn_cins2 (syn_csset)))
  have p0035 :=
    @g_oqelins4 (syn_csn (.cv z)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r)
      (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0001
  have p0036 :=
    @g_otsnelsi3 (.cv z) (.cv y) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0024 p0015
      p0007
  have p0037 := @g_oteltxp (.cv z) (.cv y) (.cv x) (syn_c2nd) (syn_c1st)
  have p0038 :=
    @g_ancom (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd))
      (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st))
  have p0039 := (Nominal.biimpRefl (syn_wbr (.cv z) (syn_c1st) (.cv x)))
  have p0040 := (Nominal.biimpRefl (syn_wbr (.cv z) (syn_c2nd) (.cv y)))
  have p0041 :=
    @g_anbi12i (syn_wbr (.cv z) (syn_c1st) (.cv x))
      (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st))
      (syn_wbr (.cv z) (syn_c2nd) (.cv y))
      (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd)) p0039 p0040
  have p0042 :=
    @g_bitr4i
      (syn_wa (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd))
        (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st))
        (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd)))
      (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv x)) (syn_wbr (.cv z) (syn_c2nd) (.cv y)))
      p0038 p0041
  have p0043 := @g_op1st2nd (.cv x) (.cv y) (.cv z) p0007 p0015
  have p0044 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd))
        (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st)))
      (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv x)) (syn_wbr (.cv z) (syn_c2nd) (.cv y)))
      (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) p0037 p0042 p0043
  have p0045 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv z))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) p0035 p0036 p0044
  have p0046 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))
      (syn_cins2 (syn_csset)) p0020
  have p0047 := @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0012
  have p0048 := @g_opelssetsn (.cv z) (.cv r) p0024 p0001
  have p0049_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv r)) (syn_csset)) (.objMem z r)) :=
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
      p0048
  have p0049 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv z))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv r)) (syn_csset)) (.objMem z r) p0046
      p0047 p0049_e02_recanon
  have p0050 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv z))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
      (.classMem (syn_cop (syn_csn (.cv z))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem z r) p0045 p0049
  have p0051 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem
          (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)) p0034 p0050
  have p0052 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)) z p0051
  have p0053 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0015 dv_cache_0016
  have p0054 := (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv y)))
  have p0055 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV z
      (syn_cop (.cv x) (.cv y)) (.cv r) dv_cache_0017 dv_cache_0018)
  have p0056_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex z
          (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)))) :=
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
      p0055
  have p0056 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (.cv r))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)))
      p0054 p0056_e01_recanon
  have p0057 :=
    @g_n_3bitr4i
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv y)) p0052 p0053 p0056
  have p0058 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv)
          (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv y)) p0032 p0033 p0057
  have p0059 :=
    @g_elin
      (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
      (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))
  have p0060 := @g_opex (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)) p0012 p0003
  have p0061 :=
    @g_oqelins4 (syn_csn (.cv q)) (syn_csn (.cv z)) (syn_csn (.cv y))
      (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
      (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0060
  have p0062 := @g_vex q
  have p0063 :=
    @g_otsnelsi3 (.cv q) (.cv z) (.cv y) (syn_ctxp (syn_c2nd) (syn_c1st)) p0062 p0024
      p0015
  have p0064 := @g_oteltxp (.cv q) (.cv z) (.cv y) (syn_c2nd) (syn_c1st)
  have p0065 :=
    @g_ancom (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd))
      (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st))
  have p0066 := (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c1st) (.cv y)))
  have p0067 := (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c2nd) (.cv z)))
  have p0068 :=
    @g_anbi12i (syn_wbr (.cv q) (syn_c1st) (.cv y))
      (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st))
      (syn_wbr (.cv q) (syn_c2nd) (.cv z))
      (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd)) p0066 p0067
  have p0069 :=
    @g_bitr4i
      (syn_wa (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd))
        (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st))
        (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd)))
      (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv y)) (syn_wbr (.cv q) (syn_c2nd) (.cv z)))
      p0065 p0068
  have p0070 := @g_op1st2nd (.cv y) (.cv z) (.cv q) p0015 p0024
  have p0071 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv q) (syn_cop (.cv z) (.cv y))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd))
        (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st)))
      (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv y)) (syn_wbr (.cv q) (syn_c2nd) (.cv z)))
      (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) p0064 p0069 p0070
  have p0072 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))))
        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (.classMem (syn_cop (.cv q) (syn_cop (.cv z) (.cv y))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) p0061 p0063 p0071
  have p0073 :=
    @g_otelins2 (syn_csn (.cv q)) (syn_csn (.cv z))
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
      (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0030
  have p0074 :=
    @g_otelins2 (syn_csn (.cv q)) (syn_csn (.cv y))
      (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
      (syn_cins2 (syn_cins3 (syn_csset))) p0020
  have p0075 :=
    @g_otelins2 (syn_csn (.cv q)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))
      (syn_cins3 (syn_csset)) p0012
  have p0076 := @g_otelins3 (syn_csn (.cv q)) (.cv r) (.cv a) (syn_csset) p0002
  have p0077 := @g_opelssetsn (.cv q) (.cv r) p0062 p0001
  have p0078_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv q)) (.cv r)) (syn_csset)) (.objMem q r)) :=
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
      p0077
  have p0078 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins3 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (.cv r) (.cv a))) (syn_cins3 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv q)) (.cv r)) (syn_csset)) (.objMem q r) p0075
      p0076 p0078_e02_recanon
  have p0079 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
        (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))
      (.classMem
        (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins3 (syn_csset))))
      (.objMem q r) p0073 p0074 p0078
  have p0080 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classEq (.cv q) (syn_cop (.cv y) (.cv z)))
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
      (.objMem q r) p0072 p0079
  have p0081 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
              (syn_cop (syn_csn (.cv y))
                (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
          (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem
          (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
                (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
      (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)) p0059 p0080
  have p0082 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
      (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)) q p0081
  have p0083 :=
    @g_elima1c q
      (syn_cop (syn_csn (.cv z))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
      dv_cache_0019 dv_cache_0020
  have p0084 := (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv z)))
  have p0085 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV q
      (syn_cop (.cv y) (.cv z)) (.cv r) dv_cache_0021 dv_cache_0022)
  have p0086_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv y) (.cv z)) (.cv r)) (syn_wex q
          (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)))) :=
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
      p0085
  have p0086 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv z))
      (.classMem (syn_cop (.cv y) (.cv z)) (.cv r))
      (syn_wex q (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)))
      p0084 p0086_e01_recanon
  have p0087 :=
    @g_n_3bitr4i
      (syn_wex q (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z))
              (syn_cop (syn_csn (.cv y))
                (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))))
      (syn_wex q (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv z)) p0082 p0083 p0086
  have p0088 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv)
          (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      (syn_wbr (.cv x) (.cv r) (.cv y))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv z)) p0058 p0087
  have p0089 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cxp (syn_cvv)
            (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv)
            (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (.classMem
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))))
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) p0029
      p0088
  have p0090 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y))
      (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
      (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      p0020
  have p0091 :=
    @g_oqelins4 (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv r) (.cv a)
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))
      p0002
  have p0092 :=
    @g_elin
      (syn_cop (syn_csn (.cv y))
        (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
      (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_cins2 (syn_cins2 (syn_csset)))
  have p0093 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv r)
      (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0001
  have p0094 :=
    @g_otsnelsi3 (.cv y) (.cv z) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0015 p0024
      p0007
  have p0095 :=
    @g_ancom (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd))
      (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st))
  have p0096 := @g_oteltxp (.cv y) (.cv z) (.cv x) (syn_c2nd) (syn_c1st)
  have p0097 := (Nominal.biimpRefl (syn_wbr (.cv y) (syn_c1st) (.cv x)))
  have p0098 := (Nominal.biimpRefl (syn_wbr (.cv y) (syn_c2nd) (.cv z)))
  have p0099 :=
    @g_anbi12i (syn_wbr (.cv y) (syn_c1st) (.cv x))
      (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st))
      (syn_wbr (.cv y) (syn_c2nd) (.cv z))
      (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd)) p0097 p0098
  have p0100 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd))
        (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st))
        (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd)))
      (.classMem (syn_cop (.cv y) (syn_cop (.cv z) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (syn_wbr (.cv y) (syn_c2nd) (.cv z)))
      p0095 p0096 p0099
  have p0101 := @g_op1st2nd (.cv x) (.cv z) (.cv y) p0007 p0024
  have p0102 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv x))))
        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (.classMem (syn_cop (.cv y) (syn_cop (.cv z) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (syn_wbr (.cv y) (syn_c2nd) (.cv z)))
      (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) p0094 p0100 p0101
  have p0103 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv x))))
        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) p0093 p0102
  have p0104 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))
      (syn_cins2 (syn_csset)) p0030
  have p0105 := @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0012
  have p0106 := @g_opelssetsn (.cv y) (.cv r) p0015 p0001
  have p0107_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_csset)) (.objMem y r)) :=
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
      p0106
  have p0107 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_csset)) (.objMem y r) p0104
      p0105 p0107_e02_recanon
  have p0108 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classEq (.cv y) (syn_cop (.cv x) (.cv z)))
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem y r) p0103 p0107
  have p0109 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem
          (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)) p0092 p0108
  have p0110 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)) y p0109
  have p0111 :=
    @g_elima1c y (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0023 dv_cache_0024
  have p0112 := (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv z)))
  have p0113 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y
      (syn_cop (.cv x) (.cv z)) (.cv r) dv_cache_0025 dv_cache_0026)
  have p0114_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv x) (.cv z)) (.cv r)) (syn_wex y
          (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)))) :=
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
      p0113
  have p0114 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv z))
      (.classMem (syn_cop (.cv x) (.cv z)) (.cv r))
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)))
      p0112 p0114_e01_recanon
  have p0115 :=
    @g_n_3bitr4i
      (syn_wex y (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv z)) p0110 p0111 p0114
  have p0116 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4
            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      (.classMem
        (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv z)) p0090 p0091 p0115
  have p0117 :=
    @g_notbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4
            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      (syn_wbr (.cv x) (.cv r) (.cv z)) p0116
  have p0118 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cxp (syn_cvv)
            (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))))
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
      (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      (.neg (syn_wbr (.cv x) (.cv r) (.cv z))) p0089 p0117
  have p0119 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cdif (syn_cin
            (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
          (syn_cins2 (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin
            (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))) (.neg
          (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
                (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))))
      (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
        (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))
      p0028 p0118
  have p0120 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
      (.objMem z a)
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cdif (syn_cin
            (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
          (syn_cins2 (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
        (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))
      p0027 p0119
  have p0121 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
              (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
            (syn_cins2 (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (.classMem (syn_cop (syn_csn (.cv z))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
            (syn_cins2 (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))))
      (syn_wa (.objMem z a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
          (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))))
      p0019 p0120
  have p0122 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
              (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
            (syn_cins2 (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))))
      (syn_wa (.objMem z a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
          (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))))
      z p0121
  have p0123 :=
    (Nominal.biimpRefl (syn_wrex z (.cv a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
          (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))))
  have p0124 :=
    @g_rexanali
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
      (syn_wbr (.cv x) (.cv r) (.cv z)) z (.cv a)
  have p0125_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex z (.cv a) (syn_wa
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))) (syn_wex z (syn_wa (.objMem z a) (syn_wa
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))))) :=
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
      p0123
  have p0125 :=
    @g_bitr3i
      (syn_wex z (syn_wa (.objMem z a) (syn_wa
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))))
      (syn_wrex z (.cv a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
          (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))))
      (.neg (syn_wral z (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (syn_wbr (.cv x) (.cv r) (.cv z)))))
      p0125_e00_recanon p0124
  have p0126 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
              (syn_cins2 (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))
          (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
              (syn_cins2 (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))))
      (syn_wex z (syn_wa (.objMem z a) (syn_wa
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))))
      (.neg (syn_wral z (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (syn_wbr (.cv x) (.cv r) (.cv z)))))
      p0018 p0122 p0125
  have p0127 :=
    @g_anbi12i
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem y a)
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
              (syn_cins2 (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
      (.neg (syn_wral z (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (syn_wbr (.cv x) (.cv r) (.cv z)))))
      p0017 p0126
  have p0128 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                  (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                (syn_cins2 (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                  (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                (syn_cins2 (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))))
      (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      p0011 p0127
  have p0129 :=
    @g_exbii
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                  (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                (syn_cins2 (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))))
      (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      y p0128
  have p0130 :=
    (Nominal.biimpRefl (syn_wrex y (.cv a) (.neg (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z)))))))
  have p0131 :=
    @g_rexnal
      (syn_wral z (.cv a)
        (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
          (syn_wbr (.cv x) (.cv r) (.cv z))))
      y (.cv a)
  have p0132_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex y (.cv a) (.neg (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))) (syn_wex y (syn_wa (.objMem y a) (.neg
              (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y))
                    (syn_wbr (.cv y) (.cv r) (.cv z)))
                  (syn_wbr (.cv x) (.cv r) (.cv z)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wral, syn_wbr, syn_cop, syn_cun,
          syn_cnin, syn_wnan, syn_ccompl]
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
      p0130
  have p0132 :=
    @g_bitr3i
      (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      (syn_wrex y (.cv a) (.neg (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      p0132_e00_recanon p0131
  have p0133 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                    (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                  (syn_cins2 (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
          (syn_c1c)))
      (syn_wex y (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                    (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                  (syn_cins2 (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))))
      (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      p0010 p0129 p0132
  have p0134 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.objMem x a)
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                    (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                  (syn_cins2 (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
          (syn_c1c)))
      (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      p0009 p0133
  have p0135 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
        (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif
                    (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                        (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
            (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
          (syn_cins2 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                      (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                        (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
            (syn_c1c))))
      (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      p0005 p0134
  have p0136 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
        (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif
                    (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                        (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
            (syn_c1c))))
      (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      x p0135
  have p0137 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a))
      (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
            (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif
                  (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                  (syn_cins2 (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
          (syn_c1c)))
      dv_cache_0027 dv_cache_0028
  have p0138 :=
    (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z))))))))
  have p0139_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                  (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                  (syn_wbr (.cv x) (.cv r) (.cv z))))))) (syn_wex x (syn_wa (.objMem x a) (.neg
              (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                    (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                    (syn_wbr (.cv x) (.cv r) (.cv z))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wral]
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
      p0138
  have p0139 :=
    @g_n_3bitr4i
      (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
          (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                  (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                        (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                          (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
              (syn_c1c)))))
      (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                  (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                  (syn_wbr (.cv x) (.cv r) (.cv z))))))))
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                  (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                        (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                          (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      p0136 p0137 p0139_e02_recanon
  have p0140 :=
    @g_rexnal
      (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (syn_wbr (.cv x) (.cv r) (.cv z)))))
      x (.cv a)
  have p0141 :=
    @g_bitri
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                  (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                        (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                          (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      (.neg (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      p0139 p0140
  have p0142 :=
    @g_con2bii
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                  (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                        (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                          (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      p0141
  have p0143 :=
    @g_bitr4i
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima
            (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                    (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                          (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                  (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                            (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
                (syn_c1c))) (syn_c1c))))
      (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset))
              (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                    (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                          (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                  (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                            (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
                (syn_c1c))) (syn_c1c))))
      (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      p0004 p0142
  have p0144 :=
    @g_opabbi2i
      (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      r a
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                  (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                        (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                          (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      dv_cache_0029 dv_cache_0030 dv_cache_0031 p0143
  have p0145 :=
    @g_eqtr4i (syn_ctrans)
      (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
                (syn_wbr (.cv x) (.cv r) (.cv z)))))))
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                  (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                        (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                          (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      p0000 p0144
  have p0146 := @g_ssetex
  have p0147 := @g_ins2ex (syn_csset) p0146
  have p0148 := @g_ins2ex (syn_cins2 (syn_csset)) p0147
  have p0149 := @g_ins2ex (syn_cins2 (syn_cins2 (syn_csset))) p0148
  have p0150 := @g_vvex
  have p0151 := @g_n_2ndex
  have p0152 := @g_n_1stex
  have p0153 := @g_txpex (syn_c2nd) (syn_c1st) p0151 p0152
  have p0154 := @g_si3ex (syn_ctxp (syn_c2nd) (syn_c1st)) p0153
  have p0155 := @g_ins4ex (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0154
  have p0156 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_cins2 (syn_cins2 (syn_csset))) p0155 p0148
  have p0157 := @g_n_1cex
  have p0158 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_c1c) p0156 p0157
  have p0159 :=
    @g_ins4ex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))
      p0158
  have p0160 :=
    @g_xpex (syn_cvv)
      (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      p0150 p0159
  have p0162 := @g_ins3ex (syn_csset) p0146
  have p0163 := @g_ins2ex (syn_cins3 (syn_csset)) p0162
  have p0164 := @g_ins2ex (syn_cins2 (syn_cins3 (syn_csset))) p0163
  have p0165 := @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0164
  have p0166 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) p0155 p0165
  have p0168 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
      (syn_c1c) p0166 p0157
  have p0169 :=
    @g_inex
      (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))
      p0160 p0168
  have p0170 :=
    @g_ins2ex
      (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      p0159
  have p0171 :=
    @g_difex
      (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
      (syn_cins2 (syn_cins4 (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
      p0169 p0170
  have p0172 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
        (syn_cins2 (syn_cins4 (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      p0149 p0171
  have p0174 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
            (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
          (syn_cins2 (syn_cins4 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      (syn_c1c) p0172 p0157
  have p0175 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
              (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
            (syn_cins2 (syn_cins4 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))
      p0148 p0174
  have p0177 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
              (syn_cins2 (syn_cins4 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
      (syn_c1c) p0175 p0157
  have p0178 :=
    @g_inex (syn_cins2 (syn_csset))
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                  (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                (syn_cins2 (syn_cins4 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
        (syn_c1c))
      p0147 p0177
  have p0180 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
            (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif
                  (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))
                  (syn_cins2 (syn_cins4 (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
          (syn_c1c)))
      (syn_c1c) p0178 p0157
  have p0181 :=
    @g_complex
      (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                      (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                        (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
            (syn_c1c))) (syn_c1c))
      p0180
  have p0182 :=
    @g_eqeltri (syn_ctrans)
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima
                  (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin
                        (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin
                                (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
                          (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin
                              (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      (syn_cvv) p0145 p0181
  exact p0182


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_refex : Nominal.NPrf (.classMem (syn_cref) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have fresh_r_ne_p : r ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_r : p ≠ r := Ne.symm fresh_r_ne_p
  have dv_cache_0001 : a ≠ r := by exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0004 : x ∉ ((syn_cop (.cv r) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((syn_ctxp (syn_ccompl
            (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
              (syn_c1c))) (syn_csset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cop (syn_csn (.cv x)) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_r, or_false, not_false_eq_true])
  have dv_cache_0007 :
    p ∉ ((syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_cop (.cv x) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, or_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_r, not_false_eq_true])
  have dv_cache_0010 :
    r ∉
      ((syn_ccompl (syn_cima (syn_ctxp (syn_ccompl
                (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                  (syn_c1c))) (syn_csset)) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    a ∉
      ((syn_ccompl (syn_cima (syn_ctxp (syn_ccompl
                (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                  (syn_c1c))) (syn_csset)) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ref x r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_vex r
  have p0002 := @g_vex a
  have p0003 := @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a))
      (syn_cima (syn_ctxp (syn_ccompl
            (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
              (syn_c1c))) (syn_csset)) (syn_c1c))
      p0003
  have p0005 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a))
      (syn_ctxp (syn_ccompl
          (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))
        (syn_csset))
      dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_oteltxp (syn_csn (.cv x)) (.cv r) (.cv a)
      (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
          (syn_c1c)))
      (syn_csset)
  have p0007 := @g_snex (.cv x)
  have p0008 := @g_opex (syn_csn (.cv x)) (.cv r) p0007 p0001
  have p0009 :=
    @g_elcompl (syn_cop (syn_csn (.cv x)) (.cv r))
      (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))
      p0008
  have p0010 :=
    @g_elima1c p (syn_cop (syn_csn (.cv x)) (.cv r))
      (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) dv_cache_0006
      dv_cache_0007
  have p0011 :=
    @g_oteltxp (syn_csn (.cv p)) (syn_csn (.cv x)) (.cv r)
      (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)
  have p0012 := @g_vex p
  have p0013 := @g_vex x
  have p0014 := @g_opsnelsi (.cv p) (.cv x) (syn_cin (syn_c1st) (syn_c2nd)) p0012 p0013
  have p0015 := @g_elin (syn_cop (.cv p) (.cv x)) (syn_c1st) (syn_c2nd)
  have p0016 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) (.cv x)))
  have p0017 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c2nd) (.cv x)))
  have p0018 :=
    @g_anbi12i (syn_wbr (.cv p) (syn_c1st) (.cv x))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))
      (syn_wbr (.cv p) (syn_c2nd) (.cv x))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_c2nd)) p0016 p0017
  have p0019 := @g_op1st2nd (.cv x) (.cv x) (.cv p) p0013 p0013
  have p0020 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv p) (.cv x)) (syn_cin (syn_c1st) (syn_c2nd)))
      (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))
        (.classMem (syn_cop (.cv p) (.cv x)) (syn_c2nd)))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c2nd) (.cv x)))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) p0015 p0018 p0019
  have p0021 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn (.cv x)))
        (syn_csi (syn_cin (syn_c1st) (syn_c2nd))))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_cin (syn_c1st) (syn_c2nd)))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) p0014 p0020
  have p0022 := @g_opelssetsn (.cv p) (.cv r) p0012 p0001
  have p0023_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r)) :=
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
      p0022
  have p0023 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn (.cv x)))
        (syn_csi (syn_cin (syn_c1st) (syn_c2nd))))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r) p0021
      p0023_e01_recanon
  have p0024 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn (.cv x)))
          (syn_csi (syn_cin (syn_c1st) (syn_c2nd))))
        (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)) p0011 p0023
  have p0025 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)) p p0024
  have p0026 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv r))
        (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))
      (syn_wex p (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r)))
          (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)))
      p0010 p0025
  have p0027 := (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv x)))
  have p0028 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (syn_cop (.cv x) (.cv x)) (.cv r) dv_cache_0008 dv_cache_0009)
  have p0029_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv x) (.cv x)) (.cv r)) (syn_wex p
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)))) :=
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
      p0028
  have p0029 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv x))
      (.classMem (syn_cop (.cv x) (.cv x)) (.cv r))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)))
      p0027 p0029_e01_recanon
  have p0030 :=
    @g_bitr4i
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv r))
        (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)))
      (syn_wbr (.cv x) (.cv r) (.cv x)) p0026 p0029
  have p0031 :=
    @g_xchbinx
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_ccompl
          (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
            (syn_c1c))))
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv r))
        (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv x)) p0009 p0030
  have p0032 := @g_opelssetsn (.cv x) (.cv a) p0013 p0002
  have p0033_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a)) :=
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
      p0032
  have p0033 :=
    @g_anbi12ci
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_ccompl
          (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
            (syn_c1c))))
      (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a) p0031
      p0033_e01_recanon
  have p0034 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl
            (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
              (syn_c1c))) (syn_csset)))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_ccompl
            (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
              (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)))
      (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))) p0006 p0033
  have p0035 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl
            (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
              (syn_c1c))) (syn_csset)))
      (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))) x p0034
  have p0036 :=
    @g_bitri
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl
              (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                (syn_c1c))) (syn_csset)) (syn_c1c)))
      (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_ctxp
            (syn_ccompl
              (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                (syn_c1c))) (syn_csset))))
      (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x))))) p0005
      p0035
  have p0037 :=
    (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))))
  have p0038 := @g_rexnal (syn_wbr (.cv x) (.cv r) (.cv x)) x (.cv a)
  have p0039_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex x (.cv a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x))))
        (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wbr, syn_cop, syn_cun, syn_cnin,
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
      p0037
  have p0039 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl
              (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                (syn_c1c))) (syn_csset)) (syn_c1c)))
      (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))))
      (syn_wrex x (.cv a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x))))
      (.neg (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x)))) p0036
      p0039_e01_recanon p0038
  have p0040 :=
    @g_con2bii
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl
              (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                (syn_c1c))) (syn_csset)) (syn_c1c)))
      (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))) p0039
  have p0041 :=
    @g_bitr4i
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl
                (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                  (syn_c1c))) (syn_csset)) (syn_c1c))))
      (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl
                (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                  (syn_c1c))) (syn_csset)) (syn_c1c))))
      (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))) p0004 p0040
  have p0042 :=
    @g_opabbi2i (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))) r a
      (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl
              (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                (syn_c1c))) (syn_csset)) (syn_c1c)))
      dv_cache_0010 dv_cache_0011 dv_cache_0012 p0041
  have p0043 :=
    @g_eqtr4i (syn_cref)
      (syn_copab r a (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))))
      (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl
              (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                (syn_c1c))) (syn_csset)) (syn_c1c)))
      p0000 p0042
  have p0044 := @g_n_1stex
  have p0045 := @g_n_2ndex
  have p0046 := @g_inex (syn_c1st) (syn_c2nd) p0044 p0045
  have p0047 := @g_siex (syn_cin (syn_c1st) (syn_c2nd)) p0046
  have p0048 := @g_ssetex
  have p0049 := @g_txpex (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset) p0047 p0048
  have p0050 := @g_n_1cex
  have p0051 :=
    @g_imaex (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)
      p0049 p0050
  have p0052 :=
    @g_complex
      (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))
      p0051
  have p0054 :=
    @g_txpex
      (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
          (syn_c1c)))
      (syn_csset) p0052 p0048
  have p0056 :=
    @g_imaex
      (syn_ctxp (syn_ccompl
          (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))
        (syn_csset))
      (syn_c1c) p0054 p0050
  have p0057 :=
    @g_complex
      (syn_cima (syn_ctxp (syn_ccompl
            (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
              (syn_c1c))) (syn_csset)) (syn_c1c))
      p0056
  have p0058 :=
    @g_eqeltri (syn_cref)
      (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl
              (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))
                (syn_c1c))) (syn_csset)) (syn_c1c)))
      (syn_cvv) p0043 p0057
  exact p0058


end NFChoice.DirectNominalPrf.WPPReplay

end
