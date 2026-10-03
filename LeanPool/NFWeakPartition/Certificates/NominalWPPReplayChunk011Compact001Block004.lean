/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk011Compact001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk011Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_imadif (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun (syn_ccnv F)) (.classEq (syn_cima F (syn_cdif A B))
          (syn_cdif (syn_cima F A) (syn_cima F B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_wfun (syn_ccnv F))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_ccnv F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdif A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cima F (syn_cdif A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cdif (syn_cima F A) (syn_cima F B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wfun (syn_ccnv F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_F,
          not_false_eq_true])
  have p0000 :=
    @g_anandir (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))
      (syn_wbr (.cv x) F (.cv y))
  have p0001 :=
    @g_exbii
      (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (syn_wbr (.cv x) F (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))))
      x p0000
  have p0002 :=
    @g_n_19_40 (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
      (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))) x
  have p0003 :=
    @g_sylbi
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (syn_wbr (.cv x) F (.cv y))))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
          (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
        (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y)))))
      p0001 p0002
  have p0004 := @g_nfv (syn_wfun (syn_ccnv F)) x dv_cache_0001
  have p0005 :=
    @g_nfe1 (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))) x
  have p0006 :=
    @g_nfan (syn_wfun (syn_ccnv F))
      (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))) x
      p0004 p0005
  have p0007 := @g_funmo x (.cv y) (syn_ccnv F) dv_cache_0002 dv_cache_0003
  have p0008 := @g_brcnv (.cv y) (.cv x) F
  have p0009 :=
    @g_mobii (syn_wbr (.cv y) (syn_ccnv F) (.cv x)) (syn_wbr (.cv x) F (.cv y)) x p0008
  have p0010 :=
    @g_sylib (syn_wfun (syn_ccnv F)) (syn_wmo x (syn_wbr (.cv y) (syn_ccnv F) (.cv x)))
      (syn_wmo x (syn_wbr (.cv x) F (.cv y))) p0007 p0009
  have p0011 := @g_mopick (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)) x
  have p0012 :=
    @g_sylan (syn_wfun (syn_ccnv F)) (syn_wmo x (syn_wbr (.cv x) F (.cv y)))
      (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))
      (.imp (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))) p0010 p0011
  have p0013 :=
    @g_con2d
      (syn_wa (syn_wfun (syn_ccnv F))
        (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))))
      (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) B) p0012
  have p0014 := @g_imnan (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))
  have p0015 :=
    @g_sylib
      (syn_wa (syn_wfun (syn_ccnv F))
        (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))))
      (.imp (.classMem (.cv x) B) (.neg (syn_wbr (.cv x) F (.cv y))))
      (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) p0013 p0014
  have p0016 :=
    @g_alrimi
      (syn_wa (syn_wfun (syn_ccnv F))
        (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))))
      (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) x p0006 p0015
  have p0017 :=
    @g_ex (syn_wfun (syn_ccnv F))
      (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))
      (.all x (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) p0016
  have p0018 := @g_exancom (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)) x
  have p0019 := @g_alnex (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))) x
  have p0020 :=
    @g_n_3imtr3g (syn_wfun (syn_ccnv F))
      (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))
      (.all x (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))))
      (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) p0017
      p0018 p0019
  have p0021 :=
    @g_anim2d (syn_wfun (syn_ccnv F))
      (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))))
      (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) p0020
  have p0022 :=
    @g_syl5
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (syn_wbr (.cv x) F (.cv y))))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
        (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wfun (syn_ccnv F))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
        (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))))
      p0003 p0021
  have p0023 :=
    @g_n_19_29r (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
      (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) x
  have p0024 :=
    @g_sylan2br
      (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
      (.all x (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
          (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))))
      p0019 p0023
  have p0025 :=
    @g_andi (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
      (.neg (.classMem (.cv x) B)) (.neg (syn_wbr (.cv x) F (.cv y)))
  have p0026 := @g_ianor (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))
  have p0027 :=
    @g_anbi2i (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))
      (syn_wo (.neg (.classMem (.cv x) B)) (.neg (syn_wbr (.cv x) F (.cv y))))
      (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) p0026
  have p0028 :=
    @g_an32 (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))
  have p0029 := @g_pm3_24 (syn_wbr (.cv x) F (.cv y))
  have p0030 :=
    @g_intnan (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (syn_wbr (.cv x) F (.cv y))))
      (.classMem (.cv x) A) p0029
  have p0031 :=
    @g_anass (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))
      (.neg (syn_wbr (.cv x) F (.cv y)))
  have p0032 :=
    @g_mtbir
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (.neg (syn_wbr (.cv x) F (.cv y))))
      (syn_wa (.classMem (.cv x) A)
        (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (syn_wbr (.cv x) F (.cv y)))))
      p0030 p0031
  have p0033 :=
    @g_biorfi
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (.neg (syn_wbr (.cv x) F (.cv y))))
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (.neg (.classMem (.cv x) B)))
      p0032
  have p0034 :=
    @g_bitri
      (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (syn_wbr (.cv x) F (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (.neg (.classMem (.cv x) B)))
      (syn_wo (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
          (.neg (.classMem (.cv x) B)))
        (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
          (.neg (syn_wbr (.cv x) F (.cv y)))))
      p0028 p0033
  have p0035 :=
    @g_n_3bitr4i
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (syn_wo (.neg (.classMem (.cv x) B)) (.neg (syn_wbr (.cv x) F (.cv y)))))
      (syn_wo (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
          (.neg (.classMem (.cv x) B)))
        (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
          (.neg (syn_wbr (.cv x) F (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (syn_wbr (.cv x) F (.cv y)))
      p0025 p0027 p0034
  have p0036 :=
    @g_exbii
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
        (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (syn_wbr (.cv x) F (.cv y)))
      x p0035
  have p0037 :=
    @g_sylib
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
        (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))
          (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (syn_wbr (.cv x) F (.cv y))))
      p0024 p0036
  have p0038 :=
    @g_impbid1 (syn_wfun (syn_ccnv F))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (syn_wbr (.cv x) F (.cv y))))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
        (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))))
      p0022 p0037
  have p0039 :=
    @g_elima2 x (.cv y) F (syn_cdif A B) dv_cache_0002 dv_cache_0004 dv_cache_0005
  have p0040 := @g_eldif (.cv x) A B
  have p0041 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdif A B))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (syn_wbr (.cv x) F (.cv y)) p0040
  have p0042 :=
    @g_exbii (syn_wa (.classMem (.cv x) (syn_cdif A B)) (syn_wbr (.cv x) F (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (syn_wbr (.cv x) F (.cv y)))
      x p0041
  have p0043 :=
    @g_bitri (.classMem (.cv y) (syn_cima F (syn_cdif A B)))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_cdif A B)) (syn_wbr (.cv x) F (.cv y))))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (syn_wbr (.cv x) F (.cv y))))
      p0039 p0042
  have p0044 := @g_eldif (.cv y) (syn_cima F A) (syn_cima F B)
  have p0045 := @g_elima2 x (.cv y) F A dv_cache_0002 dv_cache_0004 dv_cache_0006
  have p0046 := @g_elima2 x (.cv y) F B dv_cache_0002 dv_cache_0004 dv_cache_0007
  have p0047 :=
    @g_notbii (.classMem (.cv y) (syn_cima F B))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) p0046
  have p0048 :=
    @g_anbi12i (.classMem (.cv y) (syn_cima F A))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
      (.neg (.classMem (.cv y) (syn_cima F B)))
      (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) p0045
      p0047
  have p0049 :=
    @g_bitri (.classMem (.cv y) (syn_cdif (syn_cima F A) (syn_cima F B)))
      (syn_wa (.classMem (.cv y) (syn_cima F A)) (.neg (.classMem (.cv y) (syn_cima F B))))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
        (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))))
      p0044 p0048
  have p0050 :=
    @g_n_3bitr4g (syn_wfun (syn_ccnv F))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (syn_wbr (.cv x) F (.cv y))))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
        (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))))
      (.classMem (.cv y) (syn_cima F (syn_cdif A B)))
      (.classMem (.cv y) (syn_cdif (syn_cima F A) (syn_cima F B))) p0038 p0043 p0049
  have p0051 :=
    @g_eqrdv (syn_wfun (syn_ccnv F)) y (syn_cima F (syn_cdif A B))
      (syn_cdif (syn_cima F A) (syn_cima F B)) dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0050
  exact p0051

@[expose]
noncomputable def g_imain (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun (syn_ccnv F))
        (.classEq (syn_cima F (syn_cin A B)) (syn_cin (syn_cima F A) (syn_cima F B)))) :=
  by
  have p0000 := @g_imadif A (syn_cdif A B) F
  have p0001 := @g_imadif A B F
  have p0002 :=
    @g_difeq2d (syn_wfun (syn_ccnv F)) (syn_cima F (syn_cdif A B))
      (syn_cdif (syn_cima F A) (syn_cima F B)) (syn_cima F A) p0001
  have p0003 :=
    @g_eqtrd (syn_wfun (syn_ccnv F)) (syn_cima F (syn_cdif A (syn_cdif A B)))
      (syn_cdif (syn_cima F A) (syn_cima F (syn_cdif A B)))
      (syn_cdif (syn_cima F A) (syn_cdif (syn_cima F A) (syn_cima F B))) p0000 p0002
  have p0004 := @g_dfin4 A B
  have p0005 := @g_imaeq2i (syn_cin A B) (syn_cdif A (syn_cdif A B)) F p0004
  have p0006 := @g_dfin4 (syn_cima F A) (syn_cima F B)
  have p0007 :=
    @g_n_3eqtr4g (syn_wfun (syn_ccnv F)) (syn_cima F (syn_cdif A (syn_cdif A B)))
      (syn_cdif (syn_cima F A) (syn_cdif (syn_cima F A) (syn_cima F B)))
      (syn_cima F (syn_cin A B)) (syn_cin (syn_cima F A) (syn_cima F B)) p0003 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_fneq1 (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wfn F A) (syn_wfn G A))) :=
  by
  have p0000 := @g_funeq F G
  have p0001 := @g_dmeq F G
  have p0002 := @g_eqeq1d (.classEq F G) (syn_cdm F) (syn_cdm G) A p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wfun F) (syn_wfun G) (.classEq (syn_cdm F) A)
      (.classEq (syn_cdm G) A) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wfn F A))
  have p0005 := (Nominal.biimpRefl (syn_wfn G A))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A))
      (syn_wa (syn_wfun G) (.classEq (syn_cdm G) A)) (syn_wfn F A) (syn_wfn G A) p0003
      p0004 p0005
  exact p0006

@[expose]
noncomputable def g_fneq2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfn F A) (syn_wfn F B))) :=
  by
  have p0000 := @g_eqeq2 A B (syn_cdm F)
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classEq (syn_cdm F) A) (.classEq (syn_cdm F) B)
      (syn_wfun F) p0000
  have p0002 := (Nominal.biimpRefl (syn_wfn F A))
  have p0003 := (Nominal.biimpRefl (syn_wfn F B))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A))
      (syn_wa (syn_wfun F) (.classEq (syn_cdm F) B)) (syn_wfn F A) (syn_wfn F B) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fneq1d (ph : Wff) (A : Class) (F : Class) (G : Class)
    (hyp_fneq1d_1 : Nominal.NPrf (.imp ph (.classEq F G))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wfn F A) (syn_wfn G A))) :=
  by
  have p0000 := @g_fneq1 A F G
  have p0001 :=
    @g_syl ph (.classEq F G) (syn_wb (syn_wfn F A) (syn_wfn G A)) hyp_fneq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_fneq2d (ph : Wff) (A : Class) (B : Class) (F : Class)
    (hyp_fneq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wfn F A) (syn_wfn F B))) :=
  by
  have p0000 := @g_fneq2 A B F
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wfn F A) (syn_wfn F B)) hyp_fneq2d_1 p0000
  exact p0001

@[expose]
noncomputable def g_fneq1i (A : Class) (F : Class) (G : Class)
    (hyp_fneq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wfn G A)) :=
  by
  have p0000 := @g_fneq1 A F G
  have p0001 := Nominal.mp hyp_fneq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_fneq2i (A : Class) (B : Class) (F : Class)
    (hyp_fneq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wfn F B)) :=
  by
  have p0000 := @g_fneq2 A B F
  have p0001 := Nominal.mp hyp_fneq2i_1 p0000
  exact p0001

@[expose]
noncomputable def g_fnfun (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wfun F)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wfn F A))
  have p0001 := @g_simplbi (syn_wfn F A) (syn_wfun F) (.classEq (syn_cdm F) A) p0000
  exact p0001

@[expose]
noncomputable def g_fndm (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (.classEq (syn_cdm F) A)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wfn F A))
  have p0001 := @g_simprbi (syn_wfn F A) (syn_wfun F) (.classEq (syn_cdm F) A) p0000
  exact p0001

@[expose]
noncomputable def g_funfni (ph : Wff) (A : Class) (B : Class) (F : Class)
    (hyp_funfni_1 : Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem B (syn_cdm F))) ph)) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) ph) :=
  by
  have p0000 := @g_fnfun A F
  have p0001 := @g_adantr (syn_wfn F A) (syn_wfun F) (.classMem B A) p0000
  have p0002 := @g_fndm A F
  have p0003 := @g_eleq2d (syn_wfn F A) (syn_cdm F) A B p0002
  have p0004 := @g_biimpar (syn_wfn F A) (.classMem B (syn_cdm F)) (.classMem B A) p0003
  have p0005 :=
    @g_syl2anc (syn_wa (syn_wfn F A) (.classMem B A)) (syn_wfun F)
      (.classMem B (syn_cdm F)) ph p0001 p0004 hyp_funfni_1
  exact p0005

@[expose]
noncomputable def g_fnbr (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wbr B F C)) (.classMem B A)) :=
  by
  have p0000 := @g_fndm A F
  have p0001 := @g_breldm B C F
  have p0002 :=
    @g_adantl (syn_wbr B F C) (.classMem B (syn_cdm F)) (.classEq (syn_cdm F) A) p0001
  have p0003 := @g_simpl (.classEq (syn_cdm F) A) (syn_wbr B F C)
  have p0004 :=
    @g_eleqtrd (syn_wa (.classEq (syn_cdm F) A) (syn_wbr B F C)) B (syn_cdm F) A p0002
      p0003
  have p0005 :=
    @g_sylan (syn_wfn F A) (.classEq (syn_cdm F) A) (syn_wbr B F C) (.classMem B A) p0000
      p0004
  exact p0005

@[expose]
noncomputable def g_fnop (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem (syn_cop B C) F)) (.classMem B A)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr B F C))
  have p0001 := @g_fnbr A B C F
  have p0002 :=
    @g_sylan2br (.classMem (syn_cop B C) F) (syn_wfn F A) (syn_wbr B F C) (.classMem B A)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fneu (y : Var) (A : Class) (B : Class) (F : Class) (dv_B_y : y ∉ B.fv)
    (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (syn_weu y (syn_wbr B F (.cv y)))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, dv_B_y, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ ((syn_cdm F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0006 :
    x ∉ ((Wff.imp (syn_wfun F) (syn_weu y (syn_wbr B F (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_F, fresh_x_not_B, fresh_x_ne_y, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_breq1 (.cv x) B (.cv y) F
  have p0001 :=
    @g_eubidv (.classEq (.cv x) B) (syn_wbr (.cv x) F (.cv y)) (syn_wbr B F (.cv y)) y
      dv_cache_0001 p0000
  have p0002 :=
    @g_imbi2d (.classEq (.cv x) B) (syn_weu y (syn_wbr (.cv x) F (.cv y)))
      (syn_weu y (syn_wbr B F (.cv y))) (syn_wfun F) p0001
  have p0003 := @g_eldm y (.cv x) F dv_cache_0002 dv_cache_0003
  have p0004 := @g_funmo y (.cv x) F dv_cache_0002 dv_cache_0003
  have p0005 := @g_exmoeu2 (syn_wbr (.cv x) F (.cv y)) y
  have p0006 :=
    @g_syl5ib (syn_wfun F) (syn_wmo y (syn_wbr (.cv x) F (.cv y)))
      (syn_wex y (syn_wbr (.cv x) F (.cv y))) (syn_weu y (syn_wbr (.cv x) F (.cv y)))
      p0004 p0005
  have p0007 :=
    @g_sylbi (.classMem (.cv x) (syn_cdm F)) (syn_wex y (syn_wbr (.cv x) F (.cv y)))
      (.imp (syn_wfun F) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) p0003 p0006
  have p0008 :=
    @g_vtoclga (.imp (syn_wfun F) (syn_weu y (syn_wbr (.cv x) F (.cv y))))
      (.imp (syn_wfun F) (syn_weu y (syn_wbr B F (.cv y)))) x B (syn_cdm F) dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0002 p0007
  have p0009 :=
    @g_impcom (.classMem B (syn_cdm F)) (syn_wfun F) (syn_weu y (syn_wbr B F (.cv y)))
      p0008
  have p0010 := @g_funfni (syn_weu y (syn_wbr B F (.cv y))) A B F p0009
  exact p0010

@[expose]
noncomputable def g_fneu2 (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_B_y : y ∉ B.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem B A))
        (syn_weu y (.classMem (syn_cop B (.cv y)) F))) :=
  by
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have p0000 := @g_fneu y A B F dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.biimpRefl (syn_wbr B F (.cv y)))
  have p0002 := @g_eubii (syn_wbr B F (.cv y)) (.classMem (syn_cop B (.cv y)) F) y p0001
  have p0003 :=
    @g_sylib (syn_wa (syn_wfn F A) (.classMem B A)) (syn_weu y (syn_wbr B F (.cv y)))
      (syn_weu y (.classMem (syn_cop B (.cv y)) F)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_fnun (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0)))
        (syn_wfn (syn_cun F G) (syn_cun A B))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wfn F A))
  have p0001 := (Nominal.biimpRefl (syn_wfn G B))
  have p0002 := @g_ineq12 (syn_cdm F) A (syn_cdm G) B
  have p0003 :=
    @g_eqeq1d (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin A B) (syn_c0) p0002
  have p0004 :=
    @g_anbi2d (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.classEq (syn_cin A B) (syn_c0)) (syn_wa (syn_wfun F) (syn_wfun G)) p0003
  have p0005 := @g_funun F G
  have p0006 :=
    @g_syl6bir (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (syn_wfun (syn_cun F G)) p0004 p0005
  have p0007 := @g_dmun F G
  have p0008 := @g_uneq12 (syn_cdm F) A (syn_cdm G) B
  have p0009 :=
    @g_syl5eq (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_cdm (syn_cun F G)) (syn_cun (syn_cdm F) (syn_cdm G)) (syn_cun A B) p0007 p0008
  have p0010 :=
    @g_jctird (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfun (syn_cun F G)) (.classEq (syn_cdm (syn_cun F G)) (syn_cun A B)) p0006
      p0009
  have p0011 := (Nominal.biimpRefl (syn_wfn (syn_cun F G) (syn_cun A B)))
  have p0012 :=
    @g_syl6ibr (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wa (syn_wfun (syn_cun F G)) (.classEq (syn_cdm (syn_cun F G)) (syn_cun A B)))
      (syn_wfn (syn_cun F G) (syn_cun A B)) p0010 p0011
  have p0013 :=
    @g_exp3a (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0))
      (syn_wfn (syn_cun F G) (syn_cun A B)) p0012
  have p0014 :=
    @g_impcom (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_wa (syn_wfun F) (syn_wfun G))
      (.imp (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B))) p0013
  have p0015 :=
    @g_an4s (syn_wfun F) (syn_wfun G) (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)
      (.imp (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B))) p0014
  have p0016 :=
    @g_syl2anb (syn_wfn F A) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A))
      (syn_wa (syn_wfun G) (.classEq (syn_cdm G) B))
      (.imp (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B)))
      (syn_wfn G B) p0000 p0001 p0015
  have p0017 :=
    @g_imp (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0))
      (syn_wfn (syn_cun F G) (syn_cun A B)) p0016
  exact p0017

@[expose]
noncomputable def g_fnco (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A))
        (syn_wfn (syn_ccom F G) B)) :=
  by
  have p0000 := @g_fnfun A F
  have p0001 := @g_fnfun B G
  have p0002 := @g_funco F G
  have p0003 :=
    @g_syl2an (syn_wfn F A) (syn_wfun F) (syn_wfun G) (syn_wfun (syn_ccom F G))
      (syn_wfn G B) p0000 p0001 p0002
  have p0004 :=
    @g_n_3adant3 (syn_wfn F A) (syn_wfn G B) (syn_wfun (syn_ccom F G))
      (syn_wss (syn_crn G) A) p0003
  have p0005 := @g_fndm A F
  have p0006 := @g_sseq2d (syn_wfn F A) (syn_cdm F) A (syn_crn G) p0005
  have p0007 :=
    @g_biimpar (syn_wfn F A) (syn_wss (syn_crn G) (syn_cdm F)) (syn_wss (syn_crn G) A)
      p0006
  have p0008 := @g_dmcosseq F G
  have p0009 :=
    @g_syl (syn_wa (syn_wfn F A) (syn_wss (syn_crn G) A))
      (syn_wss (syn_crn G) (syn_cdm F)) (.classEq (syn_cdm (syn_ccom F G)) (syn_cdm G))
      p0007 p0008
  have p0010 :=
    @g_n_3adant2 (syn_wfn F A) (syn_wss (syn_crn G) A)
      (.classEq (syn_cdm (syn_ccom F G)) (syn_cdm G)) (syn_wfn G B) p0009
  have p0011 := @g_fndm B G
  have p0012 :=
    @g_n_3ad2ant2 (syn_wfn G B) (syn_wfn F A) (.classEq (syn_cdm G) B)
      (syn_wss (syn_crn G) A) p0011
  have p0013 :=
    @g_eqtrd (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A))
      (syn_cdm (syn_ccom F G)) (syn_cdm G) B p0010 p0012
  have p0014 := (Nominal.biimpRefl (syn_wfn (syn_ccom F G) B))
  have p0015 :=
    @g_sylanbrc (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A))
      (syn_wfun (syn_ccom F G)) (.classEq (syn_cdm (syn_ccom F G)) B)
      (syn_wfn (syn_ccom F G) B) p0004 p0013 p0014
  exact p0015

@[expose]
noncomputable def g_fnresdm (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (.classEq (syn_cres F A) F)) :=
  by
  have p0000 := @g_fndm A F
  have p0001 := @g_eqimss (syn_cdm F) A
  have p0002 := @g_ssreseq F A
  have p0003 :=
    @g_n_3syl (syn_wfn F A) (.classEq (syn_cdm F) A) (syn_wss (syn_cdm F) A)
      (.classEq (syn_cres F A) F) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fnssresb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wb (syn_wfn (syn_cres F B) B) (syn_wss B A))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wfn (syn_cres F B) B))
  have p0001 := @g_fnfun A F
  have p0002 := @g_funres B F
  have p0003 := @g_syl (syn_wfn F A) (syn_wfun F) (syn_wfun (syn_cres F B)) p0001 p0002
  have p0004 :=
    @g_biantrurd (syn_wfn F A) (syn_wfun (syn_cres F B))
      (.classEq (syn_cdm (syn_cres F B)) B) p0003
  have p0005 := @g_ssdmres B F
  have p0006 := @g_fndm A F
  have p0007 := @g_sseq2d (syn_wfn F A) (syn_cdm F) A B p0006
  have p0008 :=
    @g_syl5bbr (.classEq (syn_cdm (syn_cres F B)) B) (syn_wss B (syn_cdm F)) (syn_wfn F A)
      (syn_wss B A) p0005 p0007
  have p0009 :=
    @g_bitr3d (syn_wfn F A) (.classEq (syn_cdm (syn_cres F B)) B)
      (syn_wa (syn_wfun (syn_cres F B)) (.classEq (syn_cdm (syn_cres F B)) B))
      (syn_wss B A) p0004 p0008
  have p0010 :=
    @g_syl5bb (syn_wfn (syn_cres F B) B)
      (syn_wa (syn_wfun (syn_cres F B)) (.classEq (syn_cdm (syn_cres F B)) B))
      (syn_wfn F A) (syn_wss B A) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_fnssres (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wfn (syn_cres F B) B)) :=
  by
  have p0000 := @g_fnssresb A B F
  have p0001 := @g_biimpar (syn_wfn F A) (syn_wfn (syn_cres F B) B) (syn_wss B A) p0000
  exact p0001

@[expose]
noncomputable def g_fnresin1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfn F A) (syn_wfn (syn_cres F (syn_cin A B)) (syn_cin A B))) :=
  by
  have p0000 := @g_inss1 A B
  have p0001 := @g_fnssres A (syn_cin A B) F
  have p0002 :=
    @g_mpan2 (syn_wfn F A) (syn_wss (syn_cin A B) A)
      (syn_wfn (syn_cres F (syn_cin A B)) (syn_cin A B)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fnres (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wfn (syn_cres F A) A)
        (syn_wral x A (syn_weu y (syn_wbr (.cv x) F (.cv y))))) :=
  by
  have dv_cache_0001 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cres F A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, dv_F_x, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cres F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, dv_F_y, dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
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
  have dv_cache_0006 : x ∉ ((syn_cdm (syn_cres F A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, dv_F_x,
          dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0008 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have p0000 :=
    @g_ancom (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y))))
      (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y))))
  have p0001 := @g_brres (.cv x) (.cv y) F A
  have p0002 := @g_ancom (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) A)
  have p0003 :=
    @g_bitri (syn_wbr (.cv x) (syn_cres F A) (.cv y))
      (syn_wa (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) A))
      (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) p0001 p0002
  have p0004 :=
    @g_mobii (syn_wbr (.cv x) (syn_cres F A) (.cv y))
      (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) y p0003
  have p0005 :=
    @g_moanimv (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)) y dv_cache_0001
  have p0006 :=
    @g_bitri (syn_wmo y (syn_wbr (.cv x) (syn_cres F A) (.cv y)))
      (syn_wmo y (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))))
      (.imp (.classMem (.cv x) A) (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) p0004 p0005
  have p0007 :=
    @g_albii (syn_wmo y (syn_wbr (.cv x) (syn_cres F A) (.cv y)))
      (.imp (.classMem (.cv x) A) (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) x p0006
  have p0008 := @g_dffun6 x y (syn_cres F A) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0009 := (Nominal.biimpRefl (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y)))))
  have p0010 :=
    @g_n_3bitr4i (.all x (syn_wmo y (syn_wbr (.cv x) (syn_cres F A) (.cv y))))
      (.all x (.imp (.classMem (.cv x) A) (syn_wmo y (syn_wbr (.cv x) F (.cv y)))))
      (syn_wfun (syn_cres F A)) (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y))))
      p0007 p0008 p0009
  have p0011 := @g_dmres F A
  have p0012 := @g_inss1 A (syn_cdm F)
  have p0013 := @g_eqsstri (syn_cdm (syn_cres F A)) (syn_cin A (syn_cdm F)) A p0011 p0012
  have p0014 := @g_eqss (syn_cdm (syn_cres F A)) A
  have p0015 :=
    @g_mpbiran (.classEq (syn_cdm (syn_cres F A)) A) (syn_wss (syn_cdm (syn_cres F A)) A)
      (syn_wss A (syn_cdm (syn_cres F A))) p0013 p0014
  have p0016 := @g_dfss3 x A (syn_cdm (syn_cres F A)) dv_cache_0005 dv_cache_0006
  have p0017 := @g_elin2 (.cv x) A (syn_cdm F) (syn_cdm (syn_cres F A)) p0011
  have p0018 :=
    @g_baib (.classMem (.cv x) (syn_cdm (syn_cres F A))) (.classMem (.cv x) A)
      (.classMem (.cv x) (syn_cdm F)) p0017
  have p0019 := @g_eldm y (.cv x) F dv_cache_0007 dv_cache_0008
  have p0020 :=
    @g_syl6bb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cdm (syn_cres F A)))
      (.classMem (.cv x) (syn_cdm F)) (syn_wex y (syn_wbr (.cv x) F (.cv y))) p0018 p0019
  have p0021 :=
    @g_ralbiia (.classMem (.cv x) (syn_cdm (syn_cres F A)))
      (syn_wex y (syn_wbr (.cv x) F (.cv y))) x A p0020
  have p0022 :=
    @g_n_3bitri (.classEq (syn_cdm (syn_cres F A)) A) (syn_wss A (syn_cdm (syn_cres F A)))
      (syn_wral x A (.classMem (.cv x) (syn_cdm (syn_cres F A))))
      (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y)))) p0015 p0016 p0021
  have p0023 :=
    @g_anbi12i (syn_wfun (syn_cres F A))
      (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y))))
      (.classEq (syn_cdm (syn_cres F A)) A)
      (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y)))) p0010 p0022
  have p0024 :=
    @g_r19_26 (syn_wex y (syn_wbr (.cv x) F (.cv y)))
      (syn_wmo y (syn_wbr (.cv x) F (.cv y))) x A
  have p0025 :=
    @g_n_3bitr4i
      (syn_wa (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y))))
        (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y)))))
      (syn_wa (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y))))
        (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y)))))
      (syn_wa (syn_wfun (syn_cres F A)) (.classEq (syn_cdm (syn_cres F A)) A))
      (syn_wral x A (syn_wa (syn_wex y (syn_wbr (.cv x) F (.cv y)))
          (syn_wmo y (syn_wbr (.cv x) F (.cv y)))))
      p0000 p0023 p0024
  have p0026 := (Nominal.biimpRefl (syn_wfn (syn_cres F A) A))
  have p0027 := @g_eu5 (syn_wbr (.cv x) F (.cv y)) y
  have p0028 :=
    @g_ralbii (syn_weu y (syn_wbr (.cv x) F (.cv y)))
      (syn_wa (syn_wex y (syn_wbr (.cv x) F (.cv y))) (syn_wmo y (syn_wbr (.cv x) F (.cv y))))
      x A p0027
  have p0029 :=
    @g_n_3bitr4i (syn_wa (syn_wfun (syn_cres F A)) (.classEq (syn_cdm (syn_cres F A)) A))
      (syn_wral x A (syn_wa (syn_wex y (syn_wbr (.cv x) F (.cv y)))
          (syn_wmo y (syn_wbr (.cv x) F (.cv y)))))
      (syn_wfn (syn_cres F A) A) (syn_wral x A (syn_weu y (syn_wbr (.cv x) F (.cv y))))
      p0025 p0026 p0028
  exact p0029

@[expose]
noncomputable def g_fnresi (A : Class) :
    Nominal.NPrf (syn_wfn (syn_cres (syn_cid) A) A) :=
  by
  have p0000 := @g_funi
  have p0001 := @g_funres A (syn_cid)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_dmresi A
  have p0004 := (Nominal.biimpRefl (syn_wfn (syn_cres (syn_cid) A) A))
  have p0005 :=
    @g_mpbir2an (syn_wfn (syn_cres (syn_cid) A) A) (syn_wfun (syn_cres (syn_cid) A))
      (.classEq (syn_cdm (syn_cres (syn_cid) A)) A) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_fn0 (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F (syn_c0)) (.classEq F (syn_c0))) :=
  by
  have p0000 := @g_fndm (syn_c0) F
  have p0001 := @g_dmeq0 F
  have p0002 :=
    @g_sylibr (syn_wfn F (syn_c0)) (.classEq (syn_cdm F) (syn_c0)) (.classEq F (syn_c0))
      p0000 p0001
  have p0003 := @g_fun0
  have p0004 := @g_dm0
  have p0005 := (Nominal.biimpRefl (syn_wfn (syn_c0) (syn_c0)))
  have p0006 :=
    @g_mpbir2an (syn_wfn (syn_c0) (syn_c0)) (syn_wfun (syn_c0))
      (.classEq (syn_cdm (syn_c0)) (syn_c0)) p0003 p0004 p0005
  have p0007 := @g_fneq1 (syn_c0) F (syn_c0)
  have p0008 :=
    @g_mpbiri (.classEq F (syn_c0)) (syn_wfn F (syn_c0)) (syn_wfn (syn_c0) (syn_c0)) p0006
      p0007
  have p0009 := @g_impbii (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) p0002 p0008
  exact p0009

@[expose]
noncomputable def g_fnopabg (ph : Wff) (x : Var) (y : Var) (A : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_fnopabg_1 :
      Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))) :
    Nominal.NPrf (syn_wb (syn_wral x A (syn_weu y ph)) (syn_wfn F A)) :=
  by
  have dv_cache_0001 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have p0000 := @g_moanimv (.classMem (.cv x) A) ph y dv_cache_0001
  have p0001 :=
    @g_albii (syn_wmo y (syn_wa (.classMem (.cv x) A) ph))
      (.imp (.classMem (.cv x) A) (syn_wmo y ph)) x p0000
  have p0002 := @g_funopab (syn_wa (.classMem (.cv x) A) ph) x y dv_cache_0002
  have p0003 := (Nominal.biimpRefl (syn_wral x A (syn_wmo y ph)))
  have p0004 :=
    @g_n_3bitr4ri (.all x (syn_wmo y (syn_wa (.classMem (.cv x) A) ph)))
      (.all x (.imp (.classMem (.cv x) A) (syn_wmo y ph)))
      (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))
      (syn_wral x A (syn_wmo y ph)) p0001 p0002 p0003
  have p0005 := @g_dmopab3 ph x y A dv_cache_0003 dv_cache_0004 dv_cache_0002
  have p0006 :=
    @g_anbi12i (syn_wral x A (syn_wmo y ph))
      (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))
      (syn_wral x A (syn_wex y ph))
      (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A) p0004 p0005
  have p0007 := @g_r19_26 (syn_wmo y ph) (syn_wex y ph) x A
  have p0008 :=
    (Nominal.biimpRefl (syn_wfn (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) A))
  have p0009 :=
    @g_n_3bitr4i (syn_wa (syn_wral x A (syn_wmo y ph)) (syn_wral x A (syn_wex y ph)))
      (syn_wa (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))
        (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A))
      (syn_wral x A (syn_wa (syn_wmo y ph) (syn_wex y ph)))
      (syn_wfn (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) A) p0006 p0007 p0008
  have p0010 := @g_eu5 ph y
  have p0011 := @g_ancom (syn_wex y ph) (syn_wmo y ph)
  have p0012 :=
    @g_bitri (syn_weu y ph) (syn_wa (syn_wex y ph) (syn_wmo y ph))
      (syn_wa (syn_wmo y ph) (syn_wex y ph)) p0010 p0011
  have p0013 := @g_ralbii (syn_weu y ph) (syn_wa (syn_wmo y ph) (syn_wex y ph)) x A p0012
  have p0014 :=
    @g_fneq1i A F (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) hyp_fnopabg_1
  have p0015 :=
    @g_n_3bitr4i (syn_wral x A (syn_wa (syn_wmo y ph) (syn_wex y ph)))
      (syn_wfn (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) A)
      (syn_wral x A (syn_weu y ph)) (syn_wfn F A) p0009 p0013 p0014
  exact p0015

@[expose]
noncomputable def g_fnopab2g (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fnopab2g_1 : Nominal.NPrf (.classEq F
          (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))) :
    Nominal.NPrf (syn_wb (syn_wral x A (.classMem B (syn_cvv))) (syn_wfn F A)) :=
  by
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_eueq y B dv_cache_0001
  have p0001 :=
    @g_ralbii (.classMem B (syn_cvv)) (syn_weu y (.classEq (.cv y) B)) x A p0000
  have p0002 :=
    @g_fnopabg (.classEq (.cv y) B) x y A F dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_fnopab2g_1
  have p0003 :=
    @g_bitri (syn_wral x A (.classMem B (syn_cvv)))
      (syn_wral x A (syn_weu y (.classEq (.cv y) B))) (syn_wfn F A) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fnopab (ph : Wff) (x : Var) (y : Var) (A : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_fnopab_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (syn_weu y ph)))
    (hyp_fnopab_2 :
      Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))) :
    Nominal.NPrf (syn_wfn F A) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_rgen (syn_weu y ph) x A hyp_fnopab_1
  have p0001 :=
    @g_fnopabg ph x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fnopab_2
  have p0002 := @g_mpbi (syn_wral x A (syn_weu y ph)) (syn_wfn F A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fnopab2 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fnopab2_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_fnopab2_2 : Nominal.NPrf (.classEq F
          (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))) :
    Nominal.NPrf (syn_wfn F A) :=
  by
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_eueq1 y B dv_cache_0001 hyp_fnopab2_1
  have p0001 := @g_a1i (syn_weu y (.classEq (.cv y) B)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_fnopab (.classEq (.cv y) B) x y A F dv_cache_0002 dv_cache_0003 dv_cache_0004 p0001
      hyp_fnopab2_2
  exact p0002

@[expose]
noncomputable def g_feq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wf F A B) (syn_wf G A B))) :=
  by
  have p0000 := @g_fneq1 A F G
  have p0001 := @g_rneq F G
  have p0002 := @g_sseq1d (.classEq F G) (syn_crn F) (syn_crn G) B p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wfn F A) (syn_wfn G A) (syn_wss (syn_crn F) B)
      (syn_wss (syn_crn G) B) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wf F A B))
  have p0005 := (Nominal.biimpRefl (syn_wf G A B))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B))
      (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) (syn_wf F A B) (syn_wf G A B) p0003
      p0004 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_feq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf F A C) (syn_wf F B C))) :=
  by
  have p0000 := @g_fneq2 A B F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wfn F A) (syn_wfn F B) (syn_wss (syn_crn F) C) p0000
  have p0002 := (Nominal.biimpRefl (syn_wf F A C))
  have p0003 := (Nominal.biimpRefl (syn_wf F B C))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C))
      (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C)) (syn_wf F A C) (syn_wf F B C) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_feq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf F C A) (syn_wf F C B))) :=
  by
  have p0000 := @g_sseq2 A B (syn_crn F)
  have p0001 :=
    @g_anbi2d (.classEq A B) (syn_wss (syn_crn F) A) (syn_wss (syn_crn F) B) (syn_wfn F C)
      p0000
  have p0002 := (Nominal.biimpRefl (syn_wf F C A))
  have p0003 := (Nominal.biimpRefl (syn_wf F C B))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F C) (syn_wss (syn_crn F) A))
      (syn_wa (syn_wfn F C) (syn_wss (syn_crn F) B)) (syn_wf F C A) (syn_wf F C B) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_feq1i (A : Class) (B : Class) (F : Class) (G : Class)
    (hyp_feq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (syn_wb (syn_wf F A B) (syn_wf G A B)) :=
  by
  have p0000 := @g_feq1 A B F G
  have p0001 := Nominal.mp hyp_feq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_feq2i (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_feq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wf F A C) (syn_wf F B C)) :=
  by
  have p0000 := @g_feq2 A B C F
  have p0001 := Nominal.mp hyp_feq2i_1 p0000
  exact p0001

@[expose]
noncomputable def g_ffn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wfn F A)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf F A B))
  have p0001 := @g_simplbi (syn_wf F A B) (syn_wfn F A) (syn_wss (syn_crn F) B) p0000
  exact p0001

@[expose]
noncomputable def g_dffn2 (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wf F A (syn_cvv))) :=
  by
  have p0000 := @g_ssv (syn_crn F)
  have p0001 := @g_biantru (syn_wss (syn_crn F) (syn_cvv)) (syn_wfn F A) p0000
  have p0002 := (Nominal.biimpRefl (syn_wf F A (syn_cvv)))
  have p0003 :=
    @g_bitr4i (syn_wfn F A) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) (syn_cvv)))
      (syn_wf F A (syn_cvv)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ffun (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wfun F)) :=
  by
  have p0000 := @g_ffn A B F
  have p0001 := @g_fnfun A F
  have p0002 := @g_syl (syn_wf F A B) (syn_wfn F A) (syn_wfun F) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fdm (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (.classEq (syn_cdm F) A)) :=
  by
  have p0000 := @g_ffn A B F
  have p0001 := @g_fndm A F
  have p0002 := @g_syl (syn_wf F A B) (syn_wfn F A) (.classEq (syn_cdm F) A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_frn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wss (syn_crn F) B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf F A B))
  have p0001 := @g_simprbi (syn_wf F A B) (syn_wfn F A) (syn_wss (syn_crn F) B) p0000
  exact p0001

@[expose]
noncomputable def g_dffn3 (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wf F A (syn_crn F))) :=
  by
  have p0000 := @g_ssid (syn_crn F)
  have p0001 := @g_biantru (syn_wss (syn_crn F) (syn_crn F)) (syn_wfn F A) p0000
  have p0002 := (Nominal.biimpRefl (syn_wf F A (syn_crn F)))
  have p0003 :=
    @g_bitr4i (syn_wfn F A) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) (syn_crn F)))
      (syn_wf F A (syn_crn F)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fss (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F A B) (syn_wss B C)) (syn_wf F A C)) :=
  by
  have p0000 := @g_sstr2 (syn_crn F) B C
  have p0001 :=
    @g_com12 (syn_wss (syn_crn F) B) (syn_wss B C) (syn_wss (syn_crn F) C) p0000
  have p0002 :=
    @g_anim2d (syn_wss B C) (syn_wss (syn_crn F) B) (syn_wss (syn_crn F) C) (syn_wfn F A)
      p0001
  have p0003 := (Nominal.biimpRefl (syn_wf F A B))
  have p0004 := (Nominal.biimpRefl (syn_wf F A C))
  have p0005 :=
    @g_n_3imtr4g (syn_wss B C) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B))
      (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C)) (syn_wf F A B) (syn_wf F A C) p0002
      p0003 p0004
  have p0006 := @g_impcom (syn_wss B C) (syn_wf F A B) (syn_wf F A C) p0005
  exact p0006

@[expose]
noncomputable def g_fco (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf F B C) (syn_wf G A B)) (syn_wf (syn_ccom F G) A C)) :=
  by
  have p0000 := @g_fnco B A F G
  have p0001 :=
    @g_n_3expib (syn_wfn F B) (syn_wfn G A) (syn_wss (syn_crn G) B)
      (syn_wfn (syn_ccom F G) A) p0000
  have p0002 :=
    @g_adantr (syn_wfn F B)
      (.imp (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) (syn_wfn (syn_ccom F G) A))
      (syn_wss (syn_crn F) C) p0001
  have p0003 := @g_rncoss F G
  have p0004 := @g_sstr (syn_crn (syn_ccom F G)) (syn_crn F) C
  have p0005 :=
    @g_mpan (syn_wss (syn_crn (syn_ccom F G)) (syn_crn F)) (syn_wss (syn_crn F) C)
      (syn_wss (syn_crn (syn_ccom F G)) C) p0003 p0004
  have p0006 :=
    @g_adantl (syn_wss (syn_crn F) C) (syn_wss (syn_crn (syn_ccom F G)) C) (syn_wfn F B)
      p0005
  have p0007 :=
    @g_jctird (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C))
      (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) (syn_wfn (syn_ccom F G) A)
      (syn_wss (syn_crn (syn_ccom F G)) C) p0002 p0006
  have p0008 :=
    @g_imp (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C))
      (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B))
      (syn_wa (syn_wfn (syn_ccom F G) A) (syn_wss (syn_crn (syn_ccom F G)) C)) p0007
  have p0009 := (Nominal.biimpRefl (syn_wf F B C))
  have p0010 := (Nominal.biimpRefl (syn_wf G A B))
  have p0011 :=
    @g_anbi12i (syn_wf F B C) (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C))
      (syn_wf G A B) (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) p0009 p0010
  have p0012 := (Nominal.biimpRefl (syn_wf (syn_ccom F G) A C))
  have p0013 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C))
        (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)))
      (syn_wa (syn_wfn (syn_ccom F G) A) (syn_wss (syn_crn (syn_ccom F G)) C))
      (syn_wa (syn_wf F B C) (syn_wf G A B)) (syn_wf (syn_ccom F G) A C) p0008 p0011 p0012
  exact p0013

@[expose]
noncomputable def g_fssxp (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wss F (syn_cxp A B))) :=
  by
  have p0000 := @g_ssdmrn F
  have p0001 := @g_fdm A B F
  have p0002 := @g_eqimss (syn_cdm F) A
  have p0003 :=
    @g_syl (syn_wf F A B) (.classEq (syn_cdm F) A) (syn_wss (syn_cdm F) A) p0001 p0002
  have p0004 := @g_frn A B F
  have p0005 := @g_xpss12 (syn_cdm F) A (syn_crn F) B
  have p0006 :=
    @g_syl2anc (syn_wf F A B) (syn_wss (syn_cdm F) A) (syn_wss (syn_crn F) B)
      (syn_wss (syn_cxp (syn_cdm F) (syn_crn F)) (syn_cxp A B)) p0003 p0004 p0005
  have p0007 :=
    @g_syl5ss (syn_wf F A B) F (syn_cxp (syn_cdm F) (syn_crn F)) (syn_cxp A B) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_opelf (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf F A B) (.classMem (syn_cop C D) F))
        (syn_wa (.classMem C A) (.classMem D B))) :=
  by
  have p0000 := @g_fssxp A B F
  have p0001 := @g_sseld (syn_wf F A B) F (syn_cxp A B) (syn_cop C D) p0000
  have p0002 := @g_opelxp C D A B
  have p0003 :=
    @g_syl6ib (syn_wf F A B) (.classMem (syn_cop C D) F)
      (.classMem (syn_cop C D) (syn_cxp A B)) (syn_wa (.classMem C A) (.classMem D B))
      p0001 p0002
  have p0004 :=
    @g_imp (syn_wf F A B) (.classMem (syn_cop C D) F)
      (syn_wa (.classMem C A) (.classMem D B)) p0003
  exact p0004

@[expose]
noncomputable def g_fun (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wf F A C) (syn_wf G B D)) (.classEq (syn_cin A B) (syn_c0)))
        (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D))) :=
  by
  have p0000 := @g_fnun A B F G
  have p0001 :=
    @g_expcom (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0))
      (syn_wfn (syn_cun F G) (syn_cun A B)) p0000
  have p0002 := @g_rnun F G
  have p0003 := @g_unss12 (syn_crn F) C (syn_crn G) D
  have p0004 :=
    @g_syl5eqss (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D))
      (syn_crn (syn_cun F G)) (syn_cun (syn_crn F) (syn_crn G)) (syn_cun C D) p0002 p0003
  have p0005 :=
    @g_a1i
      (.imp (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D))
        (syn_wss (syn_crn (syn_cun F G)) (syn_cun C D)))
      (.classEq (syn_cin A B) (syn_c0)) p0004
  have p0006 :=
    @g_anim12d (.classEq (syn_cin A B) (syn_c0)) (syn_wa (syn_wfn F A) (syn_wfn G B))
      (syn_wfn (syn_cun F G) (syn_cun A B))
      (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D))
      (syn_wss (syn_crn (syn_cun F G)) (syn_cun C D)) p0001 p0005
  have p0007 := (Nominal.biimpRefl (syn_wf F A C))
  have p0008 := (Nominal.biimpRefl (syn_wf G B D))
  have p0009 :=
    @g_anbi12i (syn_wf F A C) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C))
      (syn_wf G B D) (syn_wa (syn_wfn G B) (syn_wss (syn_crn G) D)) p0007 p0008
  have p0010 :=
    @g_an4 (syn_wfn F A) (syn_wss (syn_crn F) C) (syn_wfn G B) (syn_wss (syn_crn G) D)
  have p0011 :=
    @g_bitri (syn_wa (syn_wf F A C) (syn_wf G B D))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C))
        (syn_wa (syn_wfn G B) (syn_wss (syn_crn G) D)))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B))
        (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D)))
      p0009 p0010
  have p0012 := (Nominal.biimpRefl (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D)))
  have p0013 :=
    @g_n_3imtr4g (.classEq (syn_cin A B) (syn_c0))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B))
        (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D)))
      (syn_wa (syn_wfn (syn_cun F G) (syn_cun A B))
        (syn_wss (syn_crn (syn_cun F G)) (syn_cun C D)))
      (syn_wa (syn_wf F A C) (syn_wf G B D))
      (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D)) p0006 p0011 p0012
  have p0014 :=
    @g_impcom (.classEq (syn_cin A B) (syn_c0)) (syn_wa (syn_wf F A C) (syn_wf G B D))
      (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D)) p0013
  exact p0014

@[expose]
noncomputable def g_fnfco (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (syn_wf G B A)) (syn_wfn (syn_ccom F G) B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf G B A))
  have p0001 := @g_fnco A B F G
  have p0002 :=
    @g_n_3expb (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A)
      (syn_wfn (syn_ccom F G) B) p0001
  have p0003 :=
    @g_sylan2b (syn_wf G B A) (syn_wfn F A) (syn_wa (syn_wfn G B) (syn_wss (syn_crn G) A))
      (syn_wfn (syn_ccom F G) B) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_fssres (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf F A B) (syn_wss C A)) (syn_wf (syn_cres F C) C B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf F A B))
  have p0001 := @g_fnssres A C F
  have p0002 := @g_resss F C
  have p0003 := @g_rnss (syn_cres F C) F
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_sstr (syn_crn (syn_cres F C)) (syn_crn F) B
  have p0006 :=
    @g_mpan (syn_wss (syn_crn (syn_cres F C)) (syn_crn F)) (syn_wss (syn_crn F) B)
      (syn_wss (syn_crn (syn_cres F C)) B) p0004 p0005
  have p0007 :=
    @g_anim12i (syn_wa (syn_wfn F A) (syn_wss C A)) (syn_wfn (syn_cres F C) C)
      (syn_wss (syn_crn F) B) (syn_wss (syn_crn (syn_cres F C)) B) p0001 p0006
  have p0008 :=
    @g_an32s (syn_wfn F A) (syn_wss C A) (syn_wss (syn_crn F) B)
      (syn_wa (syn_wfn (syn_cres F C) C) (syn_wss (syn_crn (syn_cres F C)) B)) p0007
  have p0009 :=
    @g_sylanb (syn_wf F A B) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wss C A)
      (syn_wa (syn_wfn (syn_cres F C) C) (syn_wss (syn_crn (syn_cres F C)) B)) p0000 p0008
  have p0010 := (Nominal.biimpRefl (syn_wf (syn_cres F C) C B))
  have p0011 :=
    @g_sylibr (syn_wa (syn_wf F A B) (syn_wss C A))
      (syn_wa (syn_wfn (syn_cres F C) C) (syn_wss (syn_crn (syn_cres F C)) B))
      (syn_wf (syn_cres F C) C B) p0009 p0010
  exact p0011

@[expose]
noncomputable def g_fcoi1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (.classEq (syn_ccom F (syn_cres (syn_cid) A)) F)) :=
  by
  have p0000 := @g_coi1 F
  have p0001 := @g_reseq1i (syn_ccom F (syn_cid)) F A p0000
  have p0002 := @g_resco F (syn_cid) A
  have p0003 :=
    @g_eqtr3i (syn_cres (syn_ccom F (syn_cid)) A) (syn_cres F A)
      (syn_ccom F (syn_cres (syn_cid) A)) p0001 p0002
  have p0004 := @g_ffn A B F
  have p0005 := @g_fnresdm A F
  have p0006 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (.classEq (syn_cres F A) F) p0004 p0005
  have p0007 :=
    @g_syl5eqr (syn_wf F A B) (syn_ccom F (syn_cres (syn_cid) A)) (syn_cres F A) F p0003
      p0006
  exact p0007

@[expose]
noncomputable def g_feu (y : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf F A B) (.classMem C A))
        (syn_wreu y B (.classMem (syn_cop C (.cv y)) F))) :=
  by
  have dv_cache_0001 : y ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wf F A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union,
          dv_A_y, dv_B_y, dv_F_y, or_false, not_false_eq_true])
  have p0000 := @g_ffn A B F
  have p0001 := @g_fneu2 y A C F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylan (syn_wf F A B) (syn_wfn F A) (.classMem C A)
      (syn_weu y (.classMem (syn_cop C (.cv y)) F)) p0000 p0001
  have p0003 := @g_opelf A B C (.cv y) F
  have p0004 :=
    @g_simprd (syn_wa (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F)) (.classMem C A)
      (.classMem (.cv y) B) p0003
  have p0005 :=
    @g_ex (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F) (.classMem (.cv y) B) p0004
  have p0006 :=
    @g_pm4_71rd (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F) (.classMem (.cv y) B)
      p0005
  have p0007 :=
    @g_eubidv (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F)
      (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F)) y dv_cache_0003
      p0006
  have p0008 :=
    @g_adantr (syn_wf F A B)
      (syn_wb (syn_weu y (.classMem (syn_cop C (.cv y)) F))
        (syn_weu y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F))))
      (.classMem C A) p0007
  have p0009 :=
    @g_mpbid (syn_wa (syn_wf F A B) (.classMem C A))
      (syn_weu y (.classMem (syn_cop C (.cv y)) F))
      (syn_weu y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F))) p0002
      p0008
  have p0010 := (Nominal.biimpRefl (syn_wreu y B (.classMem (syn_cop C (.cv y)) F)))
  have p0011 :=
    @g_sylibr (syn_wa (syn_wf F A B) (.classMem C A))
      (syn_weu y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F)))
      (syn_wreu y B (.classMem (syn_cop C (.cv y)) F)) p0009 p0010
  exact p0011

@[expose]
noncomputable def g_f0 (A : Class) : Nominal.NPrf (syn_wf (syn_c0) (syn_c0) A) :=
  by
  have p0000 := @g_fun0
  have p0001 := @g_dm0
  have p0002 := (Nominal.biimpRefl (syn_wfn (syn_c0) (syn_c0)))
  have p0003 :=
    @g_mpbir2an (syn_wfn (syn_c0) (syn_c0)) (syn_wfun (syn_c0))
      (.classEq (syn_cdm (syn_c0)) (syn_c0)) p0000 p0001 p0002
  have p0004 := @g_rn0
  have p0005 := @g_n_0ss A
  have p0006 := @g_eqsstri (syn_crn (syn_c0)) (syn_c0) A p0004 p0005
  have p0007 := (Nominal.biimpRefl (syn_wf (syn_c0) (syn_c0) A))
  have p0008 :=
    @g_mpbir2an (syn_wf (syn_c0) (syn_c0) A) (syn_wfn (syn_c0) (syn_c0))
      (syn_wss (syn_crn (syn_c0)) A) p0003 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_fconst (A : Class) (B : Class)
    (hyp_fconst_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) :=
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
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_fconstopab x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @g_fnopab2 x y A B (syn_cxp A (syn_csn B)) dv_cache_0001 dv_cache_0002 dv_cache_0004
      dv_cache_0005 hyp_fconst_1 p0000
  have p0002 := @g_rnxpss A (syn_csn B)
  have p0003 := (Nominal.biimpRefl (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)))
  have p0004 :=
    @g_mpbir2an (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))
      (syn_wfn (syn_cxp A (syn_csn B)) A)
      (syn_wss (syn_crn (syn_cxp A (syn_csn B))) (syn_csn B)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fconstg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
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
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 := @g_sneq (.cv x) B
  have p0001 := @g_xpeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) A p0000
  have p0002 :=
    @g_feq1 A (syn_csn (.cv x)) (syn_cxp A (syn_csn (.cv x))) (syn_cxp A (syn_csn B))
  have p0003 := @g_feq3 (syn_csn (.cv x)) (syn_csn B) A (syn_cxp A (syn_csn B))
  have p0004 :=
    @g_sylan9bb (.classEq (syn_cxp A (syn_csn (.cv x))) (syn_cxp A (syn_csn B)))
      (syn_wf (syn_cxp A (syn_csn (.cv x))) A (syn_csn (.cv x)))
      (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn (.cv x)))
      (.classEq (syn_csn (.cv x)) (syn_csn B))
      (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) p0002 p0003
  have p0005 :=
    @g_syl2anc (.classEq (.cv x) B)
      (.classEq (syn_cxp A (syn_csn (.cv x))) (syn_cxp A (syn_csn B)))
      (.classEq (syn_csn (.cv x)) (syn_csn B))
      (syn_wb (syn_wf (syn_cxp A (syn_csn (.cv x))) A (syn_csn (.cv x)))
        (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)))
      p0001 p0000 p0004
  have p0006 := @g_vex x
  have p0007 := @g_fconst A (.cv x) p0006
  have p0008 :=
    @g_vtoclg (syn_wf (syn_cxp A (syn_csn (.cv x))) A (syn_csn (.cv x)))
      (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) x B V dv_cache_0001 dv_cache_0002
      p0005 p0007
  exact p0008

@[expose]
noncomputable def g_fnconstg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (syn_wfn (syn_cxp A (syn_csn B)) A)) :=
  by
  have p0000 := @g_fconstg A B V
  have p0001 := @g_ffn A (syn_csn B) (syn_cxp A (syn_csn B))
  have p0002 :=
    @g_syl (.classMem B V) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))
      (syn_wfn (syn_cxp A (syn_csn B)) A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_f1eq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wf1 F A B) (syn_wf1 G A B))) :=
  by
  have p0000 := @g_feq1 A B F G
  have p0001 := @g_cnveq F G
  have p0002 := @g_funeqd (.classEq F G) (syn_ccnv F) (syn_ccnv G) p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wf F A B) (syn_wf G A B) (syn_wfun (syn_ccnv F))
      (syn_wfun (syn_ccnv G)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0005 := (Nominal.biimpRefl (syn_wf1 G A B))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))
      (syn_wa (syn_wf G A B) (syn_wfun (syn_ccnv G))) (syn_wf1 F A B) (syn_wf1 G A B)
      p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_f1eq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1 F A C) (syn_wf1 F B C))) :=
  by
  have p0000 := @g_feq2 A B C F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wf F A C) (syn_wf F B C) (syn_wfun (syn_ccnv F)) p0000
  have p0002 := (Nominal.biimpRefl (syn_wf1 F A C))
  have p0003 := (Nominal.biimpRefl (syn_wf1 F B C))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf F A C) (syn_wfun (syn_ccnv F)))
      (syn_wa (syn_wf F B C) (syn_wfun (syn_ccnv F))) (syn_wf1 F A C) (syn_wf1 F B C)
      p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_f1eq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1 F C A) (syn_wf1 F C B))) :=
  by
  have p0000 := @g_feq3 A B C F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wf F C A) (syn_wf F C B) (syn_wfun (syn_ccnv F)) p0000
  have p0002 := (Nominal.biimpRefl (syn_wf1 F C A))
  have p0003 := (Nominal.biimpRefl (syn_wf1 F C B))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf F C A) (syn_wfun (syn_ccnv F)))
      (syn_wa (syn_wf F C B) (syn_wfun (syn_ccnv F))) (syn_wf1 F C A) (syn_wf1 F C B)
      p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_dff12 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wf1 F A B)
        (syn_wa (syn_wf F A B) (.all y (syn_wmo x (syn_wbr (.cv x) F (.cv y)))))) :=
  by
  have dv_cache_0001 : x ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0001 := @g_funcnv2 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_anbi2i (syn_wfun (syn_ccnv F)) (.all y (syn_wmo x (syn_wbr (.cv x) F (.cv y))))
      (syn_wf F A B) p0001
  have p0003 :=
    @g_bitri (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))
      (syn_wa (syn_wf F A B) (.all y (syn_wmo x (syn_wbr (.cv x) F (.cv y))))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_f1f (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wf F A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0001 := @g_simplbi (syn_wf1 F A B) (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0000
  exact p0001

@[expose]
noncomputable def g_f1fn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wfn F A)) :=
  by
  have p0000 := @g_f1f A B F
  have p0001 := @g_ffn A B F
  have p0002 := @g_syl (syn_wf1 F A B) (syn_wf F A B) (syn_wfn F A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_f1ss (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1 F A B) (syn_wss B C)) (syn_wf1 F A C)) :=
  by
  have p0000 := @g_f1f A B F
  have p0001 := @g_fss A B C F
  have p0002 :=
    @g_sylan (syn_wf1 F A B) (syn_wf F A B) (syn_wss B C) (syn_wf F A C) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0004 := @g_simprbi (syn_wf1 F A B) (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0003
  have p0005 := @g_adantr (syn_wf1 F A B) (syn_wfun (syn_ccnv F)) (syn_wss B C) p0004
  have p0006 := (Nominal.biimpRefl (syn_wf1 F A C))
  have p0007 :=
    @g_sylanbrc (syn_wa (syn_wf1 F A B) (syn_wss B C)) (syn_wf F A C)
      (syn_wfun (syn_ccnv F)) (syn_wf1 F A C) p0002 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_f1co (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1 F B C) (syn_wf1 G A B)) (syn_wf1 (syn_ccom F G) A C)) :=
  by
  have p0000 := @g_fco A B C F G
  have p0001 := @g_funco (syn_ccnv G) (syn_ccnv F)
  have p0002 := @g_cnvco F G
  have p0003 :=
    @g_funeqi (syn_ccnv (syn_ccom F G)) (syn_ccom (syn_ccnv G) (syn_ccnv F)) p0002
  have p0004 :=
    @g_sylibr (syn_wa (syn_wfun (syn_ccnv G)) (syn_wfun (syn_ccnv F)))
      (syn_wfun (syn_ccom (syn_ccnv G) (syn_ccnv F))) (syn_wfun (syn_ccnv (syn_ccom F G)))
      p0001 p0003
  have p0005 :=
    @g_ancoms (syn_wfun (syn_ccnv G)) (syn_wfun (syn_ccnv F))
      (syn_wfun (syn_ccnv (syn_ccom F G))) p0004
  have p0006 :=
    @g_anim12i (syn_wa (syn_wf F B C) (syn_wf G A B)) (syn_wf (syn_ccom F G) A C)
      (syn_wa (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv G)))
      (syn_wfun (syn_ccnv (syn_ccom F G))) p0000 p0005
  have p0007 :=
    @g_an4s (syn_wf F B C) (syn_wf G A B) (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv G))
      (syn_wa (syn_wf (syn_ccom F G) A C) (syn_wfun (syn_ccnv (syn_ccom F G)))) p0006
  have p0008 := (Nominal.biimpRefl (syn_wf1 F B C))
  have p0009 := (Nominal.biimpRefl (syn_wf1 G A B))
  have p0010 :=
    @g_anbi12i (syn_wf1 F B C) (syn_wa (syn_wf F B C) (syn_wfun (syn_ccnv F)))
      (syn_wf1 G A B) (syn_wa (syn_wf G A B) (syn_wfun (syn_ccnv G))) p0008 p0009
  have p0011 := (Nominal.biimpRefl (syn_wf1 (syn_ccom F G) A C))
  have p0012 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wf F B C) (syn_wfun (syn_ccnv F)))
        (syn_wa (syn_wf G A B) (syn_wfun (syn_ccnv G))))
      (syn_wa (syn_wf (syn_ccom F G) A C) (syn_wfun (syn_ccnv (syn_ccom F G))))
      (syn_wa (syn_wf1 F B C) (syn_wf1 G A B)) (syn_wf1 (syn_ccom F G) A C) p0007 p0010
      p0011
  exact p0012

@[expose]
noncomputable def g_foeq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wfo F A B) (syn_wfo G A B))) :=
  by
  have p0000 := @g_fneq1 A F G
  have p0001 := @g_rneq F G
  have p0002 := @g_eqeq1d (.classEq F G) (syn_crn F) (syn_crn G) B p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wfn F A) (syn_wfn G A) (.classEq (syn_crn F) B)
      (.classEq (syn_crn G) B) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wfo F A B))
  have p0005 := (Nominal.biimpRefl (syn_wfo G A B))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
      (syn_wa (syn_wfn G A) (.classEq (syn_crn G) B)) (syn_wfo F A B) (syn_wfo G A B)
      p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_foeq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfo F A C) (syn_wfo F B C))) :=
  by
  have p0000 := @g_fneq2 A B F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wfn F A) (syn_wfn F B) (.classEq (syn_crn F) C) p0000
  have p0002 := (Nominal.biimpRefl (syn_wfo F A C))
  have p0003 := (Nominal.biimpRefl (syn_wfo F B C))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) C))
      (syn_wa (syn_wfn F B) (.classEq (syn_crn F) C)) (syn_wfo F A C) (syn_wfo F B C)
      p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_foeq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfo F C A) (syn_wfo F C B))) :=
  by
  have p0000 := @g_eqeq2 A B (syn_crn F)
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classEq (syn_crn F) A) (.classEq (syn_crn F) B)
      (syn_wfn F C) p0000
  have p0002 := (Nominal.biimpRefl (syn_wfo F C A))
  have p0003 := (Nominal.biimpRefl (syn_wfo F C B))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F C) (.classEq (syn_crn F) A))
      (syn_wa (syn_wfn F C) (.classEq (syn_crn F) B)) (syn_wfo F C A) (syn_wfo F C B)
      p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fof (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (syn_wf F A B)) :=
  by
  have p0000 := @g_eqimss (syn_crn F) B
  have p0001 :=
    @g_anim2i (.classEq (syn_crn F) B) (syn_wss (syn_crn F) B) (syn_wfn F A) p0000
  have p0002 := (Nominal.biimpRefl (syn_wfo F A B))
  have p0003 := (Nominal.biimpRefl (syn_wf F A B))
  have p0004 :=
    @g_n_3imtr4i (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
      (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wfo F A B) (syn_wf F A B) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fofun (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (syn_wfun F)) :=
  by
  have p0000 := @g_fof A B F
  have p0001 := @g_ffun A B F
  have p0002 := @g_syl (syn_wfo F A B) (syn_wf F A B) (syn_wfun F) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fofn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (syn_wfn F A)) :=
  by
  have p0000 := @g_fof A B F
  have p0001 := @g_ffn A B F
  have p0002 := @g_syl (syn_wfo F A B) (syn_wf F A B) (syn_wfn F A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_forn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (.classEq (syn_crn F) B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wfo F A B))
  have p0001 := @g_simprbi (syn_wfo F A B) (syn_wfn F A) (.classEq (syn_crn F) B) p0000
  exact p0001

@[expose]
noncomputable def g_dffo2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (syn_wfo F A B) (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B))) :=
  by
  have p0000 := @g_fof A B F
  have p0001 := @g_forn A B F
  have p0002 := @g_jca (syn_wfo F A B) (syn_wf F A B) (.classEq (syn_crn F) B) p0000 p0001
  have p0003 := @g_ffn A B F
  have p0004 := (Nominal.biimpRefl (syn_wfo F A B))
  have p0005 :=
    @g_biimpri (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) p0004
  have p0006 :=
    @g_sylan (syn_wf F A B) (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wfo F A B) p0003
      p0005
  have p0007 :=
    @g_impbii (syn_wfo F A B) (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B)) p0002 p0006
  exact p0007

@[expose]
noncomputable def g_foima (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (.classEq (syn_cima F A) B)) :=
  by
  have p0000 := @g_imadmrn F
  have p0001 := @g_fof A B F
  have p0002 := @g_fdm A B F
  have p0003 := @g_imaeq2 (syn_cdm F) A F
  have p0004 :=
    @g_n_3syl (syn_wfo F A B) (syn_wf F A B) (.classEq (syn_cdm F) A)
      (.classEq (syn_cima F (syn_cdm F)) (syn_cima F A)) p0001 p0002 p0003
  have p0005 :=
    @g_syl5reqr (syn_wfo F A B) (syn_crn F) (syn_cima F (syn_cdm F)) (syn_cima F A) p0000
      p0004
  have p0006 := @g_forn A B F
  have p0007 := @g_eqtrd (syn_wfo F A B) (syn_cima F A) (syn_crn F) B p0005 p0006
  exact p0007

@[expose]
noncomputable def g_dffn4 (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wfo F A (syn_crn F))) :=
  by
  have p0000 := @g_eqid (syn_crn F)
  have p0001 := @g_biantru (.classEq (syn_crn F) (syn_crn F)) (syn_wfn F A) p0000
  have p0002 := (Nominal.biimpRefl (syn_wfo F A (syn_crn F)))
  have p0003 :=
    @g_bitr4i (syn_wfn F A) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) (syn_crn F)))
      (syn_wfo F A (syn_crn F)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fores (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
        (syn_wfo (syn_cres F A) A (syn_cima F A))) :=
  by
  have p0000 := @g_funres A F
  have p0001 :=
    @g_anim1i (syn_wfun F) (syn_wfun (syn_cres F A)) (syn_wss A (syn_cdm F)) p0000
  have p0002 := (Nominal.biimpRefl (syn_wfn (syn_cres F A) A))
  have p0003 := @g_dfima3 F A
  have p0004 := @g_eqcomi (syn_cima F A) (syn_crn (syn_cres F A)) p0003
  have p0005 := (Nominal.biimpRefl (syn_wfo (syn_cres F A) A (syn_cima F A)))
  have p0006 :=
    @g_mpbiran2 (syn_wfo (syn_cres F A) A (syn_cima F A)) (syn_wfn (syn_cres F A) A)
      (.classEq (syn_crn (syn_cres F A)) (syn_cima F A)) p0004 p0005
  have p0007 := @g_ssdmres A F
  have p0008 :=
    @g_anbi2i (syn_wss A (syn_cdm F)) (.classEq (syn_cdm (syn_cres F A)) A)
      (syn_wfun (syn_cres F A)) p0007
  have p0009 :=
    @g_n_3bitr4i (syn_wfn (syn_cres F A) A)
      (syn_wa (syn_wfun (syn_cres F A)) (.classEq (syn_cdm (syn_cres F A)) A))
      (syn_wfo (syn_cres F A) A (syn_cima F A))
      (syn_wa (syn_wfun (syn_cres F A)) (syn_wss A (syn_cdm F))) p0002 p0006 p0008
  have p0010 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (syn_wa (syn_wfun (syn_cres F A)) (syn_wss A (syn_cdm F)))
      (syn_wfo (syn_cres F A) A (syn_cima F A)) p0001 p0009
  exact p0010

@[expose]
noncomputable def g_foco (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfo F B C) (syn_wfo G A B)) (syn_wfo (syn_ccom F G) A C)) :=
  by
  have p0000 := @g_fco A B C F G
  have p0001 :=
    @g_ad2ant2r (syn_wf F B C) (syn_wf G A B) (syn_wf (syn_ccom F G) A C)
      (.classEq (syn_crn F) C) (.classEq (syn_crn G) B) p0000
  have p0002 := @g_fdm B C F
  have p0003 := @g_eqtr3 (syn_cdm F) (syn_crn G) B
  have p0004 :=
    @g_sylan (syn_wf F B C) (.classEq (syn_cdm F) B) (.classEq (syn_crn G) B)
      (.classEq (syn_cdm F) (syn_crn G)) p0002 p0003
  have p0005 := @g_rncoeq F G
  have p0006 :=
    @g_eqeq1d (.classEq (syn_cdm F) (syn_crn G)) (syn_crn (syn_ccom F G)) (syn_crn F) C
      p0005
  have p0007 :=
    @g_biimpar (.classEq (syn_cdm F) (syn_crn G)) (.classEq (syn_crn (syn_ccom F G)) C)
      (.classEq (syn_crn F) C) p0006
  have p0008 :=
    @g_sylan (syn_wa (syn_wf F B C) (.classEq (syn_crn G) B))
      (.classEq (syn_cdm F) (syn_crn G)) (.classEq (syn_crn F) C)
      (.classEq (syn_crn (syn_ccom F G)) C) p0004 p0007
  have p0009 :=
    @g_an32s (syn_wf F B C) (.classEq (syn_crn G) B) (.classEq (syn_crn F) C)
      (.classEq (syn_crn (syn_ccom F G)) C) p0008
  have p0010 :=
    @g_adantrl (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C)) (.classEq (syn_crn G) B)
      (.classEq (syn_crn (syn_ccom F G)) C) (syn_wf G A B) p0009
  have p0011 :=
    @g_jca
      (syn_wa (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C))
        (syn_wa (syn_wf G A B) (.classEq (syn_crn G) B)))
      (syn_wf (syn_ccom F G) A C) (.classEq (syn_crn (syn_ccom F G)) C) p0001 p0010
  have p0012 := @g_dffo2 B C F
  have p0013 := @g_dffo2 A B G
  have p0014 :=
    @g_anbi12i (syn_wfo F B C) (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C))
      (syn_wfo G A B) (syn_wa (syn_wf G A B) (.classEq (syn_crn G) B)) p0012 p0013
  have p0015 := @g_dffo2 A C (syn_ccom F G)
  have p0016 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C))
        (syn_wa (syn_wf G A B) (.classEq (syn_crn G) B)))
      (syn_wa (syn_wf (syn_ccom F G) A C) (.classEq (syn_crn (syn_ccom F G)) C))
      (syn_wa (syn_wfo F B C) (syn_wfo G A B)) (syn_wfo (syn_ccom F G) A C) p0011 p0014
      p0015
  exact p0016

@[expose]
noncomputable def g_f1oeq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wf1o F A B) (syn_wf1o G A B))) :=
  by
  have p0000 := @g_f1eq1 A B F G
  have p0001 := @g_foeq1 A B F G
  have p0002 :=
    @g_anbi12d (.classEq F G) (syn_wf1 F A B) (syn_wf1 G A B) (syn_wfo F A B)
      (syn_wfo G A B) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wf1o F A B))
  have p0004 := (Nominal.biimpRefl (syn_wf1o G A B))
  have p0005 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wf1 F A B) (syn_wfo F A B))
      (syn_wa (syn_wf1 G A B) (syn_wfo G A B)) (syn_wf1o F A B) (syn_wf1o G A B) p0002
      p0003 p0004
  exact p0005

@[expose]
noncomputable def g_f1oeq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1o F A C) (syn_wf1o F B C))) :=
  by
  have p0000 := @g_f1eq2 A B C F
  have p0001 := @g_foeq2 A B C F
  have p0002 :=
    @g_anbi12d (.classEq A B) (syn_wf1 F A C) (syn_wf1 F B C) (syn_wfo F A C)
      (syn_wfo F B C) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wf1o F A C))
  have p0004 := (Nominal.biimpRefl (syn_wf1o F B C))
  have p0005 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf1 F A C) (syn_wfo F A C))
      (syn_wa (syn_wf1 F B C) (syn_wfo F B C)) (syn_wf1o F A C) (syn_wf1o F B C) p0002
      p0003 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
