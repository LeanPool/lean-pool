/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NA50WN14DBlock002
public import LeanPool.NFWeakPartition.Certificates.NAPD051C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C052C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C053C001Block001
public import LeanPool.NFWeakPartition.Certificates.NAR4C054C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C055C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C056C001Block003
public import LeanPool.NFWeakPartition.Certificates.NAR4C057C001Block006
public import LeanPool.NFWeakPartition.Certificates.NAR4C058C001Block001
public import LeanPool.NFWeakPartition.NAR4C059C001Part005
public import LeanPool.NFWeakPartition.Certificates.NAR4C060C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C061C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C062C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C063C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C064C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C065C001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C066C001Block001
public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block007
public import LeanPool.NFWeakPartition.NAR4C068C001Part063
public import LeanPool.NFWeakPartition.Certificates.NAR4C069C001Block001
public import LeanPool.NFWeakPartition.NAR4C070C001Part004
public import LeanPool.NFWeakPartition.NAR4C071C001Part007
public import LeanPool.NFWeakPartition.NAR4C072C001Part017
public import LeanPool.NFWeakPartition.Certificates.NAR4C073C001Block004
public import LeanPool.NFWeakPartition.NAR4C074C001Part012
public import LeanPool.NFWeakPartition.Certificates.NAR4C075C001Block002
public import LeanPool.NFWeakPartition.NAR4C076C001Part013
public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block017
public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block065
public import LeanPool.NFWeakPartition.NAR4C079C001Part005
public import LeanPool.NFWeakPartition.NAR4C080C001Part001
public import LeanPool.NFWeakPartition.NAR4C081C001Part005
public import LeanPool.NFWeakPartition.NAR4C082C001Part006
public import LeanPool.NFWeakPartition.NAR4C083C001Part004
public import LeanPool.NFWeakPartition.NAR4C084C001Part004
public import LeanPool.NFWeakPartition.NAR4C085C001Part001
public import LeanPool.NFWeakPartition.NAR4C086C001Part001
public import LeanPool.NFWeakPartition.NAR4C087C001Part004
public import LeanPool.NFWeakPartition.Certificates.NAR5H088P001Block002
public import LeanPool.NFWeakPartition.Certificates.NAR4C089C001Block003
public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block045
public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart008
public import LeanPool.NFWeakPartition.NAR4H5C092M3Part003
public import LeanPool.NFWeakPartition.NAR4H5C093M3Part005
public import LeanPool.NFWeakPartition.NAR4H5C094M3Part003
public import LeanPool.NFWeakPartition.NAR4H5C095M3Part046
public import LeanPool.NFWeakPartition.NAR4H5C096M3Part004
public import LeanPool.NFWeakPartition.Certificates.NAR4H5C097M3Block001
public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012ACompact002Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isoeq1 (A : Class) (B : Class) (R : Class) (S : Class) (G : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq H G) (syn_wb (syn_wiso H R S A B) (syn_wiso G R S A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ G.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classEq H G)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_H, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq H G)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_H, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0009 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0010 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0012 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : x ∉ (G).fv :=
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
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0015 : y ∉ (G).fv :=
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
        simp only [fresh_y_not_G, not_false_eq_true])
  have p0000 := @g_f1oeq1 A B H G
  have p0001 := @g_fveq1 (.cv x) H G
  have p0002 := @g_fveq1 (.cv y) H G
  have p0003 :=
    @g_breq12d (.classEq H G) (syn_cfv H (.cv x)) (syn_cfv G (.cv x)) (syn_cfv H (.cv y))
      (syn_cfv G (.cv y)) S p0001 p0002
  have p0004 :=
    @g_bibi2d (.classEq H G) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv G (.cv x)) S (syn_cfv G (.cv y))) (syn_wbr (.cv x) R (.cv y))
      p0003
  have p0005 :=
    @g_n_2ralbidv (.classEq H G)
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv G (.cv x)) S (syn_cfv G (.cv y))))
      x y A A dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    @g_anbi12d (.classEq H G) (syn_wf1o H A B) (syn_wf1o G A B)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv G (.cv x)) S (syn_cfv G (.cv y))))))
      p0000 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S G
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0014 dv_cache_0015
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0009 :=
    @g_n_3bitr4g (.classEq H G)
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wa (syn_wf1o G A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv G (.cv x)) S (syn_cfv G (.cv y)))))))
      (syn_wiso H R S A B) (syn_wiso G R S A B) p0006 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_isoeq2 (A : Class) (B : Class) (R : Class) (S : Class) (T : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq R T) (syn_wb (syn_wiso H R S A B) (syn_wiso H T S A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ T.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_T : x ∉ T.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_T : y ∉ T.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classEq R T)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_T, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq R T)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_T, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0009 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0010 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0012 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : x ∉ (T).fv :=
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
        simp only [fresh_x_not_T, not_false_eq_true])
  have dv_cache_0015 : y ∉ (T).fv :=
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
        simp only [fresh_y_not_T, not_false_eq_true])
  have p0000 := @g_breq (.cv x) (.cv y) R T
  have p0001 :=
    @g_bibi1d (.classEq R T) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) T (.cv y))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))) p0000
  have p0002 :=
    @g_n_2ralbidv (.classEq R T)
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (.cv x) T (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      x y A A dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @g_anbi2d (.classEq R T)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) T (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wf1o H A B) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B T S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0014 dv_cache_0015 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0006 :=
    @g_n_3bitr4g (.classEq R T)
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) T (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wiso H R S A B) (syn_wiso H T S A B) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_isoeq3 (A : Class) (B : Class) (R : Class) (S : Class) (T : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq S T) (syn_wb (syn_wiso H R S A B) (syn_wiso H R T A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ T.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_T : x ∉ T.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_T : y ∉ T.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classEq S T)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_S, fresh_x_not_T, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq S T)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_S, fresh_y_not_T, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0009 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0010 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0012 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : x ∉ (T).fv :=
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
        simp only [fresh_x_not_T, not_false_eq_true])
  have dv_cache_0015 : y ∉ (T).fv :=
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
        simp only [fresh_y_not_T, not_false_eq_true])
  have p0000 := @g_breq (syn_cfv H (.cv x)) (syn_cfv H (.cv y)) S T
  have p0001 :=
    @g_bibi2d (.classEq S T) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H (.cv x)) T (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))
      p0000
  have p0002 :=
    @g_n_2ralbidv (.classEq S T)
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) T (syn_cfv H (.cv y))))
      x y A A dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @g_anbi2d (.classEq S T)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) T (syn_cfv H (.cv y))))))
      (syn_wf1o H A B) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R T H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0014 dv_cache_0015 dv_cache_0013
  have p0006 :=
    @g_n_3bitr4g (.classEq S T)
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) T (syn_cfv H (.cv y)))))))
      (syn_wiso H R S A B) (syn_wiso H R T A B) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_isoeq4 (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq A C) (syn_wb (syn_wiso H R S A B) (syn_wiso H R S C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0009 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0010 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0012 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_f1oeq2 A C B H
  have p0001 :=
    @g_raleq
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      y A C dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_raleqbi1dv
      (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))
      (syn_wral y C (syn_wb (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))
      x A C dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @g_anbi12d (.classEq A C) (syn_wf1o H A B) (syn_wf1o H C B)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wral x C (syn_wral y C (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0003 dv_cache_0001 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y C B R S H
      dv_cache_0004 dv_cache_0002 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0006 :=
    @g_n_3bitr4g (.classEq A C)
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wa (syn_wf1o H C B) (syn_wral x C (syn_wral y C (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wiso H R S A B) (syn_wiso H R S C B) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_isoeq5 (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq B C) (syn_wb (syn_wiso H R S A B) (syn_wiso H R S A C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
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
  have dv_cache_0005 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0006 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0007 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0008 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0009 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0010 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0013 : y ∉ (C).fv :=
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
        simp only [fresh_y_not_C, not_false_eq_true])
  have p0000 := @g_f1oeq3 B C A H
  have p0001 :=
    @g_anbi1d (.classEq B C) (syn_wf1o H A B) (syn_wf1o H A C)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A C R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0012 dv_cache_0013 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0004 :=
    @g_n_3bitr4g (.classEq B C)
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wa (syn_wf1o H A C) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wiso H R S A B) (syn_wiso H R S A C) p0001 p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isof1o (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wiso H R S A B) (syn_wf1o H A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
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
  have dv_cache_0005 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0006 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0007 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0008 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0009 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0010 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0001 :=
    @g_simplbi (syn_wiso H R S A B) (syn_wf1o H A B)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      p0000
  exact p0001

@[expose]
noncomputable def g_isorel (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wiso H R S A B) (syn_wa (.classMem C A) (.classMem D A)))
        (syn_wb (syn_wbr C R D) (syn_wbr (syn_cfv H C) S (syn_cfv H D)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
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
  have dv_cache_0005 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0006 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0007 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0008 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0009 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0010 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0013 : y ∉ (C).fv :=
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
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0014 : y ∉ (D).fv :=
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
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0015 :
    x ∉
      ((syn_wb (syn_wbr C R (.cv y)) (syn_wbr (syn_cfv H C) S (syn_cfv H (.cv y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_C, fresh_x_ne_y, fresh_x_not_R, fresh_x_not_H,
          fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0016 :
    y ∉ ((syn_wb (syn_wbr C R D) (syn_wbr (syn_cfv H C) S (syn_cfv H D)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_C, fresh_y_not_D, fresh_y_not_R, fresh_y_not_H, fresh_y_not_S,
          or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0001 :=
    @g_simprbi (syn_wiso H R S A B) (syn_wf1o H A B)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      p0000
  have p0002 := @g_breq1 (.cv x) C (.cv y) R
  have p0003 := @g_fveq2 (.cv x) C H
  have p0004 :=
    @g_breq1d (.classEq (.cv x) C) (syn_cfv H (.cv x)) (syn_cfv H C) (syn_cfv H (.cv y)) S
      p0003
  have p0005 :=
    @g_bibi12d (.classEq (.cv x) C) (syn_wbr (.cv x) R (.cv y)) (syn_wbr C R (.cv y))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H C) S (syn_cfv H (.cv y))) p0002 p0004
  have p0006 := @g_breq2 (.cv y) D C R
  have p0007 := @g_fveq2 (.cv y) D H
  have p0008 :=
    @g_breq2d (.classEq (.cv y) D) (syn_cfv H (.cv y)) (syn_cfv H D) (syn_cfv H C) S p0007
  have p0009 :=
    @g_bibi12d (.classEq (.cv y) D) (syn_wbr C R (.cv y)) (syn_wbr C R D)
      (syn_wbr (syn_cfv H C) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H C) S (syn_cfv H D)) p0006 p0008
  have p0010 :=
    @g_rspc2v
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr C R D) (syn_wbr (syn_cfv H C) S (syn_cfv H D)))
      (syn_wb (syn_wbr C R (.cv y)) (syn_wbr (syn_cfv H C) S (syn_cfv H (.cv y)))) x y C D
      A A dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0001 dv_cache_0001
      dv_cache_0002 dv_cache_0015 dv_cache_0016 dv_cache_0011 p0005 p0009
  have p0011 :=
    @g_mpan9 (syn_wiso H R S A B)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wa (.classMem C A) (.classMem D A))
      (syn_wb (syn_wbr C R D) (syn_wbr (syn_cfv H C) S (syn_cfv H D))) p0001 p0010
  exact p0011

@[expose]
noncomputable def g_isoid (A : Class) (R : Class) :
    Nominal.NPrf (syn_wiso (syn_cres (syn_cid) A) R R A A) :=
  by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ ((syn_cres (syn_cid) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cres (syn_cid) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_f1oi A
  have p0001 := @g_fvresi A (.cv x)
  have p0002 := @g_fvresi A (.cv y)
  have p0003 :=
    @g_breqan12d (.classMem (.cv x) A) (.classMem (.cv y) A)
      (syn_cfv (syn_cres (syn_cid) A) (.cv x)) (.cv x)
      (syn_cfv (syn_cres (syn_cid) A) (.cv y)) (.cv y) R p0001 p0002
  have p0004 :=
    @g_bicomd (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wbr (syn_cfv (syn_cres (syn_cid) A) (.cv x)) R
        (syn_cfv (syn_cres (syn_cid) A) (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0003
  have p0005 :=
    @g_rgen2a
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv (syn_cres (syn_cid) A) (.cv x)) R
          (syn_cfv (syn_cres (syn_cid) A) (.cv y))))
      x y A dv_cache_0001 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A A R R
      (syn_cres (syn_cid) A) dv_cache_0002 dv_cache_0001 dv_cache_0002 dv_cache_0001
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0007 :=
    @g_mpbir2an (syn_wiso (syn_cres (syn_cid) A) R R A A)
      (syn_wf1o (syn_cres (syn_cid) A) A A)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv (syn_cres (syn_cid) A) (.cv x)) R
              (syn_cfv (syn_cres (syn_cid) A) (.cv y))))))
      p0000 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_isocnv (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wiso H R S A B) (syn_wiso (syn_ccnv H) S R B A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_H : w ∉ H.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
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
  have dv_cache_0001 : x ∉ ((syn_cfv (syn_ccnv H) (.cv z))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_H, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cfv (syn_ccnv H) (.cv z))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_H, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cfv (syn_ccnv H) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, fresh_y_not_H, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S (syn_cfv H (.cv y)))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_H, fresh_x_ne_y, fresh_x_not_S,
          fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
            (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))))
          (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_H, fresh_y_ne_w, fresh_y_not_S,
          fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
                (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B,
          fresh_z_not_H, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_R, fresh_z_not_S,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    w ∉
      ((syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
                (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_not_B,
          fresh_w_not_H, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_R, fresh_w_not_S,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0012 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0013 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0014 : y ∉ (B).fv :=
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
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0015 : x ∉ (H).fv :=
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
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0016 : y ∉ (H).fv :=
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
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0017 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0018 : y ∉ (R).fv :=
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
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0019 : x ∉ (S).fv :=
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
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0020 : y ∉ (S).fv :=
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
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0021 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0022 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0023 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0024 : z ∉ ((syn_ccnv H)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_z_not_H,
          not_false_eq_true])
  have dv_cache_0025 : w ∉ ((syn_ccnv H)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_w_not_H,
          not_false_eq_true])
  have dv_cache_0026 : z ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0027 : w ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_S, not_false_eq_true])
  have dv_cache_0028 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0029 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have p0000 := @g_f1ocnv A B H
  have p0001 :=
    @g_adantr (syn_wf1o H A B) (syn_wf1o (syn_ccnv H) B A)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      p0000
  have p0002 := @g_f1ocnvfv2 A B (.cv z) H
  have p0003 :=
    @g_adantrr (syn_wf1o H A B) (.classMem (.cv z) B)
      (.classEq (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) (.cv z)) (.classMem (.cv w) B)
      p0002
  have p0004 := @g_f1ocnvfv2 A B (.cv w) H
  have p0005 :=
    @g_adantrl (syn_wf1o H A B) (.classMem (.cv w) B)
      (.classEq (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))) (.cv w)) (.classMem (.cv z) B)
      p0004
  have p0006 :=
    @g_breq12d
      (syn_wa (syn_wf1o H A B) (syn_wa (.classMem (.cv z) B) (.classMem (.cv w) B)))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) (.cv z)
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))) (.cv w) S p0003 p0005
  have p0007 :=
    @g_adantlr (syn_wf1o H A B) (syn_wa (.classMem (.cv z) B) (.classMem (.cv w) B))
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
          (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w)))) (syn_wbr (.cv z) S (.cv w)))
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      p0006
  have p0008 := @g_f1of B A (syn_ccnv H)
  have p0009 :=
    @g_syl (syn_wf1o H A B) (syn_wf1o (syn_ccnv H) B A) (syn_wf (syn_ccnv H) B A) p0000
      p0008
  have p0010 := @g_ffvelrn B A (.cv z) (syn_ccnv H)
  have p0011 := @g_ffvelrn B A (.cv w) (syn_ccnv H)
  have p0012 :=
    @g_anim12dan (syn_wf (syn_ccnv H) B A) (.classMem (.cv z) B)
      (.classMem (syn_cfv (syn_ccnv H) (.cv z)) A) (.classMem (.cv w) B)
      (.classMem (syn_cfv (syn_ccnv H) (.cv w)) A) p0010 p0011
  have p0013 := @g_breq1 (.cv x) (syn_cfv (syn_ccnv H) (.cv z)) (.cv y) R
  have p0014 := @g_fveq2 (.cv x) (syn_cfv (syn_ccnv H) (.cv z)) H
  have p0015 :=
    @g_breq1d (.classEq (.cv x) (syn_cfv (syn_ccnv H) (.cv z))) (syn_cfv H (.cv x))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) (syn_cfv H (.cv y)) S p0014
  have p0016 :=
    @g_bibi12d (.classEq (.cv x) (syn_cfv (syn_ccnv H) (.cv z)))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (.cv y))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S (syn_cfv H (.cv y))) p0013
      p0015
  have p0017 :=
    @g_bicom (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (.cv y))
      (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S (syn_cfv H (.cv y)))
  have p0018 :=
    @g_syl6bb (.classEq (.cv x) (syn_cfv (syn_ccnv H) (.cv z)))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (.cv y))
        (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (.cv y)))
      p0016 p0017
  have p0019 := @g_fveq2 (.cv y) (syn_cfv (syn_ccnv H) (.cv w)) H
  have p0020 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (syn_ccnv H) (.cv w))) (syn_cfv H (.cv y))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w)))
      (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S p0019
  have p0021 :=
    @g_breq2 (.cv y) (syn_cfv (syn_ccnv H) (.cv w)) (syn_cfv (syn_ccnv H) (.cv z)) R
  have p0022 :=
    @g_bibi12d (.classEq (.cv y) (syn_cfv (syn_ccnv H) (.cv w)))
      (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
        (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (.cv y))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))) p0020
      p0021
  have p0023 :=
    @g_rspc2va
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
          (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))))
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (.cv y)))
      x y (syn_cfv (syn_ccnv H) (.cv z)) (syn_cfv (syn_ccnv H) (.cv w)) A A dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0018 p0022
  have p0024 :=
    @g_sylan
      (syn_wa (syn_wf (syn_ccnv H) B A) (syn_wa (.classMem (.cv z) B) (.classMem (.cv w) B)))
      (syn_wa (.classMem (syn_cfv (syn_ccnv H) (.cv z)) A)
        (.classMem (syn_cfv (syn_ccnv H) (.cv w)) A))
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
          (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))))
      p0012 p0023
  have p0025 :=
    @g_an32s (syn_wf (syn_ccnv H) B A)
      (syn_wa (.classMem (.cv z) B) (.classMem (.cv w) B))
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
          (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))))
      p0024
  have p0026 :=
    @g_sylanl1 (syn_wf1o H A B) (syn_wf (syn_ccnv H) B A)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wa (.classMem (.cv z) B) (.classMem (.cv w) B))
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
          (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))))
      p0009 p0025
  have p0027 :=
    @g_bitr3d
      (syn_wa (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A
              (syn_wb (syn_wbr (.cv x) R (.cv y))
                (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
        (syn_wa (.classMem (.cv z) B) (.classMem (.cv w) B)))
      (syn_wbr (syn_cfv H (syn_cfv (syn_ccnv H) (.cv z))) S
        (syn_cfv H (syn_cfv (syn_ccnv H) (.cv w))))
      (syn_wbr (.cv z) S (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))) p0007
      p0026
  have p0028 :=
    @g_ralrimivva
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wb (syn_wbr (.cv z) S (.cv w))
        (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))))
      z w B B dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0027
  have p0029 :=
    @g_jca
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wf1o (syn_ccnv H) B A)
      (syn_wral z B (syn_wral w B (syn_wb (syn_wbr (.cv z) S (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R (syn_cfv (syn_ccnv H) (.cv w))))))
      p0001 p0028
  have p0030 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0004 dv_cache_0005 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0008
  have p0031 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso z w B A S R
      (syn_ccnv H) dv_cache_0021 dv_cache_0009 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0012
  have p0032 :=
    @g_n_3imtr4i
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wa (syn_wf1o (syn_ccnv H) B A) (syn_wral z B (syn_wral w B
            (syn_wb (syn_wbr (.cv z) S (.cv w)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv z)) R
                (syn_cfv (syn_ccnv H) (.cv w)))))))
      (syn_wiso H R S A B) (syn_wiso (syn_ccnv H) S R B A) p0029 p0030 p0031
  exact p0032


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isores2 (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf
      (syn_wb (syn_wiso H R S A B) (syn_wiso H R (syn_cin S (syn_cxp B B)) A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_wa (syn_wf1o H A B) (.classMem (.cv x) A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_H, fresh_y_ne_x,
          or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wf1o H A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, fresh_x_not_H, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0009 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0010 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0012 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : x ∉ ((syn_cin S (syn_cxp B B))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_S, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cin S (syn_cxp B B))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_S, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_f1of A B H
  have p0001 := @g_ffvelrn A B (.cv x) H
  have p0002 :=
    @g_adantrr (syn_wf H A B) (.classMem (.cv x) A) (.classMem (syn_cfv H (.cv x)) B)
      (.classMem (.cv y) A) p0001
  have p0003 := @g_ffvelrn A B (.cv y) H
  have p0004 :=
    @g_adantrl (syn_wf H A B) (.classMem (.cv y) A) (.classMem (syn_cfv H (.cv y)) B)
      (.classMem (.cv x) A) p0003
  have p0005 := @g_brinxp (syn_cfv H (.cv x)) (syn_cfv H (.cv y)) B B S
  have p0006 :=
    @g_syl2anc
      (syn_wa (syn_wf H A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)))
      (.classMem (syn_cfv H (.cv x)) B) (.classMem (syn_cfv H (.cv y)) B)
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))))
      p0002 p0004 p0005
  have p0007 :=
    @g_sylan (syn_wf1o H A B) (syn_wf H A B)
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))))
      p0000 p0006
  have p0008 :=
    @g_anassrs (syn_wf1o H A B) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))))
      p0007
  have p0009 :=
    @g_bibi2d
      (syn_wa (syn_wa (syn_wf1o H A B) (.classMem (.cv x) A)) (.classMem (.cv y) A))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0008
  have p0010 :=
    @g_ralbidva (syn_wa (syn_wf1o H A B) (.classMem (.cv x) A))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (.cv x) R (.cv y))
        (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))))
      y A dv_cache_0001 p0009
  have p0011 :=
    @g_ralbidva (syn_wf1o H A B)
      (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))
      (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))))
      x A dv_cache_0002 p0010
  have p0012 :=
    @g_pm5_32i (syn_wf1o H A B)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))))))
      p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0014 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R
      (syn_cin S (syn_cxp B B)) H dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0014 dv_cache_0015
      dv_cache_0013
  have p0015 :=
    @g_n_3bitr4i
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))
      (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
              (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))))))
      (syn_wiso H R S A B) (syn_wiso H R (syn_cin S (syn_cxp B B)) A B) p0012 p0013 p0014
  exact p0015

@[expose]
noncomputable def g_isores1 (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf
      (syn_wb (syn_wiso H R S A B) (syn_wiso H (syn_cin R (syn_cxp A A)) S A B)) :=
  by
  have p0000 := @g_isocnv A B R S H
  have p0001 := @g_isores2 B A S R (syn_ccnv H)
  have p0002 :=
    @g_sylib (syn_wiso H R S A B) (syn_wiso (syn_ccnv H) S R B A)
      (syn_wiso (syn_ccnv H) S (syn_cin R (syn_cxp A A)) B A) p0000 p0001
  have p0003 := @g_isocnv B A S (syn_cin R (syn_cxp A A)) (syn_ccnv H)
  have p0004 :=
    @g_syl (syn_wiso H R S A B) (syn_wiso (syn_ccnv H) S (syn_cin R (syn_cxp A A)) B A)
      (syn_wiso (syn_ccnv (syn_ccnv H)) (syn_cin R (syn_cxp A A)) S A B) p0002 p0003
  have p0005 := @g_cnvcnv H
  have p0006 := @g_isoeq1 A B (syn_cin R (syn_cxp A A)) S H (syn_ccnv (syn_ccnv H))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_sylib (syn_wiso H R S A B)
      (syn_wiso (syn_ccnv (syn_ccnv H)) (syn_cin R (syn_cxp A A)) S A B)
      (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) p0004 p0007
  have p0009 := @g_isocnv A B (syn_cin R (syn_cxp A A)) S H
  have p0010 :=
    @g_sylibr (syn_wiso H (syn_cin R (syn_cxp A A)) S A B)
      (syn_wiso (syn_ccnv H) S (syn_cin R (syn_cxp A A)) B A)
      (syn_wiso (syn_ccnv H) S R B A) p0009 p0001
  have p0011 := @g_isocnv B A S R (syn_ccnv H)
  have p0012 :=
    @g_syl (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) (syn_wiso (syn_ccnv H) S R B A)
      (syn_wiso (syn_ccnv (syn_ccnv H)) R S A B) p0010 p0011
  have p0013 := @g_isoeq1 A B R S H (syn_ccnv (syn_ccnv H))
  have p0014 := Nominal.mp p0005 p0013
  have p0015 :=
    @g_sylib (syn_wiso H (syn_cin R (syn_cxp A A)) S A B)
      (syn_wiso (syn_ccnv (syn_ccnv H)) R S A B) (syn_wiso H R S A B) p0012 p0014
  have p0016 :=
    @g_impbii (syn_wiso H R S A B) (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) p0008
      p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isotr (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (T : Class) (G : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wiso H R S A B) (syn_wiso G S T B C))
        (syn_wiso (syn_ccom G H) R T A C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv ∪ T.fv ∪ G.fv ∪ H.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  let v : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  let y : Var := freshVar proofSupport 5
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_H : w ∉ H.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_T : u ∉ T.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_G : u ∉ G.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_H : u ∉ H.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_T : v ∉ T.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_G : v ∉ G.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_H : v ∉ H.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_T : x ∉ T.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_T : y ∉ T.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_x : w ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_v_ne_x : v ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have dv_cache_0001 : u ∉ ((syn_cfv H (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_H, or_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((syn_cfv H (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_not_H, or_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((syn_cfv H (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_y, fresh_v_not_H, or_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0005 : v ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_B, not_false_eq_true])
  have dv_cache_0006 :
    u ∉
      ((syn_wb (syn_wbr (syn_cfv H (.cv x)) S (.cv v))
          (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_H, fresh_u_ne_v, fresh_u_not_S,
          fresh_u_not_G, fresh_u_not_T, or_false, not_false_eq_true])
  have dv_cache_0007 :
    v ∉
      ((syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
          (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_not_H, fresh_v_ne_y, fresh_v_not_S,
          fresh_v_not_G, fresh_v_not_T, or_false, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0012 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0013 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((syn_wb (syn_wbr (.cv x) R (.cv w))
          (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv w))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_w, fresh_z_not_R, fresh_z_not_H,
          fresh_z_not_S, or_false, not_false_eq_true])
  have dv_cache_0015 :
    w ∉
      ((syn_wb (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_R, fresh_w_not_H,
          fresh_w_not_S, or_false, not_false_eq_true])
  have dv_cache_0016 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0017 : y ∉ (A).fv :=
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0018 :
    x ∉
      ((syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
                (syn_wb (syn_wbr (.cv z) R (.cv w))
                  (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))))))
          (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B
                (syn_wb (syn_wbr (.cv u) S (.cv v))
                  (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B,
          fresh_x_not_H, fresh_x_ne_z, fresh_x_ne_w, fresh_x_not_R, fresh_x_not_S,
          fresh_x_not_C, fresh_x_not_G, fresh_x_ne_u, fresh_x_ne_v, fresh_x_not_T,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0019 :
    y ∉
      ((syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
                (syn_wb (syn_wbr (.cv z) R (.cv w))
                  (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))))))
          (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B
                (syn_wb (syn_wbr (.cv u) S (.cv v))
                  (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B,
          fresh_y_not_H, fresh_y_ne_z, fresh_y_ne_w, fresh_y_not_R, fresh_y_not_S,
          fresh_y_not_C, fresh_y_not_G, fresh_y_ne_u, fresh_y_ne_v, fresh_y_not_T,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0020 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0021 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0022 : w ∉ (B).fv :=
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
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0023 : z ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_H, not_false_eq_true])
  have dv_cache_0024 : w ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_H, not_false_eq_true])
  have dv_cache_0025 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0026 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0027 : z ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0028 : w ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_S, not_false_eq_true])
  have dv_cache_0029 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0030 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0031 : u ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_G, not_false_eq_true])
  have dv_cache_0032 : v ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_G, not_false_eq_true])
  have dv_cache_0033 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
  have dv_cache_0034 : v ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_S, not_false_eq_true])
  have dv_cache_0035 : u ∉ (T).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_T, not_false_eq_true])
  have dv_cache_0036 : v ∉ (T).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_T, not_false_eq_true])
  have dv_cache_0037 : x ∉ (A).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0038 : x ∉ (C).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0039 : y ∉ (C).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0040 : x ∉ ((syn_ccom G H)).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_x_not_G, fresh_x_not_H, or_false, not_false_eq_true])
  have dv_cache_0041 : y ∉ ((syn_ccom G H)).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_y_not_G, fresh_y_not_H, or_false, not_false_eq_true])
  have dv_cache_0042 : x ∉ (R).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0043 : y ∉ (R).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0044 : x ∉ (T).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_T, not_false_eq_true])
  have dv_cache_0045 : y ∉ (T).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_T, not_false_eq_true])
  have p0000 := @g_f1oco A B C G H
  have p0001 :=
    @g_ad2ant2r (syn_wf1o G B C) (syn_wf1o H A B) (syn_wf1o (syn_ccom G H) A C)
      (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
            (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))
      (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
            (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))
      p0000
  have p0002 :=
    @g_ancoms
      (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
              (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v)))))))
      (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
              (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))))))
      (syn_wf1o (syn_ccom G H) A C) p0001
  have p0003 := @g_f1of A B H
  have p0004 := @g_ffvelrn A B (.cv x) H
  have p0005 :=
    @g_ex (syn_wf H A B) (.classMem (.cv x) A) (.classMem (syn_cfv H (.cv x)) B) p0004
  have p0006 := @g_ffvelrn A B (.cv y) H
  have p0007 :=
    @g_ex (syn_wf H A B) (.classMem (.cv y) A) (.classMem (syn_cfv H (.cv y)) B) p0006
  have p0008 :=
    @g_anim12d (syn_wf H A B) (.classMem (.cv x) A) (.classMem (syn_cfv H (.cv x)) B)
      (.classMem (.cv y) A) (.classMem (syn_cfv H (.cv y)) B) p0005 p0007
  have p0009 :=
    @g_syl (syn_wf1o H A B) (syn_wf H A B)
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (syn_wa (.classMem (syn_cfv H (.cv x)) B) (.classMem (syn_cfv H (.cv y)) B)))
      p0003 p0008
  have p0010 :=
    @g_adantr (syn_wf1o H A B)
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (syn_wa (.classMem (syn_cfv H (.cv x)) B) (.classMem (syn_cfv H (.cv y)) B)))
      (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
            (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))
      p0009
  have p0011 := @g_breq1 (.cv u) (syn_cfv H (.cv x)) (.cv v) S
  have p0012 := @g_fveq2 (.cv u) (syn_cfv H (.cv x)) G
  have p0013 :=
    @g_breq1d (.classEq (.cv u) (syn_cfv H (.cv x))) (syn_cfv G (.cv u))
      (syn_cfv G (syn_cfv H (.cv x))) (syn_cfv G (.cv v)) T p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv u) (syn_cfv H (.cv x))) (syn_wbr (.cv u) S (.cv v))
      (syn_wbr (syn_cfv H (.cv x)) S (.cv v))
      (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v)))
      (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (.cv v))) p0011 p0013
  have p0015 := @g_breq2 (.cv v) (syn_cfv H (.cv y)) (syn_cfv H (.cv x)) S
  have p0016 := @g_fveq2 (.cv v) (syn_cfv H (.cv y)) G
  have p0017 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv H (.cv y))) (syn_cfv G (.cv v))
      (syn_cfv G (syn_cfv H (.cv y))) (syn_cfv G (syn_cfv H (.cv x))) T p0016
  have p0018 :=
    @g_bibi12d (.classEq (.cv v) (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H (.cv x)) S (.cv v))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (.cv v)))
      (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))) p0015
      p0017
  have p0019 :=
    @g_rspc2v
      (syn_wb (syn_wbr (.cv u) S (.cv v)) (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))))
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (.cv v))
        (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (.cv v))))
      u v (syn_cfv H (.cv x)) (syn_cfv H (.cv y)) B B dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 p0014 p0018
  have p0020 :=
    @g_com12 (syn_wa (.classMem (syn_cfv H (.cv x)) B) (.classMem (syn_cfv H (.cv y)) B))
      (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
            (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))))
      p0019
  have p0021 :=
    @g_adantl
      (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
            (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))
      (.imp (syn_wa (.classMem (syn_cfv H (.cv x)) B) (.classMem (syn_cfv H (.cv y)) B))
        (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
          (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y))))))
      (syn_wf1o G B C) p0020
  have p0022 :=
    @g_sylan9
      (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
              (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wa (.classMem (syn_cfv H (.cv x)) B) (.classMem (syn_cfv H (.cv y)) B))
      (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
              (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v)))))))
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))))
      p0010 p0021
  have p0023 :=
    @g_imp
      (syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
              (syn_wb (syn_wbr (.cv z) R (.cv w))
                (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))) (syn_wa (syn_wf1o G B C)
          (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
                (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
        (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))))
      p0022
  have p0024 := @g_breq1 (.cv z) (.cv x) (.cv w) R
  have p0025 := @g_fveq2 (.cv z) (.cv x) H
  have p0026_e00_recanon :
    Nominal.NPrf (.imp (.objEq z x) (.classEq (syn_cfv H (.cv z)) (syn_cfv H (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cfv syn_cio syn_cuni syn_wex syn_wa syn_csn syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0026 :=
    @g_breq1d (.objEq z x) (syn_cfv H (.cv z)) (syn_cfv H (.cv x)) (syn_cfv H (.cv w)) S
      p0026_e00_recanon
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (syn_wb (syn_wbr (.cv z) R (.cv w)) (syn_wbr (.cv x) R (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0027 :=
    @g_bibi12d (.objEq z x) (syn_wbr (.cv z) R (.cv w)) (syn_wbr (.cv x) R (.cv w))
      (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv w))) p0027_e00_recanon p0026
  have p0028 := @g_breq2 (.cv w) (.cv y) (.cv x) R
  have p0029 := @g_fveq2 (.cv w) (.cv y) H
  have p0030_e00_recanon :
    Nominal.NPrf (.imp (.objEq w y) (.classEq (syn_cfv H (.cv w)) (syn_cfv H (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cfv syn_cio syn_cuni syn_wex syn_wa syn_csn syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0030 :=
    @g_breq2d (.objEq w y) (syn_cfv H (.cv w)) (syn_cfv H (.cv y)) (syn_cfv H (.cv x)) S
      p0030_e00_recanon
  have p0031_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (syn_wb (syn_wbr (.cv x) R (.cv w)) (syn_wbr (.cv x) R (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0028
  have p0031 :=
    @g_bibi12d (.objEq w y) (syn_wbr (.cv x) R (.cv w)) (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv w)))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))) p0031_e00_recanon p0030
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (syn_wb (syn_wb (syn_wbr (.cv z) R (.cv w))
            (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))
          (syn_wb (syn_wbr (.cv x) R (.cv w))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv w)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0032_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y)) (syn_wb (syn_wb (syn_wbr (.cv x) R (.cv w))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv w))))
          (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @g_rspc2v
      (syn_wb (syn_wbr (.cv z) R (.cv w)) (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wb (syn_wbr (.cv x) R (.cv w)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv w))))
      z w (.cv x) (.cv y) A A dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      p0032_e00_recanon p0032_e01_recanon
  have p0033 :=
    @g_impcom (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
            (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      p0032
  have p0034 :=
    @g_adantll
      (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
            (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wf1o H A B) p0033
  have p0035 :=
    @g_adantlr
      (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
              (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))
      (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
              (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v)))))))
      p0034
  have p0036 :=
    @g_ad2antrr (syn_wf1o H A B) (syn_wf H A B)
      (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
            (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))
      (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
              (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v)))))))
      p0003
  have p0037 := @g_fvco3 A B (.cv x) G H
  have p0038 := @g_fvco3 A B (.cv y) G H
  have p0039 :=
    @g_breqan12d (syn_wa (syn_wf H A B) (.classMem (.cv x) A))
      (syn_wa (syn_wf H A B) (.classMem (.cv y) A)) (syn_cfv (syn_ccom G H) (.cv x))
      (syn_cfv G (syn_cfv H (.cv x))) (syn_cfv (syn_ccom G H) (.cv y))
      (syn_cfv G (syn_cfv H (.cv y))) T p0037 p0038
  have p0040 :=
    @g_anandis (syn_wf H A B) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (syn_wb (syn_wbr (syn_cfv (syn_ccom G H) (.cv x)) T (syn_cfv (syn_ccom G H) (.cv y)))
        (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))))
      p0039
  have p0041 :=
    @g_sylan
      (syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
              (syn_wb (syn_wbr (.cv z) R (.cv w))
                (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))) (syn_wa (syn_wf1o G B C)
          (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
                (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))
      (syn_wf H A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wb (syn_wbr (syn_cfv (syn_ccom G H) (.cv x)) T (syn_cfv (syn_ccom G H) (.cv y)))
        (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y)))))
      p0036 p0040
  have p0042 :=
    @g_n_3bitr4d
      (syn_wa (syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
                (syn_wb (syn_wbr (.cv z) R (.cv w))
                  (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))))))
          (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B
                (syn_wb (syn_wbr (.cv u) S (.cv v))
                  (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv G (syn_cfv H (.cv x))) T (syn_cfv G (syn_cfv H (.cv y))))
      (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (syn_cfv (syn_ccom G H) (.cv x)) T (syn_cfv (syn_ccom G H) (.cv y))) p0023
      p0035 p0041
  have p0043 :=
    @g_ralrimivva
      (syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
              (syn_wb (syn_wbr (.cv z) R (.cv w))
                (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))) (syn_wa (syn_wf1o G B C)
          (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
                (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))
      (syn_wb (syn_wbr (.cv x) R (.cv y))
        (syn_wbr (syn_cfv (syn_ccom G H) (.cv x)) T (syn_cfv (syn_ccom G H) (.cv y))))
      x y A A dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0042
  have p0044 :=
    @g_jca
      (syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
              (syn_wb (syn_wbr (.cv z) R (.cv w))
                (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))) (syn_wa (syn_wf1o G B C)
          (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
                (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))
      (syn_wf1o (syn_ccom G H) A C)
      (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
            (syn_wbr (syn_cfv (syn_ccom G H) (.cv x)) T (syn_cfv (syn_ccom G H) (.cv y))))))
      p0002 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso z w A B R S H
      dv_cache_0012 dv_cache_0013 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0016
  have p0046 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso u v B C S T G
      dv_cache_0004 dv_cache_0005 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
      dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0008
  have p0047 :=
    @g_anbi12i (syn_wiso H R S A B)
      (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A (syn_wb (syn_wbr (.cv z) R (.cv w))
              (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w)))))))
      (syn_wiso G S T B C)
      (syn_wa (syn_wf1o G B C) (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
              (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v)))))))
      p0045 p0046
  have p0048 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A C R T
      (syn_ccom G H) dv_cache_0037 dv_cache_0017 dv_cache_0038 dv_cache_0039 dv_cache_0040
      dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0020
  have p0049 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wf1o H A B) (syn_wral z A (syn_wral w A
              (syn_wb (syn_wbr (.cv z) R (.cv w))
                (syn_wbr (syn_cfv H (.cv z)) S (syn_cfv H (.cv w))))))) (syn_wa (syn_wf1o G B C)
          (syn_wral u B (syn_wral v B (syn_wb (syn_wbr (.cv u) S (.cv v))
                (syn_wbr (syn_cfv G (.cv u)) T (syn_cfv G (.cv v))))))))
      (syn_wa (syn_wf1o (syn_ccom G H) A C) (syn_wral x A (syn_wral y A
            (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv (syn_ccom G H) (.cv x)) T
                (syn_cfv (syn_ccom G H) (.cv y)))))))
      (syn_wa (syn_wiso H R S A B) (syn_wiso G S T B C)) (syn_wiso (syn_ccom G H) R T A C)
      p0044 p0047 p0048
  exact p0049


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isoini (A : Class) (B : Class) (D : Class) (R : Class) (S : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wiso H R S A B) (.classMem D A))
        (.classEq (syn_cima H (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))))
          (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ H.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wiso H R S A B) (.classMem D A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_x_not_A,
          fresh_x_not_B, fresh_x_not_H, fresh_x_not_R, fresh_x_not_S, fresh_x_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wbr (.cv y) S (syn_cfv H D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_D, fresh_x_not_H, fresh_x_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_S, fresh_y_not_D, fresh_y_not_H, or_false,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_wa (syn_wiso H R S A B) (.classMem D A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_y_not_A,
          fresh_y_not_B, fresh_y_not_H, fresh_y_not_R, fresh_y_not_S, fresh_y_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_H, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_R, fresh_y_not_D, or_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_R, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0011 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have p0000 := @g_elin (.cv y) B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))
  have p0001 := @g_eliniseg S (syn_cfv H D) (.cv y)
  have p0002 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D))))
      (syn_wbr (.cv y) S (syn_cfv H D)) (.classMem (.cv y) B) p0001
  have p0003 :=
    @g_bitri
      (.classMem (.cv y) (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))))
      (syn_wa (.classMem (.cv y) B)
        (.classMem (.cv y) (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))))
      (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D))) p0000 p0002
  have p0004 := @g_isof1o A B R S H
  have p0005 := @g_f1ofo A B H
  have p0006 := @g_syl (syn_wiso H R S A B) (syn_wf1o H A B) (syn_wfo H A B) p0004 p0005
  have p0007 := @g_forn A B H
  have p0008 :=
    @g_syl (syn_wiso H R S A B) (syn_wfo H A B) (.classEq (syn_crn H) B) p0006 p0007
  have p0009 := @g_eleq2d (syn_wiso H R S A B) (syn_crn H) B (.cv y) p0008
  have p0010 := @g_f1ofn A B H
  have p0011 := @g_syl (syn_wiso H R S A B) (syn_wf1o H A B) (syn_wfn H A) p0004 p0010
  have p0012 := @g_fvelrnb x A (.cv y) H dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0013 :=
    @g_syl (syn_wiso H R S A B) (syn_wfn H A)
      (syn_wb (.classMem (.cv y) (syn_crn H))
        (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y))))
      p0011 p0012
  have p0014 :=
    @g_bitr3d (syn_wiso H R S A B) (.classMem (.cv y) (syn_crn H)) (.classMem (.cv y) B)
      (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y))) p0009 p0013
  have p0015 :=
    @g_anbi1d (syn_wiso H R S A B) (.classMem (.cv y) B)
      (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y)))
      (syn_wbr (.cv y) S (syn_cfv H D)) p0014
  have p0016 :=
    @g_adantr (syn_wiso H R S A B)
      (syn_wb (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D)))
        (syn_wa (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y)))
          (syn_wbr (.cv y) S (syn_cfv H D))))
      (.classMem D A) p0015
  have p0017 := @g_elin (.cv x) A (syn_cima (syn_ccnv R) (syn_csn D))
  have p0018 := @g_eliniseg R D (.cv x)
  have p0019 :=
    @g_anbi2i (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn D)))
      (syn_wbr (.cv x) R D) (.classMem (.cv x) A) p0018
  have p0020 :=
    @g_bitri (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn D))))
      (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) R D)) p0017 p0019
  have p0021 :=
    @g_anbi1i (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))))
      (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) R D)) (syn_wbr (.cv x) H (.cv y))
      p0020
  have p0022 :=
    @g_anass (.classMem (.cv x) A) (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))
  have p0023 :=
    @g_bitri
      (syn_wa (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))))
        (syn_wbr (.cv x) H (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) R D)) (syn_wbr (.cv x) H (.cv y)))
      (syn_wa (.classMem (.cv x) A) (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))))
      p0021 p0022
  have p0024 := @g_fnbrfvb A (.cv x) (.cv y) H
  have p0025 :=
    @g_sylan (syn_wiso H R S A B) (syn_wfn H A) (.classMem (.cv x) A)
      (syn_wb (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv x) H (.cv y))) p0011
      p0024
  have p0026 :=
    @g_adantrr (syn_wiso H R S A B) (.classMem (.cv x) A)
      (syn_wb (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv x) H (.cv y)))
      (.classMem D A) p0025
  have p0027 :=
    @g_bicomd (syn_wa (syn_wiso H R S A B) (syn_wa (.classMem (.cv x) A) (.classMem D A)))
      (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv x) H (.cv y)) p0026
  have p0028 := @g_isorel A B (.cv x) D R S H
  have p0029 :=
    @g_anbi12d
      (syn_wa (syn_wiso H R S A B) (syn_wa (.classMem (.cv x) A) (.classMem D A)))
      (syn_wbr (.cv x) H (.cv y)) (.classEq (syn_cfv H (.cv x)) (.cv y))
      (syn_wbr (.cv x) R D) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H D)) p0027 p0028
  have p0030 := @g_ancom (syn_wbr (.cv x) H (.cv y)) (syn_wbr (.cv x) R D)
  have p0031 := @g_breq1 (syn_cfv H (.cv x)) (.cv y) (syn_cfv H D) S
  have p0032 :=
    @g_pm5_32i (.classEq (syn_cfv H (.cv x)) (.cv y))
      (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H D)) (syn_wbr (.cv y) S (syn_cfv H D))
      p0031
  have p0033 :=
    @g_n_3bitr3g
      (syn_wa (syn_wiso H R S A B) (syn_wa (.classMem (.cv x) A) (.classMem D A)))
      (syn_wa (syn_wbr (.cv x) H (.cv y)) (syn_wbr (.cv x) R D))
      (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y))
        (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H D)))
      (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y)))
      (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)))
      p0029 p0030 p0032
  have p0034 :=
    @g_exp32 (syn_wiso H R S A B) (.classMem (.cv x) A) (.classMem D A)
      (syn_wb (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y)))
        (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))))
      p0033
  have p0035 :=
    @g_com23 (syn_wiso H R S A B) (.classMem (.cv x) A) (.classMem D A)
      (syn_wb (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y)))
        (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))))
      p0034
  have p0036 :=
    @g_imp (syn_wiso H R S A B) (.classMem D A)
      (.imp (.classMem (.cv x) A)
        (syn_wb (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y)))
          (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)))))
      p0035
  have p0037 :=
    @g_pm5_32d (syn_wa (syn_wiso H R S A B) (.classMem D A)) (.classMem (.cv x) A)
      (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y)))
      (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)))
      p0036
  have p0038 :=
    @g_syl5bb
      (syn_wa (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))))
        (syn_wbr (.cv x) H (.cv y)))
      (syn_wa (.classMem (.cv x) A) (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))))
      (syn_wa (syn_wiso H R S A B) (.classMem D A))
      (syn_wa (.classMem (.cv x) A)
        (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))))
      p0023 p0037
  have p0039 :=
    @g_rexbidv2 (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_wbr (.cv x) H (.cv y))
      (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))) x
      (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) A dv_cache_0004 p0038
  have p0040 :=
    @g_r19_41v (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)) x
      A dv_cache_0005
  have p0041 :=
    @g_syl6bb (syn_wa (syn_wiso H R S A B) (.classMem D A))
      (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y)))
      (syn_wrex x A
        (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))))
      (syn_wa (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y)))
        (syn_wbr (.cv y) S (syn_cfv H D)))
      p0039 p0040
  have p0042 :=
    @g_bitr4d (syn_wa (syn_wiso H R S A B) (.classMem D A))
      (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D)))
      (syn_wa (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y)))
        (syn_wbr (.cv y) S (syn_cfv H D)))
      (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y)))
      p0016 p0041
  have p0043 :=
    @g_syl5bb
      (.classMem (.cv y) (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))))
      (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D)))
      (syn_wa (syn_wiso H R S A B) (.classMem D A))
      (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y)))
      p0003 p0042
  have p0044 :=
    @g_eqabdv (syn_wa (syn_wiso H R S A B) (.classMem D A))
      (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y)))
      y (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))) dv_cache_0006
      dv_cache_0007 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x H
      (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) dv_cache_0008 dv_cache_0003
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0046 :=
    @g_syl6reqr (syn_wa (syn_wiso H R S A B) (.classMem D A))
      (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D))))
      (.cab y (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))
          (syn_wbr (.cv x) H (.cv y))))
      (syn_cima H (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))) p0044 p0045
  exact p0046


end NFChoice.DirectNominalPrf.WPPReplay

end
