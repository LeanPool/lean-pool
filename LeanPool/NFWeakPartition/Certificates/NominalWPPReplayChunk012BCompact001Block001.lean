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

/-- Checked nominal proof certificate identified upstream as `g_isoeq1`. -/
@[expose]
noncomputable def gIsoeq1 (A : Class) (B : Class) (R : Class) (S : Class) (G : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq H G) (synWb (synWiso H R S A B) (synWiso G R S A B))) :=
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
  have p0000 := @gF1oeq1 A B H G
  have p0001 := @gFveq1 (.cv x) H G
  have p0002 := @gFveq1 (.cv y) H G
  have p0003 :=
    @gBreq12d (.classEq H G) (synCfv H (.cv x)) (synCfv G (.cv x)) (synCfv H (.cv y))
      (synCfv G (.cv y)) S p0001 p0002
  have p0004 :=
    @gBibi2d (.classEq H G) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
      (synWbr (synCfv G (.cv x)) S (synCfv G (.cv y))) (synWbr (.cv x) R (.cv y))
      p0003
  have p0005 :=
    @gN2ralbidv (.classEq H G)
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv G (.cv x)) S (synCfv G (.cv y))))
      x y A A dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    @gAnbi12d (.classEq H G) (synWf1o H A B) (synWf1o G A B)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv G (.cv x)) S (synCfv G (.cv y))))))
      p0000 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S G
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0014 dv_cache_0015
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0009 :=
    @gN3bitr4g (.classEq H G)
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWa (synWf1o G A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv G (.cv x)) S (synCfv G (.cv y)))))))
      (synWiso H R S A B) (synWiso G R S A B) p0006 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_isoeq2`. -/
@[expose]
noncomputable def gIsoeq2 (A : Class) (B : Class) (R : Class) (S : Class) (T : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq R T) (synWb (synWiso H R S A B) (synWiso H T S A B))) :=
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
  have p0000 := @gBreq (.cv x) (.cv y) R T
  have p0001 :=
    @gBibi1d (.classEq R T) (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) T (.cv y))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))) p0000
  have p0002 :=
    @gN2ralbidv (.classEq R T)
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr (.cv x) T (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      x y A A dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @gAnbi2d (.classEq R T)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWral x A (synWral y A (synWb (synWbr (.cv x) T (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWf1o H A B) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B T S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0014 dv_cache_0015 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0006 :=
    @gN3bitr4g (.classEq R T)
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) T (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWiso H R S A B) (synWiso H T S A B) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_isoeq3`. -/
@[expose]
noncomputable def gIsoeq3 (A : Class) (B : Class) (R : Class) (S : Class) (T : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq S T) (synWb (synWiso H R S A B) (synWiso H R T A B))) :=
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
  have p0000 := @gBreq (synCfv H (.cv x)) (synCfv H (.cv y)) S T
  have p0001 :=
    @gBibi2d (.classEq S T) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
      (synWbr (synCfv H (.cv x)) T (synCfv H (.cv y))) (synWbr (.cv x) R (.cv y))
      p0000
  have p0002 :=
    @gN2ralbidv (.classEq S T)
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) T (synCfv H (.cv y))))
      x y A A dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @gAnbi2d (.classEq S T)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) T (synCfv H (.cv y))))))
      (synWf1o H A B) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R T H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0014 dv_cache_0015 dv_cache_0013
  have p0006 :=
    @gN3bitr4g (.classEq S T)
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) T (synCfv H (.cv y)))))))
      (synWiso H R S A B) (synWiso H R T A B) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_isoeq4`. -/
@[expose]
noncomputable def gIsoeq4 (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq A C) (synWb (synWiso H R S A B) (synWiso H R S C B))) :=
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
  have p0000 := @gF1oeq2 A C B H
  have p0001 :=
    @gRaleq
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      y A C dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gRaleqbi1dv
      (synWral y A (synWb (synWbr (.cv x) R (.cv y))
          (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))
      (synWral y C (synWb (synWbr (.cv x) R (.cv y))
          (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))
      x A C dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @gAnbi12d (.classEq A C) (synWf1o H A B) (synWf1o H C B)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWral x C (synWral y C (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0003 dv_cache_0001 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y C B R S H
      dv_cache_0004 dv_cache_0002 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0006 :=
    @gN3bitr4g (.classEq A C)
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWa (synWf1o H C B) (synWral x C (synWral y C (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWiso H R S A B) (synWiso H R S C B) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_isoeq5`. -/
@[expose]
noncomputable def gIsoeq5 (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (.classEq B C) (synWb (synWiso H R S A B) (synWiso H R S A C))) :=
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
  have p0000 := @gF1oeq3 B C A H
  have p0001 :=
    @gAnbi1d (.classEq B C) (synWf1o H A B) (synWf1o H A C)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A C R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0012 dv_cache_0013 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0004 :=
    @gN3bitr4g (.classEq B C)
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWa (synWf1o H A C) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWiso H R S A B) (synWiso H R S A C) p0001 p0002 p0003
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

/-- Checked nominal proof certificate identified upstream as `g_isof1o`. -/
@[expose]
noncomputable def gIsof1o (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf (.imp (synWiso H R S A B) (synWf1o H A B)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0001 :=
    @gSimplbi (synWiso H R S A B) (synWf1o H A B)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_isorel`. -/
@[expose]
noncomputable def gIsorel (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWiso H R S A B) (synWa (.classMem C A) (.classMem D A)))
        (synWb (synWbr C R D) (synWbr (synCfv H C) S (synCfv H D)))) :=
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
      ((synWb (synWbr C R (.cv y)) (synWbr (synCfv H C) S (synCfv H (.cv y))))).fv :=
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
    y ∉ ((synWb (synWbr C R D) (synWbr (synCfv H C) S (synCfv H D)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0001 :=
    @gSimprbi (synWiso H R S A B) (synWf1o H A B)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      p0000
  have p0002 := @gBreq1 (.cv x) C (.cv y) R
  have p0003 := @gFveq2 (.cv x) C H
  have p0004 :=
    @gBreq1d (.classEq (.cv x) C) (synCfv H (.cv x)) (synCfv H C) (synCfv H (.cv y)) S
      p0003
  have p0005 :=
    @gBibi12d (.classEq (.cv x) C) (synWbr (.cv x) R (.cv y)) (synWbr C R (.cv y))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
      (synWbr (synCfv H C) S (synCfv H (.cv y))) p0002 p0004
  have p0006 := @gBreq2 (.cv y) D C R
  have p0007 := @gFveq2 (.cv y) D H
  have p0008 :=
    @gBreq2d (.classEq (.cv y) D) (synCfv H (.cv y)) (synCfv H D) (synCfv H C) S p0007
  have p0009 :=
    @gBibi12d (.classEq (.cv y) D) (synWbr C R (.cv y)) (synWbr C R D)
      (synWbr (synCfv H C) S (synCfv H (.cv y)))
      (synWbr (synCfv H C) S (synCfv H D)) p0006 p0008
  have p0010 :=
    @gRspc2v
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr C R D) (synWbr (synCfv H C) S (synCfv H D)))
      (synWb (synWbr C R (.cv y)) (synWbr (synCfv H C) S (synCfv H (.cv y)))) x y C D
      A A dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0001 dv_cache_0001
      dv_cache_0002 dv_cache_0015 dv_cache_0016 dv_cache_0011 p0005 p0009
  have p0011 :=
    @gMpan9 (synWiso H R S A B)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWa (.classMem C A) (.classMem D A))
      (synWb (synWbr C R D) (synWbr (synCfv H C) S (synCfv H D))) p0001 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_isoid`. -/
@[expose]
noncomputable def gIsoid (A : Class) (R : Class) :
    Nominal.NPrf (synWiso (synCres (synCid) A) R R A A) :=
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
  have dv_cache_0003 : x ∉ ((synCres (synCid) A)).fv :=
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
  have dv_cache_0004 : y ∉ ((synCres (synCid) A)).fv :=
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
  have p0000 := @gF1oi A
  have p0001 := @gFvresi A (.cv x)
  have p0002 := @gFvresi A (.cv y)
  have p0003 :=
    @gBreqan12d (.classMem (.cv x) A) (.classMem (.cv y) A)
      (synCfv (synCres (synCid) A) (.cv x)) (.cv x)
      (synCfv (synCres (synCid) A) (.cv y)) (.cv y) R p0001 p0002
  have p0004 :=
    @gBicomd (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWbr (synCfv (synCres (synCid) A) (.cv x)) R
        (synCfv (synCres (synCid) A) (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0003
  have p0005 :=
    @gRgen2a
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv (synCres (synCid) A) (.cv x)) R
          (synCfv (synCres (synCid) A) (.cv y))))
      x y A dv_cache_0001 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A A R R
      (synCres (synCid) A) dv_cache_0002 dv_cache_0001 dv_cache_0002 dv_cache_0001
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0007 :=
    @gMpbir2an (synWiso (synCres (synCid) A) R R A A)
      (synWf1o (synCres (synCid) A) A A)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv (synCres (synCid) A) (.cv x)) R
              (synCfv (synCres (synCid) A) (.cv y))))))
      p0000 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_isocnv`. -/
@[expose]
noncomputable def gIsocnv (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf (.imp (synWiso H R S A B) (synWiso (synCcnv H) S R B A)) :=
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
  have dv_cache_0001 : x ∉ ((synCfv (synCcnv H) (.cv z))).fv := by
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
  have dv_cache_0002 : y ∉ ((synCfv (synCcnv H) (.cv z))).fv :=
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
  have dv_cache_0003 : y ∉ ((synCfv (synCcnv H) (.cv w))).fv :=
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
      ((synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S (synCfv H (.cv y)))
          (synWbr (synCfv (synCcnv H) (.cv z)) R (.cv y)))).fv :=
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
      ((synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
            (synCfv H (synCfv (synCcnv H) (.cv w))))
          (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))))).fv :=
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
      ((synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
                (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))).fv :=
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
      ((synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
                (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))).fv :=
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
  have dv_cache_0024 : z ∉ ((synCcnv H)).fv :=
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
  have dv_cache_0025 : w ∉ ((synCcnv H)).fv :=
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
  have p0000 := @gF1ocnv A B H
  have p0001 :=
    @gAdantr (synWf1o H A B) (synWf1o (synCcnv H) B A)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      p0000
  have p0002 := @gF1ocnvfv2 A B (.cv z) H
  have p0003 :=
    @gAdantrr (synWf1o H A B) (.classMem (.cv z) B)
      (.classEq (synCfv H (synCfv (synCcnv H) (.cv z))) (.cv z)) (.classMem (.cv w) B)
      p0002
  have p0004 := @gF1ocnvfv2 A B (.cv w) H
  have p0005 :=
    @gAdantrl (synWf1o H A B) (.classMem (.cv w) B)
      (.classEq (synCfv H (synCfv (synCcnv H) (.cv w))) (.cv w)) (.classMem (.cv z) B)
      p0004
  have p0006 :=
    @gBreq12d
      (synWa (synWf1o H A B) (synWa (.classMem (.cv z) B) (.classMem (.cv w) B)))
      (synCfv H (synCfv (synCcnv H) (.cv z))) (.cv z)
      (synCfv H (synCfv (synCcnv H) (.cv w))) (.cv w) S p0003 p0005
  have p0007 :=
    @gAdantlr (synWf1o H A B) (synWa (.classMem (.cv z) B) (.classMem (.cv w) B))
      (synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
          (synCfv H (synCfv (synCcnv H) (.cv w)))) (synWbr (.cv z) S (.cv w)))
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      p0006
  have p0008 := @gF1of B A (synCcnv H)
  have p0009 :=
    @gSyl (synWf1o H A B) (synWf1o (synCcnv H) B A) (synWf (synCcnv H) B A) p0000
      p0008
  have p0010 := @gFfvelrn B A (.cv z) (synCcnv H)
  have p0011 := @gFfvelrn B A (.cv w) (synCcnv H)
  have p0012 :=
    @gAnim12dan (synWf (synCcnv H) B A) (.classMem (.cv z) B)
      (.classMem (synCfv (synCcnv H) (.cv z)) A) (.classMem (.cv w) B)
      (.classMem (synCfv (synCcnv H) (.cv w)) A) p0010 p0011
  have p0013 := @gBreq1 (.cv x) (synCfv (synCcnv H) (.cv z)) (.cv y) R
  have p0014 := @gFveq2 (.cv x) (synCfv (synCcnv H) (.cv z)) H
  have p0015 :=
    @gBreq1d (.classEq (.cv x) (synCfv (synCcnv H) (.cv z))) (synCfv H (.cv x))
      (synCfv H (synCfv (synCcnv H) (.cv z))) (synCfv H (.cv y)) S p0014
  have p0016 :=
    @gBibi12d (.classEq (.cv x) (synCfv (synCcnv H) (.cv z)))
      (synWbr (.cv x) R (.cv y)) (synWbr (synCfv (synCcnv H) (.cv z)) R (.cv y))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
      (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S (synCfv H (.cv y))) p0013
      p0015
  have p0017 :=
    @gBicom (synWbr (synCfv (synCcnv H) (.cv z)) R (.cv y))
      (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S (synCfv H (.cv y)))
  have p0018 :=
    @gSyl6bb (.classEq (.cv x) (synCfv (synCcnv H) (.cv z)))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr (synCfv (synCcnv H) (.cv z)) R (.cv y))
        (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S (synCfv H (.cv y))))
      (synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S (synCfv H (.cv y)))
        (synWbr (synCfv (synCcnv H) (.cv z)) R (.cv y)))
      p0016 p0017
  have p0019 := @gFveq2 (.cv y) (synCfv (synCcnv H) (.cv w)) H
  have p0020 :=
    @gBreq2d (.classEq (.cv y) (synCfv (synCcnv H) (.cv w))) (synCfv H (.cv y))
      (synCfv H (synCfv (synCcnv H) (.cv w)))
      (synCfv H (synCfv (synCcnv H) (.cv z))) S p0019
  have p0021 :=
    @gBreq2 (.cv y) (synCfv (synCcnv H) (.cv w)) (synCfv (synCcnv H) (.cv z)) R
  have p0022 :=
    @gBibi12d (.classEq (.cv y) (synCfv (synCcnv H) (.cv w)))
      (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S (synCfv H (.cv y)))
      (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
        (synCfv H (synCfv (synCcnv H) (.cv w))))
      (synWbr (synCfv (synCcnv H) (.cv z)) R (.cv y))
      (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))) p0020
      p0021
  have p0023 :=
    @gRspc2va
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
          (synCfv H (synCfv (synCcnv H) (.cv w))))
        (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))))
      (synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S (synCfv H (.cv y)))
        (synWbr (synCfv (synCcnv H) (.cv z)) R (.cv y)))
      x y (synCfv (synCcnv H) (.cv z)) (synCfv (synCcnv H) (.cv w)) A A dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0018 p0022
  have p0024 :=
    @gSylan
      (synWa (synWf (synCcnv H) B A) (synWa (.classMem (.cv z) B) (.classMem (.cv w) B)))
      (synWa (.classMem (synCfv (synCcnv H) (.cv z)) A)
        (.classMem (synCfv (synCcnv H) (.cv w)) A))
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
          (synCfv H (synCfv (synCcnv H) (.cv w))))
        (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))))
      p0012 p0023
  have p0025 :=
    @gAn32s (synWf (synCcnv H) B A)
      (synWa (.classMem (.cv z) B) (.classMem (.cv w) B))
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
          (synCfv H (synCfv (synCcnv H) (.cv w))))
        (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))))
      p0024
  have p0026 :=
    @gSylanl1 (synWf1o H A B) (synWf (synCcnv H) B A)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWa (.classMem (.cv z) B) (.classMem (.cv w) B))
      (synWb (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
          (synCfv H (synCfv (synCcnv H) (.cv w))))
        (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))))
      p0009 p0025
  have p0027 :=
    @gBitr3d
      (synWa (synWa (synWf1o H A B) (synWral x A (synWral y A
              (synWb (synWbr (.cv x) R (.cv y))
                (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
        (synWa (.classMem (.cv z) B) (.classMem (.cv w) B)))
      (synWbr (synCfv H (synCfv (synCcnv H) (.cv z))) S
        (synCfv H (synCfv (synCcnv H) (.cv w))))
      (synWbr (.cv z) S (.cv w))
      (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))) p0007
      p0026
  have p0028 :=
    @gRalrimivva
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWb (synWbr (.cv z) S (.cv w))
        (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))))
      z w B B dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0027
  have p0029 :=
    @gJca
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWf1o (synCcnv H) B A)
      (synWral z B (synWral w B (synWb (synWbr (.cv z) S (.cv w))
            (synWbr (synCfv (synCcnv H) (.cv z)) R (synCfv (synCcnv H) (.cv w))))))
      p0001 p0028
  have p0030 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0004 dv_cache_0005 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0008
  have p0031 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso z w B A S R
      (synCcnv H) dv_cache_0021 dv_cache_0009 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0012
  have p0032 :=
    @gN3imtr4i
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWa (synWf1o (synCcnv H) B A) (synWral z B (synWral w B
            (synWb (synWbr (.cv z) S (.cv w)) (synWbr (synCfv (synCcnv H) (.cv z)) R
                (synCfv (synCcnv H) (.cv w)))))))
      (synWiso H R S A B) (synWiso (synCcnv H) S R B A) p0029 p0030 p0031
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

/-- Checked nominal proof certificate identified upstream as `g_isores2`. -/
@[expose]
noncomputable def gIsores2 (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf
      (synWb (synWiso H R S A B) (synWiso H R (synCin S (synCxp B B)) A B)) :=
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
  have dv_cache_0001 : y ∉ ((synWa (synWf1o H A B) (.classMem (.cv x) A))).fv := by
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
  have dv_cache_0002 : x ∉ ((synWf1o H A B)).fv :=
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
  have dv_cache_0014 : x ∉ ((synCin S (synCxp B B))).fv :=
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
  have dv_cache_0015 : y ∉ ((synCin S (synCxp B B))).fv :=
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
  have p0000 := @gF1of A B H
  have p0001 := @gFfvelrn A B (.cv x) H
  have p0002 :=
    @gAdantrr (synWf H A B) (.classMem (.cv x) A) (.classMem (synCfv H (.cv x)) B)
      (.classMem (.cv y) A) p0001
  have p0003 := @gFfvelrn A B (.cv y) H
  have p0004 :=
    @gAdantrl (synWf H A B) (.classMem (.cv y) A) (.classMem (synCfv H (.cv y)) B)
      (.classMem (.cv x) A) p0003
  have p0005 := @gBrinxp (synCfv H (.cv x)) (synCfv H (.cv y)) B B S
  have p0006 :=
    @gSyl2anc
      (synWa (synWf H A B) (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)))
      (.classMem (synCfv H (.cv x)) B) (.classMem (synCfv H (.cv y)) B)
      (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
        (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y))))
      p0002 p0004 p0005
  have p0007 :=
    @gSylan (synWf1o H A B) (synWf H A B)
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
        (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y))))
      p0000 p0006
  have p0008 :=
    @gAnassrs (synWf1o H A B) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
        (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y))))
      p0007
  have p0009 :=
    @gBibi2d
      (synWa (synWa (synWf1o H A B) (.classMem (.cv x) A)) (.classMem (.cv y) A))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
      (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0008
  have p0010 :=
    @gRalbidva (synWa (synWf1o H A B) (.classMem (.cv x) A))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr (.cv x) R (.cv y))
        (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y))))
      y A dv_cache_0001 p0009
  have p0011 :=
    @gRalbidva (synWf1o H A B)
      (synWral y A (synWb (synWbr (.cv x) R (.cv y))
          (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))
      (synWral y A (synWb (synWbr (.cv x) R (.cv y))
          (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y)))))
      x A dv_cache_0002 p0010
  have p0012 :=
    @gPm532i (synWf1o H A B)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))))
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y))))))
      p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R S H
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0014 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A B R
      (synCin S (synCxp B B)) H dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0014 dv_cache_0015
      dv_cache_0013
  have p0015 :=
    @gN3bitr4i
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))
      (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv H (.cv x)) (synCin S (synCxp B B)) (synCfv H (.cv y)))))))
      (synWiso H R S A B) (synWiso H R (synCin S (synCxp B B)) A B) p0012 p0013 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_isores1`. -/
@[expose]
noncomputable def gIsores1 (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf
      (synWb (synWiso H R S A B) (synWiso H (synCin R (synCxp A A)) S A B)) :=
  by
  have p0000 := @gIsocnv A B R S H
  have p0001 := @gIsores2 B A S R (synCcnv H)
  have p0002 :=
    @gSylib (synWiso H R S A B) (synWiso (synCcnv H) S R B A)
      (synWiso (synCcnv H) S (synCin R (synCxp A A)) B A) p0000 p0001
  have p0003 := @gIsocnv B A S (synCin R (synCxp A A)) (synCcnv H)
  have p0004 :=
    @gSyl (synWiso H R S A B) (synWiso (synCcnv H) S (synCin R (synCxp A A)) B A)
      (synWiso (synCcnv (synCcnv H)) (synCin R (synCxp A A)) S A B) p0002 p0003
  have p0005 := @gCnvcnv H
  have p0006 := @gIsoeq1 A B (synCin R (synCxp A A)) S H (synCcnv (synCcnv H))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gSylib (synWiso H R S A B)
      (synWiso (synCcnv (synCcnv H)) (synCin R (synCxp A A)) S A B)
      (synWiso H (synCin R (synCxp A A)) S A B) p0004 p0007
  have p0009 := @gIsocnv A B (synCin R (synCxp A A)) S H
  have p0010 :=
    @gSylibr (synWiso H (synCin R (synCxp A A)) S A B)
      (synWiso (synCcnv H) S (synCin R (synCxp A A)) B A)
      (synWiso (synCcnv H) S R B A) p0009 p0001
  have p0011 := @gIsocnv B A S R (synCcnv H)
  have p0012 :=
    @gSyl (synWiso H (synCin R (synCxp A A)) S A B) (synWiso (synCcnv H) S R B A)
      (synWiso (synCcnv (synCcnv H)) R S A B) p0010 p0011
  have p0013 := @gIsoeq1 A B R S H (synCcnv (synCcnv H))
  have p0014 := Nominal.mp p0005 p0013
  have p0015 :=
    @gSylib (synWiso H (synCin R (synCxp A A)) S A B)
      (synWiso (synCcnv (synCcnv H)) R S A B) (synWiso H R S A B) p0012 p0014
  have p0016 :=
    @gImpbii (synWiso H R S A B) (synWiso H (synCin R (synCxp A A)) S A B) p0008
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

/-- Checked nominal proof certificate identified upstream as `g_isotr`. -/
@[expose]
noncomputable def gIsotr (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (T : Class) (G : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWiso H R S A B) (synWiso G S T B C))
        (synWiso (synCcom G H) R T A C)) :=
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
  have dv_cache_0001 : u ∉ ((synCfv H (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_H, or_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((synCfv H (.cv x))).fv :=
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
  have dv_cache_0003 : v ∉ ((synCfv H (.cv y))).fv :=
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
      ((synWb (synWbr (synCfv H (.cv x)) S (.cv v))
          (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (.cv v))))).fv :=
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
      ((synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
          (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))))).fv :=
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
      ((synWb (synWbr (.cv x) R (.cv w))
          (synWbr (synCfv H (.cv x)) S (synCfv H (.cv w))))).fv :=
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
      ((synWb (synWbr (.cv x) R (.cv y))
          (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))).fv :=
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
      ((synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
                (synWb (synWbr (.cv z) R (.cv w))
                  (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))))))
          (synWa (synWf1o G B C) (synWral u B (synWral v B
                (synWb (synWbr (.cv u) S (.cv v))
                  (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))).fv :=
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
      ((synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
                (synWb (synWbr (.cv z) R (.cv w))
                  (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))))))
          (synWa (synWf1o G B C) (synWral u B (synWral v B
                (synWb (synWbr (.cv u) S (.cv v))
                  (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))).fv :=
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
  have dv_cache_0040 : x ∉ ((synCcom G H)).fv :=
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
  have dv_cache_0041 : y ∉ ((synCcom G H)).fv :=
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
  have p0000 := @gF1oco A B C G H
  have p0001 :=
    @gAd2ant2r (synWf1o G B C) (synWf1o H A B) (synWf1o (synCcom G H) A C)
      (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
            (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))
      (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
            (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))
      p0000
  have p0002 :=
    @gAncoms
      (synWa (synWf1o G B C) (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
              (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v)))))))
      (synWa (synWf1o H A B) (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
              (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))))))
      (synWf1o (synCcom G H) A C) p0001
  have p0003 := @gF1of A B H
  have p0004 := @gFfvelrn A B (.cv x) H
  have p0005 :=
    @gEx (synWf H A B) (.classMem (.cv x) A) (.classMem (synCfv H (.cv x)) B) p0004
  have p0006 := @gFfvelrn A B (.cv y) H
  have p0007 :=
    @gEx (synWf H A B) (.classMem (.cv y) A) (.classMem (synCfv H (.cv y)) B) p0006
  have p0008 :=
    @gAnim12d (synWf H A B) (.classMem (.cv x) A) (.classMem (synCfv H (.cv x)) B)
      (.classMem (.cv y) A) (.classMem (synCfv H (.cv y)) B) p0005 p0007
  have p0009 :=
    @gSyl (synWf1o H A B) (synWf H A B)
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (synWa (.classMem (synCfv H (.cv x)) B) (.classMem (synCfv H (.cv y)) B)))
      p0003 p0008
  have p0010 :=
    @gAdantr (synWf1o H A B)
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (synWa (.classMem (synCfv H (.cv x)) B) (.classMem (synCfv H (.cv y)) B)))
      (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
            (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))
      p0009
  have p0011 := @gBreq1 (.cv u) (synCfv H (.cv x)) (.cv v) S
  have p0012 := @gFveq2 (.cv u) (synCfv H (.cv x)) G
  have p0013 :=
    @gBreq1d (.classEq (.cv u) (synCfv H (.cv x))) (synCfv G (.cv u))
      (synCfv G (synCfv H (.cv x))) (synCfv G (.cv v)) T p0012
  have p0014 :=
    @gBibi12d (.classEq (.cv u) (synCfv H (.cv x))) (synWbr (.cv u) S (.cv v))
      (synWbr (synCfv H (.cv x)) S (.cv v))
      (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v)))
      (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (.cv v))) p0011 p0013
  have p0015 := @gBreq2 (.cv v) (synCfv H (.cv y)) (synCfv H (.cv x)) S
  have p0016 := @gFveq2 (.cv v) (synCfv H (.cv y)) G
  have p0017 :=
    @gBreq2d (.classEq (.cv v) (synCfv H (.cv y))) (synCfv G (.cv v))
      (synCfv G (synCfv H (.cv y))) (synCfv G (synCfv H (.cv x))) T p0016
  have p0018 :=
    @gBibi12d (.classEq (.cv v) (synCfv H (.cv y)))
      (synWbr (synCfv H (.cv x)) S (.cv v))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
      (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (.cv v)))
      (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))) p0015
      p0017
  have p0019 :=
    @gRspc2v
      (synWb (synWbr (.cv u) S (.cv v)) (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))
      (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
        (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))))
      (synWb (synWbr (synCfv H (.cv x)) S (.cv v))
        (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (.cv v))))
      u v (synCfv H (.cv x)) (synCfv H (.cv y)) B B dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 p0014 p0018
  have p0020 :=
    @gCom12 (synWa (.classMem (synCfv H (.cv x)) B) (.classMem (synCfv H (.cv y)) B))
      (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
            (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))
      (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
        (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))))
      p0019
  have p0021 :=
    @gAdantl
      (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
            (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))
      (.imp (synWa (.classMem (synCfv H (.cv x)) B) (.classMem (synCfv H (.cv y)) B))
        (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
          (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y))))))
      (synWf1o G B C) p0020
  have p0022 :=
    @gSylan9
      (synWa (synWf1o H A B) (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
              (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWa (.classMem (synCfv H (.cv x)) B) (.classMem (synCfv H (.cv y)) B))
      (synWa (synWf1o G B C) (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
              (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v)))))))
      (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
        (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))))
      p0010 p0021
  have p0023 :=
    @gImp
      (synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
              (synWb (synWbr (.cv z) R (.cv w))
                (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))) (synWa (synWf1o G B C)
          (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
                (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWb (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
        (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))))
      p0022
  have p0024 := @gBreq1 (.cv z) (.cv x) (.cv w) R
  have p0025 := @gFveq2 (.cv z) (.cv x) H
  have p0026_e00_recanon :
    Nominal.NPrf (.imp (.objEq z x) (.classEq (synCfv H (.cv z)) (synCfv H (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCfv synCio synCuni synWex synWa synCsn synWbr synCop synCun
          synCnin synWnan synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0026 :=
    @gBreq1d (.objEq z x) (synCfv H (.cv z)) (synCfv H (.cv x)) (synCfv H (.cv w)) S
      p0026_e00_recanon
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (synWb (synWbr (.cv z) R (.cv w)) (synWbr (.cv x) R (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0027 :=
    @gBibi12d (.objEq z x) (synWbr (.cv z) R (.cv w)) (synWbr (.cv x) R (.cv w))
      (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv w))) p0027_e00_recanon p0026
  have p0028 := @gBreq2 (.cv w) (.cv y) (.cv x) R
  have p0029 := @gFveq2 (.cv w) (.cv y) H
  have p0030_e00_recanon :
    Nominal.NPrf (.imp (.objEq w y) (.classEq (synCfv H (.cv w)) (synCfv H (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCfv synCio synCuni synWex synWa synCsn synWbr synCop synCun
          synCnin synWnan synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0030 :=
    @gBreq2d (.objEq w y) (synCfv H (.cv w)) (synCfv H (.cv y)) (synCfv H (.cv x)) S
      p0030_e00_recanon
  have p0031_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (synWb (synWbr (.cv x) R (.cv w)) (synWbr (.cv x) R (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0028
  have p0031 :=
    @gBibi12d (.objEq w y) (synWbr (.cv x) R (.cv w)) (synWbr (.cv x) R (.cv y))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv w)))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))) p0031_e00_recanon p0030
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (synWb (synWb (synWbr (.cv z) R (.cv w))
            (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))
          (synWb (synWbr (.cv x) R (.cv w))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv w)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0032_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y)) (synWb (synWb (synWbr (.cv x) R (.cv w))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv w))))
          (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @gRspc2v
      (synWb (synWbr (.cv z) R (.cv w)) (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWb (synWbr (.cv x) R (.cv w)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv w))))
      z w (.cv x) (.cv y) A A dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      p0032_e00_recanon p0032_e01_recanon
  have p0033 :=
    @gImpcom (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
            (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      p0032
  have p0034 :=
    @gAdantll
      (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
            (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWf1o H A B) p0033
  have p0035 :=
    @gAdantlr
      (synWa (synWf1o H A B) (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
              (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y))))
      (synWa (synWf1o G B C) (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
              (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v)))))))
      p0034
  have p0036 :=
    @gAd2antrr (synWf1o H A B) (synWf H A B)
      (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
            (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))
      (synWa (synWf1o G B C) (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
              (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v)))))))
      p0003
  have p0037 := @gFvco3 A B (.cv x) G H
  have p0038 := @gFvco3 A B (.cv y) G H
  have p0039 :=
    @gBreqan12d (synWa (synWf H A B) (.classMem (.cv x) A))
      (synWa (synWf H A B) (.classMem (.cv y) A)) (synCfv (synCcom G H) (.cv x))
      (synCfv G (synCfv H (.cv x))) (synCfv (synCcom G H) (.cv y))
      (synCfv G (synCfv H (.cv y))) T p0037 p0038
  have p0040 :=
    @gAnandis (synWf H A B) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (synWb (synWbr (synCfv (synCcom G H) (.cv x)) T (synCfv (synCcom G H) (.cv y)))
        (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))))
      p0039
  have p0041 :=
    @gSylan
      (synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
              (synWb (synWbr (.cv z) R (.cv w))
                (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))) (synWa (synWf1o G B C)
          (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
                (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))
      (synWf H A B) (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWb (synWbr (synCfv (synCcom G H) (.cv x)) T (synCfv (synCcom G H) (.cv y)))
        (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y)))))
      p0036 p0040
  have p0042 :=
    @gN3bitr4d
      (synWa (synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
                (synWb (synWbr (.cv z) R (.cv w))
                  (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))))))
          (synWa (synWf1o G B C) (synWral u B (synWral v B
                (synWb (synWbr (.cv u) S (.cv v))
                  (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))
        (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)))
      (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))
      (synWbr (synCfv G (synCfv H (.cv x))) T (synCfv G (synCfv H (.cv y))))
      (synWbr (.cv x) R (.cv y))
      (synWbr (synCfv (synCcom G H) (.cv x)) T (synCfv (synCcom G H) (.cv y))) p0023
      p0035 p0041
  have p0043 :=
    @gRalrimivva
      (synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
              (synWb (synWbr (.cv z) R (.cv w))
                (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))) (synWa (synWf1o G B C)
          (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
                (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))
      (synWb (synWbr (.cv x) R (.cv y))
        (synWbr (synCfv (synCcom G H) (.cv x)) T (synCfv (synCcom G H) (.cv y))))
      x y A A dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0042
  have p0044 :=
    @gJca
      (synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
              (synWb (synWbr (.cv z) R (.cv w))
                (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))) (synWa (synWf1o G B C)
          (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
                (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))
      (synWf1o (synCcom G H) A C)
      (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv (synCcom G H) (.cv x)) T (synCfv (synCcom G H) (.cv y))))))
      p0002 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso z w A B R S H
      dv_cache_0012 dv_cache_0013 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0016
  have p0046 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso u v B C S T G
      dv_cache_0004 dv_cache_0005 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
      dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0008
  have p0047 :=
    @gAnbi12i (synWiso H R S A B)
      (synWa (synWf1o H A B) (synWral z A (synWral w A (synWb (synWbr (.cv z) R (.cv w))
              (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w)))))))
      (synWiso G S T B C)
      (synWa (synWf1o G B C) (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
              (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v)))))))
      p0045 p0046
  have p0048 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y A C R T
      (synCcom G H) dv_cache_0037 dv_cache_0017 dv_cache_0038 dv_cache_0039 dv_cache_0040
      dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0020
  have p0049 :=
    @gN3imtr4i
      (synWa (synWa (synWf1o H A B) (synWral z A (synWral w A
              (synWb (synWbr (.cv z) R (.cv w))
                (synWbr (synCfv H (.cv z)) S (synCfv H (.cv w))))))) (synWa (synWf1o G B C)
          (synWral u B (synWral v B (synWb (synWbr (.cv u) S (.cv v))
                (synWbr (synCfv G (.cv u)) T (synCfv G (.cv v))))))))
      (synWa (synWf1o (synCcom G H) A C) (synWral x A (synWral y A
            (synWb (synWbr (.cv x) R (.cv y)) (synWbr (synCfv (synCcom G H) (.cv x)) T
                (synCfv (synCcom G H) (.cv y)))))))
      (synWa (synWiso H R S A B) (synWiso G S T B C)) (synWiso (synCcom G H) R T A C)
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

/-- Checked nominal proof certificate identified upstream as `g_isoini`. -/
@[expose]
noncomputable def gIsoini (A : Class) (B : Class) (D : Class) (R : Class) (S : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWiso H R S A B) (.classMem D A))
        (.classEq (synCima H (synCin A (synCima (synCcnv R) (synCsn D))))
          (synCin B (synCima (synCcnv S) (synCsn (synCfv H D)))))) :=
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
  have dv_cache_0004 : x ∉ ((synWa (synWiso H R S A B) (.classMem D A))).fv :=
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
  have dv_cache_0005 : x ∉ ((synWbr (.cv y) S (synCfv H D))).fv :=
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
    y ∉ ((synCin B (synCima (synCcnv S) (synCsn (synCfv H D))))).fv :=
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
  have dv_cache_0007 : y ∉ ((synWa (synWiso H R S A B) (.classMem D A))).fv :=
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
  have dv_cache_0009 : y ∉ ((synCin A (synCima (synCcnv R) (synCsn D)))).fv :=
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
  have dv_cache_0010 : x ∉ ((synCin A (synCima (synCcnv R) (synCsn D)))).fv :=
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
  have p0000 := @gElin (.cv y) B (synCima (synCcnv S) (synCsn (synCfv H D)))
  have p0001 := @gEliniseg S (synCfv H D) (.cv y)
  have p0002 :=
    @gAnbi2i (.classMem (.cv y) (synCima (synCcnv S) (synCsn (synCfv H D))))
      (synWbr (.cv y) S (synCfv H D)) (.classMem (.cv y) B) p0001
  have p0003 :=
    @gBitri
      (.classMem (.cv y) (synCin B (synCima (synCcnv S) (synCsn (synCfv H D)))))
      (synWa (.classMem (.cv y) B)
        (.classMem (.cv y) (synCima (synCcnv S) (synCsn (synCfv H D)))))
      (synWa (.classMem (.cv y) B) (synWbr (.cv y) S (synCfv H D))) p0000 p0002
  have p0004 := @gIsof1o A B R S H
  have p0005 := @gF1ofo A B H
  have p0006 := @gSyl (synWiso H R S A B) (synWf1o H A B) (synWfo H A B) p0004 p0005
  have p0007 := @gForn A B H
  have p0008 :=
    @gSyl (synWiso H R S A B) (synWfo H A B) (.classEq (synCrn H) B) p0006 p0007
  have p0009 := @gEleq2d (synWiso H R S A B) (synCrn H) B (.cv y) p0008
  have p0010 := @gF1ofn A B H
  have p0011 := @gSyl (synWiso H R S A B) (synWf1o H A B) (synWfn H A) p0004 p0010
  have p0012 := @gFvelrnb x A (.cv y) H dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0013 :=
    @gSyl (synWiso H R S A B) (synWfn H A)
      (synWb (.classMem (.cv y) (synCrn H))
        (synWrex x A (.classEq (synCfv H (.cv x)) (.cv y))))
      p0011 p0012
  have p0014 :=
    @gBitr3d (synWiso H R S A B) (.classMem (.cv y) (synCrn H)) (.classMem (.cv y) B)
      (synWrex x A (.classEq (synCfv H (.cv x)) (.cv y))) p0009 p0013
  have p0015 :=
    @gAnbi1d (synWiso H R S A B) (.classMem (.cv y) B)
      (synWrex x A (.classEq (synCfv H (.cv x)) (.cv y)))
      (synWbr (.cv y) S (synCfv H D)) p0014
  have p0016 :=
    @gAdantr (synWiso H R S A B)
      (synWb (synWa (.classMem (.cv y) B) (synWbr (.cv y) S (synCfv H D)))
        (synWa (synWrex x A (.classEq (synCfv H (.cv x)) (.cv y)))
          (synWbr (.cv y) S (synCfv H D))))
      (.classMem D A) p0015
  have p0017 := @gElin (.cv x) A (synCima (synCcnv R) (synCsn D))
  have p0018 := @gEliniseg R D (.cv x)
  have p0019 :=
    @gAnbi2i (.classMem (.cv x) (synCima (synCcnv R) (synCsn D)))
      (synWbr (.cv x) R D) (.classMem (.cv x) A) p0018
  have p0020 :=
    @gBitri (.classMem (.cv x) (synCin A (synCima (synCcnv R) (synCsn D))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) (synCima (synCcnv R) (synCsn D))))
      (synWa (.classMem (.cv x) A) (synWbr (.cv x) R D)) p0017 p0019
  have p0021 :=
    @gAnbi1i (.classMem (.cv x) (synCin A (synCima (synCcnv R) (synCsn D))))
      (synWa (.classMem (.cv x) A) (synWbr (.cv x) R D)) (synWbr (.cv x) H (.cv y))
      p0020
  have p0022 :=
    @gAnass (.classMem (.cv x) A) (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y))
  have p0023 :=
    @gBitri
      (synWa (.classMem (.cv x) (synCin A (synCima (synCcnv R) (synCsn D))))
        (synWbr (.cv x) H (.cv y)))
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) R D)) (synWbr (.cv x) H (.cv y)))
      (synWa (.classMem (.cv x) A) (synWa (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y))))
      p0021 p0022
  have p0024 := @gFnbrfvb A (.cv x) (.cv y) H
  have p0025 :=
    @gSylan (synWiso H R S A B) (synWfn H A) (.classMem (.cv x) A)
      (synWb (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv x) H (.cv y))) p0011
      p0024
  have p0026 :=
    @gAdantrr (synWiso H R S A B) (.classMem (.cv x) A)
      (synWb (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv x) H (.cv y)))
      (.classMem D A) p0025
  have p0027 :=
    @gBicomd (synWa (synWiso H R S A B) (synWa (.classMem (.cv x) A) (.classMem D A)))
      (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv x) H (.cv y)) p0026
  have p0028 := @gIsorel A B (.cv x) D R S H
  have p0029 :=
    @gAnbi12d
      (synWa (synWiso H R S A B) (synWa (.classMem (.cv x) A) (.classMem D A)))
      (synWbr (.cv x) H (.cv y)) (.classEq (synCfv H (.cv x)) (.cv y))
      (synWbr (.cv x) R D) (synWbr (synCfv H (.cv x)) S (synCfv H D)) p0027 p0028
  have p0030 := @gAncom (synWbr (.cv x) H (.cv y)) (synWbr (.cv x) R D)
  have p0031 := @gBreq1 (synCfv H (.cv x)) (.cv y) (synCfv H D) S
  have p0032 :=
    @gPm532i (.classEq (synCfv H (.cv x)) (.cv y))
      (synWbr (synCfv H (.cv x)) S (synCfv H D)) (synWbr (.cv y) S (synCfv H D))
      p0031
  have p0033 :=
    @gN3bitr3g
      (synWa (synWiso H R S A B) (synWa (.classMem (.cv x) A) (.classMem D A)))
      (synWa (synWbr (.cv x) H (.cv y)) (synWbr (.cv x) R D))
      (synWa (.classEq (synCfv H (.cv x)) (.cv y))
        (synWbr (synCfv H (.cv x)) S (synCfv H D)))
      (synWa (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y)))
      (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D)))
      p0029 p0030 p0032
  have p0034 :=
    @gExp32 (synWiso H R S A B) (.classMem (.cv x) A) (.classMem D A)
      (synWb (synWa (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y)))
        (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D))))
      p0033
  have p0035 :=
    @gCom23 (synWiso H R S A B) (.classMem (.cv x) A) (.classMem D A)
      (synWb (synWa (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y)))
        (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D))))
      p0034
  have p0036 :=
    @gImp (synWiso H R S A B) (.classMem D A)
      (.imp (.classMem (.cv x) A)
        (synWb (synWa (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y)))
          (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D)))))
      p0035
  have p0037 :=
    @gPm532d (synWa (synWiso H R S A B) (.classMem D A)) (.classMem (.cv x) A)
      (synWa (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y)))
      (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D)))
      p0036
  have p0038 :=
    @gSyl5bb
      (synWa (.classMem (.cv x) (synCin A (synCima (synCcnv R) (synCsn D))))
        (synWbr (.cv x) H (.cv y)))
      (synWa (.classMem (.cv x) A) (synWa (synWbr (.cv x) R D) (synWbr (.cv x) H (.cv y))))
      (synWa (synWiso H R S A B) (.classMem D A))
      (synWa (.classMem (.cv x) A)
        (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D))))
      p0023 p0037
  have p0039 :=
    @gRexbidv2 (synWa (synWiso H R S A B) (.classMem D A)) (synWbr (.cv x) H (.cv y))
      (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D))) x
      (synCin A (synCima (synCcnv R) (synCsn D))) A dv_cache_0004 p0038
  have p0040 :=
    @gR1941v (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D)) x
      A dv_cache_0005
  have p0041 :=
    @gSyl6bb (synWa (synWiso H R S A B) (.classMem D A))
      (synWrex x (synCin A (synCima (synCcnv R) (synCsn D))) (synWbr (.cv x) H (.cv y)))
      (synWrex x A
        (synWa (.classEq (synCfv H (.cv x)) (.cv y)) (synWbr (.cv y) S (synCfv H D))))
      (synWa (synWrex x A (.classEq (synCfv H (.cv x)) (.cv y)))
        (synWbr (.cv y) S (synCfv H D)))
      p0039 p0040
  have p0042 :=
    @gBitr4d (synWa (synWiso H R S A B) (.classMem D A))
      (synWa (.classMem (.cv y) B) (synWbr (.cv y) S (synCfv H D)))
      (synWa (synWrex x A (.classEq (synCfv H (.cv x)) (.cv y)))
        (synWbr (.cv y) S (synCfv H D)))
      (synWrex x (synCin A (synCima (synCcnv R) (synCsn D))) (synWbr (.cv x) H (.cv y)))
      p0016 p0041
  have p0043 :=
    @gSyl5bb
      (.classMem (.cv y) (synCin B (synCima (synCcnv S) (synCsn (synCfv H D)))))
      (synWa (.classMem (.cv y) B) (synWbr (.cv y) S (synCfv H D)))
      (synWa (synWiso H R S A B) (.classMem D A))
      (synWrex x (synCin A (synCima (synCcnv R) (synCsn D))) (synWbr (.cv x) H (.cv y)))
      p0003 p0042
  have p0044 :=
    @gEqabdv (synWa (synWiso H R S A B) (.classMem D A))
      (synWrex x (synCin A (synCima (synCcnv R) (synCsn D))) (synWbr (.cv x) H (.cv y)))
      y (synCin B (synCima (synCcnv S) (synCsn (synCfv H D)))) dv_cache_0006
      dv_cache_0007 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x H
      (synCin A (synCima (synCcnv R) (synCsn D))) dv_cache_0008 dv_cache_0003
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0046 :=
    @gSyl6reqr (synWa (synWiso H R S A B) (.classMem D A))
      (synCin B (synCima (synCcnv S) (synCsn (synCfv H D))))
      (.cab y (synWrex x (synCin A (synCima (synCcnv R) (synCsn D)))
          (synWbr (.cv x) H (.cv y))))
      (synCima H (synCin A (synCima (synCcnv R) (synCsn D)))) p0044 p0045
  exact p0046


end NFChoice.DirectNominalPrf.WPPReplay

end
