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

/-- Checked nominal proof certificate identified upstream as `g_imadif`. -/
@[expose]
noncomputable def gImadif (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun (synCcnv F)) (.classEq (synCima F (synCdif A B))
          (synCdif (synCima F A) (synCima F B)))) :=
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
  have dv_cache_0001 : x ∉ ((synWfun (synCcnv F))).fv := by
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
  have dv_cache_0003 : x ∉ ((synCcnv F)).fv :=
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
  have dv_cache_0005 : x ∉ ((synCdif A B)).fv :=
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
  have dv_cache_0008 : y ∉ ((synCima F (synCdif A B))).fv :=
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
  have dv_cache_0009 : y ∉ ((synCdif (synCima F A) (synCima F B))).fv :=
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
  have dv_cache_0010 : y ∉ ((synWfun (synCcnv F))).fv :=
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
    @gAnandir (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))
      (synWbr (.cv x) F (.cv y))
  have p0001 :=
    @gExbii
      (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (synWbr (.cv x) F (.cv y)))
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (synWa (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y))))
      x p0000
  have p0002 :=
    @gN1940 (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
      (synWa (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y))) x
  have p0003 :=
    @gSylbi
      (synWex x (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (synWbr (.cv x) F (.cv y))))
      (synWex x (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
          (synWa (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y)))))
      (synWa (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
        (synWex x (synWa (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y)))))
      p0001 p0002
  have p0004 := @gNfv (synWfun (synCcnv F)) x dv_cache_0001
  have p0005 :=
    @gNfe1 (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))) x
  have p0006 :=
    @gNfan (synWfun (synCcnv F))
      (synWex x (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))) x
      p0004 p0005
  have p0007 := @gFunmo x (.cv y) (synCcnv F) dv_cache_0002 dv_cache_0003
  have p0008 := @gBrcnv (.cv y) (.cv x) F
  have p0009 :=
    @gMobii (synWbr (.cv y) (synCcnv F) (.cv x)) (synWbr (.cv x) F (.cv y)) x p0008
  have p0010 :=
    @gSylib (synWfun (synCcnv F)) (synWmo x (synWbr (.cv y) (synCcnv F) (.cv x)))
      (synWmo x (synWbr (.cv x) F (.cv y))) p0007 p0009
  have p0011 := @gMopick (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)) x
  have p0012 :=
    @gSylan (synWfun (synCcnv F)) (synWmo x (synWbr (.cv x) F (.cv y)))
      (synWex x (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))
      (.imp (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))) p0010 p0011
  have p0013 :=
    @gCon2d
      (synWa (synWfun (synCcnv F))
        (synWex x (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))))
      (synWbr (.cv x) F (.cv y)) (.classMem (.cv x) B) p0012
  have p0014 := @gImnan (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))
  have p0015 :=
    @gSylib
      (synWa (synWfun (synCcnv F))
        (synWex x (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))))
      (.imp (.classMem (.cv x) B) (.neg (synWbr (.cv x) F (.cv y))))
      (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))) p0013 p0014
  have p0016 :=
    @gAlrimi
      (synWa (synWfun (synCcnv F))
        (synWex x (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))))
      (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))) x p0006 p0015
  have p0017 :=
    @gEx (synWfun (synCcnv F))
      (synWex x (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))
      (.all x (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))) p0016
  have p0018 := @gExancom (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)) x
  have p0019 := @gAlnex (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))) x
  have p0020 :=
    @gN3imtr3g (synWfun (synCcnv F))
      (synWex x (synWa (synWbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))
      (.all x (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))))
      (synWex x (synWa (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y))))
      (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))) p0017
      p0018 p0019
  have p0021 :=
    @gAnim2d (synWfun (synCcnv F))
      (synWex x (synWa (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y))))
      (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))))
      (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))) p0020
  have p0022 :=
    @gSyl5
      (synWex x (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (synWbr (.cv x) F (.cv y))))
      (synWa (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
        (synWex x (synWa (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y)))))
      (synWfun (synCcnv F))
      (synWa (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
        (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))))
      p0003 p0021
  have p0023 :=
    @gN1929r (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
      (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))) x
  have p0024 :=
    @gSylan2br
      (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))))
      (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
      (.all x (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))))
      (synWex x (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
          (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))))
      p0019 p0023
  have p0025 :=
    @gAndi (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
      (.neg (.classMem (.cv x) B)) (.neg (synWbr (.cv x) F (.cv y)))
  have p0026 := @gIanor (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))
  have p0027 :=
    @gAnbi2i (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))
      (synWo (.neg (.classMem (.cv x) B)) (.neg (synWbr (.cv x) F (.cv y))))
      (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))) p0026
  have p0028 :=
    @gAn32 (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)) (synWbr (.cv x) F (.cv y))
  have p0029 := @gPm324 (synWbr (.cv x) F (.cv y))
  have p0030 :=
    @gIntnan (synWa (synWbr (.cv x) F (.cv y)) (.neg (synWbr (.cv x) F (.cv y))))
      (.classMem (.cv x) A) p0029
  have p0031 :=
    @gAnass (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))
      (.neg (synWbr (.cv x) F (.cv y)))
  have p0032 :=
    @gMtbir
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (.neg (synWbr (.cv x) F (.cv y))))
      (synWa (.classMem (.cv x) A)
        (synWa (synWbr (.cv x) F (.cv y)) (.neg (synWbr (.cv x) F (.cv y)))))
      p0030 p0031
  have p0033 :=
    @gBiorfi
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (.neg (synWbr (.cv x) F (.cv y))))
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (.neg (.classMem (.cv x) B)))
      p0032
  have p0034 :=
    @gBitri
      (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (synWbr (.cv x) F (.cv y)))
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (.neg (.classMem (.cv x) B)))
      (synWo (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
          (.neg (.classMem (.cv x) B)))
        (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
          (.neg (synWbr (.cv x) F (.cv y)))))
      p0028 p0033
  have p0035 :=
    @gN3bitr4i
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (synWo (.neg (.classMem (.cv x) B)) (.neg (synWbr (.cv x) F (.cv y)))))
      (synWo (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
          (.neg (.classMem (.cv x) B)))
        (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
          (.neg (synWbr (.cv x) F (.cv y)))))
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))))
      (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (synWbr (.cv x) F (.cv y)))
      p0025 p0027 p0034
  have p0036 :=
    @gExbii
      (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
        (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))))
      (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (synWbr (.cv x) F (.cv y)))
      x p0035
  have p0037 :=
    @gSylib
      (synWa (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
        (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))))
      (synWex x (synWa (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)))
          (.neg (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))))
      (synWex x (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (synWbr (.cv x) F (.cv y))))
      p0024 p0036
  have p0038 :=
    @gImpbid1 (synWfun (synCcnv F))
      (synWex x (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (synWbr (.cv x) F (.cv y))))
      (synWa (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
        (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))))
      p0022 p0037
  have p0039 :=
    @gElima2 x (.cv y) F (synCdif A B) dv_cache_0002 dv_cache_0004 dv_cache_0005
  have p0040 := @gEldif (.cv x) A B
  have p0041 :=
    @gAnbi1i (.classMem (.cv x) (synCdif A B))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (synWbr (.cv x) F (.cv y)) p0040
  have p0042 :=
    @gExbii (synWa (.classMem (.cv x) (synCdif A B)) (synWbr (.cv x) F (.cv y)))
      (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
        (synWbr (.cv x) F (.cv y)))
      x p0041
  have p0043 :=
    @gBitri (.classMem (.cv y) (synCima F (synCdif A B)))
      (synWex x (synWa (.classMem (.cv x) (synCdif A B)) (synWbr (.cv x) F (.cv y))))
      (synWex x (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (synWbr (.cv x) F (.cv y))))
      p0039 p0042
  have p0044 := @gEldif (.cv y) (synCima F A) (synCima F B)
  have p0045 := @gElima2 x (.cv y) F A dv_cache_0002 dv_cache_0004 dv_cache_0006
  have p0046 := @gElima2 x (.cv y) F B dv_cache_0002 dv_cache_0004 dv_cache_0007
  have p0047 :=
    @gNotbii (.classMem (.cv y) (synCima F B))
      (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y)))) p0046
  have p0048 :=
    @gAnbi12i (.classMem (.cv y) (synCima F A))
      (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
      (.neg (.classMem (.cv y) (synCima F B)))
      (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))) p0045
      p0047
  have p0049 :=
    @gBitri (.classMem (.cv y) (synCdif (synCima F A) (synCima F B)))
      (synWa (.classMem (.cv y) (synCima F A)) (.neg (.classMem (.cv y) (synCima F B))))
      (synWa (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
        (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))))
      p0044 p0048
  have p0050 :=
    @gN3bitr4g (synWfun (synCcnv F))
      (synWex x (synWa (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (synWbr (.cv x) F (.cv y))))
      (synWa (synWex x (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
        (.neg (synWex x (synWa (.classMem (.cv x) B) (synWbr (.cv x) F (.cv y))))))
      (.classMem (.cv y) (synCima F (synCdif A B)))
      (.classMem (.cv y) (synCdif (synCima F A) (synCima F B))) p0038 p0043 p0049
  have p0051 :=
    @gEqrdv (synWfun (synCcnv F)) y (synCima F (synCdif A B))
      (synCdif (synCima F A) (synCima F B)) dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0050
  exact p0051

/-- Checked nominal proof certificate identified upstream as `g_imain`. -/
@[expose]
noncomputable def gImain (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun (synCcnv F))
        (.classEq (synCima F (synCin A B)) (synCin (synCima F A) (synCima F B)))) :=
  by
  have p0000 := @gImadif A (synCdif A B) F
  have p0001 := @gImadif A B F
  have p0002 :=
    @gDifeq2d (synWfun (synCcnv F)) (synCima F (synCdif A B))
      (synCdif (synCima F A) (synCima F B)) (synCima F A) p0001
  have p0003 :=
    @gEqtrd (synWfun (synCcnv F)) (synCima F (synCdif A (synCdif A B)))
      (synCdif (synCima F A) (synCima F (synCdif A B)))
      (synCdif (synCima F A) (synCdif (synCima F A) (synCima F B))) p0000 p0002
  have p0004 := @gDfin4 A B
  have p0005 := @gImaeq2i (synCin A B) (synCdif A (synCdif A B)) F p0004
  have p0006 := @gDfin4 (synCima F A) (synCima F B)
  have p0007 :=
    @gN3eqtr4g (synWfun (synCcnv F)) (synCima F (synCdif A (synCdif A B)))
      (synCdif (synCima F A) (synCdif (synCima F A) (synCima F B)))
      (synCima F (synCin A B)) (synCin (synCima F A) (synCima F B)) p0003 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_fneq1`. -/
@[expose]
noncomputable def gFneq1 (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (synWb (synWfn F A) (synWfn G A))) :=
  by
  have p0000 := @gFuneq F G
  have p0001 := @gDmeq F G
  have p0002 := @gEqeq1d (.classEq F G) (synCdm F) (synCdm G) A p0001
  have p0003 :=
    @gAnbi12d (.classEq F G) (synWfun F) (synWfun G) (.classEq (synCdm F) A)
      (.classEq (synCdm G) A) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWfn F A))
  have p0005 := (Nominal.biimpRefl (synWfn G A))
  have p0006 :=
    @gN3bitr4g (.classEq F G) (synWa (synWfun F) (.classEq (synCdm F) A))
      (synWa (synWfun G) (.classEq (synCdm G) A)) (synWfn F A) (synWfn G A) p0003
      p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fneq2`. -/
@[expose]
noncomputable def gFneq2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWfn F A) (synWfn F B))) :=
  by
  have p0000 := @gEqeq2 A B (synCdm F)
  have p0001 :=
    @gAnbi2d (.classEq A B) (.classEq (synCdm F) A) (.classEq (synCdm F) B)
      (synWfun F) p0000
  have p0002 := (Nominal.biimpRefl (synWfn F A))
  have p0003 := (Nominal.biimpRefl (synWfn F B))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (synWfun F) (.classEq (synCdm F) A))
      (synWa (synWfun F) (.classEq (synCdm F) B)) (synWfn F A) (synWfn F B) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fneq1d`. -/
@[expose]
noncomputable def gFneq1d (ph : Wff) (A : Class) (F : Class) (G : Class)
    (hyp_fneq1d_1 : Nominal.NPrf (.imp ph (.classEq F G))) :
    Nominal.NPrf (.imp ph (synWb (synWfn F A) (synWfn G A))) :=
  by
  have p0000 := @gFneq1 A F G
  have p0001 :=
    @gSyl ph (.classEq F G) (synWb (synWfn F A) (synWfn G A)) hyp_fneq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fneq2d`. -/
@[expose]
noncomputable def gFneq2d (ph : Wff) (A : Class) (B : Class) (F : Class)
    (hyp_fneq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWfn F A) (synWfn F B))) :=
  by
  have p0000 := @gFneq2 A B F
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWfn F A) (synWfn F B)) hyp_fneq2d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fneq1i`. -/
@[expose]
noncomputable def gFneq1i (A : Class) (F : Class) (G : Class)
    (hyp_fneq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (synWb (synWfn F A) (synWfn G A)) :=
  by
  have p0000 := @gFneq1 A F G
  have p0001 := Nominal.mp hyp_fneq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fneq2i`. -/
@[expose]
noncomputable def gFneq2i (A : Class) (B : Class) (F : Class)
    (hyp_fneq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWfn F A) (synWfn F B)) :=
  by
  have p0000 := @gFneq2 A B F
  have p0001 := Nominal.mp hyp_fneq2i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fnfun`. -/
@[expose]
noncomputable def gFnfun (A : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfn F A) (synWfun F)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWfn F A))
  have p0001 := @gSimplbi (synWfn F A) (synWfun F) (.classEq (synCdm F) A) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fndm`. -/
@[expose]
noncomputable def gFndm (A : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfn F A) (.classEq (synCdm F) A)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWfn F A))
  have p0001 := @gSimprbi (synWfn F A) (synWfun F) (.classEq (synCdm F) A) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_funfni`. -/
@[expose]
noncomputable def gFunfni (ph : Wff) (A : Class) (B : Class) (F : Class)
    (hyp_funfni_1 : Nominal.NPrf (.imp (synWa (synWfun F) (.classMem B (synCdm F))) ph)) :
    Nominal.NPrf (.imp (synWa (synWfn F A) (.classMem B A)) ph) :=
  by
  have p0000 := @gFnfun A F
  have p0001 := @gAdantr (synWfn F A) (synWfun F) (.classMem B A) p0000
  have p0002 := @gFndm A F
  have p0003 := @gEleq2d (synWfn F A) (synCdm F) A B p0002
  have p0004 := @gBiimpar (synWfn F A) (.classMem B (synCdm F)) (.classMem B A) p0003
  have p0005 :=
    @gSyl2anc (synWa (synWfn F A) (.classMem B A)) (synWfun F)
      (.classMem B (synCdm F)) ph p0001 p0004 hyp_funfni_1
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fnbr`. -/
@[expose]
noncomputable def gFnbr (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (synWa (synWfn F A) (synWbr B F C)) (.classMem B A)) :=
  by
  have p0000 := @gFndm A F
  have p0001 := @gBreldm B C F
  have p0002 :=
    @gAdantl (synWbr B F C) (.classMem B (synCdm F)) (.classEq (synCdm F) A) p0001
  have p0003 := @gSimpl (.classEq (synCdm F) A) (synWbr B F C)
  have p0004 :=
    @gEleqtrd (synWa (.classEq (synCdm F) A) (synWbr B F C)) B (synCdm F) A p0002
      p0003
  have p0005 :=
    @gSylan (synWfn F A) (.classEq (synCdm F) A) (synWbr B F C) (.classMem B A) p0000
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fnop`. -/
@[expose]
noncomputable def gFnop (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem (synCop B C) F)) (.classMem B A)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr B F C))
  have p0001 := @gFnbr A B C F
  have p0002 :=
    @gSylan2br (.classMem (synCop B C) F) (synWfn F A) (synWbr B F C) (.classMem B A)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fneu`. -/
@[expose]
noncomputable def gFneu (y : Var) (A : Class) (B : Class) (F : Class) (dv_B_y : y ∉ B.fv)
    (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem B A)) (synWeu y (synWbr B F (.cv y)))) :=
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
  have dv_cache_0005 : x ∉ ((synCdm F)).fv :=
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
    x ∉ ((Wff.imp (synWfun F) (synWeu y (synWbr B F (.cv y))))).fv :=
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
  have p0000 := @gBreq1 (.cv x) B (.cv y) F
  have p0001 :=
    @gEubidv (.classEq (.cv x) B) (synWbr (.cv x) F (.cv y)) (synWbr B F (.cv y)) y
      dv_cache_0001 p0000
  have p0002 :=
    @gImbi2d (.classEq (.cv x) B) (synWeu y (synWbr (.cv x) F (.cv y)))
      (synWeu y (synWbr B F (.cv y))) (synWfun F) p0001
  have p0003 := @gEldm y (.cv x) F dv_cache_0002 dv_cache_0003
  have p0004 := @gFunmo y (.cv x) F dv_cache_0002 dv_cache_0003
  have p0005 := @gExmoeu2 (synWbr (.cv x) F (.cv y)) y
  have p0006 :=
    @gSyl5ib (synWfun F) (synWmo y (synWbr (.cv x) F (.cv y)))
      (synWex y (synWbr (.cv x) F (.cv y))) (synWeu y (synWbr (.cv x) F (.cv y)))
      p0004 p0005
  have p0007 :=
    @gSylbi (.classMem (.cv x) (synCdm F)) (synWex y (synWbr (.cv x) F (.cv y)))
      (.imp (synWfun F) (synWeu y (synWbr (.cv x) F (.cv y)))) p0003 p0006
  have p0008 :=
    @gVtoclga (.imp (synWfun F) (synWeu y (synWbr (.cv x) F (.cv y))))
      (.imp (synWfun F) (synWeu y (synWbr B F (.cv y)))) x B (synCdm F) dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0002 p0007
  have p0009 :=
    @gImpcom (.classMem B (synCdm F)) (synWfun F) (synWeu y (synWbr B F (.cv y)))
      p0008
  have p0010 := @gFunfni (synWeu y (synWbr B F (.cv y))) A B F p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_fneu2`. -/
@[expose]
noncomputable def gFneu2 (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_B_y : y ∉ B.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem B A))
        (synWeu y (.classMem (synCop B (.cv y)) F))) :=
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
  have p0000 := @gFneu y A B F dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.biimpRefl (synWbr B F (.cv y)))
  have p0002 := @gEubii (synWbr B F (.cv y)) (.classMem (synCop B (.cv y)) F) y p0001
  have p0003 :=
    @gSylib (synWa (synWfn F A) (.classMem B A)) (synWeu y (synWbr B F (.cv y)))
      (synWeu y (.classMem (synCop B (.cv y)) F)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fnun`. -/
@[expose]
noncomputable def gFnun (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWfn F A) (synWfn G B)) (.classEq (synCin A B) (synC0)))
        (synWfn (synCun F G) (synCun A B))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWfn F A))
  have p0001 := (Nominal.biimpRefl (synWfn G B))
  have p0002 := @gIneq12 (synCdm F) A (synCdm G) B
  have p0003 :=
    @gEqeq1d (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synCin (synCdm F) (synCdm G)) (synCin A B) (synC0) p0002
  have p0004 :=
    @gAnbi2d (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.classEq (synCin A B) (synC0)) (synWa (synWfun F) (synWfun G)) p0003
  have p0005 := @gFunun F G
  have p0006 :=
    @gSyl6bir (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synWa (synWa (synWfun F) (synWfun G)) (.classEq (synCin A B) (synC0)))
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (synWfun (synCun F G)) p0004 p0005
  have p0007 := @gDmun F G
  have p0008 := @gUneq12 (synCdm F) A (synCdm G) B
  have p0009 :=
    @gSyl5eq (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synCdm (synCun F G)) (synCun (synCdm F) (synCdm G)) (synCun A B) p0007 p0008
  have p0010 :=
    @gJctird (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synWa (synWa (synWfun F) (synWfun G)) (.classEq (synCin A B) (synC0)))
      (synWfun (synCun F G)) (.classEq (synCdm (synCun F G)) (synCun A B)) p0006
      p0009
  have p0011 := (Nominal.biimpRefl (synWfn (synCun F G) (synCun A B)))
  have p0012 :=
    @gSyl6ibr (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synWa (synWa (synWfun F) (synWfun G)) (.classEq (synCin A B) (synC0)))
      (synWa (synWfun (synCun F G)) (.classEq (synCdm (synCun F G)) (synCun A B)))
      (synWfn (synCun F G) (synCun A B)) p0010 p0011
  have p0013 :=
    @gExp3a (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synWa (synWfun F) (synWfun G)) (.classEq (synCin A B) (synC0))
      (synWfn (synCun F G) (synCun A B)) p0012
  have p0014 :=
    @gImpcom (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synWa (synWfun F) (synWfun G))
      (.imp (.classEq (synCin A B) (synC0)) (synWfn (synCun F G) (synCun A B))) p0013
  have p0015 :=
    @gAn4s (synWfun F) (synWfun G) (.classEq (synCdm F) A) (.classEq (synCdm G) B)
      (.imp (.classEq (synCin A B) (synC0)) (synWfn (synCun F G) (synCun A B))) p0014
  have p0016 :=
    @gSyl2anb (synWfn F A) (synWa (synWfun F) (.classEq (synCdm F) A))
      (synWa (synWfun G) (.classEq (synCdm G) B))
      (.imp (.classEq (synCin A B) (synC0)) (synWfn (synCun F G) (synCun A B)))
      (synWfn G B) p0000 p0001 p0015
  have p0017 :=
    @gImp (synWa (synWfn F A) (synWfn G B)) (.classEq (synCin A B) (synC0))
      (synWfn (synCun F G) (synCun A B)) p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_fnco`. -/
@[expose]
noncomputable def gFnco (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWfn F A) (synWfn G B) (synWss (synCrn G) A))
        (synWfn (synCcom F G) B)) :=
  by
  have p0000 := @gFnfun A F
  have p0001 := @gFnfun B G
  have p0002 := @gFunco F G
  have p0003 :=
    @gSyl2an (synWfn F A) (synWfun F) (synWfun G) (synWfun (synCcom F G))
      (synWfn G B) p0000 p0001 p0002
  have p0004 :=
    @gN3adant3 (synWfn F A) (synWfn G B) (synWfun (synCcom F G))
      (synWss (synCrn G) A) p0003
  have p0005 := @gFndm A F
  have p0006 := @gSseq2d (synWfn F A) (synCdm F) A (synCrn G) p0005
  have p0007 :=
    @gBiimpar (synWfn F A) (synWss (synCrn G) (synCdm F)) (synWss (synCrn G) A)
      p0006
  have p0008 := @gDmcosseq F G
  have p0009 :=
    @gSyl (synWa (synWfn F A) (synWss (synCrn G) A))
      (synWss (synCrn G) (synCdm F)) (.classEq (synCdm (synCcom F G)) (synCdm G))
      p0007 p0008
  have p0010 :=
    @gN3adant2 (synWfn F A) (synWss (synCrn G) A)
      (.classEq (synCdm (synCcom F G)) (synCdm G)) (synWfn G B) p0009
  have p0011 := @gFndm B G
  have p0012 :=
    @gN3ad2ant2 (synWfn G B) (synWfn F A) (.classEq (synCdm G) B)
      (synWss (synCrn G) A) p0011
  have p0013 :=
    @gEqtrd (synW3a (synWfn F A) (synWfn G B) (synWss (synCrn G) A))
      (synCdm (synCcom F G)) (synCdm G) B p0010 p0012
  have p0014 := (Nominal.biimpRefl (synWfn (synCcom F G) B))
  have p0015 :=
    @gSylanbrc (synW3a (synWfn F A) (synWfn G B) (synWss (synCrn G) A))
      (synWfun (synCcom F G)) (.classEq (synCdm (synCcom F G)) B)
      (synWfn (synCcom F G) B) p0004 p0013 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_fnresdm`. -/
@[expose]
noncomputable def gFnresdm (A : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfn F A) (.classEq (synCres F A) F)) :=
  by
  have p0000 := @gFndm A F
  have p0001 := @gEqimss (synCdm F) A
  have p0002 := @gSsreseq F A
  have p0003 :=
    @gN3syl (synWfn F A) (.classEq (synCdm F) A) (synWss (synCdm F) A)
      (.classEq (synCres F A) F) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fnssresb`. -/
@[expose]
noncomputable def gFnssresb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfn F A) (synWb (synWfn (synCres F B) B) (synWss B A))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWfn (synCres F B) B))
  have p0001 := @gFnfun A F
  have p0002 := @gFunres B F
  have p0003 := @gSyl (synWfn F A) (synWfun F) (synWfun (synCres F B)) p0001 p0002
  have p0004 :=
    @gBiantrurd (synWfn F A) (synWfun (synCres F B))
      (.classEq (synCdm (synCres F B)) B) p0003
  have p0005 := @gSsdmres B F
  have p0006 := @gFndm A F
  have p0007 := @gSseq2d (synWfn F A) (synCdm F) A B p0006
  have p0008 :=
    @gSyl5bbr (.classEq (synCdm (synCres F B)) B) (synWss B (synCdm F)) (synWfn F A)
      (synWss B A) p0005 p0007
  have p0009 :=
    @gBitr3d (synWfn F A) (.classEq (synCdm (synCres F B)) B)
      (synWa (synWfun (synCres F B)) (.classEq (synCdm (synCres F B)) B))
      (synWss B A) p0004 p0008
  have p0010 :=
    @gSyl5bb (synWfn (synCres F B) B)
      (synWa (synWfun (synCres F B)) (.classEq (synCdm (synCres F B)) B))
      (synWfn F A) (synWss B A) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_fnssres`. -/
@[expose]
noncomputable def gFnssres (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWa (synWfn F A) (synWss B A)) (synWfn (synCres F B) B)) :=
  by
  have p0000 := @gFnssresb A B F
  have p0001 := @gBiimpar (synWfn F A) (synWfn (synCres F B) B) (synWss B A) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fnresin1`. -/
@[expose]
noncomputable def gFnresin1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfn F A) (synWfn (synCres F (synCin A B)) (synCin A B))) :=
  by
  have p0000 := @gInss1 A B
  have p0001 := @gFnssres A (synCin A B) F
  have p0002 :=
    @gMpan2 (synWfn F A) (synWss (synCin A B) A)
      (synWfn (synCres F (synCin A B)) (synCin A B)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fnres`. -/
@[expose]
noncomputable def gFnres (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWfn (synCres F A) A)
        (synWral x A (synWeu y (synWbr (.cv x) F (.cv y))))) :=
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
  have dv_cache_0002 : x ∉ ((synCres F A)).fv :=
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
  have dv_cache_0003 : y ∉ ((synCres F A)).fv :=
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
  have dv_cache_0006 : x ∉ ((synCdm (synCres F A))).fv :=
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
    @gAncom (synWral x A (synWmo y (synWbr (.cv x) F (.cv y))))
      (synWral x A (synWex y (synWbr (.cv x) F (.cv y))))
  have p0001 := @gBrres (.cv x) (.cv y) F A
  have p0002 := @gAncom (synWbr (.cv x) F (.cv y)) (.classMem (.cv x) A)
  have p0003 :=
    @gBitri (synWbr (.cv x) (synCres F A) (.cv y))
      (synWa (synWbr (.cv x) F (.cv y)) (.classMem (.cv x) A))
      (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))) p0001 p0002
  have p0004 :=
    @gMobii (synWbr (.cv x) (synCres F A) (.cv y))
      (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))) y p0003
  have p0005 :=
    @gMoanimv (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y)) y dv_cache_0001
  have p0006 :=
    @gBitri (synWmo y (synWbr (.cv x) (synCres F A) (.cv y)))
      (synWmo y (synWa (.classMem (.cv x) A) (synWbr (.cv x) F (.cv y))))
      (.imp (.classMem (.cv x) A) (synWmo y (synWbr (.cv x) F (.cv y)))) p0004 p0005
  have p0007 :=
    @gAlbii (synWmo y (synWbr (.cv x) (synCres F A) (.cv y)))
      (.imp (.classMem (.cv x) A) (synWmo y (synWbr (.cv x) F (.cv y)))) x p0006
  have p0008 := @gDffun6 x y (synCres F A) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0009 := (Nominal.biimpRefl (synWral x A (synWmo y (synWbr (.cv x) F (.cv y)))))
  have p0010 :=
    @gN3bitr4i (.all x (synWmo y (synWbr (.cv x) (synCres F A) (.cv y))))
      (.all x (.imp (.classMem (.cv x) A) (synWmo y (synWbr (.cv x) F (.cv y)))))
      (synWfun (synCres F A)) (synWral x A (synWmo y (synWbr (.cv x) F (.cv y))))
      p0007 p0008 p0009
  have p0011 := @gDmres F A
  have p0012 := @gInss1 A (synCdm F)
  have p0013 := @gEqsstri (synCdm (synCres F A)) (synCin A (synCdm F)) A p0011 p0012
  have p0014 := @gEqss (synCdm (synCres F A)) A
  have p0015 :=
    @gMpbiran (.classEq (synCdm (synCres F A)) A) (synWss (synCdm (synCres F A)) A)
      (synWss A (synCdm (synCres F A))) p0013 p0014
  have p0016 := @gDfss3 x A (synCdm (synCres F A)) dv_cache_0005 dv_cache_0006
  have p0017 := @gElin2 (.cv x) A (synCdm F) (synCdm (synCres F A)) p0011
  have p0018 :=
    @gBaib (.classMem (.cv x) (synCdm (synCres F A))) (.classMem (.cv x) A)
      (.classMem (.cv x) (synCdm F)) p0017
  have p0019 := @gEldm y (.cv x) F dv_cache_0007 dv_cache_0008
  have p0020 :=
    @gSyl6bb (.classMem (.cv x) A) (.classMem (.cv x) (synCdm (synCres F A)))
      (.classMem (.cv x) (synCdm F)) (synWex y (synWbr (.cv x) F (.cv y))) p0018 p0019
  have p0021 :=
    @gRalbiia (.classMem (.cv x) (synCdm (synCres F A)))
      (synWex y (synWbr (.cv x) F (.cv y))) x A p0020
  have p0022 :=
    @gN3bitri (.classEq (synCdm (synCres F A)) A) (synWss A (synCdm (synCres F A)))
      (synWral x A (.classMem (.cv x) (synCdm (synCres F A))))
      (synWral x A (synWex y (synWbr (.cv x) F (.cv y)))) p0015 p0016 p0021
  have p0023 :=
    @gAnbi12i (synWfun (synCres F A))
      (synWral x A (synWmo y (synWbr (.cv x) F (.cv y))))
      (.classEq (synCdm (synCres F A)) A)
      (synWral x A (synWex y (synWbr (.cv x) F (.cv y)))) p0010 p0022
  have p0024 :=
    @gR1926 (synWex y (synWbr (.cv x) F (.cv y)))
      (synWmo y (synWbr (.cv x) F (.cv y))) x A
  have p0025 :=
    @gN3bitr4i
      (synWa (synWral x A (synWmo y (synWbr (.cv x) F (.cv y))))
        (synWral x A (synWex y (synWbr (.cv x) F (.cv y)))))
      (synWa (synWral x A (synWex y (synWbr (.cv x) F (.cv y))))
        (synWral x A (synWmo y (synWbr (.cv x) F (.cv y)))))
      (synWa (synWfun (synCres F A)) (.classEq (synCdm (synCres F A)) A))
      (synWral x A (synWa (synWex y (synWbr (.cv x) F (.cv y)))
          (synWmo y (synWbr (.cv x) F (.cv y)))))
      p0000 p0023 p0024
  have p0026 := (Nominal.biimpRefl (synWfn (synCres F A) A))
  have p0027 := @gEu5 (synWbr (.cv x) F (.cv y)) y
  have p0028 :=
    @gRalbii (synWeu y (synWbr (.cv x) F (.cv y)))
      (synWa (synWex y (synWbr (.cv x) F (.cv y))) (synWmo y (synWbr (.cv x) F (.cv y))))
      x A p0027
  have p0029 :=
    @gN3bitr4i (synWa (synWfun (synCres F A)) (.classEq (synCdm (synCres F A)) A))
      (synWral x A (synWa (synWex y (synWbr (.cv x) F (.cv y)))
          (synWmo y (synWbr (.cv x) F (.cv y)))))
      (synWfn (synCres F A) A) (synWral x A (synWeu y (synWbr (.cv x) F (.cv y))))
      p0025 p0026 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_fnresi`. -/
@[expose]
noncomputable def gFnresi (A : Class) :
    Nominal.NPrf (synWfn (synCres (synCid) A) A) :=
  by
  have p0000 := @gFuni
  have p0001 := @gFunres A (synCid)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gDmresi A
  have p0004 := (Nominal.biimpRefl (synWfn (synCres (synCid) A) A))
  have p0005 :=
    @gMpbir2an (synWfn (synCres (synCid) A) A) (synWfun (synCres (synCid) A))
      (.classEq (synCdm (synCres (synCid) A)) A) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fn0`. -/
@[expose]
noncomputable def gFn0 (F : Class) :
    Nominal.NPrf (synWb (synWfn F (synC0)) (.classEq F (synC0))) :=
  by
  have p0000 := @gFndm (synC0) F
  have p0001 := @gDmeq0 F
  have p0002 :=
    @gSylibr (synWfn F (synC0)) (.classEq (synCdm F) (synC0)) (.classEq F (synC0))
      p0000 p0001
  have p0003 := @gFun0
  have p0004 := @gDm0
  have p0005 := (Nominal.biimpRefl (synWfn (synC0) (synC0)))
  have p0006 :=
    @gMpbir2an (synWfn (synC0) (synC0)) (synWfun (synC0))
      (.classEq (synCdm (synC0)) (synC0)) p0003 p0004 p0005
  have p0007 := @gFneq1 (synC0) F (synC0)
  have p0008 :=
    @gMpbiri (.classEq F (synC0)) (synWfn F (synC0)) (synWfn (synC0) (synC0)) p0006
      p0007
  have p0009 := @gImpbii (synWfn F (synC0)) (.classEq F (synC0)) p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_fnopabg`. -/
@[expose]
noncomputable def gFnopabg (ph : Wff) (x : Var) (y : Var) (A : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_fnopabg_1 :
      Nominal.NPrf (.classEq F (synCopab x y (synWa (.classMem (.cv x) A) ph)))) :
    Nominal.NPrf (synWb (synWral x A (synWeu y ph)) (synWfn F A)) :=
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
  have p0000 := @gMoanimv (.classMem (.cv x) A) ph y dv_cache_0001
  have p0001 :=
    @gAlbii (synWmo y (synWa (.classMem (.cv x) A) ph))
      (.imp (.classMem (.cv x) A) (synWmo y ph)) x p0000
  have p0002 := @gFunopab (synWa (.classMem (.cv x) A) ph) x y dv_cache_0002
  have p0003 := (Nominal.biimpRefl (synWral x A (synWmo y ph)))
  have p0004 :=
    @gN3bitr4ri (.all x (synWmo y (synWa (.classMem (.cv x) A) ph)))
      (.all x (.imp (.classMem (.cv x) A) (synWmo y ph)))
      (synWfun (synCopab x y (synWa (.classMem (.cv x) A) ph)))
      (synWral x A (synWmo y ph)) p0001 p0002 p0003
  have p0005 := @gDmopab3 ph x y A dv_cache_0003 dv_cache_0004 dv_cache_0002
  have p0006 :=
    @gAnbi12i (synWral x A (synWmo y ph))
      (synWfun (synCopab x y (synWa (.classMem (.cv x) A) ph)))
      (synWral x A (synWex y ph))
      (.classEq (synCdm (synCopab x y (synWa (.classMem (.cv x) A) ph))) A) p0004 p0005
  have p0007 := @gR1926 (synWmo y ph) (synWex y ph) x A
  have p0008 :=
    (Nominal.biimpRefl (synWfn (synCopab x y (synWa (.classMem (.cv x) A) ph)) A))
  have p0009 :=
    @gN3bitr4i (synWa (synWral x A (synWmo y ph)) (synWral x A (synWex y ph)))
      (synWa (synWfun (synCopab x y (synWa (.classMem (.cv x) A) ph)))
        (.classEq (synCdm (synCopab x y (synWa (.classMem (.cv x) A) ph))) A))
      (synWral x A (synWa (synWmo y ph) (synWex y ph)))
      (synWfn (synCopab x y (synWa (.classMem (.cv x) A) ph)) A) p0006 p0007 p0008
  have p0010 := @gEu5 ph y
  have p0011 := @gAncom (synWex y ph) (synWmo y ph)
  have p0012 :=
    @gBitri (synWeu y ph) (synWa (synWex y ph) (synWmo y ph))
      (synWa (synWmo y ph) (synWex y ph)) p0010 p0011
  have p0013 := @gRalbii (synWeu y ph) (synWa (synWmo y ph) (synWex y ph)) x A p0012
  have p0014 :=
    @gFneq1i A F (synCopab x y (synWa (.classMem (.cv x) A) ph)) hyp_fnopabg_1
  have p0015 :=
    @gN3bitr4i (synWral x A (synWa (synWmo y ph) (synWex y ph)))
      (synWfn (synCopab x y (synWa (.classMem (.cv x) A) ph)) A)
      (synWral x A (synWeu y ph)) (synWfn F A) p0009 p0013 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_fnopab2g`. -/
@[expose]
noncomputable def gFnopab2g (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fnopab2g_1 : Nominal.NPrf (.classEq F
          (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))) :
    Nominal.NPrf (synWb (synWral x A (.classMem B (synCvv))) (synWfn F A)) :=
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
  have p0000 := @gEueq y B dv_cache_0001
  have p0001 :=
    @gRalbii (.classMem B (synCvv)) (synWeu y (.classEq (.cv y) B)) x A p0000
  have p0002 :=
    @gFnopabg (.classEq (.cv y) B) x y A F dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_fnopab2g_1
  have p0003 :=
    @gBitri (synWral x A (.classMem B (synCvv)))
      (synWral x A (synWeu y (.classEq (.cv y) B))) (synWfn F A) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fnopab`. -/
@[expose]
noncomputable def gFnopab (ph : Wff) (x : Var) (y : Var) (A : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_fnopab_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (synWeu y ph)))
    (hyp_fnopab_2 :
      Nominal.NPrf (.classEq F (synCopab x y (synWa (.classMem (.cv x) A) ph)))) :
    Nominal.NPrf (synWfn F A) :=
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
  have p0000 := @gRgen (synWeu y ph) x A hyp_fnopab_1
  have p0001 :=
    @gFnopabg ph x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fnopab_2
  have p0002 := @gMpbi (synWral x A (synWeu y ph)) (synWfn F A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fnopab2`. -/
@[expose]
noncomputable def gFnopab2 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fnopab2_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_fnopab2_2 : Nominal.NPrf (.classEq F
          (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))) :
    Nominal.NPrf (synWfn F A) :=
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
  have p0000 := @gEueq1 y B dv_cache_0001 hyp_fnopab2_1
  have p0001 := @gA1i (synWeu y (.classEq (.cv y) B)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @gFnopab (.classEq (.cv y) B) x y A F dv_cache_0002 dv_cache_0003 dv_cache_0004 p0001
      hyp_fnopab2_2
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_feq1`. -/
@[expose]
noncomputable def gFeq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (synWb (synWf F A B) (synWf G A B))) :=
  by
  have p0000 := @gFneq1 A F G
  have p0001 := @gRneq F G
  have p0002 := @gSseq1d (.classEq F G) (synCrn F) (synCrn G) B p0001
  have p0003 :=
    @gAnbi12d (.classEq F G) (synWfn F A) (synWfn G A) (synWss (synCrn F) B)
      (synWss (synCrn G) B) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWf F A B))
  have p0005 := (Nominal.biimpRefl (synWf G A B))
  have p0006 :=
    @gN3bitr4g (.classEq F G) (synWa (synWfn F A) (synWss (synCrn F) B))
      (synWa (synWfn G A) (synWss (synCrn G) B)) (synWf F A B) (synWf G A B) p0003
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

/-- Checked nominal proof certificate identified upstream as `g_feq2`. -/
@[expose]
noncomputable def gFeq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWf F A C) (synWf F B C))) :=
  by
  have p0000 := @gFneq2 A B F
  have p0001 :=
    @gAnbi1d (.classEq A B) (synWfn F A) (synWfn F B) (synWss (synCrn F) C) p0000
  have p0002 := (Nominal.biimpRefl (synWf F A C))
  have p0003 := (Nominal.biimpRefl (synWf F B C))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (synWfn F A) (synWss (synCrn F) C))
      (synWa (synWfn F B) (synWss (synCrn F) C)) (synWf F A C) (synWf F B C) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_feq3`. -/
@[expose]
noncomputable def gFeq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWf F C A) (synWf F C B))) :=
  by
  have p0000 := @gSseq2 A B (synCrn F)
  have p0001 :=
    @gAnbi2d (.classEq A B) (synWss (synCrn F) A) (synWss (synCrn F) B) (synWfn F C)
      p0000
  have p0002 := (Nominal.biimpRefl (synWf F C A))
  have p0003 := (Nominal.biimpRefl (synWf F C B))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (synWfn F C) (synWss (synCrn F) A))
      (synWa (synWfn F C) (synWss (synCrn F) B)) (synWf F C A) (synWf F C B) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_feq1i`. -/
@[expose]
noncomputable def gFeq1i (A : Class) (B : Class) (F : Class) (G : Class)
    (hyp_feq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (synWb (synWf F A B) (synWf G A B)) :=
  by
  have p0000 := @gFeq1 A B F G
  have p0001 := Nominal.mp hyp_feq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_feq2i`. -/
@[expose]
noncomputable def gFeq2i (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_feq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWf F A C) (synWf F B C)) :=
  by
  have p0000 := @gFeq2 A B C F
  have p0001 := Nominal.mp hyp_feq2i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ffn`. -/
@[expose]
noncomputable def gFfn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (synWfn F A)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf F A B))
  have p0001 := @gSimplbi (synWf F A B) (synWfn F A) (synWss (synCrn F) B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dffn2`. -/
@[expose]
noncomputable def gDffn2 (A : Class) (F : Class) :
    Nominal.NPrf (synWb (synWfn F A) (synWf F A (synCvv))) :=
  by
  have p0000 := @gSsv (synCrn F)
  have p0001 := @gBiantru (synWss (synCrn F) (synCvv)) (synWfn F A) p0000
  have p0002 := (Nominal.biimpRefl (synWf F A (synCvv)))
  have p0003 :=
    @gBitr4i (synWfn F A) (synWa (synWfn F A) (synWss (synCrn F) (synCvv)))
      (synWf F A (synCvv)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ffun`. -/
@[expose]
noncomputable def gFfun (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (synWfun F)) :=
  by
  have p0000 := @gFfn A B F
  have p0001 := @gFnfun A F
  have p0002 := @gSyl (synWf F A B) (synWfn F A) (synWfun F) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fdm`. -/
@[expose]
noncomputable def gFdm (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (.classEq (synCdm F) A)) :=
  by
  have p0000 := @gFfn A B F
  have p0001 := @gFndm A F
  have p0002 := @gSyl (synWf F A B) (synWfn F A) (.classEq (synCdm F) A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_frn`. -/
@[expose]
noncomputable def gFrn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (synWss (synCrn F) B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf F A B))
  have p0001 := @gSimprbi (synWf F A B) (synWfn F A) (synWss (synCrn F) B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dffn3`. -/
@[expose]
noncomputable def gDffn3 (A : Class) (F : Class) :
    Nominal.NPrf (synWb (synWfn F A) (synWf F A (synCrn F))) :=
  by
  have p0000 := @gSsid (synCrn F)
  have p0001 := @gBiantru (synWss (synCrn F) (synCrn F)) (synWfn F A) p0000
  have p0002 := (Nominal.biimpRefl (synWf F A (synCrn F)))
  have p0003 :=
    @gBitr4i (synWfn F A) (synWa (synWfn F A) (synWss (synCrn F) (synCrn F)))
      (synWf F A (synCrn F)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fss`. -/
@[expose]
noncomputable def gFss (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (synWa (synWf F A B) (synWss B C)) (synWf F A C)) :=
  by
  have p0000 := @gSstr2 (synCrn F) B C
  have p0001 :=
    @gCom12 (synWss (synCrn F) B) (synWss B C) (synWss (synCrn F) C) p0000
  have p0002 :=
    @gAnim2d (synWss B C) (synWss (synCrn F) B) (synWss (synCrn F) C) (synWfn F A)
      p0001
  have p0003 := (Nominal.biimpRefl (synWf F A B))
  have p0004 := (Nominal.biimpRefl (synWf F A C))
  have p0005 :=
    @gN3imtr4g (synWss B C) (synWa (synWfn F A) (synWss (synCrn F) B))
      (synWa (synWfn F A) (synWss (synCrn F) C)) (synWf F A B) (synWf F A C) p0002
      p0003 p0004
  have p0006 := @gImpcom (synWss B C) (synWf F A B) (synWf F A C) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fco`. -/
@[expose]
noncomputable def gFco (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf F B C) (synWf G A B)) (synWf (synCcom F G) A C)) :=
  by
  have p0000 := @gFnco B A F G
  have p0001 :=
    @gN3expib (synWfn F B) (synWfn G A) (synWss (synCrn G) B)
      (synWfn (synCcom F G) A) p0000
  have p0002 :=
    @gAdantr (synWfn F B)
      (.imp (synWa (synWfn G A) (synWss (synCrn G) B)) (synWfn (synCcom F G) A))
      (synWss (synCrn F) C) p0001
  have p0003 := @gRncoss F G
  have p0004 := @gSstr (synCrn (synCcom F G)) (synCrn F) C
  have p0005 :=
    @gMpan (synWss (synCrn (synCcom F G)) (synCrn F)) (synWss (synCrn F) C)
      (synWss (synCrn (synCcom F G)) C) p0003 p0004
  have p0006 :=
    @gAdantl (synWss (synCrn F) C) (synWss (synCrn (synCcom F G)) C) (synWfn F B)
      p0005
  have p0007 :=
    @gJctird (synWa (synWfn F B) (synWss (synCrn F) C))
      (synWa (synWfn G A) (synWss (synCrn G) B)) (synWfn (synCcom F G) A)
      (synWss (synCrn (synCcom F G)) C) p0002 p0006
  have p0008 :=
    @gImp (synWa (synWfn F B) (synWss (synCrn F) C))
      (synWa (synWfn G A) (synWss (synCrn G) B))
      (synWa (synWfn (synCcom F G) A) (synWss (synCrn (synCcom F G)) C)) p0007
  have p0009 := (Nominal.biimpRefl (synWf F B C))
  have p0010 := (Nominal.biimpRefl (synWf G A B))
  have p0011 :=
    @gAnbi12i (synWf F B C) (synWa (synWfn F B) (synWss (synCrn F) C))
      (synWf G A B) (synWa (synWfn G A) (synWss (synCrn G) B)) p0009 p0010
  have p0012 := (Nominal.biimpRefl (synWf (synCcom F G) A C))
  have p0013 :=
    @gN3imtr4i
      (synWa (synWa (synWfn F B) (synWss (synCrn F) C))
        (synWa (synWfn G A) (synWss (synCrn G) B)))
      (synWa (synWfn (synCcom F G) A) (synWss (synCrn (synCcom F G)) C))
      (synWa (synWf F B C) (synWf G A B)) (synWf (synCcom F G) A C) p0008 p0011 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_fssxp`. -/
@[expose]
noncomputable def gFssxp (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (synWss F (synCxp A B))) :=
  by
  have p0000 := @gSsdmrn F
  have p0001 := @gFdm A B F
  have p0002 := @gEqimss (synCdm F) A
  have p0003 :=
    @gSyl (synWf F A B) (.classEq (synCdm F) A) (synWss (synCdm F) A) p0001 p0002
  have p0004 := @gFrn A B F
  have p0005 := @gXpss12 (synCdm F) A (synCrn F) B
  have p0006 :=
    @gSyl2anc (synWf F A B) (synWss (synCdm F) A) (synWss (synCrn F) B)
      (synWss (synCxp (synCdm F) (synCrn F)) (synCxp A B)) p0003 p0004 p0005
  have p0007 :=
    @gSyl5ss (synWf F A B) F (synCxp (synCdm F) (synCrn F)) (synCxp A B) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_opelf`. -/
@[expose]
noncomputable def gOpelf (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf F A B) (.classMem (synCop C D) F))
        (synWa (.classMem C A) (.classMem D B))) :=
  by
  have p0000 := @gFssxp A B F
  have p0001 := @gSseld (synWf F A B) F (synCxp A B) (synCop C D) p0000
  have p0002 := @gOpelxp C D A B
  have p0003 :=
    @gSyl6ib (synWf F A B) (.classMem (synCop C D) F)
      (.classMem (synCop C D) (synCxp A B)) (synWa (.classMem C A) (.classMem D B))
      p0001 p0002
  have p0004 :=
    @gImp (synWf F A B) (.classMem (synCop C D) F)
      (synWa (.classMem C A) (.classMem D B)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fun`. -/
@[expose]
noncomputable def gFun (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWf F A C) (synWf G B D)) (.classEq (synCin A B) (synC0)))
        (synWf (synCun F G) (synCun A B) (synCun C D))) :=
  by
  have p0000 := @gFnun A B F G
  have p0001 :=
    @gExpcom (synWa (synWfn F A) (synWfn G B)) (.classEq (synCin A B) (synC0))
      (synWfn (synCun F G) (synCun A B)) p0000
  have p0002 := @gRnun F G
  have p0003 := @gUnss12 (synCrn F) C (synCrn G) D
  have p0004 :=
    @gSyl5eqss (synWa (synWss (synCrn F) C) (synWss (synCrn G) D))
      (synCrn (synCun F G)) (synCun (synCrn F) (synCrn G)) (synCun C D) p0002 p0003
  have p0005 :=
    @gA1i
      (.imp (synWa (synWss (synCrn F) C) (synWss (synCrn G) D))
        (synWss (synCrn (synCun F G)) (synCun C D)))
      (.classEq (synCin A B) (synC0)) p0004
  have p0006 :=
    @gAnim12d (.classEq (synCin A B) (synC0)) (synWa (synWfn F A) (synWfn G B))
      (synWfn (synCun F G) (synCun A B))
      (synWa (synWss (synCrn F) C) (synWss (synCrn G) D))
      (synWss (synCrn (synCun F G)) (synCun C D)) p0001 p0005
  have p0007 := (Nominal.biimpRefl (synWf F A C))
  have p0008 := (Nominal.biimpRefl (synWf G B D))
  have p0009 :=
    @gAnbi12i (synWf F A C) (synWa (synWfn F A) (synWss (synCrn F) C))
      (synWf G B D) (synWa (synWfn G B) (synWss (synCrn G) D)) p0007 p0008
  have p0010 :=
    @gAn4 (synWfn F A) (synWss (synCrn F) C) (synWfn G B) (synWss (synCrn G) D)
  have p0011 :=
    @gBitri (synWa (synWf F A C) (synWf G B D))
      (synWa (synWa (synWfn F A) (synWss (synCrn F) C))
        (synWa (synWfn G B) (synWss (synCrn G) D)))
      (synWa (synWa (synWfn F A) (synWfn G B))
        (synWa (synWss (synCrn F) C) (synWss (synCrn G) D)))
      p0009 p0010
  have p0012 := (Nominal.biimpRefl (synWf (synCun F G) (synCun A B) (synCun C D)))
  have p0013 :=
    @gN3imtr4g (.classEq (synCin A B) (synC0))
      (synWa (synWa (synWfn F A) (synWfn G B))
        (synWa (synWss (synCrn F) C) (synWss (synCrn G) D)))
      (synWa (synWfn (synCun F G) (synCun A B))
        (synWss (synCrn (synCun F G)) (synCun C D)))
      (synWa (synWf F A C) (synWf G B D))
      (synWf (synCun F G) (synCun A B) (synCun C D)) p0006 p0011 p0012
  have p0014 :=
    @gImpcom (.classEq (synCin A B) (synC0)) (synWa (synWf F A C) (synWf G B D))
      (synWf (synCun F G) (synCun A B) (synCun C D)) p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_fnfco`. -/
@[expose]
noncomputable def gFnfco (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (synWf G B A)) (synWfn (synCcom F G) B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf G B A))
  have p0001 := @gFnco A B F G
  have p0002 :=
    @gN3expb (synWfn F A) (synWfn G B) (synWss (synCrn G) A)
      (synWfn (synCcom F G) B) p0001
  have p0003 :=
    @gSylan2b (synWf G B A) (synWfn F A) (synWa (synWfn G B) (synWss (synCrn G) A))
      (synWfn (synCcom F G) B) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fssres`. -/
@[expose]
noncomputable def gFssres (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf F A B) (synWss C A)) (synWf (synCres F C) C B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf F A B))
  have p0001 := @gFnssres A C F
  have p0002 := @gResss F C
  have p0003 := @gRnss (synCres F C) F
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gSstr (synCrn (synCres F C)) (synCrn F) B
  have p0006 :=
    @gMpan (synWss (synCrn (synCres F C)) (synCrn F)) (synWss (synCrn F) B)
      (synWss (synCrn (synCres F C)) B) p0004 p0005
  have p0007 :=
    @gAnim12i (synWa (synWfn F A) (synWss C A)) (synWfn (synCres F C) C)
      (synWss (synCrn F) B) (synWss (synCrn (synCres F C)) B) p0001 p0006
  have p0008 :=
    @gAn32s (synWfn F A) (synWss C A) (synWss (synCrn F) B)
      (synWa (synWfn (synCres F C) C) (synWss (synCrn (synCres F C)) B)) p0007
  have p0009 :=
    @gSylanb (synWf F A B) (synWa (synWfn F A) (synWss (synCrn F) B)) (synWss C A)
      (synWa (synWfn (synCres F C) C) (synWss (synCrn (synCres F C)) B)) p0000 p0008
  have p0010 := (Nominal.biimpRefl (synWf (synCres F C) C B))
  have p0011 :=
    @gSylibr (synWa (synWf F A B) (synWss C A))
      (synWa (synWfn (synCres F C) C) (synWss (synCrn (synCres F C)) B))
      (synWf (synCres F C) C B) p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_fcoi1`. -/
@[expose]
noncomputable def gFcoi1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (.classEq (synCcom F (synCres (synCid) A)) F)) :=
  by
  have p0000 := @gCoi1 F
  have p0001 := @gReseq1i (synCcom F (synCid)) F A p0000
  have p0002 := @gResco F (synCid) A
  have p0003 :=
    @gEqtr3i (synCres (synCcom F (synCid)) A) (synCres F A)
      (synCcom F (synCres (synCid) A)) p0001 p0002
  have p0004 := @gFfn A B F
  have p0005 := @gFnresdm A F
  have p0006 :=
    @gSyl (synWf F A B) (synWfn F A) (.classEq (synCres F A) F) p0004 p0005
  have p0007 :=
    @gSyl5eqr (synWf F A B) (synCcom F (synCres (synCid) A)) (synCres F A) F p0003
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_feu`. -/
@[expose]
noncomputable def gFeu (y : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWf F A B) (.classMem C A))
        (synWreu y B (.classMem (synCop C (.cv y)) F))) :=
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
  have dv_cache_0003 : y ∉ ((synWf F A B)).fv :=
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
  have p0000 := @gFfn A B F
  have p0001 := @gFneu2 y A C F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gSylan (synWf F A B) (synWfn F A) (.classMem C A)
      (synWeu y (.classMem (synCop C (.cv y)) F)) p0000 p0001
  have p0003 := @gOpelf A B C (.cv y) F
  have p0004 :=
    @gSimprd (synWa (synWf F A B) (.classMem (synCop C (.cv y)) F)) (.classMem C A)
      (.classMem (.cv y) B) p0003
  have p0005 :=
    @gEx (synWf F A B) (.classMem (synCop C (.cv y)) F) (.classMem (.cv y) B) p0004
  have p0006 :=
    @gPm471rd (synWf F A B) (.classMem (synCop C (.cv y)) F) (.classMem (.cv y) B)
      p0005
  have p0007 :=
    @gEubidv (synWf F A B) (.classMem (synCop C (.cv y)) F)
      (synWa (.classMem (.cv y) B) (.classMem (synCop C (.cv y)) F)) y dv_cache_0003
      p0006
  have p0008 :=
    @gAdantr (synWf F A B)
      (synWb (synWeu y (.classMem (synCop C (.cv y)) F))
        (synWeu y (synWa (.classMem (.cv y) B) (.classMem (synCop C (.cv y)) F))))
      (.classMem C A) p0007
  have p0009 :=
    @gMpbid (synWa (synWf F A B) (.classMem C A))
      (synWeu y (.classMem (synCop C (.cv y)) F))
      (synWeu y (synWa (.classMem (.cv y) B) (.classMem (synCop C (.cv y)) F))) p0002
      p0008
  have p0010 := (Nominal.biimpRefl (synWreu y B (.classMem (synCop C (.cv y)) F)))
  have p0011 :=
    @gSylibr (synWa (synWf F A B) (.classMem C A))
      (synWeu y (synWa (.classMem (.cv y) B) (.classMem (synCop C (.cv y)) F)))
      (synWreu y B (.classMem (synCop C (.cv y)) F)) p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_f0`. -/
@[expose]
noncomputable def gF0 (A : Class) : Nominal.NPrf (synWf (synC0) (synC0) A) :=
  by
  have p0000 := @gFun0
  have p0001 := @gDm0
  have p0002 := (Nominal.biimpRefl (synWfn (synC0) (synC0)))
  have p0003 :=
    @gMpbir2an (synWfn (synC0) (synC0)) (synWfun (synC0))
      (.classEq (synCdm (synC0)) (synC0)) p0000 p0001 p0002
  have p0004 := @gRn0
  have p0005 := @gN0ss A
  have p0006 := @gEqsstri (synCrn (synC0)) (synC0) A p0004 p0005
  have p0007 := (Nominal.biimpRefl (synWf (synC0) (synC0) A))
  have p0008 :=
    @gMpbir2an (synWf (synC0) (synC0) A) (synWfn (synC0) (synC0))
      (synWss (synCrn (synC0)) A) p0003 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fconst`. -/
@[expose]
noncomputable def gFconst (A : Class) (B : Class)
    (hyp_fconst_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWf (synCxp A (synCsn B)) A (synCsn B)) :=
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
    @gFconstopab x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @gFnopab2 x y A B (synCxp A (synCsn B)) dv_cache_0001 dv_cache_0002 dv_cache_0004
      dv_cache_0005 hyp_fconst_1 p0000
  have p0002 := @gRnxpss A (synCsn B)
  have p0003 := (Nominal.biimpRefl (synWf (synCxp A (synCsn B)) A (synCsn B)))
  have p0004 :=
    @gMpbir2an (synWf (synCxp A (synCsn B)) A (synCsn B))
      (synWfn (synCxp A (synCsn B)) A)
      (synWss (synCrn (synCxp A (synCsn B))) (synCsn B)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fconstg`. -/
@[expose]
noncomputable def gFconstg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (synWf (synCxp A (synCsn B)) A (synCsn B))) :=
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
  have dv_cache_0002 : x ∉ ((synWf (synCxp A (synCsn B)) A (synCsn B))).fv :=
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
  have p0000 := @gSneq (.cv x) B
  have p0001 := @gXpeq2d (.classEq (.cv x) B) (synCsn (.cv x)) (synCsn B) A p0000
  have p0002 :=
    @gFeq1 A (synCsn (.cv x)) (synCxp A (synCsn (.cv x))) (synCxp A (synCsn B))
  have p0003 := @gFeq3 (synCsn (.cv x)) (synCsn B) A (synCxp A (synCsn B))
  have p0004 :=
    @gSylan9bb (.classEq (synCxp A (synCsn (.cv x))) (synCxp A (synCsn B)))
      (synWf (synCxp A (synCsn (.cv x))) A (synCsn (.cv x)))
      (synWf (synCxp A (synCsn B)) A (synCsn (.cv x)))
      (.classEq (synCsn (.cv x)) (synCsn B))
      (synWf (synCxp A (synCsn B)) A (synCsn B)) p0002 p0003
  have p0005 :=
    @gSyl2anc (.classEq (.cv x) B)
      (.classEq (synCxp A (synCsn (.cv x))) (synCxp A (synCsn B)))
      (.classEq (synCsn (.cv x)) (synCsn B))
      (synWb (synWf (synCxp A (synCsn (.cv x))) A (synCsn (.cv x)))
        (synWf (synCxp A (synCsn B)) A (synCsn B)))
      p0001 p0000 p0004
  have p0006 := @gVex x
  have p0007 := @gFconst A (.cv x) p0006
  have p0008 :=
    @gVtoclg (synWf (synCxp A (synCsn (.cv x))) A (synCsn (.cv x)))
      (synWf (synCxp A (synCsn B)) A (synCsn B)) x B V dv_cache_0001 dv_cache_0002
      p0005 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fnconstg`. -/
@[expose]
noncomputable def gFnconstg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (synWfn (synCxp A (synCsn B)) A)) :=
  by
  have p0000 := @gFconstg A B V
  have p0001 := @gFfn A (synCsn B) (synCxp A (synCsn B))
  have p0002 :=
    @gSyl (.classMem B V) (synWf (synCxp A (synCsn B)) A (synCsn B))
      (synWfn (synCxp A (synCsn B)) A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_f1eq1`. -/
@[expose]
noncomputable def gF1eq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (synWb (synWf1 F A B) (synWf1 G A B))) :=
  by
  have p0000 := @gFeq1 A B F G
  have p0001 := @gCnveq F G
  have p0002 := @gFuneqd (.classEq F G) (synCcnv F) (synCcnv G) p0001
  have p0003 :=
    @gAnbi12d (.classEq F G) (synWf F A B) (synWf G A B) (synWfun (synCcnv F))
      (synWfun (synCcnv G)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWf1 F A B))
  have p0005 := (Nominal.biimpRefl (synWf1 G A B))
  have p0006 :=
    @gN3bitr4g (.classEq F G) (synWa (synWf F A B) (synWfun (synCcnv F)))
      (synWa (synWf G A B) (synWfun (synCcnv G))) (synWf1 F A B) (synWf1 G A B)
      p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_f1eq2`. -/
@[expose]
noncomputable def gF1eq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWf1 F A C) (synWf1 F B C))) :=
  by
  have p0000 := @gFeq2 A B C F
  have p0001 :=
    @gAnbi1d (.classEq A B) (synWf F A C) (synWf F B C) (synWfun (synCcnv F)) p0000
  have p0002 := (Nominal.biimpRefl (synWf1 F A C))
  have p0003 := (Nominal.biimpRefl (synWf1 F B C))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (synWf F A C) (synWfun (synCcnv F)))
      (synWa (synWf F B C) (synWfun (synCcnv F))) (synWf1 F A C) (synWf1 F B C)
      p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_f1eq3`. -/
@[expose]
noncomputable def gF1eq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWf1 F C A) (synWf1 F C B))) :=
  by
  have p0000 := @gFeq3 A B C F
  have p0001 :=
    @gAnbi1d (.classEq A B) (synWf F C A) (synWf F C B) (synWfun (synCcnv F)) p0000
  have p0002 := (Nominal.biimpRefl (synWf1 F C A))
  have p0003 := (Nominal.biimpRefl (synWf1 F C B))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (synWf F C A) (synWfun (synCcnv F)))
      (synWa (synWf F C B) (synWfun (synCcnv F))) (synWf1 F C A) (synWf1 F C B)
      p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dff12`. -/
@[expose]
noncomputable def gDff12 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWf1 F A B)
        (synWa (synWf F A B) (.all y (synWmo x (synWbr (.cv x) F (.cv y)))))) :=
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
  have p0000 := (Nominal.biimpRefl (synWf1 F A B))
  have p0001 := @gFuncnv2 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gAnbi2i (synWfun (synCcnv F)) (.all y (synWmo x (synWbr (.cv x) F (.cv y))))
      (synWf F A B) p0001
  have p0003 :=
    @gBitri (synWf1 F A B) (synWa (synWf F A B) (synWfun (synCcnv F)))
      (synWa (synWf F A B) (.all y (synWmo x (synWbr (.cv x) F (.cv y))))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_f1f`. -/
@[expose]
noncomputable def gF1f (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1 F A B) (synWf F A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf1 F A B))
  have p0001 := @gSimplbi (synWf1 F A B) (synWf F A B) (synWfun (synCcnv F)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_f1fn`. -/
@[expose]
noncomputable def gF1fn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1 F A B) (synWfn F A)) :=
  by
  have p0000 := @gF1f A B F
  have p0001 := @gFfn A B F
  have p0002 := @gSyl (synWf1 F A B) (synWf F A B) (synWfn F A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_f1ss`. -/
@[expose]
noncomputable def gF1ss (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (synWa (synWf1 F A B) (synWss B C)) (synWf1 F A C)) :=
  by
  have p0000 := @gF1f A B F
  have p0001 := @gFss A B C F
  have p0002 :=
    @gSylan (synWf1 F A B) (synWf F A B) (synWss B C) (synWf F A C) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWf1 F A B))
  have p0004 := @gSimprbi (synWf1 F A B) (synWf F A B) (synWfun (synCcnv F)) p0003
  have p0005 := @gAdantr (synWf1 F A B) (synWfun (synCcnv F)) (synWss B C) p0004
  have p0006 := (Nominal.biimpRefl (synWf1 F A C))
  have p0007 :=
    @gSylanbrc (synWa (synWf1 F A B) (synWss B C)) (synWf F A C)
      (synWfun (synCcnv F)) (synWf1 F A C) p0002 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_f1co`. -/
@[expose]
noncomputable def gF1co (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1 F B C) (synWf1 G A B)) (synWf1 (synCcom F G) A C)) :=
  by
  have p0000 := @gFco A B C F G
  have p0001 := @gFunco (synCcnv G) (synCcnv F)
  have p0002 := @gCnvco F G
  have p0003 :=
    @gFuneqi (synCcnv (synCcom F G)) (synCcom (synCcnv G) (synCcnv F)) p0002
  have p0004 :=
    @gSylibr (synWa (synWfun (synCcnv G)) (synWfun (synCcnv F)))
      (synWfun (synCcom (synCcnv G) (synCcnv F))) (synWfun (synCcnv (synCcom F G)))
      p0001 p0003
  have p0005 :=
    @gAncoms (synWfun (synCcnv G)) (synWfun (synCcnv F))
      (synWfun (synCcnv (synCcom F G))) p0004
  have p0006 :=
    @gAnim12i (synWa (synWf F B C) (synWf G A B)) (synWf (synCcom F G) A C)
      (synWa (synWfun (synCcnv F)) (synWfun (synCcnv G)))
      (synWfun (synCcnv (synCcom F G))) p0000 p0005
  have p0007 :=
    @gAn4s (synWf F B C) (synWf G A B) (synWfun (synCcnv F)) (synWfun (synCcnv G))
      (synWa (synWf (synCcom F G) A C) (synWfun (synCcnv (synCcom F G)))) p0006
  have p0008 := (Nominal.biimpRefl (synWf1 F B C))
  have p0009 := (Nominal.biimpRefl (synWf1 G A B))
  have p0010 :=
    @gAnbi12i (synWf1 F B C) (synWa (synWf F B C) (synWfun (synCcnv F)))
      (synWf1 G A B) (synWa (synWf G A B) (synWfun (synCcnv G))) p0008 p0009
  have p0011 := (Nominal.biimpRefl (synWf1 (synCcom F G) A C))
  have p0012 :=
    @gN3imtr4i
      (synWa (synWa (synWf F B C) (synWfun (synCcnv F)))
        (synWa (synWf G A B) (synWfun (synCcnv G))))
      (synWa (synWf (synCcom F G) A C) (synWfun (synCcnv (synCcom F G))))
      (synWa (synWf1 F B C) (synWf1 G A B)) (synWf1 (synCcom F G) A C) p0007 p0010
      p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_foeq1`. -/
@[expose]
noncomputable def gFoeq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (synWb (synWfo F A B) (synWfo G A B))) :=
  by
  have p0000 := @gFneq1 A F G
  have p0001 := @gRneq F G
  have p0002 := @gEqeq1d (.classEq F G) (synCrn F) (synCrn G) B p0001
  have p0003 :=
    @gAnbi12d (.classEq F G) (synWfn F A) (synWfn G A) (.classEq (synCrn F) B)
      (.classEq (synCrn G) B) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWfo F A B))
  have p0005 := (Nominal.biimpRefl (synWfo G A B))
  have p0006 :=
    @gN3bitr4g (.classEq F G) (synWa (synWfn F A) (.classEq (synCrn F) B))
      (synWa (synWfn G A) (.classEq (synCrn G) B)) (synWfo F A B) (synWfo G A B)
      p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_foeq2`. -/
@[expose]
noncomputable def gFoeq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWfo F A C) (synWfo F B C))) :=
  by
  have p0000 := @gFneq2 A B F
  have p0001 :=
    @gAnbi1d (.classEq A B) (synWfn F A) (synWfn F B) (.classEq (synCrn F) C) p0000
  have p0002 := (Nominal.biimpRefl (synWfo F A C))
  have p0003 := (Nominal.biimpRefl (synWfo F B C))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (synWfn F A) (.classEq (synCrn F) C))
      (synWa (synWfn F B) (.classEq (synCrn F) C)) (synWfo F A C) (synWfo F B C)
      p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_foeq3`. -/
@[expose]
noncomputable def gFoeq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWfo F C A) (synWfo F C B))) :=
  by
  have p0000 := @gEqeq2 A B (synCrn F)
  have p0001 :=
    @gAnbi2d (.classEq A B) (.classEq (synCrn F) A) (.classEq (synCrn F) B)
      (synWfn F C) p0000
  have p0002 := (Nominal.biimpRefl (synWfo F C A))
  have p0003 := (Nominal.biimpRefl (synWfo F C B))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (synWfn F C) (.classEq (synCrn F) A))
      (synWa (synWfn F C) (.classEq (synCrn F) B)) (synWfo F C A) (synWfo F C B)
      p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fof`. -/
@[expose]
noncomputable def gFof (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfo F A B) (synWf F A B)) :=
  by
  have p0000 := @gEqimss (synCrn F) B
  have p0001 :=
    @gAnim2i (.classEq (synCrn F) B) (synWss (synCrn F) B) (synWfn F A) p0000
  have p0002 := (Nominal.biimpRefl (synWfo F A B))
  have p0003 := (Nominal.biimpRefl (synWf F A B))
  have p0004 :=
    @gN3imtr4i (synWa (synWfn F A) (.classEq (synCrn F) B))
      (synWa (synWfn F A) (synWss (synCrn F) B)) (synWfo F A B) (synWf F A B) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fofun`. -/
@[expose]
noncomputable def gFofun (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfo F A B) (synWfun F)) :=
  by
  have p0000 := @gFof A B F
  have p0001 := @gFfun A B F
  have p0002 := @gSyl (synWfo F A B) (synWf F A B) (synWfun F) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fofn`. -/
@[expose]
noncomputable def gFofn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfo F A B) (synWfn F A)) :=
  by
  have p0000 := @gFof A B F
  have p0001 := @gFfn A B F
  have p0002 := @gSyl (synWfo F A B) (synWf F A B) (synWfn F A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_forn`. -/
@[expose]
noncomputable def gForn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfo F A B) (.classEq (synCrn F) B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWfo F A B))
  have p0001 := @gSimprbi (synWfo F A B) (synWfn F A) (.classEq (synCrn F) B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dffo2`. -/
@[expose]
noncomputable def gDffo2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (synWb (synWfo F A B) (synWa (synWf F A B) (.classEq (synCrn F) B))) :=
  by
  have p0000 := @gFof A B F
  have p0001 := @gForn A B F
  have p0002 := @gJca (synWfo F A B) (synWf F A B) (.classEq (synCrn F) B) p0000 p0001
  have p0003 := @gFfn A B F
  have p0004 := (Nominal.biimpRefl (synWfo F A B))
  have p0005 :=
    @gBiimpri (synWfo F A B) (synWa (synWfn F A) (.classEq (synCrn F) B)) p0004
  have p0006 :=
    @gSylan (synWf F A B) (synWfn F A) (.classEq (synCrn F) B) (synWfo F A B) p0003
      p0005
  have p0007 :=
    @gImpbii (synWfo F A B) (synWa (synWf F A B) (.classEq (synCrn F) B)) p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_foima`. -/
@[expose]
noncomputable def gFoima (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfo F A B) (.classEq (synCima F A) B)) :=
  by
  have p0000 := @gImadmrn F
  have p0001 := @gFof A B F
  have p0002 := @gFdm A B F
  have p0003 := @gImaeq2 (synCdm F) A F
  have p0004 :=
    @gN3syl (synWfo F A B) (synWf F A B) (.classEq (synCdm F) A)
      (.classEq (synCima F (synCdm F)) (synCima F A)) p0001 p0002 p0003
  have p0005 :=
    @gSyl5reqr (synWfo F A B) (synCrn F) (synCima F (synCdm F)) (synCima F A) p0000
      p0004
  have p0006 := @gForn A B F
  have p0007 := @gEqtrd (synWfo F A B) (synCima F A) (synCrn F) B p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dffn4`. -/
@[expose]
noncomputable def gDffn4 (A : Class) (F : Class) :
    Nominal.NPrf (synWb (synWfn F A) (synWfo F A (synCrn F))) :=
  by
  have p0000 := @gEqid (synCrn F)
  have p0001 := @gBiantru (.classEq (synCrn F) (synCrn F)) (synWfn F A) p0000
  have p0002 := (Nominal.biimpRefl (synWfo F A (synCrn F)))
  have p0003 :=
    @gBitr4i (synWfn F A) (synWa (synWfn F A) (.classEq (synCrn F) (synCrn F)))
      (synWfo F A (synCrn F)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fores`. -/
@[expose]
noncomputable def gFores (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (synWss A (synCdm F)))
        (synWfo (synCres F A) A (synCima F A))) :=
  by
  have p0000 := @gFunres A F
  have p0001 :=
    @gAnim1i (synWfun F) (synWfun (synCres F A)) (synWss A (synCdm F)) p0000
  have p0002 := (Nominal.biimpRefl (synWfn (synCres F A) A))
  have p0003 := @gDfima3 F A
  have p0004 := @gEqcomi (synCima F A) (synCrn (synCres F A)) p0003
  have p0005 := (Nominal.biimpRefl (synWfo (synCres F A) A (synCima F A)))
  have p0006 :=
    @gMpbiran2 (synWfo (synCres F A) A (synCima F A)) (synWfn (synCres F A) A)
      (.classEq (synCrn (synCres F A)) (synCima F A)) p0004 p0005
  have p0007 := @gSsdmres A F
  have p0008 :=
    @gAnbi2i (synWss A (synCdm F)) (.classEq (synCdm (synCres F A)) A)
      (synWfun (synCres F A)) p0007
  have p0009 :=
    @gN3bitr4i (synWfn (synCres F A) A)
      (synWa (synWfun (synCres F A)) (.classEq (synCdm (synCres F A)) A))
      (synWfo (synCres F A) A (synCima F A))
      (synWa (synWfun (synCres F A)) (synWss A (synCdm F))) p0002 p0006 p0008
  have p0010 :=
    @gSylibr (synWa (synWfun F) (synWss A (synCdm F)))
      (synWa (synWfun (synCres F A)) (synWss A (synCdm F)))
      (synWfo (synCres F A) A (synCima F A)) p0001 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_foco`. -/
@[expose]
noncomputable def gFoco (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfo F B C) (synWfo G A B)) (synWfo (synCcom F G) A C)) :=
  by
  have p0000 := @gFco A B C F G
  have p0001 :=
    @gAd2ant2r (synWf F B C) (synWf G A B) (synWf (synCcom F G) A C)
      (.classEq (synCrn F) C) (.classEq (synCrn G) B) p0000
  have p0002 := @gFdm B C F
  have p0003 := @gEqtr3 (synCdm F) (synCrn G) B
  have p0004 :=
    @gSylan (synWf F B C) (.classEq (synCdm F) B) (.classEq (synCrn G) B)
      (.classEq (synCdm F) (synCrn G)) p0002 p0003
  have p0005 := @gRncoeq F G
  have p0006 :=
    @gEqeq1d (.classEq (synCdm F) (synCrn G)) (synCrn (synCcom F G)) (synCrn F) C
      p0005
  have p0007 :=
    @gBiimpar (.classEq (synCdm F) (synCrn G)) (.classEq (synCrn (synCcom F G)) C)
      (.classEq (synCrn F) C) p0006
  have p0008 :=
    @gSylan (synWa (synWf F B C) (.classEq (synCrn G) B))
      (.classEq (synCdm F) (synCrn G)) (.classEq (synCrn F) C)
      (.classEq (synCrn (synCcom F G)) C) p0004 p0007
  have p0009 :=
    @gAn32s (synWf F B C) (.classEq (synCrn G) B) (.classEq (synCrn F) C)
      (.classEq (synCrn (synCcom F G)) C) p0008
  have p0010 :=
    @gAdantrl (synWa (synWf F B C) (.classEq (synCrn F) C)) (.classEq (synCrn G) B)
      (.classEq (synCrn (synCcom F G)) C) (synWf G A B) p0009
  have p0011 :=
    @gJca
      (synWa (synWa (synWf F B C) (.classEq (synCrn F) C))
        (synWa (synWf G A B) (.classEq (synCrn G) B)))
      (synWf (synCcom F G) A C) (.classEq (synCrn (synCcom F G)) C) p0001 p0010
  have p0012 := @gDffo2 B C F
  have p0013 := @gDffo2 A B G
  have p0014 :=
    @gAnbi12i (synWfo F B C) (synWa (synWf F B C) (.classEq (synCrn F) C))
      (synWfo G A B) (synWa (synWf G A B) (.classEq (synCrn G) B)) p0012 p0013
  have p0015 := @gDffo2 A C (synCcom F G)
  have p0016 :=
    @gN3imtr4i
      (synWa (synWa (synWf F B C) (.classEq (synCrn F) C))
        (synWa (synWf G A B) (.classEq (synCrn G) B)))
      (synWa (synWf (synCcom F G) A C) (.classEq (synCrn (synCcom F G)) C))
      (synWa (synWfo F B C) (synWfo G A B)) (synWfo (synCcom F G) A C) p0011 p0014
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_f1oeq1`. -/
@[expose]
noncomputable def gF1oeq1 (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (synWb (synWf1o F A B) (synWf1o G A B))) :=
  by
  have p0000 := @gF1eq1 A B F G
  have p0001 := @gFoeq1 A B F G
  have p0002 :=
    @gAnbi12d (.classEq F G) (synWf1 F A B) (synWf1 G A B) (synWfo F A B)
      (synWfo G A B) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWf1o F A B))
  have p0004 := (Nominal.biimpRefl (synWf1o G A B))
  have p0005 :=
    @gN3bitr4g (.classEq F G) (synWa (synWf1 F A B) (synWfo F A B))
      (synWa (synWf1 G A B) (synWfo G A B)) (synWf1o F A B) (synWf1o G A B) p0002
      p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_f1oeq2`. -/
@[expose]
noncomputable def gF1oeq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWf1o F A C) (synWf1o F B C))) :=
  by
  have p0000 := @gF1eq2 A B C F
  have p0001 := @gFoeq2 A B C F
  have p0002 :=
    @gAnbi12d (.classEq A B) (synWf1 F A C) (synWf1 F B C) (synWfo F A C)
      (synWfo F B C) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWf1o F A C))
  have p0004 := (Nominal.biimpRefl (synWf1o F B C))
  have p0005 :=
    @gN3bitr4g (.classEq A B) (synWa (synWf1 F A C) (synWfo F A C))
      (synWa (synWf1 F B C) (synWfo F B C)) (synWf1o F A C) (synWf1o F B C) p0002
      p0003 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
