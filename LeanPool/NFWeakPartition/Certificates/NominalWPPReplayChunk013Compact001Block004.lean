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

/-- Checked nominal proof certificate identified upstream as `g_clos1induct`. -/
@[expose]
noncomputable def gClos1induct (x : Var) (z : Var) (C : Class) (R : Class) (S : Class)
    (V : Class) (X : Class) (dv_C_x : x ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_z : z ∉ R.fv) (dv_X_x : x ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_x_z : x ≠ z)
    (hyp_clos1induct_1 : Nominal.NPrf (.classMem S (synCvv)))
    (hyp_clos1induct_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_clos1induct_3 : Nominal.NPrf (.classEq C (synCclos1 S R))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem X V) (synWss S X) (synWral x C (.all z
              (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
                (.classMem (.cv z) X))))) (synWss C X)) :=
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
  have dv_cache_0003 : x ∉ ((synCin X C)).fv :=
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
  have dv_cache_0004 : x ∉ ((synWa (.classMem (.cv z) X) (.classMem (.cv z) C))).fv :=
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
  have dv_cache_0005 : z ∉ ((synCima R (synCin X C))).fv :=
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
  have dv_cache_0006 : z ∉ ((synCin X C)).fv :=
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
  have dv_cache_0011 : a ∉ ((synCin X C)).fv :=
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
      ((synWa (synWss S (synCin X C))
          (synWss (synCima R (synCin X C)) (synCin X C)))).fv :=
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
  have p0000 := @gClos1ex R S hyp_clos1induct_1 hyp_clos1induct_2
  have p0001 := @gEqeltri C (synCclos1 S R) (synCvv) hyp_clos1induct_3 p0000
  have p0002 := @gInexg X C V (synCvv)
  have p0003 :=
    @gMpan2 (.classMem X V) (.classMem C (synCvv)) (.classMem (synCin X C) (synCvv))
      p0001 p0002
  have p0004 := @gClos1base C R S hyp_clos1induct_3
  have p0005 := @gSsin S X C
  have p0006 :=
    @gBiimpi (synWa (synWss S X) (synWss S C)) (synWss S (synCin X C)) p0005
  have p0007 := @gMpan2 (synWss S X) (synWss S C) (synWss S (synCin X C)) p0004 p0006
  have p0008 :=
    @gElima2 x (.cv z) R (synCin X C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 := @gElin (.cv z) X C
  have p0010 :=
    @gImbi12i (.classMem (.cv z) (synCima R (synCin X C)))
      (synWex x (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z))))
      (.classMem (.cv z) (synCin X C))
      (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0008 p0009
  have p0011 :=
    (Nominal.biimpRefl (synWral x C
        (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X))))
  have p0012 :=
    @gImpexp (.classMem (.cv x) C)
      (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))) (.classMem (.cv z) X)
  have p0013 := @gClos1conn (.cv x) (.cv z) C R S hyp_clos1induct_3
  have p0014 :=
    @gBiantrud (synWa (.classMem (.cv x) C) (synWbr (.cv x) R (.cv z)))
      (.classMem (.cv z) C) (.classMem (.cv z) X) p0013
  have p0015 :=
    @gAdantrl (.classMem (.cv x) C) (synWbr (.cv x) R (.cv z))
      (synWb (.classMem (.cv z) X) (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      (.classMem (.cv x) X) p0014
  have p0016 :=
    @gPm574i
      (synWa (.classMem (.cv x) C) (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
      (.classMem (.cv z) X) (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0015
  have p0017 :=
    @gBitr3i
      (.imp (.classMem (.cv x) C)
        (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))
      (.imp (synWa (.classMem (.cv x) C)
          (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))) (.classMem (.cv z) X))
      (.imp (synWa (.classMem (.cv x) C)
          (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
        (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      p0012 p0016
  have p0018 :=
    @gAlbii
      (.imp (.classMem (.cv x) C)
        (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))
      (.imp (synWa (.classMem (.cv x) C)
          (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
        (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      x p0017
  have p0019 :=
    @gBitri
      (synWral x C (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      (.all x (.imp (.classMem (.cv x) C)
          (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      (.all x (.imp (synWa (.classMem (.cv x) C)
            (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
          (synWa (.classMem (.cv z) X) (.classMem (.cv z) C))))
      p0011 p0018
  have p0020 := @gElin (.cv x) X C
  have p0021 := @gAncom (.classMem (.cv x) X) (.classMem (.cv x) C)
  have p0022 :=
    @gBitri (.classMem (.cv x) (synCin X C))
      (synWa (.classMem (.cv x) X) (.classMem (.cv x) C))
      (synWa (.classMem (.cv x) C) (.classMem (.cv x) X)) p0020 p0021
  have p0023 :=
    @gAnbi1i (.classMem (.cv x) (synCin X C))
      (synWa (.classMem (.cv x) C) (.classMem (.cv x) X)) (synWbr (.cv x) R (.cv z))
      p0022
  have p0024 :=
    @gAnass (.classMem (.cv x) C) (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))
  have p0025 :=
    @gBitri (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z)))
      (synWa (synWa (.classMem (.cv x) C) (.classMem (.cv x) X)) (synWbr (.cv x) R (.cv z)))
      (synWa (.classMem (.cv x) C) (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
      p0023 p0024
  have p0026 :=
    @gImbi1i (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z)))
      (synWa (.classMem (.cv x) C) (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
      (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0025
  have p0027 :=
    @gAlbii
      (.imp (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z)))
        (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      (.imp (synWa (.classMem (.cv x) C)
          (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
        (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      x p0026
  have p0028 :=
    @gN1923v (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z)))
      (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)) x dv_cache_0004
  have p0029 :=
    @gN3bitr2i
      (synWral x C (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      (.all x (.imp (synWa (.classMem (.cv x) C)
            (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))))
          (synWa (.classMem (.cv z) X) (.classMem (.cv z) C))))
      (.all x (.imp (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z)))
          (synWa (.classMem (.cv z) X) (.classMem (.cv z) C))))
      (.imp (synWex x (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z))))
        (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      p0019 p0027 p0028
  have p0030 :=
    @gBitr4i
      (.imp (.classMem (.cv z) (synCima R (synCin X C))) (.classMem (.cv z) (synCin X C)))
      (.imp (synWex x (synWa (.classMem (.cv x) (synCin X C)) (synWbr (.cv x) R (.cv z))))
        (synWa (.classMem (.cv z) X) (.classMem (.cv z) C)))
      (synWral x C (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      p0010 p0029
  have p0031 :=
    @gAlbii
      (.imp (.classMem (.cv z) (synCima R (synCin X C))) (.classMem (.cv z) (synCin X C)))
      (synWral x C (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
          (.classMem (.cv z) X)))
      z p0030
  have p0032 :=
    @gDfss2 z (synCima R (synCin X C)) (synCin X C) dv_cache_0005 dv_cache_0006
  have p0033 :=
    @gRalcom4
      (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z))) (.classMem (.cv z) X))
      x z C dv_cache_0007 dv_cache_0008
  have p0034 :=
    @gN3bitr4i
      (.all z (.imp (.classMem (.cv z) (synCima R (synCin X C)))
          (.classMem (.cv z) (synCin X C))))
      (.all z (synWral x C (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      (synWss (synCima R (synCin X C)) (synCin X C))
      (synWral x C (.all z (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      p0031 p0032 p0033
  have p0035 :=
    @gBiimpri (synWss (synCima R (synCin X C)) (synCin X C))
      (synWral x C (.all z (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      p0034
  have p0036 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 R S a
      dv_cache_0009 dv_cache_0010
  have p0037 :=
    @gEqtri C (synCclos1 S R)
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      hyp_clos1induct_3 p0036
  have p0038 := @gSseq2 (.cv a) (synCin X C) S
  have p0039 := @gImaeq2 (.cv a) (synCin X C) R
  have p0040 := @gId (.classEq (.cv a) (synCin X C))
  have p0041 :=
    @gSseq12d (.classEq (.cv a) (synCin X C)) (synCima R (.cv a))
      (synCima R (synCin X C)) (.cv a) (synCin X C) p0039 p0040
  have p0042 :=
    @gAnbi12d (.classEq (.cv a) (synCin X C)) (synWss S (.cv a))
      (synWss S (synCin X C)) (synWss (synCima R (.cv a)) (.cv a))
      (synWss (synCima R (synCin X C)) (synCin X C)) p0038 p0041
  have p0043 :=
    @gElabg (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
      (synWa (synWss S (synCin X C)) (synWss (synCima R (synCin X C)) (synCin X C)))
      a (synCin X C) (synCvv) dv_cache_0011 dv_cache_0012 p0042
  have p0044 :=
    @gBiimprd (.classMem (synCin X C) (synCvv))
      (.classMem (synCin X C)
        (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (synWa (synWss S (synCin X C)) (synWss (synCima R (synCin X C)) (synCin X C)))
      p0043
  have p0045 :=
    @gN3impib (.classMem (synCin X C) (synCvv)) (synWss S (synCin X C))
      (synWss (synCima R (synCin X C)) (synCin X C))
      (.classMem (synCin X C)
        (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      p0044
  have p0046 :=
    @gIntss1 (synCin X C)
      (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
  have p0047 :=
    @gSyl
      (synW3a (.classMem (synCin X C) (synCvv)) (synWss S (synCin X C))
        (synWss (synCima R (synCin X C)) (synCin X C)))
      (.classMem (synCin X C)
        (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (synWss (synCint
          (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
        (synCin X C))
      p0045 p0046
  have p0048 :=
    @gSyl5eqss
      (synW3a (.classMem (synCin X C) (synCvv)) (synWss S (synCin X C))
        (synWss (synCima R (synCin X C)) (synCin X C)))
      C
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (synCin X C) p0037 p0047
  have p0049 := @gInss1 X C
  have p0050 :=
    @gSyl6ss
      (synW3a (.classMem (synCin X C) (synCvv)) (synWss S (synCin X C))
        (synWss (synCima R (synCin X C)) (synCin X C)))
      C (synCin X C) X p0048 p0049
  have p0051 :=
    @gSyl3an (.classMem X V) (.classMem (synCin X C) (synCvv)) (synWss S X)
      (synWss S (synCin X C))
      (synWral x C (.all z (.imp (synWa (.classMem (.cv x) X) (synWbr (.cv x) R (.cv z)))
            (.classMem (.cv z) X))))
      (synWss (synCima R (synCin X C)) (synCin X C)) (synWss C X) p0003 p0007 p0035
      p0050
  exact p0051

/-- Checked nominal proof certificate identified upstream as `g_clos1is`. -/
@[expose]
noncomputable def gClos1is (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (y : Var) (z : Var) (A : Class) (C : Class) (R : Class) (S : Class)
    (dv_A_x : x ∉ A.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_R_y : y ∉ R.fv)
    (dv_R_z : z ∉ R.fv) (dv_S_x : x ∉ S.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_clos1is_1 : Nominal.NPrf (.classMem S (synCvv)))
    (hyp_clos1is_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_clos1is_3 : Nominal.NPrf (.classEq C (synCclos1 S R)))
    (hyp_clos1is_4 : Nominal.NPrf (.classMem (.cab x ph) (synCvv)))
    (hyp_clos1is_5 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps)))
    (hyp_clos1is_6 : Nominal.NPrf (.imp (.objEq x z) (synWb ph ch)))
    (hyp_clos1is_7 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph th)))
    (hyp_clos1is_8 : Nominal.NPrf (.imp (.classMem (.cv x) S) ph))
    (hyp_clos1is_9 : Nominal.NPrf
        (.imp (synW3a (.classMem (.cv y) C) (synWbr (.cv y) R (.cv z)) ps) ch)) :
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
  have p0000 := @gSsab ph x S dv_cache_0001
  have p0001 :=
    @gMpgbir (synWss S (.cab x ph)) (.imp (.classMem (.cv x) S) ph) x p0000
      hyp_clos1is_8
  have p0002 :=
    @gN3expib (.classMem (.cv y) C) (synWbr (.cv y) R (.cv z)) ps ch hyp_clos1is_9
  have p0003 := @gVex y
  have p0004_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (synWb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_clos1is_5
  have p0004 :=
    @gElab ph ps x (.cv y) dv_cache_0002 dv_cache_0003 p0003 p0004_e01_recanon
  have p0005 :=
    @gAnbi1i (.classMem (.cv y) (.cab x ph)) ps (synWbr (.cv y) R (.cv z)) p0004
  have p0006 := @gAncom ps (synWbr (.cv y) R (.cv z))
  have p0007 :=
    @gBitri (synWa (.classMem (.cv y) (.cab x ph)) (synWbr (.cv y) R (.cv z)))
      (synWa ps (synWbr (.cv y) R (.cv z))) (synWa (synWbr (.cv y) R (.cv z)) ps)
      p0005 p0006
  have p0008 := @gVex z
  have p0009_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (synWb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_clos1is_6
  have p0009 :=
    @gElab ph ch x (.cv z) dv_cache_0004 dv_cache_0005 p0008 p0009_e01_recanon
  have p0010 :=
    @gN3imtr4g (.classMem (.cv y) C) (synWa (synWbr (.cv y) R (.cv z)) ps) ch
      (synWa (.classMem (.cv y) (.cab x ph)) (synWbr (.cv y) R (.cv z)))
      (.classMem (.cv z) (.cab x ph)) p0002 p0007 p0009
  have p0011 :=
    @gAlrimiv (.classMem (.cv y) C)
      (.imp (synWa (.classMem (.cv y) (.cab x ph)) (synWbr (.cv y) R (.cv z)))
        (.classMem (.cv z) (.cab x ph)))
      z dv_cache_0006 p0010
  have p0012 :=
    @gRgen
      (.all z (.imp (synWa (.classMem (.cv y) (.cab x ph)) (synWbr (.cv y) R (.cv z)))
          (.classMem (.cv z) (.cab x ph))))
      y C p0011
  have p0013 :=
    @gClos1induct y z C R S (synCvv) (.cab x ph) dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 hyp_clos1is_1
      hyp_clos1is_2 hyp_clos1is_3
  have p0014 :=
    @gMp3an (.classMem (.cab x ph) (synCvv)) (synWss S (.cab x ph))
      (synWral y C (.all z
          (.imp (synWa (.classMem (.cv y) (.cab x ph)) (synWbr (.cv y) R (.cv z)))
            (.classMem (.cv z) (.cab x ph)))))
      (synWss C (.cab x ph)) hyp_clos1is_4 p0001 p0012 p0013
  have p0015 := @gSseli C (.cab x ph) A p0014
  have p0016 := @gElabg ph th x A C dv_cache_0014 dv_cache_0015 hyp_clos1is_7
  have p0017 := @gMpbid (.classMem A C) (.classMem A (.cab x ph)) th p0015 p0016
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

/-- Checked nominal proof certificate identified upstream as `g_clos1basesuc`. -/
@[expose]
noncomputable def gClos1basesuc (x : Var) (A : Class) (C : Class) (R : Class) (S : Class)
    (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_R_x : x ∉ R.fv)
    (hyp_clos1basesuc_1 : Nominal.NPrf (.classMem S (synCvv)))
    (hyp_clos1basesuc_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_clos1basesuc_3 : Nominal.NPrf (.classEq C (synCclos1 S R))) :
    Nominal.NPrf
      (synWb (.classMem A C) (synWo (.classMem A S) (synWrex x C (synWbr (.cv x) R A)))) :=
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
  have dv_cache_0011 : y ∉ ((synWbr (.cv z) R (.cv w))).fv :=
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
      ((Wff.imp (synWbr (.cv z) R (.cv w)) (synWrex y C (synWbr (.cv y) R (.cv w))))).fv :=
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
  have dv_cache_0013 : y ∉ ((synWbr (.cv x) R (.cv w))).fv :=
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
  have dv_cache_0014 : x ∉ ((synWbr (.cv y) R (.cv w))).fv :=
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
    y ∉ ((synWo (.classMem (.cv w) S) (synWrex x C (synWbr (.cv x) R (.cv w))))).fv :=
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
    z ∉ ((synWo (.classMem (.cv y) S) (synWrex x C (synWbr (.cv x) R (.cv y))))).fv :=
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
    w ∉ ((synWo (.classMem (.cv y) S) (synWrex x C (synWbr (.cv x) R (.cv y))))).fv :=
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
    y ∉ ((synWo (.classMem (.cv z) S) (synWrex x C (synWbr (.cv x) R (.cv z))))).fv :=
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
    y ∉ ((synWo (.classMem A S) (synWrex x C (synWbr (.cv x) R A)))).fv :=
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
  have p0000 := @gAbid2 y S dv_cache_0001
  have p0001 := @gEqcomi (.cab y (.classMem (.cv y) S)) S p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x R C
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @gUneq12i S (.cab y (.classMem (.cv y) S)) (synCima R C)
      (.cab y (synWrex x C (synWbr (.cv x) R (.cv y)))) p0001 p0002
  have p0004 := @gUnab (.classMem (.cv y) S) (synWrex x C (synWbr (.cv x) R (.cv y))) y
  have p0005 :=
    @gEqtri (synCun S (synCima R C))
      (synCun (.cab y (.classMem (.cv y) S))
        (.cab y (synWrex x C (synWbr (.cv x) R (.cv y)))))
      (.cab y (synWo (.classMem (.cv y) S) (synWrex x C (synWbr (.cv x) R (.cv y)))))
      p0003 p0004
  have p0006 := @gClos1ex R S hyp_clos1basesuc_1 hyp_clos1basesuc_2
  have p0007 := @gEqeltri C (synCclos1 S R) (synCvv) hyp_clos1basesuc_3 p0006
  have p0008 := @gImaex R C hyp_clos1basesuc_2 p0007
  have p0009 := @gUnex S (synCima R C) hyp_clos1basesuc_1 p0008
  have p0010 :=
    @gEqeltrri (synCun S (synCima R C))
      (.cab y (synWo (.classMem (.cv y) S) (synWrex x C (synWbr (.cv x) R (.cv y)))))
      (synCvv) p0005 p0009
  have p0011 := @gEleq1 (.cv y) (.cv z) S
  have p0012 := @gBreq2 (.cv y) (.cv z) (.cv x) R
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (synWb (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @gRexbidv (.objEq y z) (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R (.cv z)) x C
      dv_cache_0007 p0013_e00_recanon
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (synWb (.classMem (.cv y) S) (.classMem (.cv z) S))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0014 :=
    @gOrbi12d (.objEq y z) (.classMem (.cv y) S) (.classMem (.cv z) S)
      (synWrex x C (synWbr (.cv x) R (.cv y)))
      (synWrex x C (synWbr (.cv x) R (.cv z))) p0014_e00_recanon p0013
  have p0015 := @gEleq1 (.cv y) (.cv w) S
  have p0016 := @gBreq2 (.cv y) (.cv w) (.cv x) R
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (synWb (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gRexbidv (.objEq y w) (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R (.cv w)) x C
      dv_cache_0008 p0017_e00_recanon
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (synWb (.classMem (.cv y) S) (.classMem (.cv w) S))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0018 :=
    @gOrbi12d (.objEq y w) (.classMem (.cv y) S) (.classMem (.cv w) S)
      (synWrex x C (synWbr (.cv x) R (.cv y)))
      (synWrex x C (synWbr (.cv x) R (.cv w))) p0018_e00_recanon p0017
  have p0019 := @gEleq1 (.cv y) A S
  have p0020 := @gBreq2 (.cv y) A (.cv x) R
  have p0021 :=
    @gRexbidv (.classEq (.cv y) A) (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R A) x C
      dv_cache_0009 p0020
  have p0022 :=
    @gOrbi12d (.classEq (.cv y) A) (.classMem (.cv y) S) (.classMem A S)
      (synWrex x C (synWbr (.cv x) R (.cv y))) (synWrex x C (synWbr (.cv x) R A))
      p0019 p0021
  have p0023 := @gOrc (.classMem (.cv y) S) (synWrex x C (synWbr (.cv x) R (.cv y)))
  have p0024 := @gClos1base C R S hyp_clos1basesuc_3
  have p0025 := @gSseli S C (.cv z) p0024
  have p0026 := @gBreq1 (.cv y) (.cv z) (.cv w) R
  have p0027 :=
    @gRspcev (synWbr (.cv y) R (.cv w)) (synWbr (.cv z) R (.cv w)) y (.cv z) C
      dv_cache_0010 dv_cache_0004 dv_cache_0011 p0026
  have p0028 :=
    @gEx (.classMem (.cv z) C) (synWbr (.cv z) R (.cv w))
      (synWrex y C (synWbr (.cv y) R (.cv w))) p0027
  have p0029 :=
    @gSyl (.classMem (.cv z) S) (.classMem (.cv z) C)
      (.imp (synWbr (.cv z) R (.cv w)) (synWrex y C (synWbr (.cv y) R (.cv w)))) p0025
      p0028
  have p0030 := @gClos1conn (.cv x) (.cv z) C R S hyp_clos1basesuc_3
  have p0031 :=
    @gSyl (synWa (.classMem (.cv x) C) (synWbr (.cv x) R (.cv z)))
      (.classMem (.cv z) C)
      (.imp (synWbr (.cv z) R (.cv w)) (synWrex y C (synWbr (.cv y) R (.cv w)))) p0030
      p0028
  have p0032 :=
    @gRexlimiva (synWbr (.cv x) R (.cv z))
      (.imp (synWbr (.cv z) R (.cv w)) (synWrex y C (synWbr (.cv y) R (.cv w)))) x C
      dv_cache_0012 p0031
  have p0033 :=
    @gJaoi (.classMem (.cv z) S)
      (.imp (synWbr (.cv z) R (.cv w)) (synWrex y C (synWbr (.cv y) R (.cv w))))
      (synWrex x C (synWbr (.cv x) R (.cv z))) p0029 p0032
  have p0034 :=
    @gImpcom (synWo (.classMem (.cv z) S) (synWrex x C (synWbr (.cv x) R (.cv z))))
      (synWbr (.cv z) R (.cv w)) (synWrex y C (synWbr (.cv y) R (.cv w))) p0033
  have p0035 := @gBreq1 (.cv x) (.cv y) (.cv w) R
  have p0036_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (synWbr (.cv x) R (.cv w)) (synWbr (.cv y) R (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0036 :=
    @gCbvrexv (synWbr (.cv x) R (.cv w)) (synWbr (.cv y) R (.cv w)) x y C dv_cache_0005
      dv_cache_0004 dv_cache_0013 dv_cache_0014 p0036_e00_recanon
  have p0037 :=
    @gSylibr
      (synWa (synWbr (.cv z) R (.cv w))
        (synWo (.classMem (.cv z) S) (synWrex x C (synWbr (.cv x) R (.cv z)))))
      (synWrex y C (synWbr (.cv y) R (.cv w)))
      (synWrex x C (synWbr (.cv x) R (.cv w))) p0034 p0036
  have p0038 :=
    @gOlcd
      (synWa (synWbr (.cv z) R (.cv w))
        (synWo (.classMem (.cv z) S) (synWrex x C (synWbr (.cv x) R (.cv z)))))
      (synWrex x C (synWbr (.cv x) R (.cv w))) (.classMem (.cv w) S) p0037
  have p0039 :=
    @gN3adant1 (synWbr (.cv z) R (.cv w))
      (synWo (.classMem (.cv z) S) (synWrex x C (synWbr (.cv x) R (.cv z))))
      (synWo (.classMem (.cv w) S) (synWrex x C (synWbr (.cv x) R (.cv w))))
      (.classMem (.cv z) C) p0038
  have p0040 :=
    @gClos1is (synWo (.classMem (.cv y) S) (synWrex x C (synWbr (.cv x) R (.cv y))))
      (synWo (.classMem (.cv z) S) (synWrex x C (synWbr (.cv x) R (.cv z))))
      (synWo (.classMem (.cv w) S) (synWrex x C (synWbr (.cv x) R (.cv w))))
      (synWo (.classMem A S) (synWrex x C (synWbr (.cv x) R A))) y z w A C R S
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0001
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 hyp_clos1basesuc_1 hyp_clos1basesuc_2 hyp_clos1basesuc_3
      p0010 p0014 p0018 p0022 p0023 p0039
  have p0041 := @gSseli S C A p0024
  have p0042 := @gClos1conn (.cv x) A C R S hyp_clos1basesuc_3
  have p0043 := @gRexlimiva (synWbr (.cv x) R A) (.classMem A C) x C dv_cache_0028 p0042
  have p0044 :=
    @gJaoi (.classMem A S) (.classMem A C) (synWrex x C (synWbr (.cv x) R A)) p0041
      p0043
  have p0045 :=
    @gImpbii (.classMem A C)
      (synWo (.classMem A S) (synWrex x C (synWbr (.cv x) R A))) p0040 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_clos1baseima`. -/
@[expose]
noncomputable def gClos1baseima (C : Class) (R : Class) (S : Class)
    (hyp_clos1basesuc_1 : Nominal.NPrf (.classMem S (synCvv)))
    (hyp_clos1basesuc_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_clos1basesuc_3 : Nominal.NPrf (.classEq C (synCclos1 S R))) :
    Nominal.NPrf (.classEq C (synCun S (synCima R C))) :=
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
  have dv_cache_0005 : x ∉ ((synCun S (synCima R C))).fv :=
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
  have p0000 := @gElima y (.cv x) R C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gOrbi2i (.classMem (.cv x) (synCima R C))
      (synWrex y C (synWbr (.cv y) R (.cv x))) (.classMem (.cv x) S) p0000
  have p0002 := @gElun (.cv x) S (synCima R C)
  have p0003 :=
    @gClos1basesuc y (.cv x) C R S dv_cache_0001 dv_cache_0003 dv_cache_0002
      hyp_clos1basesuc_1 hyp_clos1basesuc_2 hyp_clos1basesuc_3
  have p0004 :=
    @gN3bitr4ri (synWo (.classMem (.cv x) S) (.classMem (.cv x) (synCima R C)))
      (synWo (.classMem (.cv x) S) (synWrex y C (synWbr (.cv y) R (.cv x))))
      (.classMem (.cv x) (synCun S (synCima R C))) (.classMem (.cv x) C) p0001 p0002
      p0003
  have p0005 := @gEqriv x C (synCun S (synCima R C)) dv_cache_0004 dv_cache_0005 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_clos1basesucg`. -/
@[expose]
noncomputable def gClos1basesucg (x : Var) (A : Class) (C : Class) (R : Class)
    (S : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv)
    (dv_R_x : x ∉ R.fv) (dv_S_x : x ∉ S.fv)
    (hyp_clos1basesucg_1 : Nominal.NPrf (.classEq C (synCclos1 S R))) :
    Nominal.NPrf
      (.imp (synWa (.classMem S V) (.classMem R W)) (synWb (.classMem A C)
          (synWo (.classMem A S) (synWrex x C (synWbr (.cv x) R A))))) :=
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
  have dv_cache_0001 : x ∉ ((synCclos1 (.cv s) (.cv r))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_s, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCclos1 S (.cv r))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCclos1 S R)).fv :=
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
      ((synWb (.classMem A (synCclos1 S R)) (synWo (.classMem A S)
            (synWrex x (synCclos1 S R) (synWbr (.cv x) R A))))).fv :=
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
      ((synWb (.classMem A (synCclos1 S (.cv r))) (synWo (.classMem A S)
            (synWrex x (synCclos1 S (.cv r)) (synWbr (.cv x) (.cv r) A))))).fv :=
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
  have p0000 := @gClos1eq1 (.cv r) (.cv s) S
  have p0001 :=
    @gEleq2d (.classEq (.cv s) S) (synCclos1 (.cv s) (.cv r)) (synCclos1 S (.cv r)) A
      p0000
  have p0002 := @gEleq2 (.cv s) S A
  have p0003 :=
    @gRexeqdv (.classEq (.cv s) S) (synWbr (.cv x) (.cv r) A) x
      (synCclos1 (.cv s) (.cv r)) (synCclos1 S (.cv r)) dv_cache_0001 dv_cache_0002
      p0000
  have p0004 :=
    @gOrbi12d (.classEq (.cv s) S) (.classMem A (.cv s)) (.classMem A S)
      (synWrex x (synCclos1 (.cv s) (.cv r)) (synWbr (.cv x) (.cv r) A))
      (synWrex x (synCclos1 S (.cv r)) (synWbr (.cv x) (.cv r) A)) p0002 p0003
  have p0005 :=
    @gBibi12d (.classEq (.cv s) S) (.classMem A (synCclos1 (.cv s) (.cv r)))
      (.classMem A (synCclos1 S (.cv r)))
      (synWo (.classMem A (.cv s))
        (synWrex x (synCclos1 (.cv s) (.cv r)) (synWbr (.cv x) (.cv r) A)))
      (synWo (.classMem A S) (synWrex x (synCclos1 S (.cv r)) (synWbr (.cv x) (.cv r) A)))
      p0001 p0004
  have p0006 := @gClos1eq2 (.cv r) S R
  have p0007 :=
    @gEleq2d (.classEq (.cv r) R) (synCclos1 S (.cv r)) (synCclos1 S R) A p0006
  have p0008 := @gBreq (.cv x) A (.cv r) R
  have p0009 :=
    @gRexeqbidv (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) A) (synWbr (.cv x) R A) x
      (synCclos1 S (.cv r)) (synCclos1 S R) dv_cache_0002 dv_cache_0003 dv_cache_0004
      p0006 p0008
  have p0010 :=
    @gOrbi2d (.classEq (.cv r) R)
      (synWrex x (synCclos1 S (.cv r)) (synWbr (.cv x) (.cv r) A))
      (synWrex x (synCclos1 S R) (synWbr (.cv x) R A)) (.classMem A S) p0009
  have p0011 :=
    @gBibi12d (.classEq (.cv r) R) (.classMem A (synCclos1 S (.cv r)))
      (.classMem A (synCclos1 S R))
      (synWo (.classMem A S) (synWrex x (synCclos1 S (.cv r)) (synWbr (.cv x) (.cv r) A)))
      (synWo (.classMem A S) (synWrex x (synCclos1 S R) (synWbr (.cv x) R A))) p0007
      p0010
  have p0012 := @gVex s
  have p0013 := @gVex r
  have p0014 := @gEqid (synCclos1 (.cv s) (.cv r))
  have p0015 :=
    @gClos1basesuc x A (synCclos1 (.cv s) (.cv r)) (.cv r) (.cv s) dv_cache_0005
      dv_cache_0001 dv_cache_0006 p0012 p0013 p0014
  have p0016 :=
    @gVtocl2g
      (synWb (.classMem A (synCclos1 (.cv s) (.cv r))) (synWo (.classMem A (.cv s))
          (synWrex x (synCclos1 (.cv s) (.cv r)) (synWbr (.cv x) (.cv r) A))))
      (synWb (.classMem A (synCclos1 S (.cv r))) (synWo (.classMem A S)
          (synWrex x (synCclos1 S (.cv r)) (synWbr (.cv x) (.cv r) A))))
      (synWb (.classMem A (synCclos1 S R))
        (synWo (.classMem A S) (synWrex x (synCclos1 S R) (synWbr (.cv x) R A))))
      s r S R V W dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      p0005 p0011 p0015
  have p0017 := @gEleq2i C (synCclos1 S R) A hyp_clos1basesucg_1
  have p0018 :=
    @gRexeqi (synWbr (.cv x) R A) x C (synCclos1 S R) dv_cache_0012 dv_cache_0003
      hyp_clos1basesucg_1
  have p0019 :=
    @gOrbi2i (synWrex x C (synWbr (.cv x) R A))
      (synWrex x (synCclos1 S R) (synWbr (.cv x) R A)) (.classMem A S) p0018
  have p0020 :=
    @gN3bitr4g (synWa (.classMem S V) (.classMem R W)) (.classMem A (synCclos1 S R))
      (synWo (.classMem A S) (synWrex x (synCclos1 S R) (synWbr (.cv x) R A)))
      (.classMem A C) (synWo (.classMem A S) (synWrex x C (synWbr (.cv x) R A))) p0016
      p0017 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_clos10`. -/
@[expose]
noncomputable def gClos10 (C : Class) (R : Class)
    (hyp_clos10_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_clos10_2 : Nominal.NPrf (.classEq C (synCclos1 (synC0) R))) :
    Nominal.NPrf (.classEq C (synC0)) :=
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
  have dv_cache_0005 : x ∉ ((synC0)).fv :=
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
  have dv_cache_0006 : y ∉ ((synC0)).fv :=
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
  have p0000 := @gN0ex
  have p0001 := @gN0ss (synC0)
  have p0002 := @gNoel (.cv x)
  have p0003 := @gPm221i (.classMem (.cv x) (synC0)) (.classMem (.cv y) (synC0)) p0002
  have p0004 :=
    @gAdantr (.classMem (.cv x) (synC0)) (.classMem (.cv y) (synC0))
      (synWbr (.cv x) R (.cv y)) p0003
  have p0005 := Nominal.gen p0004 y
  have p0006 :=
    @gRgenw
      (.all y (.imp (synWa (.classMem (.cv x) (synC0)) (synWbr (.cv x) R (.cv y)))
          (.classMem (.cv y) (synC0))))
      x C p0005
  have p0008 :=
    @gClos1induct x y C R (synC0) (synCvv) (synC0) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000
      hyp_clos10_1 hyp_clos10_2
  have p0009 :=
    @gMp3an (.classMem (synC0) (synCvv)) (synWss (synC0) (synC0))
      (synWral x C (.all y
          (.imp (synWa (.classMem (.cv x) (synC0)) (synWbr (.cv x) R (.cv y)))
            (.classMem (.cv y) (synC0)))))
      (synWss C (synC0)) p0000 p0001 p0006 p0008
  have p0010 := @gN0ss C
  have p0011 := @gEqssi C (synC0) p0009 p0010
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

/-- Checked nominal proof certificate identified upstream as `g_transex`. -/
@[expose]
noncomputable def gTransex : Nominal.NPrf (.classMem (synCtrans) (synCvv)) :=
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
  have dv_cache_0011 : y ∉ ((synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))).fv :=
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
      ((synCin (synCins2 (synCins2 (synCsset))) (synCima
            (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                  (synCxp (synCvv) (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                (synCins2 (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))).fv :=
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
      ((synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))).fv :=
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
      ((synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
              (synCxp (synCvv) (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
            (synCins2 (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c))))))).fv :=
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
    z ∉ ((synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))).fv :=
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
      ((synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset))))).fv :=
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
  have dv_cache_0017 : z ∉ ((synCop (.cv x) (.cv y))).fv :=
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
      ((synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))).fv :=
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
      ((synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))).fv :=
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
  have dv_cache_0021 : q ∉ ((synCop (.cv y) (.cv z))).fv :=
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
    y ∉ ((synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r)))).fv :=
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
      ((synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset))))).fv :=
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
  have dv_cache_0025 : y ∉ ((synCop (.cv x) (.cv z))).fv :=
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
  have dv_cache_0027 : x ∉ ((synCop (.cv r) (.cv a))).fv :=
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
      ((synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
              (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif
                    (synCin (synCxp (synCvv) (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                        (synC1c))) (synCins2 (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
            (synC1c)))).fv :=
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
      ((synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCima
                    (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                          (synCxp (synCvv) (synCins4 (synCima (synCin
                                  (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                            (synC1c))) (synCins2 (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
                (synC1c))) (synC1c)))).fv :=
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
      ((synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCima
                    (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                          (synCxp (synCvv) (synCins4 (synCima (synCin
                                  (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                            (synC1c))) (synCins2 (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
                (synC1c))) (synC1c)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTrans x y z r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @gVex r
  have p0002 := @gVex a
  have p0003 := @gOpex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @gElcompl (synCop (.cv r) (.cv a))
      (synCima (synCin (synCins2 (synCsset)) (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCima
                (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                      (synCxp (synCvv) (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                        (synC1c))) (synCins2 (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
            (synC1c))) (synC1c))
      p0003
  have p0005 :=
    @gElin (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset))
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCima
            (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                  (synCxp (synCvv) (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                (synCins2 (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
        (synC1c))
  have p0006 := @gOtelins2 (synCsn (.cv x)) (.cv r) (.cv a) (synCsset) p0001
  have p0007 := @gVex x
  have p0008 := @gOpelssetsn (.cv x) (.cv a) p0007 p0002
  have p0009_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a) p0006
      p0009_e01_recanon
  have p0010 :=
    @gElima1c y (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
      (synCin (synCins2 (synCins2 (synCsset))) (synCima
          (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                (synCxp (synCvv) (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
              (synCins2 (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
      dv_cache_0011 dv_cache_0012
  have p0011 :=
    @gElin
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
      (synCins2 (synCins2 (synCsset)))
      (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
              (synCxp (synCvv) (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
            (synCins2 (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c))
  have p0012 := @gSnex (.cv x)
  have p0013 :=
    @gOtelins2 (synCsn (.cv y)) (synCsn (.cv x)) (synCop (.cv r) (.cv a))
      (synCins2 (synCsset)) p0012
  have p0014 := @gOtelins2 (synCsn (.cv y)) (.cv r) (.cv a) (synCsset) p0001
  have p0015 := @gVex y
  have p0016 := @gOpelssetsn (.cv y) (.cv a) p0015 p0002
  have p0017_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv y)) (.cv a)) (synCsset)) (.objMem y a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv y)) (.cv a)) (synCsset)) (.objMem y a) p0013
      p0014 p0017_e02_recanon
  have p0018 :=
    @gElima1c z
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
      (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
            (synCxp (synCvv) (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
          (synCins2 (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      dv_cache_0013 dv_cache_0014
  have p0019 :=
    @gElin
      (synCop (synCsn (.cv z))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
      (synCins2 (synCins2 (synCins2 (synCsset))))
      (synCdif (synCin (synCxp (synCvv) (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
        (synCins2 (synCins4 (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
  have p0020 := @gSnex (.cv y)
  have p0021 :=
    @gOtelins2 (synCsn (.cv z)) (synCsn (.cv y))
      (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
      (synCins2 (synCins2 (synCsset))) p0020
  have p0022 :=
    @gOtelins2 (synCsn (.cv z)) (synCsn (.cv x)) (synCop (.cv r) (.cv a))
      (synCins2 (synCsset)) p0012
  have p0023 := @gOtelins2 (synCsn (.cv z)) (.cv r) (.cv a) (synCsset) p0001
  have p0024 := @gVex z
  have p0025 := @gOpelssetsn (.cv z) (.cv a) p0024 p0002
  have p0026_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv a)) (synCsset)) (.objMem z a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv a)) (synCsset)) (.objMem z a) p0023
      p0026_e01_recanon
  have p0027 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
        (synCins2 (synCins2 (synCins2 (synCsset)))))
      (.classMem
        (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.objMem z a) p0021 p0022 p0026
  have p0028 :=
    @gEldif
      (synCop (synCsn (.cv z))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
      (synCin (synCxp (synCvv) (synCins4 (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
      (synCins2 (synCins4 (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
  have p0029 :=
    @gElin
      (synCop (synCsn (.cv z))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
      (synCxp (synCvv) (synCins4 (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c))
  have p0030 := @gSnex (.cv z)
  have p0031 :=
    @gOpelxp (synCsn (.cv z))
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
      (synCvv)
      (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
  have p0032 :=
    @gMpbiran
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCxp (synCvv)
          (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      (.classMem (synCsn (.cv z)) (synCvv))
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
      p0030 p0031
  have p0033 :=
    @gOqelins4 (synCsn (.cv y)) (synCsn (.cv x)) (.cv r) (.cv a)
      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))) (synC1c))
      p0002
  have p0034 :=
    @gElin
      (synCop (synCsn (.cv z))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
      (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synCins2 (synCins2 (synCsset)))
  have p0035 :=
    @gOqelins4 (synCsn (.cv z)) (synCsn (.cv y)) (synCsn (.cv x)) (.cv r)
      (synCsi3 (synCtxp (synC2nd) (synC1st))) p0001
  have p0036 :=
    @gOtsnelsi3 (.cv z) (.cv y) (.cv x) (synCtxp (synC2nd) (synC1st)) p0024 p0015
      p0007
  have p0037 := @gOteltxp (.cv z) (.cv y) (.cv x) (synC2nd) (synC1st)
  have p0038 :=
    @gAncom (.classMem (synCop (.cv z) (.cv y)) (synC2nd))
      (.classMem (synCop (.cv z) (.cv x)) (synC1st))
  have p0039 := (Nominal.biimpRefl (synWbr (.cv z) (synC1st) (.cv x)))
  have p0040 := (Nominal.biimpRefl (synWbr (.cv z) (synC2nd) (.cv y)))
  have p0041 :=
    @gAnbi12i (synWbr (.cv z) (synC1st) (.cv x))
      (.classMem (synCop (.cv z) (.cv x)) (synC1st))
      (synWbr (.cv z) (synC2nd) (.cv y))
      (.classMem (synCop (.cv z) (.cv y)) (synC2nd)) p0039 p0040
  have p0042 :=
    @gBitr4i
      (synWa (.classMem (synCop (.cv z) (.cv y)) (synC2nd))
        (.classMem (synCop (.cv z) (.cv x)) (synC1st)))
      (synWa (.classMem (synCop (.cv z) (.cv x)) (synC1st))
        (.classMem (synCop (.cv z) (.cv y)) (synC2nd)))
      (synWa (synWbr (.cv z) (synC1st) (.cv x)) (synWbr (.cv z) (synC2nd) (.cv y)))
      p0038 p0041
  have p0043 := @gOp1st2nd (.cv x) (.cv y) (.cv z) p0007 p0015
  have p0044 :=
    @gN3bitri
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (synWa (.classMem (synCop (.cv z) (.cv y)) (synC2nd))
        (.classMem (synCop (.cv z) (.cv x)) (synC1st)))
      (synWa (synWbr (.cv z) (synC1st) (.cv x)) (synWbr (.cv z) (synC2nd) (.cv y)))
      (.classEq (.cv z) (synCop (.cv x) (.cv y))) p0037 p0042 p0043
  have p0045 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv z))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (.classEq (.cv z) (synCop (.cv x) (.cv y))) p0035 p0036 p0044
  have p0046 :=
    @gOtelins2 (synCsn (.cv z)) (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))
      (synCins2 (synCsset)) p0020
  have p0047 := @gOtelins2 (synCsn (.cv z)) (synCsn (.cv x)) (.cv r) (synCsset) p0012
  have p0048 := @gOpelssetsn (.cv z) (.cv r) p0024 p0001
  have p0049_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv r)) (synCsset)) (.objMem z r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gN3bitri
      (.classMem (synCop (synCsn (.cv z))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv r)) (synCsset)) (.objMem z r) p0046
      p0047 p0049_e02_recanon
  have p0050 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv z))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classEq (.cv z) (synCop (.cv x) (.cv y)))
      (.classMem (synCop (synCsn (.cv z))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem z r) p0045 p0049
  have p0051 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))) (.classMem
          (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.objMem z r)) p0034 p0050
  have p0052 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.objMem z r)) z p0051
  have p0053 :=
    @gElima1c z (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synCins2 (synCins2 (synCsset))))
      dv_cache_0015 dv_cache_0016
  have p0054 := (Nominal.biimpRefl (synWbr (.cv x) (.cv r) (.cv y)))
  have p0055 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV z
      (synCop (.cv x) (.cv y)) (.cv r) dv_cache_0017 dv_cache_0018)
  have p0056_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv x) (.cv y)) (.cv r)) (synWex z
          (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.objMem z r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
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
    @gBitri (synWbr (.cv x) (.cv r) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (.cv r))
      (synWex z (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.objMem z r)))
      p0054 p0056_e01_recanon
  have p0057 :=
    @gN3bitr4i
      (synWex z (.classMem (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset))))))
      (synWex z (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.objMem z r)))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv y)) p0052 p0053 p0056
  have p0058 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCxp (synCvv)
          (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv y)) p0032 p0033 p0057
  have p0059 :=
    @gElin
      (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
      (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))
  have p0060 := @gOpex (synCsn (.cv x)) (synCop (.cv r) (.cv a)) p0012 p0003
  have p0061 :=
    @gOqelins4 (synCsn (.cv q)) (synCsn (.cv z)) (synCsn (.cv y))
      (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
      (synCsi3 (synCtxp (synC2nd) (synC1st))) p0060
  have p0062 := @gVex q
  have p0063 :=
    @gOtsnelsi3 (.cv q) (.cv z) (.cv y) (synCtxp (synC2nd) (synC1st)) p0062 p0024
      p0015
  have p0064 := @gOteltxp (.cv q) (.cv z) (.cv y) (synC2nd) (synC1st)
  have p0065 :=
    @gAncom (.classMem (synCop (.cv q) (.cv z)) (synC2nd))
      (.classMem (synCop (.cv q) (.cv y)) (synC1st))
  have p0066 := (Nominal.biimpRefl (synWbr (.cv q) (synC1st) (.cv y)))
  have p0067 := (Nominal.biimpRefl (synWbr (.cv q) (synC2nd) (.cv z)))
  have p0068 :=
    @gAnbi12i (synWbr (.cv q) (synC1st) (.cv y))
      (.classMem (synCop (.cv q) (.cv y)) (synC1st))
      (synWbr (.cv q) (synC2nd) (.cv z))
      (.classMem (synCop (.cv q) (.cv z)) (synC2nd)) p0066 p0067
  have p0069 :=
    @gBitr4i
      (synWa (.classMem (synCop (.cv q) (.cv z)) (synC2nd))
        (.classMem (synCop (.cv q) (.cv y)) (synC1st)))
      (synWa (.classMem (synCop (.cv q) (.cv y)) (synC1st))
        (.classMem (synCop (.cv q) (.cv z)) (synC2nd)))
      (synWa (synWbr (.cv q) (synC1st) (.cv y)) (synWbr (.cv q) (synC2nd) (.cv z)))
      p0065 p0068
  have p0070 := @gOp1st2nd (.cv y) (.cv z) (.cv q) p0015 p0024
  have p0071 :=
    @gN3bitri
      (.classMem (synCop (.cv q) (synCop (.cv z) (.cv y))) (synCtxp (synC2nd) (synC1st)))
      (synWa (.classMem (synCop (.cv q) (.cv z)) (synC2nd))
        (.classMem (synCop (.cv q) (.cv y)) (synC1st)))
      (synWa (synWbr (.cv q) (synC1st) (.cv y)) (synWbr (.cv q) (synC2nd) (.cv z)))
      (.classEq (.cv q) (synCop (.cv y) (.cv z))) p0064 p0069 p0070
  have p0072 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z)) (synCsn (.cv y))))
        (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (.classMem (synCop (.cv q) (synCop (.cv z) (.cv y))) (synCtxp (synC2nd) (synC1st)))
      (.classEq (.cv q) (synCop (.cv y) (.cv z))) p0061 p0063 p0071
  have p0073 :=
    @gOtelins2 (synCsn (.cv q)) (synCsn (.cv z))
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
      (synCins2 (synCins2 (synCins3 (synCsset)))) p0030
  have p0074 :=
    @gOtelins2 (synCsn (.cv q)) (synCsn (.cv y))
      (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
      (synCins2 (synCins3 (synCsset))) p0020
  have p0075 :=
    @gOtelins2 (synCsn (.cv q)) (synCsn (.cv x)) (synCop (.cv r) (.cv a))
      (synCins3 (synCsset)) p0012
  have p0076 := @gOtelins3 (synCsn (.cv q)) (.cv r) (.cv a) (synCsset) p0002
  have p0077 := @gOpelssetsn (.cv q) (.cv r) p0062 p0001
  have p0078_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv q)) (.cv r)) (synCsset)) (.objMem q r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv q)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins3 (synCsset))))
      (.classMem (synCop (synCsn (.cv q)) (synCop (.cv r) (.cv a))) (synCins3 (synCsset)))
      (.classMem (synCop (synCsn (.cv q)) (.cv r)) (synCsset)) (.objMem q r) p0075
      p0076 p0078_e02_recanon
  have p0079 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
        (synCins2 (synCins2 (synCins3 (synCsset)))))
      (.classMem
        (synCop (synCsn (.cv q)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins3 (synCsset))))
      (.objMem q r) p0073 p0074 p0078
  have p0080 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classEq (.cv q) (synCop (.cv y) (.cv z)))
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
      (.objMem q r) p0072 p0079
  have p0081 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
      (synWa (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
              (synCop (synCsn (.cv y))
                (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
          (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))) (.classMem
          (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
                (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
      (synWa (.classEq (.cv q) (synCop (.cv y) (.cv z))) (.objMem q r)) p0059 p0080
  have p0082 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
      (synWa (.classEq (.cv q) (synCop (.cv y) (.cv z))) (.objMem q r)) q p0081
  have p0083 :=
    @gElima1c q
      (synCop (synCsn (.cv z))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
      dv_cache_0019 dv_cache_0020
  have p0084 := (Nominal.biimpRefl (synWbr (.cv y) (.cv r) (.cv z)))
  have p0085 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV q
      (synCop (.cv y) (.cv z)) (.cv r) dv_cache_0021 dv_cache_0022)
  have p0086_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv y) (.cv z)) (.cv r)) (synWex q
          (synWa (.classEq (.cv q) (synCop (.cv y) (.cv z))) (.objMem q r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
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
    @gBitri (synWbr (.cv y) (.cv r) (.cv z))
      (.classMem (synCop (.cv y) (.cv z)) (.cv r))
      (synWex q (synWa (.classEq (.cv q) (synCop (.cv y) (.cv z))) (.objMem q r)))
      p0084 p0086_e01_recanon
  have p0087 :=
    @gN3bitr4i
      (synWex q (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv z))
              (synCop (synCsn (.cv y))
                (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))))
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))))
      (synWex q (synWa (.classEq (.cv q) (synCop (.cv y) (.cv z))) (.objMem q r)))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv z)) p0082 p0083 p0086
  have p0088 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCxp (synCvv)
          (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      (synWbr (.cv x) (.cv r) (.cv y))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv z)) p0058 p0087
  have p0089 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCin (synCxp (synCvv)
            (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCxp (synCvv)
            (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))) (.classMem
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c))))
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z))) p0029
      p0088
  have p0090 :=
    @gOtelins2 (synCsn (.cv z)) (synCsn (.cv y))
      (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
      (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      p0020
  have p0091 :=
    @gOqelins4 (synCsn (.cv z)) (synCsn (.cv x)) (.cv r) (.cv a)
      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))) (synC1c))
      p0002
  have p0092 :=
    @gElin
      (synCop (synCsn (.cv y))
        (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
      (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synCins2 (synCins2 (synCsset)))
  have p0093 :=
    @gOqelins4 (synCsn (.cv y)) (synCsn (.cv z)) (synCsn (.cv x)) (.cv r)
      (synCsi3 (synCtxp (synC2nd) (synC1st))) p0001
  have p0094 :=
    @gOtsnelsi3 (.cv y) (.cv z) (.cv x) (synCtxp (synC2nd) (synC1st)) p0015 p0024
      p0007
  have p0095 :=
    @gAncom (.classMem (synCop (.cv y) (.cv z)) (synC2nd))
      (.classMem (synCop (.cv y) (.cv x)) (synC1st))
  have p0096 := @gOteltxp (.cv y) (.cv z) (.cv x) (synC2nd) (synC1st)
  have p0097 := (Nominal.biimpRefl (synWbr (.cv y) (synC1st) (.cv x)))
  have p0098 := (Nominal.biimpRefl (synWbr (.cv y) (synC2nd) (.cv z)))
  have p0099 :=
    @gAnbi12i (synWbr (.cv y) (synC1st) (.cv x))
      (.classMem (synCop (.cv y) (.cv x)) (synC1st))
      (synWbr (.cv y) (synC2nd) (.cv z))
      (.classMem (synCop (.cv y) (.cv z)) (synC2nd)) p0097 p0098
  have p0100 :=
    @gN3bitr4i
      (synWa (.classMem (synCop (.cv y) (.cv z)) (synC2nd))
        (.classMem (synCop (.cv y) (.cv x)) (synC1st)))
      (synWa (.classMem (synCop (.cv y) (.cv x)) (synC1st))
        (.classMem (synCop (.cv y) (.cv z)) (synC2nd)))
      (.classMem (synCop (.cv y) (synCop (.cv z) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (synWa (synWbr (.cv y) (synC1st) (.cv x)) (synWbr (.cv y) (synC2nd) (.cv z)))
      p0095 p0096 p0099
  have p0101 := @gOp1st2nd (.cv x) (.cv z) (.cv y) p0007 p0024
  have p0102 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCsn (.cv x))))
        (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (.classMem (synCop (.cv y) (synCop (.cv z) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (synWa (synWbr (.cv y) (synC1st) (.cv x)) (synWbr (.cv y) (synC2nd) (.cv z)))
      (.classEq (.cv y) (synCop (.cv x) (.cv z))) p0094 p0100 p0101
  have p0103 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCsn (.cv x))))
        (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (.classEq (.cv y) (synCop (.cv x) (.cv z))) p0093 p0102
  have p0104 :=
    @gOtelins2 (synCsn (.cv y)) (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))
      (synCins2 (synCsset)) p0030
  have p0105 := @gOtelins2 (synCsn (.cv y)) (synCsn (.cv x)) (.cv r) (synCsset) p0012
  have p0106 := @gOpelssetsn (.cv y) (.cv r) p0015 p0001
  have p0107_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv y)) (.cv r)) (synCsset)) (.objMem y r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gN3bitri
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv y)) (.cv r)) (synCsset)) (.objMem y r) p0104
      p0105 p0107_e02_recanon
  have p0108 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classEq (.cv y) (synCop (.cv x) (.cv z)))
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem y r) p0103 p0107
  have p0109 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))) (.classMem
          (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv y) (synCop (.cv x) (.cv z))) (.objMem y r)) p0092 p0108
  have p0110 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv y) (synCop (.cv x) (.cv z))) (.objMem y r)) y p0109
  have p0111 :=
    @gElima1c y (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synCins2 (synCins2 (synCsset))))
      dv_cache_0023 dv_cache_0024
  have p0112 := (Nominal.biimpRefl (synWbr (.cv x) (.cv r) (.cv z)))
  have p0113 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y
      (synCop (.cv x) (.cv z)) (.cv r) dv_cache_0025 dv_cache_0026)
  have p0114_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv x) (.cv z)) (.cv r)) (synWex y
          (synWa (.classEq (.cv y) (synCop (.cv x) (.cv z))) (.objMem y r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
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
    @gBitri (synWbr (.cv x) (.cv r) (.cv z))
      (.classMem (synCop (.cv x) (.cv z)) (.cv r))
      (synWex y (synWa (.classEq (.cv y) (synCop (.cv x) (.cv z))) (.objMem y r)))
      p0112 p0114_e01_recanon
  have p0115 :=
    @gN3bitr4i
      (synWex y (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset))))))
      (synWex y (synWa (.classEq (.cv y) (synCop (.cv x) (.cv z))) (.objMem y r)))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv z)) p0110 p0111 p0114
  have p0116 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCins2 (synCins4
            (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      (.classMem
        (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv z)) p0090 p0091 p0115
  have p0117 :=
    @gNotbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCins2 (synCins4
            (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      (synWbr (.cv x) (.cv r) (.cv z)) p0116
  have p0118 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCin (synCxp (synCvv)
            (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c))))
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
      (.neg (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCins2 (synCins4
              (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      (.neg (synWbr (.cv x) (.cv r) (.cv z))) p0089 p0117
  have p0119 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCdif (synCin
            (synCxp (synCvv) (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
          (synCins2 (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      (synWa (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCin
            (synCxp (synCvv) (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))) (.neg
          (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
                (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCins2 (synCins4
                (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))))))
      (synWa (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
        (.neg (synWbr (.cv x) (.cv r) (.cv z))))
      p0028 p0118
  have p0120 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
        (synCins2 (synCins2 (synCins2 (synCsset)))))
      (.objMem z a)
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))) (synCdif (synCin
            (synCxp (synCvv) (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
          (synCins2 (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      (synWa (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
        (.neg (synWbr (.cv x) (.cv r) (.cv z))))
      p0027 p0119
  have p0121 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
        (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
              (synCxp (synCvv) (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
            (synCins2 (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))))))
      (synWa (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
          (synCins2 (synCins2 (synCins2 (synCsset))))) (.classMem (synCop (synCsn (.cv z))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
          (synCdif (synCin (synCxp (synCvv) (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
            (synCins2 (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))))))
      (synWa (.objMem z a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
          (.neg (synWbr (.cv x) (.cv r) (.cv z)))))
      p0019 p0120
  have p0122 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
        (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
              (synCxp (synCvv) (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
            (synCins2 (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))))))
      (synWa (.objMem z a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
          (.neg (synWbr (.cv x) (.cv r) (.cv z)))))
      z p0121
  have p0123 :=
    (Nominal.biimpRefl (synWrex z (.cv a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
          (.neg (synWbr (.cv x) (.cv r) (.cv z))))))
  have p0124 :=
    @gRexanali
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
      (synWbr (.cv x) (.cv r) (.cv z)) z (.cv a)
  have p0125_e00_recanon :
    Nominal.NPrf
      (synWb (synWrex z (.cv a) (synWa
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (.neg (synWbr (.cv x) (.cv r) (.cv z))))) (synWex z (synWa (.objMem z a) (synWa
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (.neg (synWbr (.cv x) (.cv r) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
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
    @gBitr3i
      (synWex z (synWa (.objMem z a) (synWa
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (.neg (synWbr (.cv x) (.cv r) (.cv z))))))
      (synWrex z (.cv a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
          (.neg (synWbr (.cv x) (.cv r) (.cv z)))))
      (.neg (synWral z (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (synWbr (.cv x) (.cv r) (.cv z)))))
      p0125_e00_recanon p0124
  have p0126 :=
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                (synCxp (synCvv) (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
              (synCins2 (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
      (synWex z (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))))
          (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                (synCxp (synCvv) (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
              (synCins2 (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))))))))
      (synWex z (synWa (.objMem z a) (synWa
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (.neg (synWbr (.cv x) (.cv r) (.cv z))))))
      (.neg (synWral z (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (synWbr (.cv x) (.cv r) (.cv z)))))
      p0018 p0122 p0125
  have p0127 :=
    @gAnbi12i
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem y a)
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                (synCxp (synCvv) (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
              (synCins2 (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
      (.neg (synWral z (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (synWbr (.cv x) (.cv r) (.cv z)))))
      p0017 p0126
  have p0128 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCima
            (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                  (synCxp (synCvv) (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                (synCins2 (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
          (synCins2 (synCins2 (synCsset)))) (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))) (synCima
            (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                  (synCxp (synCvv) (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                (synCins2 (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c))))
      (synWa (.objMem y a) (.neg (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      p0011 p0127
  have p0129 :=
    @gExbii
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCima
            (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                  (synCxp (synCvv) (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                (synCins2 (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c))))
      (synWa (.objMem y a) (.neg (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      y p0128
  have p0130 :=
    (Nominal.biimpRefl (synWrex y (.cv a) (.neg (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z)))))))
  have p0131 :=
    @gRexnal
      (synWral z (.cv a)
        (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
          (synWbr (.cv x) (.cv r) (.cv z))))
      y (.cv a)
  have p0132_e00_recanon :
    Nominal.NPrf
      (synWb (synWrex y (.cv a) (.neg (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))) (synWex y (synWa (.objMem y a) (.neg
              (synWral z (.cv a) (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y))
                    (synWbr (.cv y) (.cv r) (.cv z)))
                  (synWbr (.cv x) (.cv r) (.cv z)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWral, synWbr, synCop, synCun,
          synCnin, synWnan, synCcompl]
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
    @gBitr3i
      (synWex y (synWa (.objMem y a) (.neg (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      (synWrex y (.cv a) (.neg (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      p0132_e00_recanon p0131
  have p0133 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCima
              (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                    (synCxp (synCvv) (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                  (synCins2 (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
          (synC1c)))
      (synWex y (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
          (synCin (synCins2 (synCins2 (synCsset))) (synCima
              (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                    (synCxp (synCvv) (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                  (synCins2 (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))))
      (synWex y (synWa (.objMem y a) (.neg (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      p0010 p0129 p0132
  have p0134 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.objMem x a)
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCima
              (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                    (synCxp (synCvv) (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                  (synCins2 (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
          (synC1c)))
      (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      p0009 p0133
  have p0135 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
        (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
              (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif
                    (synCin (synCxp (synCvv) (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                        (synC1c))) (synCins2 (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
            (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
          (synCins2 (synCsset)))
        (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCima
                (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                      (synCxp (synCvv) (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                        (synC1c))) (synCins2 (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
            (synC1c))))
      (synWa (.objMem x a) (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      p0005 p0134
  have p0136 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
        (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
              (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif
                    (synCin (synCxp (synCvv) (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                        (synC1c))) (synCins2 (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
            (synC1c))))
      (synWa (.objMem x a) (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      x p0135
  have p0137 :=
    @gElima1c x (synCop (.cv r) (.cv a))
      (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
            (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif
                  (synCin (synCxp (synCvv) (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                  (synCins2 (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
          (synC1c)))
      dv_cache_0027 dv_cache_0028
  have p0138 :=
    (Nominal.biimpRefl (synWrex x (.cv a) (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z))))))))
  have p0139_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex x (.cv a) (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
                  (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                  (synWbr (.cv x) (.cv r) (.cv z))))))) (synWex x (synWa (.objMem x a) (.neg
              (synWral y (.cv a) (synWral z (.cv a) (.imp
                    (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                    (synWbr (.cv x) (.cv r) (.cv z))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWral]
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
    @gN3bitr4i
      (synWex x (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
          (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCima
                  (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                        (synCxp (synCvv) (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                          (synC1c))) (synCins2 (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
              (synC1c)))))
      (synWex x (synWa (.objMem x a) (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
                  (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                  (synWbr (.cv x) (.cv r) (.cv z))))))))
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCima
                  (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                        (synCxp (synCvv) (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                          (synC1c))) (synCins2 (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
              (synC1c))) (synC1c)))
      (synWrex x (.cv a) (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      p0136 p0137 p0139_e02_recanon
  have p0140 :=
    @gRexnal
      (synWral y (.cv a) (synWral z (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (synWbr (.cv x) (.cv r) (.cv z)))))
      x (.cv a)
  have p0141 :=
    @gBitri
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCima
                  (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                        (synCxp (synCvv) (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                          (synC1c))) (synCins2 (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
              (synC1c))) (synC1c)))
      (synWrex x (.cv a) (.neg (synWral y (.cv a) (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      (.neg (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      p0139 p0140
  have p0142 :=
    @gCon2bii
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCima
                  (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                        (synCxp (synCvv) (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                          (synC1c))) (synCins2 (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
              (synC1c))) (synC1c)))
      (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      p0141
  have p0143 :=
    @gBitr4i
      (.classMem (synCop (.cv r) (.cv a)) (synCcompl (synCima
            (synCin (synCins2 (synCsset)) (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCima
                    (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                          (synCxp (synCvv) (synCins4 (synCima (synCin
                                  (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                            (synC1c))) (synCins2 (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
                (synC1c))) (synC1c))))
      (.neg (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset))
              (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCima
                    (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                          (synCxp (synCvv) (synCins4 (synCima (synCin
                                  (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                            (synC1c))) (synCins2 (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
                (synC1c))) (synC1c))))
      (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      p0004 p0142
  have p0144 :=
    @gOpabbi2i
      (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      r a
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCima
                  (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                        (synCxp (synCvv) (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                          (synC1c))) (synCins2 (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
              (synC1c))) (synC1c)))
      dv_cache_0029 dv_cache_0030 dv_cache_0031 p0143
  have p0145 :=
    @gEqtr4i (synCtrans)
      (synCopab r a (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
                (synWbr (.cv x) (.cv r) (.cv z)))))))
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCima
                  (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                        (synCxp (synCvv) (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                          (synC1c))) (synCins2 (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
              (synC1c))) (synC1c)))
      p0000 p0144
  have p0146 := @gSsetex
  have p0147 := @gIns2ex (synCsset) p0146
  have p0148 := @gIns2ex (synCins2 (synCsset)) p0147
  have p0149 := @gIns2ex (synCins2 (synCins2 (synCsset))) p0148
  have p0150 := @gVvex
  have p0151 := @gN2ndex
  have p0152 := @gN1stex
  have p0153 := @gTxpex (synC2nd) (synC1st) p0151 p0152
  have p0154 := @gSi3ex (synCtxp (synC2nd) (synC1st)) p0153
  have p0155 := @gIns4ex (synCsi3 (synCtxp (synC2nd) (synC1st))) p0154
  have p0156 :=
    @gInex (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synCins2 (synCins2 (synCsset))) p0155 p0148
  have p0157 := @gN1cex
  have p0158 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synCins2 (synCins2 (synCsset))))
      (synC1c) p0156 p0157
  have p0159 :=
    @gIns4ex
      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))) (synC1c))
      p0158
  have p0160 :=
    @gXpex (synCvv)
      (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      p0150 p0159
  have p0162 := @gIns3ex (synCsset) p0146
  have p0163 := @gIns2ex (synCins3 (synCsset)) p0162
  have p0164 := @gIns2ex (synCins2 (synCins3 (synCsset))) p0163
  have p0165 := @gIns2ex (synCins2 (synCins2 (synCins3 (synCsset)))) p0164
  have p0166 :=
    @gInex (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))) p0155 p0165
  have p0168 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
      (synC1c) p0166 p0157
  have p0169 :=
    @gInex
      (synCxp (synCvv) (synCins4 (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c))
      p0160 p0168
  have p0170 :=
    @gIns2ex
      (synCins4 (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      p0159
  have p0171 :=
    @gDifex
      (synCin (synCxp (synCvv) (synCins4 (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
      (synCins2 (synCins4 (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
      p0169 p0170
  have p0172 :=
    @gInex (synCins2 (synCins2 (synCins2 (synCsset))))
      (synCdif (synCin (synCxp (synCvv) (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
        (synCins2 (synCins4 (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      p0149 p0171
  have p0174 :=
    @gImaex
      (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
            (synCxp (synCvv) (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
          (synCins2 (synCins4 (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      (synC1c) p0172 p0157
  have p0175 :=
    @gInex (synCins2 (synCins2 (synCsset)))
      (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
              (synCxp (synCvv) (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
            (synCins2 (synCins4 (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c))
      p0148 p0174
  have p0177 :=
    @gImaex
      (synCin (synCins2 (synCins2 (synCsset))) (synCima
          (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                (synCxp (synCvv) (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
              (synCins2 (synCins4 (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
      (synC1c) p0175 p0157
  have p0178 :=
    @gInex (synCins2 (synCsset))
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCima
            (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                  (synCxp (synCvv) (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                (synCins2 (synCins4 (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
        (synC1c))
      p0147 p0177
  have p0180 :=
    @gImaex
      (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
            (synCima (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif
                  (synCin (synCxp (synCvv) (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) (synC1c)))
                  (synCins2 (synCins4 (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
          (synC1c)))
      (synC1c) p0178 p0157
  have p0181 :=
    @gComplex
      (synCima (synCin (synCins2 (synCsset)) (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCima
                (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                      (synCxp (synCvv) (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                        (synC1c))) (synCins2 (synCins4 (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
            (synC1c))) (synC1c))
      p0180
  have p0182 :=
    @gEqeltri (synCtrans)
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCima
                  (synCin (synCins2 (synCins2 (synCins2 (synCsset)))) (synCdif (synCin
                        (synCxp (synCvv) (synCins4 (synCima (synCin
                                (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                                (synCins2 (synCins2 (synCsset)))) (synC1c)))) (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
                          (synC1c))) (synCins2 (synCins4 (synCima (synCin
                              (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                              (synCins2 (synCins2 (synCsset)))) (synC1c)))))) (synC1c)))
              (synC1c))) (synC1c)))
      (synCvv) p0145 p0181
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

/-- Checked nominal proof certificate identified upstream as `g_refex`. -/
@[expose]
noncomputable def gRefex : Nominal.NPrf (.classMem (synCref) (synCvv)) :=
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
  have dv_cache_0004 : x ∉ ((synCop (.cv r) (.cv a))).fv :=
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
      ((synCtxp (synCcompl
            (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
              (synC1c))) (synCsset))).fv :=
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
  have dv_cache_0006 : p ∉ ((synCop (synCsn (.cv x)) (.cv r))).fv :=
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
    p ∉ ((synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))).fv :=
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
  have dv_cache_0008 : p ∉ ((synCop (.cv x) (.cv x))).fv :=
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
      ((synCcompl (synCima (synCtxp (synCcompl
                (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                  (synC1c))) (synCsset)) (synC1c)))).fv :=
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
      ((synCcompl (synCima (synCtxp (synCcompl
                (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                  (synC1c))) (synCsset)) (synC1c)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRef x r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gVex r
  have p0002 := @gVex a
  have p0003 := @gOpex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @gElcompl (synCop (.cv r) (.cv a))
      (synCima (synCtxp (synCcompl
            (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
              (synC1c))) (synCsset)) (synC1c))
      p0003
  have p0005 :=
    @gElima1c x (synCop (.cv r) (.cv a))
      (synCtxp (synCcompl
          (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c)))
        (synCsset))
      dv_cache_0004 dv_cache_0005
  have p0006 :=
    @gOteltxp (synCsn (.cv x)) (.cv r) (.cv a)
      (synCcompl (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
          (synC1c)))
      (synCsset)
  have p0007 := @gSnex (.cv x)
  have p0008 := @gOpex (synCsn (.cv x)) (.cv r) p0007 p0001
  have p0009 :=
    @gElcompl (synCop (synCsn (.cv x)) (.cv r))
      (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c))
      p0008
  have p0010 :=
    @gElima1c p (synCop (synCsn (.cv x)) (.cv r))
      (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) dv_cache_0006
      dv_cache_0007
  have p0011 :=
    @gOteltxp (synCsn (.cv p)) (synCsn (.cv x)) (.cv r)
      (synCsi (synCin (synC1st) (synC2nd))) (synCsset)
  have p0012 := @gVex p
  have p0013 := @gVex x
  have p0014 := @gOpsnelsi (.cv p) (.cv x) (synCin (synC1st) (synC2nd)) p0012 p0013
  have p0015 := @gElin (synCop (.cv p) (.cv x)) (synC1st) (synC2nd)
  have p0016 := (Nominal.biimpRefl (synWbr (.cv p) (synC1st) (.cv x)))
  have p0017 := (Nominal.biimpRefl (synWbr (.cv p) (synC2nd) (.cv x)))
  have p0018 :=
    @gAnbi12i (synWbr (.cv p) (synC1st) (.cv x))
      (.classMem (synCop (.cv p) (.cv x)) (synC1st))
      (synWbr (.cv p) (synC2nd) (.cv x))
      (.classMem (synCop (.cv p) (.cv x)) (synC2nd)) p0016 p0017
  have p0019 := @gOp1st2nd (.cv x) (.cv x) (.cv p) p0013 p0013
  have p0020 :=
    @gN3bitr2i (.classMem (synCop (.cv p) (.cv x)) (synCin (synC1st) (synC2nd)))
      (synWa (.classMem (synCop (.cv p) (.cv x)) (synC1st))
        (.classMem (synCop (.cv p) (.cv x)) (synC2nd)))
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv p) (synC2nd) (.cv x)))
      (.classEq (.cv p) (synCop (.cv x) (.cv x))) p0015 p0018 p0019
  have p0021 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv p)) (synCsn (.cv x)))
        (synCsi (synCin (synC1st) (synC2nd))))
      (.classMem (synCop (.cv p) (.cv x)) (synCin (synC1st) (synC2nd)))
      (.classEq (.cv p) (synCop (.cv x) (.cv x))) p0014 p0020
  have p0022 := @gOpelssetsn (.cv p) (.cv r) p0012 p0001
  have p0023_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv p)) (.cv r)) (synCsset)) (.objMem p r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv p)) (synCsn (.cv x)))
        (synCsi (synCin (synC1st) (synC2nd))))
      (.classEq (.cv p) (synCop (.cv x) (.cv x)))
      (.classMem (synCop (synCsn (.cv p)) (.cv r)) (synCsset)) (.objMem p r) p0021
      p0023_e01_recanon
  have p0024 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)))
      (synWa (.classMem (synCop (synCsn (.cv p)) (synCsn (.cv x)))
          (synCsi (synCin (synC1st) (synC2nd))))
        (.classMem (synCop (synCsn (.cv p)) (.cv r)) (synCsset)))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv x))) (.objMem p r)) p0011 p0023
  have p0025 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv x))) (.objMem p r)) p p0024
  have p0026 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (.cv r))
        (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c)))
      (synWex p (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv x)) (.cv r)))
          (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv x) (.cv x))) (.objMem p r)))
      p0010 p0025
  have p0027 := (Nominal.biimpRefl (synWbr (.cv x) (.cv r) (.cv x)))
  have p0028 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (synCop (.cv x) (.cv x)) (.cv r) dv_cache_0008 dv_cache_0009)
  have p0029_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv x) (.cv x)) (.cv r)) (synWex p
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv x))) (.objMem p r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
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
    @gBitri (synWbr (.cv x) (.cv r) (.cv x))
      (.classMem (synCop (.cv x) (.cv x)) (.cv r))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv x) (.cv x))) (.objMem p r)))
      p0027 p0029_e01_recanon
  have p0030 :=
    @gBitr4i
      (.classMem (synCop (synCsn (.cv x)) (.cv r))
        (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c)))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv x) (.cv x))) (.objMem p r)))
      (synWbr (.cv x) (.cv r) (.cv x)) p0026 p0029
  have p0031 :=
    @gXchbinx
      (.classMem (synCop (synCsn (.cv x)) (.cv r)) (synCcompl
          (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
            (synC1c))))
      (.classMem (synCop (synCsn (.cv x)) (.cv r))
        (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv x)) p0009 p0030
  have p0032 := @gOpelssetsn (.cv x) (.cv a) p0013 p0002
  have p0033_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gAnbi12ci
      (.classMem (synCop (synCsn (.cv x)) (.cv r)) (synCcompl
          (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
            (synC1c))))
      (.neg (synWbr (.cv x) (.cv r) (.cv x)))
      (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a) p0031
      p0033_e01_recanon
  have p0034 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCtxp (synCcompl
            (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
              (synC1c))) (synCsset)))
      (synWa (.classMem (synCop (synCsn (.cv x)) (.cv r)) (synCcompl
            (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
              (synC1c)))) (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)))
      (synWa (.objMem x a) (.neg (synWbr (.cv x) (.cv r) (.cv x)))) p0006 p0033
  have p0035 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCtxp (synCcompl
            (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
              (synC1c))) (synCsset)))
      (synWa (.objMem x a) (.neg (synWbr (.cv x) (.cv r) (.cv x)))) x p0034
  have p0036 :=
    @gBitri
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCtxp (synCcompl
              (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                (synC1c))) (synCsset)) (synC1c)))
      (synWex x (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCtxp
            (synCcompl
              (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                (synC1c))) (synCsset))))
      (synWex x (synWa (.objMem x a) (.neg (synWbr (.cv x) (.cv r) (.cv x))))) p0005
      p0035
  have p0037 :=
    (Nominal.biimpRefl (synWrex x (.cv a) (.neg (synWbr (.cv x) (.cv r) (.cv x)))))
  have p0038 := @gRexnal (synWbr (.cv x) (.cv r) (.cv x)) x (.cv a)
  have p0039_e01_recanon :
    Nominal.NPrf
      (synWb (synWrex x (.cv a) (.neg (synWbr (.cv x) (.cv r) (.cv x))))
        (synWex x (synWa (.objMem x a) (.neg (synWbr (.cv x) (.cv r) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWbr, synCop, synCun, synCnin,
          synWnan, synCcompl]
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
    @gN3bitr2i
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCtxp (synCcompl
              (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                (synC1c))) (synCsset)) (synC1c)))
      (synWex x (synWa (.objMem x a) (.neg (synWbr (.cv x) (.cv r) (.cv x)))))
      (synWrex x (.cv a) (.neg (synWbr (.cv x) (.cv r) (.cv x))))
      (.neg (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x)))) p0036
      p0039_e01_recanon p0038
  have p0040 :=
    @gCon2bii
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCtxp (synCcompl
              (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                (synC1c))) (synCsset)) (synC1c)))
      (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x))) p0039
  have p0041 :=
    @gBitr4i
      (.classMem (synCop (.cv r) (.cv a)) (synCcompl (synCima (synCtxp (synCcompl
                (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                  (synC1c))) (synCsset)) (synC1c))))
      (.neg (.classMem (synCop (.cv r) (.cv a)) (synCima (synCtxp (synCcompl
                (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                  (synC1c))) (synCsset)) (synC1c))))
      (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x))) p0004 p0040
  have p0042 :=
    @gOpabbi2i (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x))) r a
      (synCcompl (synCima (synCtxp (synCcompl
              (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                (synC1c))) (synCsset)) (synC1c)))
      dv_cache_0010 dv_cache_0011 dv_cache_0012 p0041
  have p0043 :=
    @gEqtr4i (synCref)
      (synCopab r a (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x))))
      (synCcompl (synCima (synCtxp (synCcompl
              (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                (synC1c))) (synCsset)) (synC1c)))
      p0000 p0042
  have p0044 := @gN1stex
  have p0045 := @gN2ndex
  have p0046 := @gInex (synC1st) (synC2nd) p0044 p0045
  have p0047 := @gSiex (synCin (synC1st) (synC2nd)) p0046
  have p0048 := @gSsetex
  have p0049 := @gTxpex (synCsi (synCin (synC1st) (synC2nd))) (synCsset) p0047 p0048
  have p0050 := @gN1cex
  have p0051 :=
    @gImaex (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c)
      p0049 p0050
  have p0052 :=
    @gComplex
      (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c))
      p0051
  have p0054 :=
    @gTxpex
      (synCcompl (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
          (synC1c)))
      (synCsset) p0052 p0048
  have p0056 :=
    @gImaex
      (synCtxp (synCcompl
          (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset)) (synC1c)))
        (synCsset))
      (synC1c) p0054 p0050
  have p0057 :=
    @gComplex
      (synCima (synCtxp (synCcompl
            (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
              (synC1c))) (synCsset)) (synC1c))
      p0056
  have p0058 :=
    @gEqeltri (synCref)
      (synCcompl (synCima (synCtxp (synCcompl
              (synCima (synCtxp (synCsi (synCin (synC1st) (synC2nd))) (synCsset))
                (synC1c))) (synCsset)) (synC1c)))
      (synCvv) p0043 p0057
  exact p0058


end NFChoice.DirectNominalPrf.WPPReplay

end
