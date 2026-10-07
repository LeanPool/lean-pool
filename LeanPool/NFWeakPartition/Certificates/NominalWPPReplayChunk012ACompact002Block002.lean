/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012ACompact002Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012ACompact002Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_eqfnfvd`. -/
@[expose]
noncomputable def gEqfnfvd (ph : Wff) (x : Var) (A : Class) (F : Class) (G : Class)
    (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_eqfnfvd_1 : Nominal.NPrf (.imp ph (synWfn F A)))
    (hyp_eqfnfvd_2 : Nominal.NPrf (.imp ph (synWfn G A)))
    (hyp_eqfnfvd_3 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A))
          (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))) :
    Nominal.NPrf (.imp ph (.classEq F G)) :=
  by
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have p0000 :=
    @gRalrimiva ph (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))) x A dv_cache_0001
      hyp_eqfnfvd_3
  have p0001 := @gEqfnfv x A F G dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gSyl2anc ph (synWfn F A) (synWfn G A)
      (synWb (.classEq F G) (synWral x A (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))))
      hyp_eqfnfvd_1 hyp_eqfnfvd_2 p0001
  have p0003 :=
    @gMpbird ph (.classEq F G)
      (synWral x A (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_funfvop`. -/
@[expose]
noncomputable def gFunfvop (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem A (synCdm F)))
        (.classMem (synCop A (synCfv F A)) F)) :=
  by
  have p0000 := @gEqid (synCfv F A)
  have p0001 := @gFunopfvb A (synCfv F A) F
  have p0002 :=
    @gMpbii (synWa (synWfun F) (.classMem A (synCdm F)))
      (.classEq (synCfv F A) (synCfv F A)) (.classMem (synCop A (synCfv F A)) F) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_funfvbrb`. -/
@[expose]
noncomputable def gFunfvbrb (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun F) (synWb (.classMem A (synCdm F)) (synWbr A F (synCfv F A)))) :=
  by
  have p0000 := @gFunfvop A F
  have p0001 := (Nominal.biimpRefl (synWbr A F (synCfv F A)))
  have p0002 :=
    @gSylibr (synWa (synWfun F) (.classMem A (synCdm F)))
      (.classMem (synCop A (synCfv F A)) F) (synWbr A F (synCfv F A)) p0000 p0001
  have p0003 := @gBreldm A (synCfv F A) F
  have p0004 :=
    @gAdantl (synWbr A F (synCfv F A)) (.classMem A (synCdm F)) (synWfun F) p0003
  have p0005 :=
    @gImpbida (synWfun F) (.classMem A (synCdm F)) (synWbr A F (synCfv F A)) p0002
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fvimacnvi`. -/
@[expose]
noncomputable def gFvimacnvi (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem A (synCima (synCcnv F) B)))
        (.classMem (synCfv F A) B)) :=
  by
  have p0000 := @gSnssi A (synCima (synCcnv F) B)
  have p0001 := @gFunimass2 (synCsn A) B F
  have p0002 :=
    @gSylan2 (.classMem A (synCima (synCcnv F) B)) (synWfun F)
      (synWss (synCsn A) (synCima (synCcnv F) B)) (synWss (synCima F (synCsn A)) B)
      p0000 p0001
  have p0003 := @gFvex A F
  have p0004 := @gSnss (synCfv F A) B p0003
  have p0005 := @gCnvimass F B
  have p0006 := @gSseli (synCima (synCcnv F) B) (synCdm F) A p0005
  have p0007 := @gFunfn F
  have p0008 := @gFnsnfv (synCdm F) A F
  have p0009 :=
    @gSylanb (synWfun F) (synWfn F (synCdm F)) (.classMem A (synCdm F))
      (.classEq (synCsn (synCfv F A)) (synCima F (synCsn A))) p0007 p0008
  have p0010 :=
    @gSylan2 (.classMem A (synCima (synCcnv F) B)) (synWfun F)
      (.classMem A (synCdm F))
      (.classEq (synCsn (synCfv F A)) (synCima F (synCsn A))) p0006 p0009
  have p0011 :=
    @gSseq1d (synWa (synWfun F) (.classMem A (synCima (synCcnv F) B)))
      (synCsn (synCfv F A)) (synCima F (synCsn A)) B p0010
  have p0012 :=
    @gSyl5bb (.classMem (synCfv F A) B) (synWss (synCsn (synCfv F A)) B)
      (synWa (synWfun F) (.classMem A (synCima (synCcnv F) B)))
      (synWss (synCima F (synCsn A)) B) p0004 p0011
  have p0013 :=
    @gMpbird (synWa (synWfun F) (.classMem A (synCima (synCcnv F) B)))
      (.classMem (synCfv F A) B) (synWss (synCima F (synCsn A)) B) p0002 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_fvimacnv`. -/
@[expose]
noncomputable def gFvimacnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem A (synCdm F)))
        (synWb (.classMem (synCfv F A) B) (.classMem A (synCima (synCcnv F) B)))) :=
  by
  have p0000 := @gFunfvop A F
  have p0001 := @gOpelcnv (synCfv F A) A F
  have p0002 :=
    @gSylibr (synWa (synWfun F) (.classMem A (synCdm F)))
      (.classMem (synCop A (synCfv F A)) F)
      (.classMem (synCop (synCfv F A) A) (synCcnv F)) p0000 p0001
  have p0003 := @gElimasn (synCcnv F) (synCfv F A) A
  have p0004 :=
    @gSylibr (synWa (synWfun F) (.classMem A (synCdm F)))
      (.classMem (synCop (synCfv F A) A) (synCcnv F))
      (.classMem A (synCima (synCcnv F) (synCsn (synCfv F A)))) p0002 p0003
  have p0005 := @gFvex A F
  have p0006 := @gSnss (synCfv F A) B p0005
  have p0007 := @gImass2 (synCsn (synCfv F A)) B (synCcnv F)
  have p0008 :=
    @gSylbi (.classMem (synCfv F A) B) (synWss (synCsn (synCfv F A)) B)
      (synWss (synCima (synCcnv F) (synCsn (synCfv F A))) (synCima (synCcnv F) B))
      p0006 p0007
  have p0009 :=
    @gSseld (.classMem (synCfv F A) B) (synCima (synCcnv F) (synCsn (synCfv F A)))
      (synCima (synCcnv F) B) A p0008
  have p0010 :=
    @gSyl5com (synWa (synWfun F) (.classMem A (synCdm F)))
      (.classMem A (synCima (synCcnv F) (synCsn (synCfv F A))))
      (.classMem (synCfv F A) B) (.classMem A (synCima (synCcnv F) B)) p0004 p0009
  have p0011 := @gFvimacnvi A B F
  have p0012 :=
    @gEx (synWfun F) (.classMem A (synCima (synCcnv F) B)) (.classMem (synCfv F A) B)
      p0011
  have p0013 :=
    @gAdantr (synWfun F)
      (.imp (.classMem A (synCima (synCcnv F) B)) (.classMem (synCfv F A) B))
      (.classMem A (synCdm F)) p0012
  have p0014 :=
    @gImpbid (synWa (synWfun F) (.classMem A (synCdm F))) (.classMem (synCfv F A) B)
      (.classMem A (synCima (synCcnv F) B)) p0010 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_funimass3`. -/
@[expose]
noncomputable def gFunimass3 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (synWss A (synCdm F)))
        (synWb (synWss (synCima F A) B) (synWss A (synCima (synCcnv F) B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
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
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synWa (synWfun F) (synWss A (synCdm F)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synCima (synCcnv F) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 := @gFunimass4 x A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gSsel A (synCdm F) (.cv x)
  have p0002 := @gFvimacnv (.cv x) B F
  have p0003 :=
    @gEx (synWfun F) (.classMem (.cv x) (synCdm F))
      (synWb (.classMem (synCfv F (.cv x)) B) (.classMem (.cv x) (synCima (synCcnv F) B)))
      p0002
  have p0004 :=
    @gSyl9r (synWss A (synCdm F)) (.classMem (.cv x) A) (.classMem (.cv x) (synCdm F))
      (synWfun F)
      (synWb (.classMem (synCfv F (.cv x)) B) (.classMem (.cv x) (synCima (synCcnv F) B)))
      p0001 p0003
  have p0005 :=
    @gImp31 (synWfun F) (synWss A (synCdm F)) (.classMem (.cv x) A)
      (synWb (.classMem (synCfv F (.cv x)) B) (.classMem (.cv x) (synCima (synCcnv F) B)))
      p0004
  have p0006 :=
    @gRalbidva (synWa (synWfun F) (synWss A (synCdm F)))
      (.classMem (synCfv F (.cv x)) B) (.classMem (.cv x) (synCima (synCcnv F) B)) x A
      dv_cache_0004 p0005
  have p0007 :=
    @gBitrd (synWa (synWfun F) (synWss A (synCdm F))) (synWss (synCima F A) B)
      (synWral x A (.classMem (synCfv F (.cv x)) B))
      (synWral x A (.classMem (.cv x) (synCima (synCcnv F) B))) p0000 p0006
  have p0008 := @gDfss3 x A (synCima (synCcnv F) B) dv_cache_0001 dv_cache_0005
  have p0009 :=
    @gSyl6bbr (synWa (synWfun F) (synWss A (synCdm F))) (synWss (synCima F A) B)
      (synWral x A (.classMem (.cv x) (synCima (synCcnv F) B)))
      (synWss A (synCima (synCcnv F) B)) p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_elpreima`. -/
@[expose]
noncomputable def gElpreima (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfn F A) (synWb (.classMem B (synCima (synCcnv F) C))
          (synWa (.classMem B A) (.classMem (synCfv F B) C)))) :=
  by
  have p0000 := @gCnvimass F C
  have p0001 := @gSseli (synCima (synCcnv F) C) (synCdm F) B p0000
  have p0002 := @gFndm A F
  have p0003 := @gEleq2d (synWfn F A) (synCdm F) A B p0002
  have p0004 :=
    @gSyl5ib (.classMem B (synCima (synCcnv F) C)) (.classMem B (synCdm F))
      (synWfn F A) (.classMem B A) p0001 p0003
  have p0005 := @gFnfun A F
  have p0006 := @gFvimacnvi B C F
  have p0007 :=
    @gSylan (synWfn F A) (synWfun F) (.classMem B (synCima (synCcnv F) C))
      (.classMem (synCfv F B) C) p0005 p0006
  have p0008 :=
    @gEx (synWfn F A) (.classMem B (synCima (synCcnv F) C))
      (.classMem (synCfv F B) C) p0007
  have p0009 :=
    @gJcad (synWfn F A) (.classMem B (synCima (synCcnv F) C)) (.classMem B A)
      (.classMem (synCfv F B) C) p0004 p0008
  have p0010 := @gFvimacnv B C F
  have p0011 :=
    @gFunfni (synWb (.classMem (synCfv F B) C) (.classMem B (synCima (synCcnv F) C)))
      A B F p0010
  have p0012 :=
    @gBiimpd (synWa (synWfn F A) (.classMem B A)) (.classMem (synCfv F B) C)
      (.classMem B (synCima (synCcnv F) C)) p0011
  have p0013 :=
    @gExpimpd (synWfn F A) (.classMem B A) (.classMem (synCfv F B) C)
      (.classMem B (synCima (synCcnv F) C)) p0012
  have p0014 :=
    @gImpbid (synWfn F A) (.classMem B (synCima (synCcnv F) C))
      (synWa (.classMem B A) (.classMem (synCfv F B) C)) p0009 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_fimacnv`. -/
@[expose]
noncomputable def gFimacnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (.classEq (synCima (synCcnv F) B) A)) :=
  by
  have p0000 := @gImassrn (synCcnv F) B
  have p0001 := (Nominal.classEqRefl (synCdm F))
  have p0002 := @gFdm A B F
  have p0003 := @gSsid A
  have p0004 := @gA1i (synWss A A) (synWf F A B) p0003
  have p0005 := @gEqsstrd (synWf F A B) (synCdm F) A A p0002 p0004
  have p0006 :=
    @gSyl5eqssr (synWf F A B) (synCrn (synCcnv F)) (synCdm F) A p0001 p0005
  have p0007 :=
    @gSyl5ss (synWf F A B) (synCima (synCcnv F) B) (synCrn (synCcnv F)) A p0000
      p0006
  have p0008 := @gImassrn F A
  have p0009 := @gFrn A B F
  have p0010 := @gSyl5ss (synWf F A B) (synCima F A) (synCrn F) B p0008 p0009
  have p0011 := @gFfun A B F
  have p0012 := @gSyl5sseqr (synWf F A B) A A (synCdm F) p0003 p0002
  have p0013 := @gFunimass3 A B F
  have p0014 :=
    @gSyl2anc (synWf F A B) (synWfun F) (synWss A (synCdm F))
      (synWb (synWss (synCima F A) B) (synWss A (synCima (synCcnv F) B))) p0011
      p0012 p0013
  have p0015 :=
    @gMpbid (synWf F A B) (synWss (synCima F A) B)
      (synWss A (synCima (synCcnv F) B)) p0010 p0014
  have p0016 := @gEqssd (synWf F A B) (synCima (synCcnv F) B) A p0007 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_fvelrn`. -/
@[expose]
noncomputable def gFvelrn (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem A (synCdm F)))
        (.classMem (synCfv F A) (synCrn F))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (synCop A (synCfv F A)) F)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_F, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCfv F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_F, or_false, not_false_eq_true])
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
  have p0000 := @gSimpr (synWfun F) (.classMem A (synCdm F))
  have p0001 := @gFunfvop A F
  have p0002 := @gOpeq1 (.cv x) A (synCfv F A)
  have p0003 :=
    @gEleq1d (.classEq (.cv x) A) (synCop (.cv x) (synCfv F A))
      (synCop A (synCfv F A)) F p0002
  have p0004 :=
    @gSpcegv (.classMem (synCop (.cv x) (synCfv F A)) F)
      (.classMem (synCop A (synCfv F A)) F) x A (synCdm F) dv_cache_0001 dv_cache_0002
      p0003
  have p0005 :=
    @gSylc (synWa (synWfun F) (.classMem A (synCdm F))) (.classMem A (synCdm F))
      (.classMem (synCop A (synCfv F A)) F)
      (synWex x (.classMem (synCop (.cv x) (synCfv F A)) F)) p0000 p0001 p0004
  have p0006 := @gElrn2 x (synCfv F A) F dv_cache_0003 dv_cache_0004
  have p0007 :=
    @gSylibr (synWa (synWfun F) (.classMem A (synCdm F)))
      (synWex x (.classMem (synCop (.cv x) (synCfv F A)) F))
      (.classMem (synCfv F A) (synCrn F)) p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_fnfvelrn`. -/
@[expose]
noncomputable def gFnfvelrn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem B A)) (.classMem (synCfv F B) (synCrn F))) :=
  by
  have p0000 := @gFvelrn B F
  have p0001 := @gFunfni (.classMem (synCfv F B) (synCrn F)) A B F p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ffvelrn`. -/
@[expose]
noncomputable def gFfvelrn (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf F A B) (.classMem C A)) (.classMem (synCfv F C) B)) :=
  by
  have p0000 := @gFfn A B F
  have p0001 := @gFnfvelrn A C F
  have p0002 :=
    @gSylan (synWf F A B) (synWfn F A) (.classMem C A)
      (.classMem (synCfv F C) (synCrn F)) p0000 p0001
  have p0003 := @gFrn A B F
  have p0004 := @gSseld (synWf F A B) (synCrn F) B (synCfv F C) p0003
  have p0005 :=
    @gAdantr (synWf F A B)
      (.imp (.classMem (synCfv F C) (synCrn F)) (.classMem (synCfv F C) B))
      (.classMem C A) p0004
  have p0006 :=
    @gMpd (synWa (synWf F A B) (.classMem C A)) (.classMem (synCfv F C) (synCrn F))
      (.classMem (synCfv F C) B) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ffvelrni`. -/
@[expose]
noncomputable def gFfvelrni (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_ffvrni_1 : Nominal.NPrf (synWf F A B)) :
    Nominal.NPrf (.imp (.classMem C A) (.classMem (synCfv F C) B)) :=
  by
  have p0000 := @gFfvelrn A B C F
  have p0001 :=
    @gMpan (synWf F A B) (.classMem C A) (.classMem (synCfv F C) B) hyp_ffvrni_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dffo3`. -/
@[expose]
noncomputable def gDffo3 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWfo F A B) (synWa (synWf F A B)
          (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))) :=
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
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0006 : x ∉ ((Wff.classMem (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synWf F A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union,
          dv_A_x, dv_B_x, dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWf F A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union,
          dv_A_y, dv_B_y, dv_F_y, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have p0000 := @gDffo2 A B F
  have p0001 := @gFfn A B F
  have p0002 :=
    @gFnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0003 :=
    @gEqeq1d (synWfn F A) (synCrn F)
      (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) B p0002
  have p0004 :=
    @gSyl (synWf F A B) (synWfn F A)
      (synWb (.classEq (synCrn F) B)
        (.classEq (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) B))
      p0001 p0003
  have p0005 :=
    @gSimpr (synWa (synWf F A B) (.classMem (.cv x) A))
      (.classEq (.cv y) (synCfv F (.cv x)))
  have p0006 := @gFfvelrn A B (.cv x) F
  have p0007 :=
    @gAdantr (synWa (synWf F A B) (.classMem (.cv x) A))
      (.classMem (synCfv F (.cv x)) B) (.classEq (.cv y) (synCfv F (.cv x))) p0006
  have p0008 :=
    @gEqeltrd
      (synWa (synWa (synWf F A B) (.classMem (.cv x) A))
        (.classEq (.cv y) (synCfv F (.cv x))))
      (.cv y) (synCfv F (.cv x)) B p0005 p0007
  have p0009 :=
    @gExp31 (synWf F A B) (.classMem (.cv x) A) (.classEq (.cv y) (synCfv F (.cv x)))
      (.classMem (.cv y) B) p0008
  have p0010 :=
    @gRexlimdv (synWf F A B) (.classEq (.cv y) (synCfv F (.cv x)))
      (.classMem (.cv y) B) x A dv_cache_0006 dv_cache_0007 p0009
  have p0011 :=
    @gBiantrurd (synWf F A B)
      (.imp (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) B) (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))))
      p0010
  have p0012 :=
    @gDfbi2 (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) (.classMem (.cv y) B)
  have p0013 :=
    @gSyl6rbbr (synWf F A B)
      (.imp (.classMem (.cv y) B) (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))))
      (synWa (.imp (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) (.classMem (.cv y) B))
        (.imp (.classMem (.cv y) B) (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))
      (synWb (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) (.classMem (.cv y) B))
      p0011 p0012
  have p0014 :=
    @gAlbidv (synWf F A B)
      (synWb (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) B) (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) y
      dv_cache_0008 p0013
  have p0015 :=
    @gEqabcb (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) y B dv_cache_0009
  have p0016 :=
    (Nominal.biimpRefl (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))
  have p0017 :=
    @gN3bitr4g (synWf F A B)
      (.all y (synWb (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))
          (.classMem (.cv y) B)))
      (.all y (.imp (.classMem (.cv y) B)
          (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))
      (.classEq (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) B)
      (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) p0014 p0015
      p0016
  have p0018 :=
    @gBitrd (synWf F A B) (.classEq (synCrn F) B)
      (.classEq (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) B)
      (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) p0004 p0017
  have p0019 :=
    @gPm532i (synWf F A B) (.classEq (synCrn F) B)
      (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) p0018
  have p0020 :=
    @gBitri (synWfo F A B) (synWa (synWf F A B) (.classEq (synCrn F) B))
      (synWa (synWf F A B)
        (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))
      p0000 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_foelrn`. -/
@[expose]
noncomputable def gFoelrn (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfo F A B) (.classMem C B))
        (synWrex x A (.classEq C (synCfv F (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
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
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
        simp only [dv_B_x, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ ((Wff.classEq (.cv y) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synWrex x A (.classEq C (synCfv F (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_C, fresh_y_ne_x, fresh_y_not_F,
          or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gDffo3 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @gSimprbi (synWfo F A B) (synWf F A B)
      (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) p0000
  have p0002 := @gEqeq1 (.cv y) C (synCfv F (.cv x))
  have p0003 :=
    @gRexbidv (.classEq (.cv y) C) (.classEq (.cv y) (synCfv F (.cv x)))
      (.classEq C (synCfv F (.cv x))) x A dv_cache_0008 p0002
  have p0004 :=
    @gRspccva (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))
      (synWrex x A (.classEq C (synCfv F (.cv x)))) y C B dv_cache_0009 dv_cache_0004
      dv_cache_0010 p0003
  have p0005 :=
    @gSylan (synWfo F A B)
      (synWral y B (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) (.classMem C B)
      (synWrex x A (.classEq C (synCfv F (.cv x)))) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ffnfv`. -/
@[expose]
noncomputable def gFfnfv (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (synWb (synWf F A B)
        (synWa (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((synWf F A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union,
          dv_A_x, dv_B_x, dv_F_x, or_false, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synCrn F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, fresh_y_not_F,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0008 :
    y ∉ ((synWa (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_ne_x, fresh_y_not_B,
          or_false, and_false, not_false_eq_true])
  have p0000 := @gFfn A B F
  have p0001 := @gFfvelrn A B (.cv x) F
  have p0002 :=
    @gRalrimiva (synWf F A B) (.classMem (synCfv F (.cv x)) B) x A dv_cache_0001 p0001
  have p0003 :=
    @gJca (synWf F A B) (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B))
      p0000 p0002
  have p0004 := @gSimpl (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B))
  have p0005 := @gFvelrnb x A (.cv y) F dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @gBiimpd (synWfn F A) (.classMem (.cv y) (synCrn F))
      (synWrex x A (.classEq (synCfv F (.cv x)) (.cv y))) p0005
  have p0007 := @gNfra1 (.classMem (synCfv F (.cv x)) B) x A
  have p0008 := @gNfv (.classMem (.cv y) B) x dv_cache_0005
  have p0009 := @gRsp (.classMem (synCfv F (.cv x)) B) x A
  have p0010 := @gEleq1 (synCfv F (.cv x)) (.cv y) B
  have p0011 :=
    @gBiimpcd (.classEq (synCfv F (.cv x)) (.cv y)) (.classMem (synCfv F (.cv x)) B)
      (.classMem (.cv y) B) p0010
  have p0012 :=
    @gSyl6 (synWral x A (.classMem (synCfv F (.cv x)) B)) (.classMem (.cv x) A)
      (.classMem (synCfv F (.cv x)) B)
      (.imp (.classEq (synCfv F (.cv x)) (.cv y)) (.classMem (.cv y) B)) p0009 p0011
  have p0013 :=
    @gRexlimd (synWral x A (.classMem (synCfv F (.cv x)) B))
      (.classEq (synCfv F (.cv x)) (.cv y)) (.classMem (.cv y) B) x A p0007 p0008 p0012
  have p0014 :=
    @gSylan9 (synWfn F A) (.classMem (.cv y) (synCrn F))
      (synWrex x A (.classEq (synCfv F (.cv x)) (.cv y)))
      (synWral x A (.classMem (synCfv F (.cv x)) B)) (.classMem (.cv y) B) p0006 p0013
  have p0015 :=
    @gSsrdv (synWa (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B))) y
      (synCrn F) B dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 := (Nominal.biimpRefl (synWf F A B))
  have p0017 :=
    @gSylanbrc (synWa (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B)))
      (synWfn F A) (synWss (synCrn F) B) (synWf F A B) p0004 p0015 p0016
  have p0018 :=
    @gImpbii (synWf F A B)
      (synWa (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B))) p0003 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_fnfvrnss`. -/
@[expose]
noncomputable def gFnfvrnss (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B)))
        (synWss (synCrn F) B)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have p0000 := @gFfnfv x A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gFrn A B F
  have p0002 :=
    @gSylbir (synWa (synWfn F A) (synWral x A (.classMem (synCfv F (.cv x)) B)))
      (synWf F A B) (synWss (synCrn F) B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fsn`. -/
@[expose]
noncomputable def gFsn (A : Class) (B : Class) (F : Class)
    (hyp_fsn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fsn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWf F (synCsn A) (synCsn B)) (.classEq F (synCsn (synCop A B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
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
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synCsn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCsn B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_B,
          not_false_eq_true])
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
  have dv_cache_0006 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classMem (synCop A B) F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCsn (synCop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCsn (synCop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((synWf F (synCsn A) (synCsn B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_F, or_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synWf F (synCsn A) (synCsn B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gOpelf (synCsn A) (synCsn B) (.cv x) (.cv y) F
  have p0001 := @gElsn x A dv_cache_0001
  have p0002 := @gElsn y B dv_cache_0002
  have p0003 :=
    @gAnbi12i (.classMem (.cv x) (synCsn A)) (.classEq (.cv x) A)
      (.classMem (.cv y) (synCsn B)) (.classEq (.cv y) B) p0001 p0002
  have p0004 :=
    @gSylib
      (synWa (synWf F (synCsn A) (synCsn B)) (.classMem (synCop (.cv x) (.cv y)) F))
      (synWa (.classMem (.cv x) (synCsn A)) (.classMem (.cv y) (synCsn B)))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0003
  have p0005 :=
    @gEx (synWf F (synCsn A) (synCsn B)) (.classMem (synCop (.cv x) (.cv y)) F)
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0004
  have p0006 := @gSnid A hyp_fsn_1
  have p0007 :=
    @gFeu y (synCsn A) (synCsn B) A F dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0008 :=
    @gMpan2 (synWf F (synCsn A) (synCsn B)) (.classMem A (synCsn A))
      (synWreu y (synCsn B) (.classMem (synCop A (.cv y)) F)) p0006 p0007
  have p0009 :=
    @gAnbi1i (.classMem (.cv y) (synCsn B)) (.classEq (.cv y) B)
      (.classMem (synCop A (.cv y)) F) p0002
  have p0010 := @gOpeq2 (.cv y) B A
  have p0011 := @gEleq1d (.classEq (.cv y) B) (synCop A (.cv y)) (synCop A B) F p0010
  have p0012 :=
    @gPm532i (.classEq (.cv y) B) (.classMem (synCop A (.cv y)) F)
      (.classMem (synCop A B) F) p0011
  have p0013 := @gAncom (.classMem (synCop A B) F) (.classEq (.cv y) B)
  have p0014 :=
    @gBitr4i (synWa (.classEq (.cv y) B) (.classMem (synCop A (.cv y)) F))
      (synWa (.classEq (.cv y) B) (.classMem (synCop A B) F))
      (synWa (.classMem (synCop A B) F) (.classEq (.cv y) B)) p0012 p0013
  have p0015 :=
    @gBitr2i (synWa (.classMem (.cv y) (synCsn B)) (.classMem (synCop A (.cv y)) F))
      (synWa (.classEq (.cv y) B) (.classMem (synCop A (.cv y)) F))
      (synWa (.classMem (synCop A B) F) (.classEq (.cv y) B)) p0009 p0014
  have p0016 :=
    @gEubii (synWa (.classMem (synCop A B) F) (.classEq (.cv y) B))
      (synWa (.classMem (.cv y) (synCsn B)) (.classMem (synCop A (.cv y)) F)) y p0015
  have p0017 := @gEueq1 y B dv_cache_0002 hyp_fsn_2
  have p0018 :=
    @gBiantru (synWeu y (.classEq (.cv y) B)) (.classMem (synCop A B) F) p0017
  have p0019 := @gEuanv (.classMem (synCop A B) F) (.classEq (.cv y) B) y dv_cache_0007
  have p0020 :=
    @gBitr4i (.classMem (synCop A B) F)
      (synWa (.classMem (synCop A B) F) (synWeu y (.classEq (.cv y) B)))
      (synWeu y (synWa (.classMem (synCop A B) F) (.classEq (.cv y) B))) p0018 p0019
  have p0021 :=
    (Nominal.biimpRefl (synWreu y (synCsn B) (.classMem (synCop A (.cv y)) F)))
  have p0022 :=
    @gN3bitr4i (synWeu y (synWa (.classMem (synCop A B) F) (.classEq (.cv y) B)))
      (synWeu y (synWa (.classMem (.cv y) (synCsn B)) (.classMem (synCop A (.cv y)) F)))
      (.classMem (synCop A B) F)
      (synWreu y (synCsn B) (.classMem (synCop A (.cv y)) F)) p0016 p0020 p0021
  have p0023 :=
    @gSylibr (synWf F (synCsn A) (synCsn B))
      (synWreu y (synCsn B) (.classMem (synCop A (.cv y)) F))
      (.classMem (synCop A B) F) p0008 p0022
  have p0024 := @gOpeq12 (.cv x) A (.cv y) B
  have p0025 :=
    @gEleq1d (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synCop (.cv x) (.cv y))
      (synCop A B) F p0024
  have p0026 :=
    @gSyl5ibrcom (synWf F (synCsn A) (synCsn B))
      (.classMem (synCop (.cv x) (.cv y)) F)
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classMem (synCop A B) F) p0023
      p0025
  have p0027 :=
    @gImpbid (synWf F (synCsn A) (synCsn B)) (.classMem (synCop (.cv x) (.cv y)) F)
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0005 p0026
  have p0028 := @gVex x
  have p0029 := @gVex y
  have p0030 := @gOpex (.cv x) (.cv y) p0028 p0029
  have p0031 := @gElsnc (synCop (.cv x) (.cv y)) (synCop A B) p0030
  have p0032 := @gOpth (.cv x) (.cv y) A B
  have p0033 :=
    @gBitr2i (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop A B)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0031 p0032
  have p0034 :=
    @gSyl6bb (synWf F (synCsn A) (synCsn B)) (.classMem (synCop (.cv x) (.cv y)) F)
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop A B))) p0027 p0033
  have p0035 :=
    @gEqrelrdv (synWf F (synCsn A) (synCsn B)) x y F (synCsn (synCop A B))
      dv_cache_0008 dv_cache_0006 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0034
  have p0036 := @gF1osn A B hyp_fsn_1 hyp_fsn_2
  have p0037 := @gF1oeq1 (synCsn A) (synCsn B) F (synCsn (synCop A B))
  have p0038 :=
    @gMpbiri (.classEq F (synCsn (synCop A B))) (synWf1o F (synCsn A) (synCsn B))
      (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B)) p0036 p0037
  have p0039 := @gF1of (synCsn A) (synCsn B) F
  have p0040 :=
    @gSyl (.classEq F (synCsn (synCop A B))) (synWf1o F (synCsn A) (synCsn B))
      (synWf F (synCsn A) (synCsn B)) p0038 p0039
  have p0041 :=
    @gImpbii (synWf F (synCsn A) (synCsn B)) (.classEq F (synCsn (synCop A B)))
      p0035 p0040
  exact p0041


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012ACompact002Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fsn2`. -/
@[expose]
noncomputable def gFsn2 (A : Class) (B : Class) (F : Class)
    (hyp_fsn2_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (synWf F (synCsn A) B) (synWa (.classMem (synCfv F A) B)
          (.classEq F (synCsn (synCop A (synCfv F A)))))) :=
  by
  have p0000 := @gSnid A hyp_fsn2_1
  have p0001 := @gFfvelrn (synCsn A) B A F
  have p0002 :=
    @gMpan2 (synWf F (synCsn A) B) (.classMem A (synCsn A))
      (.classMem (synCfv F A) B) p0000 p0001
  have p0003 := @gFfn (synCsn A) B F
  have p0004 := @gDffn3 (synCsn A) F
  have p0005 := @gBiimpi (synWfn F (synCsn A)) (synWf F (synCsn A) (synCrn F)) p0004
  have p0006 := @gImadmrn F
  have p0007 := @gFndm (synCsn A) F
  have p0008 := @gImaeq2d (synWfn F (synCsn A)) (synCdm F) (synCsn A) F p0007
  have p0009 :=
    @gSyl5eqr (synWfn F (synCsn A)) (synCrn F) (synCima F (synCdm F))
      (synCima F (synCsn A)) p0006 p0008
  have p0010 := @gFnsnfv (synCsn A) A F
  have p0011 :=
    @gMpan2 (synWfn F (synCsn A)) (.classMem A (synCsn A))
      (.classEq (synCsn (synCfv F A)) (synCima F (synCsn A))) p0000 p0010
  have p0012 :=
    @gEqtr4d (synWfn F (synCsn A)) (synCrn F) (synCima F (synCsn A))
      (synCsn (synCfv F A)) p0009 p0011
  have p0013 := @gFeq3 (synCrn F) (synCsn (synCfv F A)) (synCsn A) F
  have p0014 :=
    @gSyl (synWfn F (synCsn A)) (.classEq (synCrn F) (synCsn (synCfv F A)))
      (synWb (synWf F (synCsn A) (synCrn F)) (synWf F (synCsn A) (synCsn (synCfv F A))))
      p0012 p0013
  have p0015 :=
    @gMpbid (synWfn F (synCsn A)) (synWf F (synCsn A) (synCrn F))
      (synWf F (synCsn A) (synCsn (synCfv F A))) p0005 p0014
  have p0016 :=
    @gSyl (synWf F (synCsn A) B) (synWfn F (synCsn A))
      (synWf F (synCsn A) (synCsn (synCfv F A))) p0003 p0015
  have p0017 :=
    @gJca (synWf F (synCsn A) B) (.classMem (synCfv F A) B)
      (synWf F (synCsn A) (synCsn (synCfv F A))) p0002 p0016
  have p0018 := @gSnssi (synCfv F A) B
  have p0019 := @gFss (synCsn A) (synCsn (synCfv F A)) B F
  have p0020 :=
    @gAncoms (synWf F (synCsn A) (synCsn (synCfv F A)))
      (synWss (synCsn (synCfv F A)) B) (synWf F (synCsn A) B) p0019
  have p0021 :=
    @gSylan (.classMem (synCfv F A) B) (synWss (synCsn (synCfv F A)) B)
      (synWf F (synCsn A) (synCsn (synCfv F A))) (synWf F (synCsn A) B) p0018 p0020
  have p0022 :=
    @gImpbii (synWf F (synCsn A) B)
      (synWa (.classMem (synCfv F A) B) (synWf F (synCsn A) (synCsn (synCfv F A))))
      p0017 p0021
  have p0023 := @gFvex A F
  have p0024 := @gFsn A (synCfv F A) F hyp_fsn2_1 p0023
  have p0025 :=
    @gAnbi2i (synWf F (synCsn A) (synCsn (synCfv F A)))
      (.classEq F (synCsn (synCop A (synCfv F A)))) (.classMem (synCfv F A) B) p0024
  have p0026 :=
    @gBitri (synWf F (synCsn A) B)
      (synWa (.classMem (synCfv F A) B) (synWf F (synCsn A) (synCsn (synCfv F A))))
      (synWa (.classMem (synCfv F A) B) (.classEq F (synCsn (synCop A (synCfv F A)))))
      p0022 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_ressnop0`. -/
@[expose]
noncomputable def gRessnop0 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A C)) (.classEq (synCres (synCsn (synCop A B)) C) (synC0))) :=
  by
  have p0000 := @gOpelxp A B C (synCvv)
  have p0001 :=
    @gSimplbi (.classMem (synCop A B) (synCxp C (synCvv))) (.classMem A C)
      (.classMem B (synCvv)) p0000
  have p0002 :=
    @gCon3i (.classMem (synCop A B) (synCxp C (synCvv))) (.classMem A C) p0001
  have p0003 := (Nominal.classEqRefl (synCres (synCsn (synCop A B)) C))
  have p0004 := @gIncom (synCsn (synCop A B)) (synCxp C (synCvv))
  have p0005 :=
    @gEqtri (synCres (synCsn (synCop A B)) C)
      (synCin (synCsn (synCop A B)) (synCxp C (synCvv)))
      (synCin (synCxp C (synCvv)) (synCsn (synCop A B))) p0003 p0004
  have p0006 := @gDisjsn (synCxp C (synCvv)) (synCop A B)
  have p0007 :=
    @gBiimpri (.classEq (synCin (synCxp C (synCvv)) (synCsn (synCop A B))) (synC0))
      (.neg (.classMem (synCop A B) (synCxp C (synCvv)))) p0006
  have p0008 :=
    @gSyl5eq (.neg (.classMem (synCop A B) (synCxp C (synCvv))))
      (synCres (synCsn (synCop A B)) C)
      (synCin (synCxp C (synCvv)) (synCsn (synCop A B))) (synC0) p0005 p0007
  have p0009 :=
    @gSyl (.neg (.classMem A C)) (.neg (.classMem (synCop A B) (synCxp C (synCvv))))
      (.classEq (synCres (synCsn (synCop A B)) C) (synC0)) p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_fvconst`. -/
@[expose]
noncomputable def gFvconst (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf F A (synCsn B)) (.classMem C A)) (.classEq (synCfv F C) B)) :=
  by
  have p0000 := @gFfvelrn A (synCsn B) C F
  have p0001 := @gElsni (synCfv F C) B
  have p0002 :=
    @gSyl (synWa (synWf F A (synCsn B)) (.classMem C A))
      (.classMem (synCfv F C) (synCsn B)) (.classEq (synCfv F C) B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fvi`. -/
@[expose]
noncomputable def gFvi (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (synCfv (synCid) A) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (synCfv (synCid) A) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gFveq2 (.cv x) A (synCid)
  have p0001 := @gId (.classEq (.cv x) A)
  have p0002 :=
    @gEqeq12d (.classEq (.cv x) A) (synCfv (synCid) (.cv x)) (synCfv (synCid) A)
      (.cv x) A p0000 p0001
  have p0003 := @gFuni
  have p0004 := @gDmi
  have p0005 := (Nominal.biimpRefl (synWfn (synCid) (synCvv)))
  have p0006 :=
    @gMpbir2an (synWfn (synCid) (synCvv)) (synWfun (synCid))
      (.classEq (synCdm (synCid)) (synCvv)) p0003 p0004 p0005
  have p0007 := @gVex x
  have p0008 := @gEquid x
  have p0009 := @gIdeq (.cv x) (.cv x) p0007
  have p0010 := (Nominal.biimpRefl (synWbr (.cv x) (synCid) (.cv x)))
  have p0011_e00_recanon :
    Nominal.NPrf (synWb (synWbr (.cv x) (synCid) (.cv x)) (.objEq x x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0011 :=
    @gBitr3i (.objEq x x) (synWbr (.cv x) (synCid) (.cv x))
      (.classMem (synCop (.cv x) (.cv x)) (synCid)) p0011_e00_recanon p0010
  have p0012 :=
    @gMpbi (.objEq x x) (.classMem (synCop (.cv x) (.cv x)) (synCid)) p0008 p0011
  have p0013 := @gFnopfvb (synCvv) (.cv x) (.cv x) (synCid)
  have p0014 :=
    @gMpbiri (synWa (synWfn (synCid) (synCvv)) (.classMem (.cv x) (synCvv)))
      (.classEq (synCfv (synCid) (.cv x)) (.cv x))
      (.classMem (synCop (.cv x) (.cv x)) (synCid)) p0012 p0013
  have p0015 :=
    @gMp2an (synWfn (synCid) (synCvv)) (.classMem (.cv x) (synCvv))
      (.classEq (synCfv (synCid) (.cv x)) (.cv x)) p0006 p0007 p0014
  have p0016 :=
    @gVtoclg (.classEq (synCfv (synCid) (.cv x)) (.cv x))
      (.classEq (synCfv (synCid) A) A) x A V dv_cache_0001 dv_cache_0002 p0002 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_fvresi`. -/
@[expose]
noncomputable def gFvresi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (.classEq (synCfv (synCres (synCid) A) B) B)) :=
  by
  have p0000 := @gFvres B A (synCid)
  have p0001 := @gFvi B A
  have p0002 :=
    @gEqtrd (.classMem B A) (synCfv (synCres (synCid) A) B) (synCfv (synCid) B) B
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fvunsn`. -/
@[expose]
noncomputable def gFvunsn (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWne B D)
        (.classEq (synCfv (synCun A (synCsn (synCop B C))) D) (synCfv A D))) :=
  by
  have p0000 := @gResundir A (synCsn (synCop B C)) (synCsn D)
  have p0001 := @gElsni B D
  have p0002 := @gNecon3ai (.classMem B (synCsn D)) B D p0001
  have p0003 := @gRessnop0 B C (synCsn D)
  have p0004 :=
    @gSyl (synWne B D) (.neg (.classMem B (synCsn D)))
      (.classEq (synCres (synCsn (synCop B C)) (synCsn D)) (synC0)) p0002 p0003
  have p0005 :=
    @gUneq2d (synWne B D) (synCres (synCsn (synCop B C)) (synCsn D)) (synC0)
      (synCres A (synCsn D)) p0004
  have p0006 := @gUn0 (synCres A (synCsn D))
  have p0007 :=
    @gSyl6eq (synWne B D)
      (synCun (synCres A (synCsn D)) (synCres (synCsn (synCop B C)) (synCsn D)))
      (synCun (synCres A (synCsn D)) (synC0)) (synCres A (synCsn D)) p0005 p0006
  have p0008 :=
    @gSyl5eq (synWne B D) (synCres (synCun A (synCsn (synCop B C))) (synCsn D))
      (synCun (synCres A (synCsn D)) (synCres (synCsn (synCop B C)) (synCsn D)))
      (synCres A (synCsn D)) p0000 p0007
  have p0009 :=
    @gFveq1d (synWne B D) D (synCres (synCun A (synCsn (synCop B C))) (synCsn D))
      (synCres A (synCsn D)) p0008
  have p0010 := @gSnidg D (synCvv)
  have p0011 := @gFvres D (synCsn D) (synCun A (synCsn (synCop B C)))
  have p0012 :=
    @gSyl (.classMem D (synCvv)) (.classMem D (synCsn D))
      (.classEq (synCfv (synCres (synCun A (synCsn (synCop B C))) (synCsn D)) D)
        (synCfv (synCun A (synCsn (synCop B C))) D))
      p0010 p0011
  have p0013 := @gFvprc D (synCres (synCun A (synCsn (synCop B C))) (synCsn D))
  have p0014 := @gFvprc D (synCun A (synCsn (synCop B C)))
  have p0015 :=
    @gEqtr4d (.neg (.classMem D (synCvv)))
      (synCfv (synCres (synCun A (synCsn (synCop B C))) (synCsn D)) D) (synC0)
      (synCfv (synCun A (synCsn (synCop B C))) D) p0013 p0014
  have p0016 :=
    @gPm261i (.classMem D (synCvv))
      (.classEq (synCfv (synCres (synCun A (synCsn (synCop B C))) (synCsn D)) D)
        (synCfv (synCun A (synCsn (synCop B C))) D))
      p0012 p0015
  have p0017 := @gFvres D (synCsn D) A
  have p0018 :=
    @gSyl (.classMem D (synCvv)) (.classMem D (synCsn D))
      (.classEq (synCfv (synCres A (synCsn D)) D) (synCfv A D)) p0010 p0017
  have p0019 := @gFvprc D (synCres A (synCsn D))
  have p0020 := @gFvprc D A
  have p0021 :=
    @gEqtr4d (.neg (.classMem D (synCvv))) (synCfv (synCres A (synCsn D)) D) (synC0)
      (synCfv A D) p0019 p0020
  have p0022 :=
    @gPm261i (.classMem D (synCvv))
      (.classEq (synCfv (synCres A (synCsn D)) D) (synCfv A D)) p0018 p0021
  have p0023 :=
    @gN3eqtr3g (synWne B D)
      (synCfv (synCres (synCun A (synCsn (synCop B C))) (synCsn D)) D)
      (synCfv (synCres A (synCsn D)) D) (synCfv (synCun A (synCsn (synCop B C))) D)
      (synCfv A D) p0009 p0016 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_fvconst2g`. -/
@[expose]
noncomputable def gFvconst2g (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem B D) (.classMem C A))
        (.classEq (synCfv (synCxp A (synCsn B)) C) B)) :=
  by
  have p0000 := @gFconstg A B D
  have p0001 := @gFvconst A B C (synCxp A (synCsn B))
  have p0002 :=
    @gSylan (.classMem B D) (synWf (synCxp A (synCsn B)) A (synCsn B))
      (.classMem C A) (.classEq (synCfv (synCxp A (synCsn B)) C) B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fvconst2`. -/
@[expose]
noncomputable def gFvconst2 (A : Class) (B : Class) (C : Class)
    (hyp_fvconst2_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem C A) (.classEq (synCfv (synCxp A (synCsn B)) C) B)) :=
  by
  have p0000 := @gFvconst2g A B C (synCvv)
  have p0001 :=
    @gMpan (.classMem B (synCvv)) (.classMem C A)
      (.classEq (synCfv (synCxp A (synCsn B)) C) B) hyp_fvconst2_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_funfvima`. -/
@[expose]
noncomputable def gFunfvima (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem B (synCdm F)))
        (.imp (.classMem B A) (.classMem (synCfv F B) (synCima F A)))) :=
  by
  have p0000 := @gDmres F A
  have p0001 := @gEleq2i (synCdm (synCres F A)) (synCin A (synCdm F)) B p0000
  have p0002 := @gElin B A (synCdm F)
  have p0003 :=
    @gBitri (.classMem B (synCdm (synCres F A))) (.classMem B (synCin A (synCdm F)))
      (synWa (.classMem B A) (.classMem B (synCdm F))) p0001 p0002
  have p0004 := @gFunres A F
  have p0005 := @gFvelrn B (synCres F A)
  have p0006 :=
    @gSylan (synWfun F) (synWfun (synCres F A)) (.classMem B (synCdm (synCres F A)))
      (.classMem (synCfv (synCres F A) B) (synCrn (synCres F A))) p0004 p0005
  have p0007 := @gFvres B A F
  have p0008 :=
    @gEleq1d (.classMem B A) (synCfv (synCres F A) B) (synCfv F B)
      (synCrn (synCres F A)) p0007
  have p0009 := @gDfima3 F A
  have p0010 := @gEleq2i (synCima F A) (synCrn (synCres F A)) (synCfv F B) p0009
  have p0011 :=
    @gSyl6rbbr (.classMem B A)
      (.classMem (synCfv (synCres F A) B) (synCrn (synCres F A)))
      (.classMem (synCfv F B) (synCrn (synCres F A)))
      (.classMem (synCfv F B) (synCima F A)) p0008 p0010
  have p0012 :=
    @gSyl5ibrcom (synWa (synWfun F) (.classMem B (synCdm (synCres F A))))
      (.classMem (synCfv F B) (synCima F A)) (.classMem B A)
      (.classMem (synCfv (synCres F A) B) (synCrn (synCres F A))) p0006 p0011
  have p0013 :=
    @gEx (synWfun F) (.classMem B (synCdm (synCres F A)))
      (.imp (.classMem B A) (.classMem (synCfv F B) (synCima F A))) p0012
  have p0014 :=
    @gSyl5bir (synWa (.classMem B A) (.classMem B (synCdm F)))
      (.classMem B (synCdm (synCres F A))) (synWfun F)
      (.imp (.classMem B A) (.classMem (synCfv F B) (synCima F A))) p0003 p0013
  have p0015 :=
    @gExp3a (synWfun F) (.classMem B A) (.classMem B (synCdm F))
      (.imp (.classMem B A) (.classMem (synCfv F B) (synCima F A))) p0014
  have p0016 :=
    @gCom12 (synWfun F) (.classMem B A)
      (.imp (.classMem B (synCdm F))
        (.imp (.classMem B A) (.classMem (synCfv F B) (synCima F A))))
      p0015
  have p0017 :=
    @gImp3a (.classMem B A) (synWfun F) (.classMem B (synCdm F))
      (.imp (.classMem B A) (.classMem (synCfv F B) (synCima F A))) p0016
  have p0018 :=
    @gPm243b (synWa (synWfun F) (.classMem B (synCdm F))) (.classMem B A)
      (.classMem (synCfv F B) (synCima F A)) p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_fniunfv`. -/
@[expose]
noncomputable def gFniunfv (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWfn F A)
        (.classEq (synCiun x A (synCfv F (.cv x))) (synCuni (synCrn F)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((synCfv F (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, or_false, not_false_eq_true])
  have p0000 :=
    @gFnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @gUnieqd (synWfn F A) (synCrn F)
      (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) p0000
  have p0002 := @gFvex (.cv x) F
  have p0003 :=
    @gDfiun2 x y A (synCfv F (.cv x)) dv_cache_0002 dv_cache_0006 dv_cache_0005 p0002
  have p0004 :=
    @gSyl6reqr (synWfn F A) (synCuni (synCrn F))
      (synCuni (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))
      (synCiun x A (synCfv F (.cv x))) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_funiunfv`. -/
@[expose]
noncomputable def gFuniunfv (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWfun F)
        (.classEq (synCiun x A (synCfv F (.cv x))) (synCuni (synCima F A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ F.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_F : w ∉ F.fv := by
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
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCfv F (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_F, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCfv F (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCfv F (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_F, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0007 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0008 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((synCopab y z
          (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_y, dv_A_x, fresh_x_ne_z,
          dv_F_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((synWa (synWfun F) (.objMem w z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_w, fresh_y_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0012 : z ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_z_not_F,
          not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv w)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((synCima F A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          Finset.mem_union, fresh_z_not_F, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0016 : y ∉ (F).fv :=
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
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0017 :
    w ∉ ((synCuni (.cab z (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_z,
          fresh_w_ne_y, fresh_w_not_F, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((synCuni (synCima F A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
          fresh_w_not_F, fresh_w_not_A, or_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((synWfun F)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_w_not_F,
          not_false_eq_true])
  have p0000 := @gFveq2 (.cv y) (.cv x) F
  have p0001 :=
    @gEqid
      (synCopab y z (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))
  have p0002 := @gFvex (.cv x) F
  have p0003 :=
    @gFvopab4 y z (.cv x) (synCfv F (.cv y)) (synCfv F (.cv x)) A
      (synCopab y z (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0000 p0001 p0002
  have p0004 :=
    @gIuneq2i x A
      (synCfv (synCopab y z
          (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y))))) (.cv x))
      (synCfv F (.cv x)) p0003
  have p0005 := @gFvex (.cv y) F
  have p0006 :=
    @gFnopab2 y z A (synCfv F (.cv y))
      (synCopab y z (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))
      dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 p0005 p0001
  have p0007 :=
    @gFniunfv x A
      (synCopab y z (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))
      dv_cache_0009 dv_cache_0010
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gEqtr3i
      (synCiun x A (synCfv (synCopab y z
            (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y))))) (.cv x)))
      (synCiun x A (synCfv F (.cv x)))
      (synCuni (synCrn (synCopab y z
            (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))))
      p0004 p0008
  have p0010 := @gRnopab2 y z A (synCfv F (.cv y)) dv_cache_0008
  have p0011 :=
    @gUnieqi
      (synCrn (synCopab y z
          (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y))))))
      (.cab z (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))) p0010
  have p0012 := @gEqcom (.cv z) (synCfv F (.cv y))
  have p0013 :=
    @gIdd (synWa (synWfun F) (.objMem w z)) (.classEq (synCfv F (.cv y)) (.cv z))
  have p0014 := @gFunbrfv (.cv y) (.cv z) F
  have p0015 :=
    @gAdantr (synWfun F)
      (.imp (synWbr (.cv y) F (.cv z)) (.classEq (synCfv F (.cv y)) (.cv z)))
      (.objMem w z) p0014
  have p0016 := @gN0i (.cv z) (.cv w)
  have p0017 := @gNdmfv (.cv y) F
  have p0018 := @gEqeq1 (synCfv F (.cv y)) (.cv z) (synC0)
  have p0019 :=
    @gSyl5ib (.neg (.classMem (.cv y) (synCdm F)))
      (.classEq (synCfv F (.cv y)) (synC0)) (.classEq (synCfv F (.cv y)) (.cv z))
      (.classEq (.cv z) (synC0)) p0017 p0018
  have p0020 :=
    @gCon1d (.classEq (synCfv F (.cv y)) (.cv z)) (.classMem (.cv y) (synCdm F))
      (.classEq (.cv z) (synC0)) p0019
  have p0021_e00_recanon :
    Nominal.NPrf (.imp (.objMem w z) (.neg (.classEq (.cv z) (synC0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synC0 synCdif synCin synCcompl synCnin synWnan synWa synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0021 :=
    @gMpan9 (.objMem w z) (.neg (.classEq (.cv z) (synC0)))
      (.classEq (synCfv F (.cv y)) (.cv z)) (.classMem (.cv y) (synCdm F))
      p0021_e00_recanon p0020
  have p0022 := @gFunbrfvb (.cv y) (.cv z) F
  have p0023 :=
    @gSylan2 (synWa (.objMem w z) (.classEq (synCfv F (.cv y)) (.cv z))) (synWfun F)
      (.classMem (.cv y) (synCdm F))
      (synWb (.classEq (synCfv F (.cv y)) (.cv z)) (synWbr (.cv y) F (.cv z))) p0021
      p0022
  have p0024 :=
    @gExpr (synWfun F) (.objMem w z) (.classEq (synCfv F (.cv y)) (.cv z))
      (synWb (.classEq (synCfv F (.cv y)) (.cv z)) (synWbr (.cv y) F (.cv z))) p0023
  have p0025 :=
    @gPm521ndd (synWa (synWfun F) (.objMem w z))
      (.classEq (synCfv F (.cv y)) (.cv z)) (.classEq (synCfv F (.cv y)) (.cv z))
      (synWbr (.cv y) F (.cv z)) p0013 p0015 p0024
  have p0026 :=
    @gSyl5bb (.classEq (.cv z) (synCfv F (.cv y)))
      (.classEq (synCfv F (.cv y)) (.cv z)) (synWa (synWfun F) (.objMem w z))
      (synWbr (.cv y) F (.cv z)) p0012 p0025
  have p0027 :=
    @gRexbidv (synWa (synWfun F) (.objMem w z)) (.classEq (.cv z) (synCfv F (.cv y)))
      (synWbr (.cv y) F (.cv z)) y A dv_cache_0011 p0026
  have p0028 :=
    @gPm532da (synWfun F) (.objMem w z)
      (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))
      (synWrex y A (synWbr (.cv y) F (.cv z))) p0027
  have p0029 :=
    @gExbidv (synWfun F)
      (synWa (.objMem w z) (synWrex y A (.classEq (.cv z) (synCfv F (.cv y)))))
      (synWa (.objMem w z) (synWrex y A (synWbr (.cv y) F (.cv z)))) z dv_cache_0012
      p0028
  have p0030 :=
    @gEluniab (synWrex y A (.classEq (.cv z) (synCfv F (.cv y)))) z (.cv w)
      dv_cache_0013
  have p0031 := @gEluni z (.cv w) (synCima F A) dv_cache_0013 dv_cache_0014
  have p0032 := @gElima y (.cv z) F A dv_cache_0015 dv_cache_0016 dv_cache_0006
  have p0033 :=
    @gAnbi2i (.classMem (.cv z) (synCima F A))
      (synWrex y A (synWbr (.cv y) F (.cv z))) (.objMem w z) p0032
  have p0034 :=
    @gExbii (synWa (.objMem w z) (.classMem (.cv z) (synCima F A)))
      (synWa (.objMem w z) (synWrex y A (synWbr (.cv y) F (.cv z)))) z p0033
  have p0035_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv w) (synCuni (synCima F A)))
        (synWex z (synWa (.objMem w z) (.classMem (.cv z) (synCima F A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa synCima synWrex synWbr synCop synCun
          synCnin synWnan synCcompl
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
      p0031
  have p0035 :=
    @gBitri (.classMem (.cv w) (synCuni (synCima F A)))
      (synWex z (synWa (.objMem w z) (.classMem (.cv z) (synCima F A))))
      (synWex z (synWa (.objMem w z) (synWrex y A (synWbr (.cv y) F (.cv z)))))
      p0035_e00_recanon p0034
  have p0036_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv w)
          (synCuni (.cab z (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))))) (synWex z
          (synWa (.objMem w z) (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa synWrex synCfv synCio synWbr synCop
          synCun synCnin synWnan synCcompl
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]
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
      p0030
  have p0036 :=
    @gN3bitr4g (synWfun F)
      (synWex z (synWa (.objMem w z) (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))))
      (synWex z (synWa (.objMem w z) (synWrex y A (synWbr (.cv y) F (.cv z)))))
      (.classMem (.cv w)
        (synCuni (.cab z (synWrex y A (.classEq (.cv z) (synCfv F (.cv y)))))))
      (.classMem (.cv w) (synCuni (synCima F A))) p0029 p0036_e01_recanon p0035
  have p0037 :=
    @gEqrdv (synWfun F) w
      (synCuni (.cab z (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))))
      (synCuni (synCima F A)) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0036
  have p0038 :=
    @gSyl5eq (synWfun F)
      (synCuni (synCrn (synCopab y z
            (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))))
      (synCuni (.cab z (synWrex y A (.classEq (.cv z) (synCfv F (.cv y))))))
      (synCuni (synCima F A)) p0011 p0037
  have p0039 :=
    @gSyl5eq (synWfun F) (synCiun x A (synCfv F (.cv x)))
      (synCuni (synCrn (synCopab y z
            (synWa (.classMem (.cv y) A) (.classEq (.cv z) (synCfv F (.cv y)))))))
      (synCuni (synCima F A)) p0009 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_eluniima`. -/
@[expose]
noncomputable def gEluniima (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWfun F) (synWb (.classMem B (synCuni (synCima F A)))
          (synWrex x A (.classMem B (synCfv F (.cv x)))))) :=
  by
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have p0000 := @gEliun x B A (synCfv F (.cv x)) dv_cache_0001
  have p0001 := @gFuniunfv x A F dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gEleq2d (synWfun F) (synCiun x A (synCfv F (.cv x))) (synCuni (synCima F A)) B
      p0001
  have p0003 :=
    @gSyl5rbbr (synWrex x A (.classMem B (synCfv F (.cv x))))
      (.classMem B (synCiun x A (synCfv F (.cv x)))) (synWfun F)
      (.classMem B (synCuni (synCima F A))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elunirn`. -/
@[expose]
noncomputable def gElunirn (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWfun F) (synWb (.classMem A (synCuni (synCrn F)))
          (synWrex x (synCdm F) (.classMem A (synCfv F (.cv x)))))) :=
  by
  have dv_cache_0001 : x ∉ ((synCdm F)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, dv_F_x,
          not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have p0000 := @gImadmrn F
  have p0001 := @gUnieqi (synCima F (synCdm F)) (synCrn F) p0000
  have p0002 :=
    @gEleq2i (synCuni (synCima F (synCdm F))) (synCuni (synCrn F)) A p0001
  have p0003 := @gEluniima x (synCdm F) A F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gSyl5bbr (.classMem A (synCuni (synCrn F)))
      (.classMem A (synCuni (synCima F (synCdm F)))) (synWfun F)
      (synWrex x (synCdm F) (.classMem A (synCfv F (.cv x)))) p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012ACompact002Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dff13`. -/
@[expose]
noncomputable def gDff13 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWf1 F A B) (synWa (synWf F A B) (synWral x A (synWral y A
              (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0003 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0004 : z ∉ ((synWfn F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union,
          fresh_z_not_F, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synWa (.classMem (.cv x) A) (.classMem (.cv y) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.objEq x y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((synCfv F (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_F, or_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((synCfv F (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_F, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synWfn F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union,
          dv_F_x, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synWfn F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union,
          dv_F_y, dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((synWbr (.cv x) F (.cv z))).fv :=
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
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, dv_F_y, or_false,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ ((synWbr (.cv y) F (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, fresh_x_ne_z, dv_F_x, or_false,
          not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : y ∉ (A).fv :=
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
        simp only [dv_A_y, not_false_eq_true])
  have p0000 := @gDff12 x z A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gFfn A B F
  have p0002 := @gBreldm (.cv x) (.cv z) F
  have p0003 := @gFndm A F
  have p0004 := @gEleq2d (synWfn F A) (synCdm F) A (.cv x) p0003
  have p0005 :=
    @gSyl5ib (synWbr (.cv x) F (.cv z)) (.classMem (.cv x) (synCdm F)) (synWfn F A)
      (.classMem (.cv x) A) p0002 p0004
  have p0006 := @gBreldm (.cv y) (.cv z) F
  have p0007 := @gEleq2d (synWfn F A) (synCdm F) A (.cv y) p0003
  have p0008 :=
    @gSyl5ib (synWbr (.cv y) F (.cv z)) (.classMem (.cv y) (synCdm F)) (synWfn F A)
      (.classMem (.cv y) A) p0006 p0007
  have p0009 :=
    @gAnim12d (synWfn F A) (synWbr (.cv x) F (.cv z)) (.classMem (.cv x) A)
      (synWbr (.cv y) F (.cv z)) (.classMem (.cv y) A) p0005 p0008
  have p0010 :=
    @gPm471rd (synWfn F A)
      (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) p0009
  have p0011 := @gEqcom (.cv z) (synCfv F (.cv x))
  have p0012 := @gFnbrfvb A (.cv x) (.cv z) F
  have p0013 :=
    @gSyl5bb (.classEq (.cv z) (synCfv F (.cv x)))
      (.classEq (synCfv F (.cv x)) (.cv z)) (synWa (synWfn F A) (.classMem (.cv x) A))
      (synWbr (.cv x) F (.cv z)) p0011 p0012
  have p0014 := @gEqcom (.cv z) (synCfv F (.cv y))
  have p0015 := @gFnbrfvb A (.cv y) (.cv z) F
  have p0016 :=
    @gSyl5bb (.classEq (.cv z) (synCfv F (.cv y)))
      (.classEq (synCfv F (.cv y)) (.cv z)) (synWa (synWfn F A) (.classMem (.cv y) A))
      (synWbr (.cv y) F (.cv z)) p0014 p0015
  have p0017 :=
    @gBi2anan9 (synWa (synWfn F A) (.classMem (.cv x) A))
      (.classEq (.cv z) (synCfv F (.cv x))) (synWbr (.cv x) F (.cv z))
      (synWa (synWfn F A) (.classMem (.cv y) A)) (.classEq (.cv z) (synCfv F (.cv y)))
      (synWbr (.cv y) F (.cv z)) p0013 p0016
  have p0018 :=
    @gAnandis (synWfn F A) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (synWb (synWa (.classEq (.cv z) (synCfv F (.cv x)))
          (.classEq (.cv z) (synCfv F (.cv y))))
        (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z))))
      p0017
  have p0019 :=
    @gPm532da (synWfn F A) (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWa (.classEq (.cv z) (synCfv F (.cv x))) (.classEq (.cv z) (synCfv F (.cv y))))
      (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z))) p0018
  have p0020 :=
    @gBitr4d (synWfn F A)
      (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z))))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (synWa (.classEq (.cv z) (synCfv F (.cv x))) (.classEq (.cv z) (synCfv F (.cv y)))))
      p0010 p0019
  have p0021 :=
    @gImbi1d (synWfn F A)
      (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (synWa (.classEq (.cv z) (synCfv F (.cv x))) (.classEq (.cv z) (synCfv F (.cv y)))))
      (.objEq x y) p0020
  have p0022 :=
    @gImpexp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWa (.classEq (.cv z) (synCfv F (.cv x))) (.classEq (.cv z) (synCfv F (.cv y))))
      (.objEq x y)
  have p0023 :=
    @gSyl6bb (synWfn F A)
      (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z))) (.objEq x y))
      (.imp (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
          (synWa (.classEq (.cv z) (synCfv F (.cv x)))
            (.classEq (.cv z) (synCfv F (.cv y))))) (.objEq x y))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
          (synWa (.classEq (.cv z) (synCfv F (.cv x))) (.classEq (.cv z) (synCfv F (.cv y))))
          (.objEq x y)))
      p0021 p0022
  have p0024 :=
    @gAlbidv (synWfn F A)
      (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z))) (.objEq x y))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
          (synWa (.classEq (.cv z) (synCfv F (.cv x))) (.classEq (.cv z) (synCfv F (.cv y))))
          (.objEq x y)))
      z dv_cache_0004 p0023
  have p0025 :=
    @gN1921v (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (.imp (synWa (.classEq (.cv z) (synCfv F (.cv x)))
          (.classEq (.cv z) (synCfv F (.cv y)))) (.objEq x y))
      z dv_cache_0005
  have p0026 :=
    @gN1923v
      (synWa (.classEq (.cv z) (synCfv F (.cv x))) (.classEq (.cv z) (synCfv F (.cv y))))
      (.objEq x y) z dv_cache_0006
  have p0027 := @gFvex (.cv x) F
  have p0028 :=
    @gEqvinc z (synCfv F (.cv x)) (synCfv F (.cv y)) dv_cache_0007 dv_cache_0008 p0027
  have p0029 :=
    @gImbi1i (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
      (synWex z (synWa (.classEq (.cv z) (synCfv F (.cv x)))
          (.classEq (.cv z) (synCfv F (.cv y)))))
      (.objEq x y) p0028
  have p0030 :=
    @gBitr4i
      (.all z (.imp (synWa (.classEq (.cv z) (synCfv F (.cv x)))
            (.classEq (.cv z) (synCfv F (.cv y)))) (.objEq x y)))
      (.imp (synWex z (synWa (.classEq (.cv z) (synCfv F (.cv x)))
            (.classEq (.cv z) (synCfv F (.cv y))))) (.objEq x y))
      (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)) p0026 p0029
  have p0031 :=
    @gImbi2i
      (.all z (.imp (synWa (.classEq (.cv z) (synCfv F (.cv x)))
            (.classEq (.cv z) (synCfv F (.cv y)))) (.objEq x y)))
      (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) p0030
  have p0032 :=
    @gBitri
      (.all z (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
            (synWa (.classEq (.cv z) (synCfv F (.cv x)))
              (.classEq (.cv z) (synCfv F (.cv y)))) (.objEq x y))))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.all z (.imp
            (synWa (.classEq (.cv z) (synCfv F (.cv x)))
              (.classEq (.cv z) (synCfv F (.cv y)))) (.objEq x y))))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)))
      p0025 p0031
  have p0033 :=
    @gSyl6bb (synWfn F A)
      (.all z (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
          (.objEq x y)))
      (.all z (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
            (synWa (.classEq (.cv z) (synCfv F (.cv x)))
              (.classEq (.cv z) (synCfv F (.cv y)))) (.objEq x y))))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)))
      p0024 p0032
  have p0034 :=
    @gN2albidv (synWfn F A)
      (.all z (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
          (.objEq x y)))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)))
      x y dv_cache_0009 dv_cache_0010 p0033
  have p0035 := @gBreq1 (.cv x) (.cv y) (.cv z) F
  have p0036_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))) :=
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
    @gMo4 (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)) x y dv_cache_0011
      dv_cache_0012 dv_cache_0013 p0036_e00_recanon
  have p0037 :=
    @gAlbii (synWmo x (synWbr (.cv x) F (.cv z)))
      (.all x (.all y (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
            (.objEq x y))))
      z p0036
  have p0038 :=
    @gAlcom
      (.all y (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
          (.objEq x y)))
      z x
  have p0039 :=
    @gAlcom
      (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z))) (.objEq x y))
      z y
  have p0040 :=
    @gAlbii
      (.all z (.all y (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
            (.objEq x y))))
      (.all y (.all z (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
            (.objEq x y))))
      x p0039
  have p0041 :=
    @gN3bitri (.all z (synWmo x (synWbr (.cv x) F (.cv z))))
      (.all z (.all x (.all y
            (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      (.all x (.all z (.all y
            (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      p0037 p0038 p0040
  have p0042 :=
    @gR2al (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)) x y A A
      dv_cache_0014 dv_cache_0013
  have p0043 :=
    @gN3bitr4g (synWfn F A)
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) F (.cv z)) (synWbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      (.all x (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)))))
      (.all z (synWmo x (synWbr (.cv x) F (.cv z))))
      (synWral x A (synWral y A
          (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y))))
      p0034 p0041 p0042
  have p0044 :=
    @gSyl (synWf F A B) (synWfn F A)
      (synWb (.all z (synWmo x (synWbr (.cv x) F (.cv z)))) (synWral x A (synWral y A
            (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)))))
      p0001 p0043
  have p0045 :=
    @gPm532i (synWf F A B) (.all z (synWmo x (synWbr (.cv x) F (.cv z))))
      (synWral x A (synWral y A
          (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y))))
      p0044
  have p0046 :=
    @gBitri (synWf1 F A B)
      (synWa (synWf F A B) (.all z (synWmo x (synWbr (.cv x) F (.cv z)))))
      (synWa (synWf F A B) (synWral x A (synWral y A
            (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.objEq x y)))))
      p0000 p0045
  exact p0046

/-- Checked nominal proof certificate identified upstream as `g_f1fveq`. -/
@[expose]
noncomputable def gF1fveq (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1 F A B) (synWa (.classMem C A) (.classMem D A)))
        (synWb (.classEq (synCfv F C) (synCfv F D)) (.classEq C D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_F : x ∉ F.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
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
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
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
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0008 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((Wff.imp (synWf1 F A B)
          (.imp (.classEq (synCfv F C) (synCfv F D)) (.classEq C D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, fresh_y_not_C, fresh_y_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((Wff.imp (synWf1 F A B)
          (.imp (.classEq (synCfv F C) (synCfv F (.cv y))) (.classEq C (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_F,
          fresh_x_not_C, fresh_x_ne_y, or_false, not_false_eq_true])
  have p0000 := @gFveq2 (.cv x) C F
  have p0001 :=
    @gEqeq1d (.classEq (.cv x) C) (synCfv F (.cv x)) (synCfv F C) (synCfv F (.cv y))
      p0000
  have p0002 := @gEqeq1 (.cv x) C (.cv y)
  have p0003 :=
    @gImbi12d (.classEq (.cv x) C) (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
      (.classEq (synCfv F C) (synCfv F (.cv y))) (.classEq (.cv x) (.cv y))
      (.classEq C (.cv y)) p0001 p0002
  have p0004 :=
    @gImbi2d (.classEq (.cv x) C)
      (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.classEq (.cv x) (.cv y)))
      (.imp (.classEq (synCfv F C) (synCfv F (.cv y))) (.classEq C (.cv y)))
      (synWf1 F A B) p0003
  have p0005 := @gFveq2 (.cv y) D F
  have p0006 :=
    @gEqeq2d (.classEq (.cv y) D) (synCfv F (.cv y)) (synCfv F D) (synCfv F C) p0005
  have p0007 := @gEqeq2 (.cv y) D C
  have p0008 :=
    @gImbi12d (.classEq (.cv y) D) (.classEq (synCfv F C) (synCfv F (.cv y)))
      (.classEq (synCfv F C) (synCfv F D)) (.classEq C (.cv y)) (.classEq C D) p0006
      p0007
  have p0009 :=
    @gImbi2d (.classEq (.cv y) D)
      (.imp (.classEq (synCfv F C) (synCfv F (.cv y))) (.classEq C (.cv y)))
      (.imp (.classEq (synCfv F C) (synCfv F D)) (.classEq C D)) (synWf1 F A B) p0008
  have p0010 :=
    @gDff13 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0011_e00_recanon :
    Nominal.NPrf
      (synWb (synWf1 F A B) (synWa (synWf F A B) (synWral x A (synWral y A
              (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
                (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0011 :=
    @gSimprbi (synWf1 F A B) (synWf F A B)
      (synWral x A (synWral y A (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      p0011_e00_recanon
  have p0012 :=
    @gRsp2
      (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.classEq (.cv x) (.cv y)))
      x y A A
  have p0013 :=
    @gSyl (synWf1 F A B)
      (synWral x A (synWral y A (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.classEq (.cv x) (.cv y))))
      p0011 p0012
  have p0014 :=
    @gCom12 (synWf1 F A B) (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y))) (.classEq (.cv x) (.cv y)))
      p0013
  have p0015 :=
    @gVtocl2ga
      (.imp (synWf1 F A B) (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
          (.classEq (.cv x) (.cv y))))
      (.imp (synWf1 F A B)
        (.imp (.classEq (synCfv F C) (synCfv F (.cv y))) (.classEq C (.cv y))))
      (.imp (synWf1 F A B) (.imp (.classEq (synCfv F C) (synCfv F D)) (.classEq C D)))
      x y C D A A dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0001 dv_cache_0002
      dv_cache_0001 dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0005 p0004 p0009
      p0014
  have p0016 :=
    @gImpcom (synWa (.classMem C A) (.classMem D A)) (synWf1 F A B)
      (.imp (.classEq (synCfv F C) (synCfv F D)) (.classEq C D)) p0015
  have p0017 := @gFveq2 C D F
  have p0018 :=
    @gImpbid1 (synWa (synWf1 F A B) (synWa (.classMem C A) (.classMem D A)))
      (.classEq (synCfv F C) (synCfv F D)) (.classEq C D) p0016 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_f1elima`. -/
@[expose]
noncomputable def gF1elima (A : Class) (B : Class) (F : Class) (X : Class) (Y : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWf1 F A B) (.classMem X A) (synWss Y A))
        (synWb (.classMem (synCfv F X) (synCima F Y)) (.classMem X Y))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ X.fv ∪ Y.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_Y : z ∉ Y.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (Y).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_Y, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((synCfv F X)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_z_not_X, fresh_z_not_F, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Wff.classMem X Y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          fresh_z_not_X, fresh_z_not_Y, or_false, not_false_eq_true])
  have dv_cache_0005 :
    z ∉ ((synWa (synWa (synWf1 F A B) (.classMem X A)) (synWss Y A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, fresh_z_not_F, fresh_z_not_X, fresh_z_not_Y,
          or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_X, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.classEq (synCfv F X) (synCfv F X))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_z_not_X, fresh_z_not_F, or_false, not_false_eq_true])
  have p0000 := @gF1fn A B F
  have p0001 :=
    @gFvelimab z A Y (synCfv F X) F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gSylan (synWf1 F A B) (synWfn F A) (synWss Y A)
      (synWb (.classMem (synCfv F X) (synCima F Y))
        (synWrex z Y (.classEq (synCfv F (.cv z)) (synCfv F X))))
      p0000 p0001
  have p0003 :=
    @gN3adant2 (synWf1 F A B) (synWss Y A)
      (synWb (.classMem (synCfv F X) (synCima F Y))
        (synWrex z Y (.classEq (synCfv F (.cv z)) (synCfv F X))))
      (.classMem X A) p0002
  have p0004 := @gSsel Y A (.cv z)
  have p0005 := @gImpac (synWss Y A) (.classMem (.cv z) Y) (.classMem (.cv z) A) p0004
  have p0006 := @gF1fveq A B (.cv z) X F
  have p0007 :=
    @gAncom2s (synWf1 F A B) (.classMem (.cv z) A) (.classMem X A)
      (synWb (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classEq (.cv z) X)) p0006
  have p0008 :=
    @gBiimpd (synWa (synWf1 F A B) (synWa (.classMem X A) (.classMem (.cv z) A)))
      (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classEq (.cv z) X) p0007
  have p0009 :=
    @gAnassrs (synWf1 F A B) (.classMem X A) (.classMem (.cv z) A)
      (.imp (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classEq (.cv z) X)) p0008
  have p0010 := @gEleq1 (.cv z) X Y
  have p0011 :=
    @gBiimpcd (.classEq (.cv z) X) (.classMem (.cv z) Y) (.classMem X Y) p0010
  have p0012 :=
    @gSylan9 (synWa (synWa (synWf1 F A B) (.classMem X A)) (.classMem (.cv z) A))
      (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classEq (.cv z) X)
      (.classMem (.cv z) Y) (.classMem X Y) p0009 p0011
  have p0013 :=
    @gAnasss (synWa (synWf1 F A B) (.classMem X A)) (.classMem (.cv z) A)
      (.classMem (.cv z) Y)
      (.imp (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classMem X Y)) p0012
  have p0014 :=
    @gSylan2 (synWa (synWss Y A) (.classMem (.cv z) Y))
      (synWa (synWf1 F A B) (.classMem X A))
      (synWa (.classMem (.cv z) A) (.classMem (.cv z) Y))
      (.imp (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classMem X Y)) p0005 p0013
  have p0015 :=
    @gAnassrs (synWa (synWf1 F A B) (.classMem X A)) (synWss Y A)
      (.classMem (.cv z) Y)
      (.imp (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classMem X Y)) p0014
  have p0016 :=
    @gRexlimdva (synWa (synWa (synWf1 F A B) (.classMem X A)) (synWss Y A))
      (.classEq (synCfv F (.cv z)) (synCfv F X)) (.classMem X Y) z Y dv_cache_0004
      dv_cache_0005 p0015
  have p0017 :=
    @gN3impa (synWf1 F A B) (.classMem X A) (synWss Y A)
      (.imp (synWrex z Y (.classEq (synCfv F (.cv z)) (synCfv F X))) (.classMem X Y))
      p0016
  have p0018 := @gEqid (synCfv F X)
  have p0019 := @gFveq2 (.cv z) X F
  have p0020 :=
    @gEqeq1d (.classEq (.cv z) X) (synCfv F (.cv z)) (synCfv F X) (synCfv F X) p0019
  have p0021 :=
    @gRspcev (.classEq (synCfv F (.cv z)) (synCfv F X))
      (.classEq (synCfv F X) (synCfv F X)) z X Y dv_cache_0006 dv_cache_0001
      dv_cache_0007 p0020
  have p0022 :=
    @gMpan2 (.classMem X Y) (.classEq (synCfv F X) (synCfv F X))
      (synWrex z Y (.classEq (synCfv F (.cv z)) (synCfv F X))) p0018 p0021
  have p0023 :=
    @gImpbid1 (synW3a (synWf1 F A B) (.classMem X A) (synWss Y A))
      (synWrex z Y (.classEq (synCfv F (.cv z)) (synCfv F X))) (.classMem X Y) p0017
      p0022
  have p0024 :=
    @gBitrd (synW3a (synWf1 F A B) (.classMem X A) (synWss Y A))
      (.classMem (synCfv F X) (synCima F Y))
      (synWrex z Y (.classEq (synCfv F (.cv z)) (synCfv F X))) (.classMem X Y) p0003
      p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_dff1o6`. -/
@[expose]
noncomputable def gDff1o6 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWf1o F A B) (synW3a (synWfn F A) (.classEq (synCrn F) B) (synWral x A
            (synWral y A (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
                (.classEq (.cv x) (.cv y))))))) :=
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
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := (Nominal.biimpRefl (synWf1o F A B))
  have p0001 :=
    @gDff13 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0002 := (Nominal.biimpRefl (synWfo F A B))
  have p0003_e00_recanon :
    Nominal.NPrf
      (synWb (synWf1 F A B) (synWa (synWf F A B) (synWral x A (synWral y A
              (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
                (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0003 :=
    @gAnbi12i (synWf1 F A B)
      (synWa (synWf F A B) (synWral x A (synWral y A
            (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (synWfo F A B) (synWa (synWfn F A) (.classEq (synCrn F) B)) p0003_e00_recanon
      p0002
  have p0004 :=
    (Nominal.biimpRefl (synW3a (synWfn F A) (.classEq (synCrn F) B) (synWral x A
          (synWral y A (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
              (.classEq (.cv x) (.cv y)))))))
  have p0005 := @gEqimss (synCrn F) B
  have p0006 :=
    @gAnim2i (.classEq (synCrn F) B) (synWss (synCrn F) B) (synWfn F A) p0005
  have p0007 := (Nominal.biimpRefl (synWf F A B))
  have p0008 :=
    @gSylibr (synWa (synWfn F A) (.classEq (synCrn F) B))
      (synWa (synWfn F A) (synWss (synCrn F) B)) (synWf F A B) p0006 p0007
  have p0009 :=
    @gPm471ri (synWa (synWfn F A) (.classEq (synCrn F) B)) (synWf F A B) p0008
  have p0010 :=
    @gAnbi1i (synWa (synWfn F A) (.classEq (synCrn F) B))
      (synWa (synWf F A B) (synWa (synWfn F A) (.classEq (synCrn F) B)))
      (synWral x A (synWral y A (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      p0009
  have p0011 :=
    @gAn32 (synWf F A B) (synWa (synWfn F A) (.classEq (synCrn F) B))
      (synWral x A (synWral y A (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
  have p0012 :=
    @gN3bitrri
      (synW3a (synWfn F A) (.classEq (synCrn F) B) (synWral x A (synWral y A
            (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (synWa (synWa (synWfn F A) (.classEq (synCrn F) B)) (synWral x A (synWral y A
            (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (synWa (synWa (synWf F A B) (synWa (synWfn F A) (.classEq (synCrn F) B)))
        (synWral x A (synWral y A (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (synWa (synWa (synWf F A B) (synWral x A (synWral y A
              (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
                (.classEq (.cv x) (.cv y)))))) (synWa (synWfn F A) (.classEq (synCrn F) B)))
      p0004 p0010 p0011
  have p0013 :=
    @gN3bitri (synWf1o F A B) (synWa (synWf1 F A B) (synWfo F A B))
      (synWa (synWa (synWf F A B) (synWral x A (synWral y A
              (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
                (.classEq (.cv x) (.cv y)))))) (synWa (synWfn F A) (.classEq (synCrn F) B)))
      (synW3a (synWfn F A) (.classEq (synCrn F) B) (synWral x A (synWral y A
            (.imp (.classEq (synCfv F (.cv x)) (synCfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      p0000 p0003 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_f1ocnvfv1`. -/
@[expose]
noncomputable def gF1ocnvfv1 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1o F A B) (.classMem C A))
        (.classEq (synCfv (synCcnv F) (synCfv F C)) C)) :=
  by
  have p0000 := @gF1ococnv1 A B F
  have p0001 :=
    @gFveq1d (synWf1o F A B) C (synCcom (synCcnv F) F) (synCres (synCid) A) p0000
  have p0002 :=
    @gAdantr (synWf1o F A B)
      (.classEq (synCfv (synCcom (synCcnv F) F) C) (synCfv (synCres (synCid) A) C))
      (.classMem C A) p0001
  have p0003 := @gF1of A B F
  have p0004 := @gFvco3 A B C (synCcnv F) F
  have p0005 :=
    @gSylan (synWf1o F A B) (synWf F A B) (.classMem C A)
      (.classEq (synCfv (synCcom (synCcnv F) F) C) (synCfv (synCcnv F) (synCfv F C)))
      p0003 p0004
  have p0006 := @gFvresi A C
  have p0007 :=
    @gAdantl (.classMem C A) (.classEq (synCfv (synCres (synCid) A) C) C)
      (synWf1o F A B) p0006
  have p0008 :=
    @gN3eqtr3d (synWa (synWf1o F A B) (.classMem C A))
      (synCfv (synCcom (synCcnv F) F) C) (synCfv (synCres (synCid) A) C)
      (synCfv (synCcnv F) (synCfv F C)) C p0002 p0005 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_f1ocnvfv2`. -/
@[expose]
noncomputable def gF1ocnvfv2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1o F A B) (.classMem C B))
        (.classEq (synCfv F (synCfv (synCcnv F) C)) C)) :=
  by
  have p0000 := @gCnvcnv F
  have p0001 := @gFveq1i (synCfv (synCcnv F) C) (synCcnv (synCcnv F)) F p0000
  have p0002 := @gF1ocnv A B F
  have p0003 := @gF1ocnvfv1 B A C (synCcnv F)
  have p0004 :=
    @gSylan (synWf1o F A B) (synWf1o (synCcnv F) B A) (.classMem C B)
      (.classEq (synCfv (synCcnv (synCcnv F)) (synCfv (synCcnv F) C)) C) p0002 p0003
  have p0005 :=
    @gSyl5eqr (synWa (synWf1o F A B) (.classMem C B))
      (synCfv F (synCfv (synCcnv F) C))
      (synCfv (synCcnv (synCcnv F)) (synCfv (synCcnv F) C)) C p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_f1ocnvfv`. -/
@[expose]
noncomputable def gF1ocnvfv (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1o F A B) (.classMem C A))
        (.imp (.classEq (synCfv F C) D) (.classEq (synCfv (synCcnv F) D) C))) :=
  by
  have p0000 := @gFveq2 D (synCfv F C) (synCcnv F)
  have p0001 :=
    @gEqcoms (.classEq (synCfv (synCcnv F) D) (synCfv (synCcnv F) (synCfv F C))) D
      (synCfv F C) p0000
  have p0002 := @gF1ocnvfv1 A B C F
  have p0003 :=
    @gEqeq2d (synWa (synWf1o F A B) (.classMem C A))
      (synCfv (synCcnv F) (synCfv F C)) C (synCfv (synCcnv F) D) p0002
  have p0004 :=
    @gSyl5ib (.classEq (synCfv F C) D)
      (.classEq (synCfv (synCcnv F) D) (synCfv (synCcnv F) (synCfv F C)))
      (synWa (synWf1o F A B) (.classMem C A)) (.classEq (synCfv (synCcnv F) D) C)
      p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_f1ocnvfvb`. -/
@[expose]
noncomputable def gF1ocnvfvb (A : Class) (B : Class) (C : Class) (D : Class)
    (F : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWf1o F A B) (.classMem C A) (.classMem D B))
        (synWb (.classEq (synCfv F C) D) (.classEq (synCfv (synCcnv F) D) C))) :=
  by
  have p0000 := @gF1ocnvfv A B C D F
  have p0001 :=
    @gN3adant3 (synWf1o F A B) (.classMem C A)
      (.imp (.classEq (synCfv F C) D) (.classEq (synCfv (synCcnv F) D) C))
      (.classMem D B) p0000
  have p0002 := @gFveq2 C (synCfv (synCcnv F) D) F
  have p0003 :=
    @gEqcoms (.classEq (synCfv F C) (synCfv F (synCfv (synCcnv F) D))) C
      (synCfv (synCcnv F) D) p0002
  have p0004 := @gF1ocnvfv2 A B D F
  have p0005 :=
    @gEqeq2d (synWa (synWf1o F A B) (.classMem D B))
      (synCfv F (synCfv (synCcnv F) D)) D (synCfv F C) p0004
  have p0006 :=
    @gSyl5ib (.classEq (synCfv (synCcnv F) D) C)
      (.classEq (synCfv F C) (synCfv F (synCfv (synCcnv F) D)))
      (synWa (synWf1o F A B) (.classMem D B)) (.classEq (synCfv F C) D) p0003 p0005
  have p0007 :=
    @gN3adant2 (synWf1o F A B) (.classMem D B)
      (.imp (.classEq (synCfv (synCcnv F) D) C) (.classEq (synCfv F C) D))
      (.classMem C A) p0006
  have p0008 :=
    @gImpbid (synW3a (synWf1o F A B) (.classMem C A) (.classMem D B))
      (.classEq (synCfv F C) D) (.classEq (synCfv (synCcnv F) D) C) p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_f1ocnvdm`. -/
@[expose]
noncomputable def gF1ocnvdm (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1o F A B) (.classMem C B)) (.classMem (synCfv (synCcnv F) C) A)) :=
  by
  have p0000 := @gF1ocnv A B F
  have p0001 := @gF1of B A (synCcnv F)
  have p0002 :=
    @gSyl (synWf1o F A B) (synWf1o (synCcnv F) B A) (synWf (synCcnv F) B A) p0000
      p0001
  have p0003 := @gFfvelrn B A C (synCcnv F)
  have p0004 :=
    @gSylan (synWf1o F A B) (synWf (synCcnv F) B A) (.classMem C B)
      (.classMem (synCfv (synCcnv F) C) A) p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end
