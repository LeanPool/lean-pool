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

@[expose]
noncomputable def g_eqfnfvd (ph : Wff) (x : Var) (A : Class) (F : Class) (G : Class)
    (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_eqfnfvd_1 : Nominal.NPrf (.imp ph (syn_wfn F A)))
    (hyp_eqfnfvd_2 : Nominal.NPrf (.imp ph (syn_wfn G A)))
    (hyp_eqfnfvd_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A))
          (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))) :
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
    @g_ralrimiva ph (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) x A dv_cache_0001
      hyp_eqfnfvd_3
  have p0001 := @g_eqfnfv x A F G dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_syl2anc ph (syn_wfn F A) (syn_wfn G A)
      (syn_wb (.classEq F G) (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))))
      hyp_eqfnfvd_1 hyp_eqfnfvd_2 p0001
  have p0003 :=
    @g_mpbird ph (.classEq F G)
      (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_funfvop (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
        (.classMem (syn_cop A (syn_cfv F A)) F)) :=
  by
  have p0000 := @g_eqid (syn_cfv F A)
  have p0001 := @g_funopfvb A (syn_cfv F A) F
  have p0002 :=
    @g_mpbii (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
      (.classEq (syn_cfv F A) (syn_cfv F A)) (.classMem (syn_cop A (syn_cfv F A)) F) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_funfvbrb (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun F) (syn_wb (.classMem A (syn_cdm F)) (syn_wbr A F (syn_cfv F A)))) :=
  by
  have p0000 := @g_funfvop A F
  have p0001 := (Nominal.biimpRefl (syn_wbr A F (syn_cfv F A)))
  have p0002 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
      (.classMem (syn_cop A (syn_cfv F A)) F) (syn_wbr A F (syn_cfv F A)) p0000 p0001
  have p0003 := @g_breldm A (syn_cfv F A) F
  have p0004 :=
    @g_adantl (syn_wbr A F (syn_cfv F A)) (.classMem A (syn_cdm F)) (syn_wfun F) p0003
  have p0005 :=
    @g_impbida (syn_wfun F) (.classMem A (syn_cdm F)) (syn_wbr A F (syn_cfv F A)) p0002
      p0004
  exact p0005

@[expose]
noncomputable def g_fvimacnvi (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B)))
        (.classMem (syn_cfv F A) B)) :=
  by
  have p0000 := @g_snssi A (syn_cima (syn_ccnv F) B)
  have p0001 := @g_funimass2 (syn_csn A) B F
  have p0002 :=
    @g_sylan2 (.classMem A (syn_cima (syn_ccnv F) B)) (syn_wfun F)
      (syn_wss (syn_csn A) (syn_cima (syn_ccnv F) B)) (syn_wss (syn_cima F (syn_csn A)) B)
      p0000 p0001
  have p0003 := @g_fvex A F
  have p0004 := @g_snss (syn_cfv F A) B p0003
  have p0005 := @g_cnvimass F B
  have p0006 := @g_sseli (syn_cima (syn_ccnv F) B) (syn_cdm F) A p0005
  have p0007 := @g_funfn F
  have p0008 := @g_fnsnfv (syn_cdm F) A F
  have p0009 :=
    @g_sylanb (syn_wfun F) (syn_wfn F (syn_cdm F)) (.classMem A (syn_cdm F))
      (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0007 p0008
  have p0010 :=
    @g_sylan2 (.classMem A (syn_cima (syn_ccnv F) B)) (syn_wfun F)
      (.classMem A (syn_cdm F))
      (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0006 p0009
  have p0011 :=
    @g_sseq1d (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B)))
      (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A)) B p0010
  have p0012 :=
    @g_syl5bb (.classMem (syn_cfv F A) B) (syn_wss (syn_csn (syn_cfv F A)) B)
      (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B)))
      (syn_wss (syn_cima F (syn_csn A)) B) p0004 p0011
  have p0013 :=
    @g_mpbird (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B)))
      (.classMem (syn_cfv F A) B) (syn_wss (syn_cima F (syn_csn A)) B) p0002 p0012
  exact p0013

@[expose]
noncomputable def g_fvimacnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
        (syn_wb (.classMem (syn_cfv F A) B) (.classMem A (syn_cima (syn_ccnv F) B)))) :=
  by
  have p0000 := @g_funfvop A F
  have p0001 := @g_opelcnv (syn_cfv F A) A F
  have p0002 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
      (.classMem (syn_cop A (syn_cfv F A)) F)
      (.classMem (syn_cop (syn_cfv F A) A) (syn_ccnv F)) p0000 p0001
  have p0003 := @g_elimasn (syn_ccnv F) (syn_cfv F A) A
  have p0004 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
      (.classMem (syn_cop (syn_cfv F A) A) (syn_ccnv F))
      (.classMem A (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A)))) p0002 p0003
  have p0005 := @g_fvex A F
  have p0006 := @g_snss (syn_cfv F A) B p0005
  have p0007 := @g_imass2 (syn_csn (syn_cfv F A)) B (syn_ccnv F)
  have p0008 :=
    @g_sylbi (.classMem (syn_cfv F A) B) (syn_wss (syn_csn (syn_cfv F A)) B)
      (syn_wss (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A))) (syn_cima (syn_ccnv F) B))
      p0006 p0007
  have p0009 :=
    @g_sseld (.classMem (syn_cfv F A) B) (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A)))
      (syn_cima (syn_ccnv F) B) A p0008
  have p0010 :=
    @g_syl5com (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
      (.classMem A (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A))))
      (.classMem (syn_cfv F A) B) (.classMem A (syn_cima (syn_ccnv F) B)) p0004 p0009
  have p0011 := @g_fvimacnvi A B F
  have p0012 :=
    @g_ex (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B)) (.classMem (syn_cfv F A) B)
      p0011
  have p0013 :=
    @g_adantr (syn_wfun F)
      (.imp (.classMem A (syn_cima (syn_ccnv F) B)) (.classMem (syn_cfv F A) B))
      (.classMem A (syn_cdm F)) p0012
  have p0014 :=
    @g_impbid (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem (syn_cfv F A) B)
      (.classMem A (syn_cima (syn_ccnv F) B)) p0010 p0013
  exact p0014

@[expose]
noncomputable def g_funimass3 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
        (syn_wb (syn_wss (syn_cima F A) B) (syn_wss A (syn_cima (syn_ccnv F) B)))) :=
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
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_cima (syn_ccnv F) B)).fv :=
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
  have p0000 := @g_funimass4 x A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_ssel A (syn_cdm F) (.cv x)
  have p0002 := @g_fvimacnv (.cv x) B F
  have p0003 :=
    @g_ex (syn_wfun F) (.classMem (.cv x) (syn_cdm F))
      (syn_wb (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B)))
      p0002
  have p0004 :=
    @g_syl9r (syn_wss A (syn_cdm F)) (.classMem (.cv x) A) (.classMem (.cv x) (syn_cdm F))
      (syn_wfun F)
      (syn_wb (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B)))
      p0001 p0003
  have p0005 :=
    @g_imp31 (syn_wfun F) (syn_wss A (syn_cdm F)) (.classMem (.cv x) A)
      (syn_wb (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B)))
      p0004
  have p0006 :=
    @g_ralbidva (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B)) x A
      dv_cache_0004 p0005
  have p0007 :=
    @g_bitrd (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wss (syn_cima F A) B)
      (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))
      (syn_wral x A (.classMem (.cv x) (syn_cima (syn_ccnv F) B))) p0000 p0006
  have p0008 := @g_dfss3 x A (syn_cima (syn_ccnv F) B) dv_cache_0001 dv_cache_0005
  have p0009 :=
    @g_syl6bbr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wss (syn_cima F A) B)
      (syn_wral x A (.classMem (.cv x) (syn_cima (syn_ccnv F) B)))
      (syn_wss A (syn_cima (syn_ccnv F) B)) p0007 p0008
  exact p0009

@[expose]
noncomputable def g_elpreima (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfn F A) (syn_wb (.classMem B (syn_cima (syn_ccnv F) C))
          (syn_wa (.classMem B A) (.classMem (syn_cfv F B) C)))) :=
  by
  have p0000 := @g_cnvimass F C
  have p0001 := @g_sseli (syn_cima (syn_ccnv F) C) (syn_cdm F) B p0000
  have p0002 := @g_fndm A F
  have p0003 := @g_eleq2d (syn_wfn F A) (syn_cdm F) A B p0002
  have p0004 :=
    @g_syl5ib (.classMem B (syn_cima (syn_ccnv F) C)) (.classMem B (syn_cdm F))
      (syn_wfn F A) (.classMem B A) p0001 p0003
  have p0005 := @g_fnfun A F
  have p0006 := @g_fvimacnvi B C F
  have p0007 :=
    @g_sylan (syn_wfn F A) (syn_wfun F) (.classMem B (syn_cima (syn_ccnv F) C))
      (.classMem (syn_cfv F B) C) p0005 p0006
  have p0008 :=
    @g_ex (syn_wfn F A) (.classMem B (syn_cima (syn_ccnv F) C))
      (.classMem (syn_cfv F B) C) p0007
  have p0009 :=
    @g_jcad (syn_wfn F A) (.classMem B (syn_cima (syn_ccnv F) C)) (.classMem B A)
      (.classMem (syn_cfv F B) C) p0004 p0008
  have p0010 := @g_fvimacnv B C F
  have p0011 :=
    @g_funfni (syn_wb (.classMem (syn_cfv F B) C) (.classMem B (syn_cima (syn_ccnv F) C)))
      A B F p0010
  have p0012 :=
    @g_biimpd (syn_wa (syn_wfn F A) (.classMem B A)) (.classMem (syn_cfv F B) C)
      (.classMem B (syn_cima (syn_ccnv F) C)) p0011
  have p0013 :=
    @g_expimpd (syn_wfn F A) (.classMem B A) (.classMem (syn_cfv F B) C)
      (.classMem B (syn_cima (syn_ccnv F) C)) p0012
  have p0014 :=
    @g_impbid (syn_wfn F A) (.classMem B (syn_cima (syn_ccnv F) C))
      (syn_wa (.classMem B A) (.classMem (syn_cfv F B) C)) p0009 p0013
  exact p0014

@[expose]
noncomputable def g_fimacnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (.classEq (syn_cima (syn_ccnv F) B) A)) :=
  by
  have p0000 := @g_imassrn (syn_ccnv F) B
  have p0001 := (Nominal.classEqRefl (syn_cdm F))
  have p0002 := @g_fdm A B F
  have p0003 := @g_ssid A
  have p0004 := @g_a1i (syn_wss A A) (syn_wf F A B) p0003
  have p0005 := @g_eqsstrd (syn_wf F A B) (syn_cdm F) A A p0002 p0004
  have p0006 :=
    @g_syl5eqssr (syn_wf F A B) (syn_crn (syn_ccnv F)) (syn_cdm F) A p0001 p0005
  have p0007 :=
    @g_syl5ss (syn_wf F A B) (syn_cima (syn_ccnv F) B) (syn_crn (syn_ccnv F)) A p0000
      p0006
  have p0008 := @g_imassrn F A
  have p0009 := @g_frn A B F
  have p0010 := @g_syl5ss (syn_wf F A B) (syn_cima F A) (syn_crn F) B p0008 p0009
  have p0011 := @g_ffun A B F
  have p0012 := @g_syl5sseqr (syn_wf F A B) A A (syn_cdm F) p0003 p0002
  have p0013 := @g_funimass3 A B F
  have p0014 :=
    @g_syl2anc (syn_wf F A B) (syn_wfun F) (syn_wss A (syn_cdm F))
      (syn_wb (syn_wss (syn_cima F A) B) (syn_wss A (syn_cima (syn_ccnv F) B))) p0011
      p0012 p0013
  have p0015 :=
    @g_mpbid (syn_wf F A B) (syn_wss (syn_cima F A) B)
      (syn_wss A (syn_cima (syn_ccnv F) B)) p0010 p0014
  have p0016 := @g_eqssd (syn_wf F A B) (syn_cima (syn_ccnv F) B) A p0007 p0015
  exact p0016

@[expose]
noncomputable def g_fvelrn (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
        (.classMem (syn_cfv F A) (syn_crn F))) :=
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
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_cop A (syn_cfv F A)) F)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cfv F A)).fv :=
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
  have p0000 := @g_simpr (syn_wfun F) (.classMem A (syn_cdm F))
  have p0001 := @g_funfvop A F
  have p0002 := @g_opeq1 (.cv x) A (syn_cfv F A)
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cfv F A))
      (syn_cop A (syn_cfv F A)) F p0002
  have p0004 :=
    @g_spcegv (.classMem (syn_cop (.cv x) (syn_cfv F A)) F)
      (.classMem (syn_cop A (syn_cfv F A)) F) x A (syn_cdm F) dv_cache_0001 dv_cache_0002
      p0003
  have p0005 :=
    @g_sylc (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem A (syn_cdm F))
      (.classMem (syn_cop A (syn_cfv F A)) F)
      (syn_wex x (.classMem (syn_cop (.cv x) (syn_cfv F A)) F)) p0000 p0001 p0004
  have p0006 := @g_elrn2 x (syn_cfv F A) F dv_cache_0003 dv_cache_0004
  have p0007 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
      (syn_wex x (.classMem (syn_cop (.cv x) (syn_cfv F A)) F))
      (.classMem (syn_cfv F A) (syn_crn F)) p0005 p0006
  exact p0007

@[expose]
noncomputable def g_fnfvelrn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (.classMem (syn_cfv F B) (syn_crn F))) :=
  by
  have p0000 := @g_fvelrn B F
  have p0001 := @g_funfni (.classMem (syn_cfv F B) (syn_crn F)) A B F p0000
  exact p0001

@[expose]
noncomputable def g_ffvelrn (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf F A B) (.classMem C A)) (.classMem (syn_cfv F C) B)) :=
  by
  have p0000 := @g_ffn A B F
  have p0001 := @g_fnfvelrn A C F
  have p0002 :=
    @g_sylan (syn_wf F A B) (syn_wfn F A) (.classMem C A)
      (.classMem (syn_cfv F C) (syn_crn F)) p0000 p0001
  have p0003 := @g_frn A B F
  have p0004 := @g_sseld (syn_wf F A B) (syn_crn F) B (syn_cfv F C) p0003
  have p0005 :=
    @g_adantr (syn_wf F A B)
      (.imp (.classMem (syn_cfv F C) (syn_crn F)) (.classMem (syn_cfv F C) B))
      (.classMem C A) p0004
  have p0006 :=
    @g_mpd (syn_wa (syn_wf F A B) (.classMem C A)) (.classMem (syn_cfv F C) (syn_crn F))
      (.classMem (syn_cfv F C) B) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_ffvelrni (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_ffvrni_1 : Nominal.NPrf (syn_wf F A B)) :
    Nominal.NPrf (.imp (.classMem C A) (.classMem (syn_cfv F C) B)) :=
  by
  have p0000 := @g_ffvelrn A B C F
  have p0001 :=
    @g_mpan (syn_wf F A B) (.classMem C A) (.classMem (syn_cfv F C) B) hyp_ffvrni_1 p0000
  exact p0001

@[expose]
noncomputable def g_dffo3 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wfo F A B) (syn_wa (syn_wf F A B)
          (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))) :=
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
  have dv_cache_0007 : x ∉ ((syn_wf F A B)).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wf F A B)).fv :=
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
  have p0000 := @g_dffo2 A B F
  have p0001 := @g_ffn A B F
  have p0002 :=
    @g_fnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0003 :=
    @g_eqeq1d (syn_wfn F A) (syn_crn F)
      (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B p0002
  have p0004 :=
    @g_syl (syn_wf F A B) (syn_wfn F A)
      (syn_wb (.classEq (syn_crn F) B)
        (.classEq (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B))
      p0001 p0003
  have p0005 :=
    @g_simpr (syn_wa (syn_wf F A B) (.classMem (.cv x) A))
      (.classEq (.cv y) (syn_cfv F (.cv x)))
  have p0006 := @g_ffvelrn A B (.cv x) F
  have p0007 :=
    @g_adantr (syn_wa (syn_wf F A B) (.classMem (.cv x) A))
      (.classMem (syn_cfv F (.cv x)) B) (.classEq (.cv y) (syn_cfv F (.cv x))) p0006
  have p0008 :=
    @g_eqeltrd
      (syn_wa (syn_wa (syn_wf F A B) (.classMem (.cv x) A))
        (.classEq (.cv y) (syn_cfv F (.cv x))))
      (.cv y) (syn_cfv F (.cv x)) B p0005 p0007
  have p0009 :=
    @g_exp31 (syn_wf F A B) (.classMem (.cv x) A) (.classEq (.cv y) (syn_cfv F (.cv x)))
      (.classMem (.cv y) B) p0008
  have p0010 :=
    @g_rexlimdv (syn_wf F A B) (.classEq (.cv y) (syn_cfv F (.cv x)))
      (.classMem (.cv y) B) x A dv_cache_0006 dv_cache_0007 p0009
  have p0011 :=
    @g_biantrurd (syn_wf F A B)
      (.imp (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))
      p0010
  have p0012 :=
    @g_dfbi2 (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B)
  have p0013 :=
    @g_syl6rbbr (syn_wf F A B)
      (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))
      (syn_wa (.imp (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B))
        (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))
      (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B))
      p0011 p0012
  have p0014 :=
    @g_albidv (syn_wf F A B)
      (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) y
      dv_cache_0008 p0013
  have p0015 :=
    @g_eqabcb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) y B dv_cache_0009
  have p0016 :=
    (Nominal.biimpRefl (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))
  have p0017 :=
    @g_n_3bitr4g (syn_wf F A B)
      (.all y (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))
          (.classMem (.cv y) B)))
      (.all y (.imp (.classMem (.cv y) B)
          (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))
      (.classEq (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B)
      (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0014 p0015
      p0016
  have p0018 :=
    @g_bitrd (syn_wf F A B) (.classEq (syn_crn F) B)
      (.classEq (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B)
      (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0004 p0017
  have p0019 :=
    @g_pm5_32i (syn_wf F A B) (.classEq (syn_crn F) B)
      (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0018
  have p0020 :=
    @g_bitri (syn_wfo F A B) (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B))
      (syn_wa (syn_wf F A B)
        (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))
      p0000 p0019
  exact p0020

@[expose]
noncomputable def g_foelrn (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfo F A B) (.classMem C B))
        (syn_wrex x A (.classEq C (syn_cfv F (.cv x))))) :=
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
  have dv_cache_0010 : y ∉ ((syn_wrex x A (.classEq C (syn_cfv F (.cv x))))).fv :=
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
    @g_dffo3 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_simprbi (syn_wfo F A B) (syn_wf F A B)
      (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0000
  have p0002 := @g_eqeq1 (.cv y) C (syn_cfv F (.cv x))
  have p0003 :=
    @g_rexbidv (.classEq (.cv y) C) (.classEq (.cv y) (syn_cfv F (.cv x)))
      (.classEq C (syn_cfv F (.cv x))) x A dv_cache_0008 p0002
  have p0004 :=
    @g_rspccva (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))
      (syn_wrex x A (.classEq C (syn_cfv F (.cv x)))) y C B dv_cache_0009 dv_cache_0004
      dv_cache_0010 p0003
  have p0005 :=
    @g_sylan (syn_wfo F A B)
      (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) (.classMem C B)
      (syn_wrex x A (.classEq C (syn_cfv F (.cv x)))) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_ffnfv (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (syn_wb (syn_wf F A B)
        (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))) :=
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
  have dv_cache_0001 : x ∉ ((syn_wf F A B)).fv := by
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
  have dv_cache_0006 : y ∉ ((syn_crn F)).fv :=
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
    y ∉ ((syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))).fv :=
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
  have p0000 := @g_ffn A B F
  have p0001 := @g_ffvelrn A B (.cv x) F
  have p0002 :=
    @g_ralrimiva (syn_wf F A B) (.classMem (syn_cfv F (.cv x)) B) x A dv_cache_0001 p0001
  have p0003 :=
    @g_jca (syn_wf F A B) (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))
      p0000 p0002
  have p0004 := @g_simpl (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))
  have p0005 := @g_fvelrnb x A (.cv y) F dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_biimpd (syn_wfn F A) (.classMem (.cv y) (syn_crn F))
      (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y))) p0005
  have p0007 := @g_nfra1 (.classMem (syn_cfv F (.cv x)) B) x A
  have p0008 := @g_nfv (.classMem (.cv y) B) x dv_cache_0005
  have p0009 := @g_rsp (.classMem (syn_cfv F (.cv x)) B) x A
  have p0010 := @g_eleq1 (syn_cfv F (.cv x)) (.cv y) B
  have p0011 :=
    @g_biimpcd (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (syn_cfv F (.cv x)) B)
      (.classMem (.cv y) B) p0010
  have p0012 :=
    @g_syl6 (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) (.classMem (.cv x) A)
      (.classMem (syn_cfv F (.cv x)) B)
      (.imp (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (.cv y) B)) p0009 p0011
  have p0013 :=
    @g_rexlimd (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))
      (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (.cv y) B) x A p0007 p0008 p0012
  have p0014 :=
    @g_sylan9 (syn_wfn F A) (.classMem (.cv y) (syn_crn F))
      (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y)))
      (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) (.classMem (.cv y) B) p0006 p0013
  have p0015 :=
    @g_ssrdv (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))) y
      (syn_crn F) B dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 := (Nominal.biimpRefl (syn_wf F A B))
  have p0017 :=
    @g_sylanbrc (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))
      (syn_wfn F A) (syn_wss (syn_crn F) B) (syn_wf F A B) p0004 p0015 p0016
  have p0018 :=
    @g_impbii (syn_wf F A B)
      (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))) p0003 p0017
  exact p0018

@[expose]
noncomputable def g_fnfvrnss (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))
        (syn_wss (syn_crn F) B)) :=
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
  have p0000 := @g_ffnfv x A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_frn A B F
  have p0002 :=
    @g_sylbir (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))
      (syn_wf F A B) (syn_wss (syn_crn F) B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fsn (A : Class) (B : Class) (F : Class)
    (hyp_fsn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wf F (syn_csn A) (syn_csn B)) (.classEq F (syn_csn (syn_cop A B)))) :=
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
  have dv_cache_0003 : y ∉ ((syn_csn A)).fv :=
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
  have dv_cache_0004 : y ∉ ((syn_csn B)).fv :=
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
  have dv_cache_0007 : y ∉ ((Wff.classMem (syn_cop A B) F)).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_csn (syn_cop A B))).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_csn (syn_cop A B))).fv :=
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
  have dv_cache_0011 : x ∉ ((syn_wf F (syn_csn A) (syn_csn B))).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_wf F (syn_csn A) (syn_csn B))).fv :=
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
  have p0000 := @g_opelf (syn_csn A) (syn_csn B) (.cv x) (.cv y) F
  have p0001 := @g_elsn x A dv_cache_0001
  have p0002 := @g_elsn y B dv_cache_0002
  have p0003 :=
    @g_anbi12i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A)
      (.classMem (.cv y) (syn_csn B)) (.classEq (.cv y) B) p0001 p0002
  have p0004 :=
    @g_sylib
      (syn_wa (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_wa (.classMem (.cv x) (syn_csn A)) (.classMem (.cv y) (syn_csn B)))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0003
  have p0005 :=
    @g_ex (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0004
  have p0006 := @g_snid A hyp_fsn_1
  have p0007 :=
    @g_feu y (syn_csn A) (syn_csn B) A F dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0008 :=
    @g_mpan2 (syn_wf F (syn_csn A) (syn_csn B)) (.classMem A (syn_csn A))
      (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F)) p0006 p0007
  have p0009 :=
    @g_anbi1i (.classMem (.cv y) (syn_csn B)) (.classEq (.cv y) B)
      (.classMem (syn_cop A (.cv y)) F) p0002
  have p0010 := @g_opeq2 (.cv y) B A
  have p0011 := @g_eleq1d (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) F p0010
  have p0012 :=
    @g_pm5_32i (.classEq (.cv y) B) (.classMem (syn_cop A (.cv y)) F)
      (.classMem (syn_cop A B) F) p0011
  have p0013 := @g_ancom (.classMem (syn_cop A B) F) (.classEq (.cv y) B)
  have p0014 :=
    @g_bitr4i (syn_wa (.classEq (.cv y) B) (.classMem (syn_cop A (.cv y)) F))
      (syn_wa (.classEq (.cv y) B) (.classMem (syn_cop A B) F))
      (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B)) p0012 p0013
  have p0015 :=
    @g_bitr2i (syn_wa (.classMem (.cv y) (syn_csn B)) (.classMem (syn_cop A (.cv y)) F))
      (syn_wa (.classEq (.cv y) B) (.classMem (syn_cop A (.cv y)) F))
      (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B)) p0009 p0014
  have p0016 :=
    @g_eubii (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B))
      (syn_wa (.classMem (.cv y) (syn_csn B)) (.classMem (syn_cop A (.cv y)) F)) y p0015
  have p0017 := @g_eueq1 y B dv_cache_0002 hyp_fsn_2
  have p0018 :=
    @g_biantru (syn_weu y (.classEq (.cv y) B)) (.classMem (syn_cop A B) F) p0017
  have p0019 := @g_euanv (.classMem (syn_cop A B) F) (.classEq (.cv y) B) y dv_cache_0007
  have p0020 :=
    @g_bitr4i (.classMem (syn_cop A B) F)
      (syn_wa (.classMem (syn_cop A B) F) (syn_weu y (.classEq (.cv y) B)))
      (syn_weu y (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B))) p0018 p0019
  have p0021 :=
    (Nominal.biimpRefl (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F)))
  have p0022 :=
    @g_n_3bitr4i (syn_weu y (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B)))
      (syn_weu y (syn_wa (.classMem (.cv y) (syn_csn B)) (.classMem (syn_cop A (.cv y)) F)))
      (.classMem (syn_cop A B) F)
      (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F)) p0016 p0020 p0021
  have p0023 :=
    @g_sylibr (syn_wf F (syn_csn A) (syn_csn B))
      (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F))
      (.classMem (syn_cop A B) F) p0008 p0022
  have p0024 := @g_opeq12 (.cv x) A (.cv y) B
  have p0025 :=
    @g_eleq1d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_cop (.cv x) (.cv y))
      (syn_cop A B) F p0024
  have p0026 :=
    @g_syl5ibrcom (syn_wf F (syn_csn A) (syn_csn B))
      (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classMem (syn_cop A B) F) p0023
      p0025
  have p0027 :=
    @g_impbid (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0005 p0026
  have p0028 := @g_vex x
  have p0029 := @g_vex y
  have p0030 := @g_opex (.cv x) (.cv y) p0028 p0029
  have p0031 := @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop A B) p0030
  have p0032 := @g_opth (.cv x) (.cv y) A B
  have p0033 :=
    @g_bitr2i (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0031 p0032
  have p0034 :=
    @g_syl6bb (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B))) p0027 p0033
  have p0035 :=
    @g_eqrelrdv (syn_wf F (syn_csn A) (syn_csn B)) x y F (syn_csn (syn_cop A B))
      dv_cache_0008 dv_cache_0006 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0034
  have p0036 := @g_f1osn A B hyp_fsn_1 hyp_fsn_2
  have p0037 := @g_f1oeq1 (syn_csn A) (syn_csn B) F (syn_csn (syn_cop A B))
  have p0038 :=
    @g_mpbiri (.classEq F (syn_csn (syn_cop A B))) (syn_wf1o F (syn_csn A) (syn_csn B))
      (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) p0036 p0037
  have p0039 := @g_f1of (syn_csn A) (syn_csn B) F
  have p0040 :=
    @g_syl (.classEq F (syn_csn (syn_cop A B))) (syn_wf1o F (syn_csn A) (syn_csn B))
      (syn_wf F (syn_csn A) (syn_csn B)) p0038 p0039
  have p0041 :=
    @g_impbii (syn_wf F (syn_csn A) (syn_csn B)) (.classEq F (syn_csn (syn_cop A B)))
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

@[expose]
noncomputable def g_fsn2 (A : Class) (B : Class) (F : Class)
    (hyp_fsn2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wf F (syn_csn A) B) (syn_wa (.classMem (syn_cfv F A) B)
          (.classEq F (syn_csn (syn_cop A (syn_cfv F A)))))) :=
  by
  have p0000 := @g_snid A hyp_fsn2_1
  have p0001 := @g_ffvelrn (syn_csn A) B A F
  have p0002 :=
    @g_mpan2 (syn_wf F (syn_csn A) B) (.classMem A (syn_csn A))
      (.classMem (syn_cfv F A) B) p0000 p0001
  have p0003 := @g_ffn (syn_csn A) B F
  have p0004 := @g_dffn3 (syn_csn A) F
  have p0005 := @g_biimpi (syn_wfn F (syn_csn A)) (syn_wf F (syn_csn A) (syn_crn F)) p0004
  have p0006 := @g_imadmrn F
  have p0007 := @g_fndm (syn_csn A) F
  have p0008 := @g_imaeq2d (syn_wfn F (syn_csn A)) (syn_cdm F) (syn_csn A) F p0007
  have p0009 :=
    @g_syl5eqr (syn_wfn F (syn_csn A)) (syn_crn F) (syn_cima F (syn_cdm F))
      (syn_cima F (syn_csn A)) p0006 p0008
  have p0010 := @g_fnsnfv (syn_csn A) A F
  have p0011 :=
    @g_mpan2 (syn_wfn F (syn_csn A)) (.classMem A (syn_csn A))
      (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0000 p0010
  have p0012 :=
    @g_eqtr4d (syn_wfn F (syn_csn A)) (syn_crn F) (syn_cima F (syn_csn A))
      (syn_csn (syn_cfv F A)) p0009 p0011
  have p0013 := @g_feq3 (syn_crn F) (syn_csn (syn_cfv F A)) (syn_csn A) F
  have p0014 :=
    @g_syl (syn_wfn F (syn_csn A)) (.classEq (syn_crn F) (syn_csn (syn_cfv F A)))
      (syn_wb (syn_wf F (syn_csn A) (syn_crn F)) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))))
      p0012 p0013
  have p0015 :=
    @g_mpbid (syn_wfn F (syn_csn A)) (syn_wf F (syn_csn A) (syn_crn F))
      (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) p0005 p0014
  have p0016 :=
    @g_syl (syn_wf F (syn_csn A) B) (syn_wfn F (syn_csn A))
      (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) p0003 p0015
  have p0017 :=
    @g_jca (syn_wf F (syn_csn A) B) (.classMem (syn_cfv F A) B)
      (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) p0002 p0016
  have p0018 := @g_snssi (syn_cfv F A) B
  have p0019 := @g_fss (syn_csn A) (syn_csn (syn_cfv F A)) B F
  have p0020 :=
    @g_ancoms (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A)))
      (syn_wss (syn_csn (syn_cfv F A)) B) (syn_wf F (syn_csn A) B) p0019
  have p0021 :=
    @g_sylan (.classMem (syn_cfv F A) B) (syn_wss (syn_csn (syn_cfv F A)) B)
      (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) (syn_wf F (syn_csn A) B) p0018 p0020
  have p0022 :=
    @g_impbii (syn_wf F (syn_csn A) B)
      (syn_wa (.classMem (syn_cfv F A) B) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))))
      p0017 p0021
  have p0023 := @g_fvex A F
  have p0024 := @g_fsn A (syn_cfv F A) F hyp_fsn2_1 p0023
  have p0025 :=
    @g_anbi2i (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A)))
      (.classEq F (syn_csn (syn_cop A (syn_cfv F A)))) (.classMem (syn_cfv F A) B) p0024
  have p0026 :=
    @g_bitri (syn_wf F (syn_csn A) B)
      (syn_wa (.classMem (syn_cfv F A) B) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))))
      (syn_wa (.classMem (syn_cfv F A) B) (.classEq F (syn_csn (syn_cop A (syn_cfv F A)))))
      p0022 p0025
  exact p0026

@[expose]
noncomputable def g_ressnop0 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A C)) (.classEq (syn_cres (syn_csn (syn_cop A B)) C) (syn_c0))) :=
  by
  have p0000 := @g_opelxp A B C (syn_cvv)
  have p0001 :=
    @g_simplbi (.classMem (syn_cop A B) (syn_cxp C (syn_cvv))) (.classMem A C)
      (.classMem B (syn_cvv)) p0000
  have p0002 :=
    @g_con3i (.classMem (syn_cop A B) (syn_cxp C (syn_cvv))) (.classMem A C) p0001
  have p0003 := (Nominal.classEqRefl (syn_cres (syn_csn (syn_cop A B)) C))
  have p0004 := @g_incom (syn_csn (syn_cop A B)) (syn_cxp C (syn_cvv))
  have p0005 :=
    @g_eqtri (syn_cres (syn_csn (syn_cop A B)) C)
      (syn_cin (syn_csn (syn_cop A B)) (syn_cxp C (syn_cvv)))
      (syn_cin (syn_cxp C (syn_cvv)) (syn_csn (syn_cop A B))) p0003 p0004
  have p0006 := @g_disjsn (syn_cxp C (syn_cvv)) (syn_cop A B)
  have p0007 :=
    @g_biimpri (.classEq (syn_cin (syn_cxp C (syn_cvv)) (syn_csn (syn_cop A B))) (syn_c0))
      (.neg (.classMem (syn_cop A B) (syn_cxp C (syn_cvv)))) p0006
  have p0008 :=
    @g_syl5eq (.neg (.classMem (syn_cop A B) (syn_cxp C (syn_cvv))))
      (syn_cres (syn_csn (syn_cop A B)) C)
      (syn_cin (syn_cxp C (syn_cvv)) (syn_csn (syn_cop A B))) (syn_c0) p0005 p0007
  have p0009 :=
    @g_syl (.neg (.classMem A C)) (.neg (.classMem (syn_cop A B) (syn_cxp C (syn_cvv))))
      (.classEq (syn_cres (syn_csn (syn_cop A B)) C) (syn_c0)) p0002 p0008
  exact p0009

@[expose]
noncomputable def g_fvconst (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf F A (syn_csn B)) (.classMem C A)) (.classEq (syn_cfv F C) B)) :=
  by
  have p0000 := @g_ffvelrn A (syn_csn B) C F
  have p0001 := @g_elsni (syn_cfv F C) B
  have p0002 :=
    @g_syl (syn_wa (syn_wf F A (syn_csn B)) (.classMem C A))
      (.classMem (syn_cfv F C) (syn_csn B)) (.classEq (syn_cfv F C) B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fvi (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cfv (syn_cid) A) A)) :=
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
  have dv_cache_0002 : x ∉ ((Wff.classEq (syn_cfv (syn_cid) A) A)).fv :=
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
  have p0000 := @g_fveq2 (.cv x) A (syn_cid)
  have p0001 := @g_id (.classEq (.cv x) A)
  have p0002 :=
    @g_eqeq12d (.classEq (.cv x) A) (syn_cfv (syn_cid) (.cv x)) (syn_cfv (syn_cid) A)
      (.cv x) A p0000 p0001
  have p0003 := @g_funi
  have p0004 := @g_dmi
  have p0005 := (Nominal.biimpRefl (syn_wfn (syn_cid) (syn_cvv)))
  have p0006 :=
    @g_mpbir2an (syn_wfn (syn_cid) (syn_cvv)) (syn_wfun (syn_cid))
      (.classEq (syn_cdm (syn_cid)) (syn_cvv)) p0003 p0004 p0005
  have p0007 := @g_vex x
  have p0008 := @g_equid x
  have p0009 := @g_ideq (.cv x) (.cv x) p0007
  have p0010 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv x)))
  have p0011_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv x)) (.objEq x x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
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
    @g_bitr3i (.objEq x x) (syn_wbr (.cv x) (syn_cid) (.cv x))
      (.classMem (syn_cop (.cv x) (.cv x)) (syn_cid)) p0011_e00_recanon p0010
  have p0012 :=
    @g_mpbi (.objEq x x) (.classMem (syn_cop (.cv x) (.cv x)) (syn_cid)) p0008 p0011
  have p0013 := @g_fnopfvb (syn_cvv) (.cv x) (.cv x) (syn_cid)
  have p0014 :=
    @g_mpbiri (syn_wa (syn_wfn (syn_cid) (syn_cvv)) (.classMem (.cv x) (syn_cvv)))
      (.classEq (syn_cfv (syn_cid) (.cv x)) (.cv x))
      (.classMem (syn_cop (.cv x) (.cv x)) (syn_cid)) p0012 p0013
  have p0015 :=
    @g_mp2an (syn_wfn (syn_cid) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (.classEq (syn_cfv (syn_cid) (.cv x)) (.cv x)) p0006 p0007 p0014
  have p0016 :=
    @g_vtoclg (.classEq (syn_cfv (syn_cid) (.cv x)) (.cv x))
      (.classEq (syn_cfv (syn_cid) A) A) x A V dv_cache_0001 dv_cache_0002 p0002 p0015
  exact p0016

@[expose]
noncomputable def g_fvresi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (.classEq (syn_cfv (syn_cres (syn_cid) A) B) B)) :=
  by
  have p0000 := @g_fvres B A (syn_cid)
  have p0001 := @g_fvi B A
  have p0002 :=
    @g_eqtrd (.classMem B A) (syn_cfv (syn_cres (syn_cid) A) B) (syn_cfv (syn_cid) B) B
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fvunsn (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wne B D)
        (.classEq (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D) (syn_cfv A D))) :=
  by
  have p0000 := @g_resundir A (syn_csn (syn_cop B C)) (syn_csn D)
  have p0001 := @g_elsni B D
  have p0002 := @g_necon3ai (.classMem B (syn_csn D)) B D p0001
  have p0003 := @g_ressnop0 B C (syn_csn D)
  have p0004 :=
    @g_syl (syn_wne B D) (.neg (.classMem B (syn_csn D)))
      (.classEq (syn_cres (syn_csn (syn_cop B C)) (syn_csn D)) (syn_c0)) p0002 p0003
  have p0005 :=
    @g_uneq2d (syn_wne B D) (syn_cres (syn_csn (syn_cop B C)) (syn_csn D)) (syn_c0)
      (syn_cres A (syn_csn D)) p0004
  have p0006 := @g_un0 (syn_cres A (syn_csn D))
  have p0007 :=
    @g_syl6eq (syn_wne B D)
      (syn_cun (syn_cres A (syn_csn D)) (syn_cres (syn_csn (syn_cop B C)) (syn_csn D)))
      (syn_cun (syn_cres A (syn_csn D)) (syn_c0)) (syn_cres A (syn_csn D)) p0005 p0006
  have p0008 :=
    @g_syl5eq (syn_wne B D) (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D))
      (syn_cun (syn_cres A (syn_csn D)) (syn_cres (syn_csn (syn_cop B C)) (syn_csn D)))
      (syn_cres A (syn_csn D)) p0000 p0007
  have p0009 :=
    @g_fveq1d (syn_wne B D) D (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D))
      (syn_cres A (syn_csn D)) p0008
  have p0010 := @g_snidg D (syn_cvv)
  have p0011 := @g_fvres D (syn_csn D) (syn_cun A (syn_csn (syn_cop B C)))
  have p0012 :=
    @g_syl (.classMem D (syn_cvv)) (.classMem D (syn_csn D))
      (.classEq (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D)
        (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D))
      p0010 p0011
  have p0013 := @g_fvprc D (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D))
  have p0014 := @g_fvprc D (syn_cun A (syn_csn (syn_cop B C)))
  have p0015 :=
    @g_eqtr4d (.neg (.classMem D (syn_cvv)))
      (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D) (syn_c0)
      (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D) p0013 p0014
  have p0016 :=
    @g_pm2_61i (.classMem D (syn_cvv))
      (.classEq (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D)
        (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D))
      p0012 p0015
  have p0017 := @g_fvres D (syn_csn D) A
  have p0018 :=
    @g_syl (.classMem D (syn_cvv)) (.classMem D (syn_csn D))
      (.classEq (syn_cfv (syn_cres A (syn_csn D)) D) (syn_cfv A D)) p0010 p0017
  have p0019 := @g_fvprc D (syn_cres A (syn_csn D))
  have p0020 := @g_fvprc D A
  have p0021 :=
    @g_eqtr4d (.neg (.classMem D (syn_cvv))) (syn_cfv (syn_cres A (syn_csn D)) D) (syn_c0)
      (syn_cfv A D) p0019 p0020
  have p0022 :=
    @g_pm2_61i (.classMem D (syn_cvv))
      (.classEq (syn_cfv (syn_cres A (syn_csn D)) D) (syn_cfv A D)) p0018 p0021
  have p0023 :=
    @g_n_3eqtr3g (syn_wne B D)
      (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D)
      (syn_cfv (syn_cres A (syn_csn D)) D) (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D)
      (syn_cfv A D) p0009 p0016 p0022
  exact p0023

@[expose]
noncomputable def g_fvconst2g (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B D) (.classMem C A))
        (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B)) :=
  by
  have p0000 := @g_fconstg A B D
  have p0001 := @g_fvconst A B C (syn_cxp A (syn_csn B))
  have p0002 :=
    @g_sylan (.classMem B D) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))
      (.classMem C A) (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fvconst2 (A : Class) (B : Class) (C : Class)
    (hyp_fvconst2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem C A) (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B)) :=
  by
  have p0000 := @g_fvconst2g A B C (syn_cvv)
  have p0001 :=
    @g_mpan (.classMem B (syn_cvv)) (.classMem C A)
      (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B) hyp_fvconst2_1 p0000
  exact p0001

@[expose]
noncomputable def g_funfvima (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem B (syn_cdm F)))
        (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A)))) :=
  by
  have p0000 := @g_dmres F A
  have p0001 := @g_eleq2i (syn_cdm (syn_cres F A)) (syn_cin A (syn_cdm F)) B p0000
  have p0002 := @g_elin B A (syn_cdm F)
  have p0003 :=
    @g_bitri (.classMem B (syn_cdm (syn_cres F A))) (.classMem B (syn_cin A (syn_cdm F)))
      (syn_wa (.classMem B A) (.classMem B (syn_cdm F))) p0001 p0002
  have p0004 := @g_funres A F
  have p0005 := @g_fvelrn B (syn_cres F A)
  have p0006 :=
    @g_sylan (syn_wfun F) (syn_wfun (syn_cres F A)) (.classMem B (syn_cdm (syn_cres F A)))
      (.classMem (syn_cfv (syn_cres F A) B) (syn_crn (syn_cres F A))) p0004 p0005
  have p0007 := @g_fvres B A F
  have p0008 :=
    @g_eleq1d (.classMem B A) (syn_cfv (syn_cres F A) B) (syn_cfv F B)
      (syn_crn (syn_cres F A)) p0007
  have p0009 := @g_dfima3 F A
  have p0010 := @g_eleq2i (syn_cima F A) (syn_crn (syn_cres F A)) (syn_cfv F B) p0009
  have p0011 :=
    @g_syl6rbbr (.classMem B A)
      (.classMem (syn_cfv (syn_cres F A) B) (syn_crn (syn_cres F A)))
      (.classMem (syn_cfv F B) (syn_crn (syn_cres F A)))
      (.classMem (syn_cfv F B) (syn_cima F A)) p0008 p0010
  have p0012 :=
    @g_syl5ibrcom (syn_wa (syn_wfun F) (.classMem B (syn_cdm (syn_cres F A))))
      (.classMem (syn_cfv F B) (syn_cima F A)) (.classMem B A)
      (.classMem (syn_cfv (syn_cres F A) B) (syn_crn (syn_cres F A))) p0006 p0011
  have p0013 :=
    @g_ex (syn_wfun F) (.classMem B (syn_cdm (syn_cres F A)))
      (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0012
  have p0014 :=
    @g_syl5bir (syn_wa (.classMem B A) (.classMem B (syn_cdm F)))
      (.classMem B (syn_cdm (syn_cres F A))) (syn_wfun F)
      (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0003 p0013
  have p0015 :=
    @g_exp3a (syn_wfun F) (.classMem B A) (.classMem B (syn_cdm F))
      (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0014
  have p0016 :=
    @g_com12 (syn_wfun F) (.classMem B A)
      (.imp (.classMem B (syn_cdm F))
        (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))))
      p0015
  have p0017 :=
    @g_imp3a (.classMem B A) (syn_wfun F) (.classMem B (syn_cdm F))
      (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0016
  have p0018 :=
    @g_pm2_43b (syn_wa (syn_wfun F) (.classMem B (syn_cdm F))) (.classMem B A)
      (.classMem (syn_cfv F B) (syn_cima F A)) p0017
  exact p0018

@[expose]
noncomputable def g_fniunfv (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wfn F A)
        (.classEq (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_crn F)))) :=
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
  have dv_cache_0006 : y ∉ ((syn_cfv F (.cv x))).fv :=
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
    @g_fnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @g_unieqd (syn_wfn F A) (syn_crn F)
      (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0000
  have p0002 := @g_fvex (.cv x) F
  have p0003 :=
    @g_dfiun2 x y A (syn_cfv F (.cv x)) dv_cache_0002 dv_cache_0006 dv_cache_0005 p0002
  have p0004 :=
    @g_syl6reqr (syn_wfn F A) (syn_cuni (syn_crn F))
      (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))
      (syn_ciun x A (syn_cfv F (.cv x))) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_funiunfv (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wfun F)
        (.classEq (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_cima F A)))) :=
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
  have dv_cache_0003 : z ∉ ((syn_cfv F (.cv y))).fv :=
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
  have dv_cache_0004 : y ∉ ((syn_cfv F (.cv x))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cfv F (.cv x))).fv :=
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
      ((syn_copab y z
          (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))).fv :=
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
  have dv_cache_0011 : y ∉ ((syn_wa (syn_wfun F) (.objMem w z))).fv :=
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
  have dv_cache_0012 : z ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0014 : z ∉ ((syn_cima F A)).fv :=
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
    w ∉ ((syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))).fv :=
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
  have dv_cache_0018 : w ∉ ((syn_cuni (syn_cima F A))).fv :=
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
  have dv_cache_0019 : w ∉ ((syn_wfun F)).fv :=
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
  have p0000 := @g_fveq2 (.cv y) (.cv x) F
  have p0001 :=
    @g_eqid
      (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))
  have p0002 := @g_fvex (.cv x) F
  have p0003 :=
    @g_fvopab4 y z (.cv x) (syn_cfv F (.cv y)) (syn_cfv F (.cv x)) A
      (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0000 p0001 p0002
  have p0004 :=
    @g_iuneq2i x A
      (syn_cfv (syn_copab y z
          (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.cv x))
      (syn_cfv F (.cv x)) p0003
  have p0005 := @g_fvex (.cv y) F
  have p0006 :=
    @g_fnopab2 y z A (syn_cfv F (.cv y))
      (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))
      dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 p0005 p0001
  have p0007 :=
    @g_fniunfv x A
      (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))
      dv_cache_0009 dv_cache_0010
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_eqtr3i
      (syn_ciun x A (syn_cfv (syn_copab y z
            (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.cv x)))
      (syn_ciun x A (syn_cfv F (.cv x)))
      (syn_cuni (syn_crn (syn_copab y z
            (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))))
      p0004 p0008
  have p0010 := @g_rnopab2 y z A (syn_cfv F (.cv y)) dv_cache_0008
  have p0011 :=
    @g_unieqi
      (syn_crn (syn_copab y z
          (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))))
      (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))) p0010
  have p0012 := @g_eqcom (.cv z) (syn_cfv F (.cv y))
  have p0013 :=
    @g_idd (syn_wa (syn_wfun F) (.objMem w z)) (.classEq (syn_cfv F (.cv y)) (.cv z))
  have p0014 := @g_funbrfv (.cv y) (.cv z) F
  have p0015 :=
    @g_adantr (syn_wfun F)
      (.imp (syn_wbr (.cv y) F (.cv z)) (.classEq (syn_cfv F (.cv y)) (.cv z)))
      (.objMem w z) p0014
  have p0016 := @g_n0i (.cv z) (.cv w)
  have p0017 := @g_ndmfv (.cv y) F
  have p0018 := @g_eqeq1 (syn_cfv F (.cv y)) (.cv z) (syn_c0)
  have p0019 :=
    @g_syl5ib (.neg (.classMem (.cv y) (syn_cdm F)))
      (.classEq (syn_cfv F (.cv y)) (syn_c0)) (.classEq (syn_cfv F (.cv y)) (.cv z))
      (.classEq (.cv z) (syn_c0)) p0017 p0018
  have p0020 :=
    @g_con1d (.classEq (syn_cfv F (.cv y)) (.cv z)) (.classMem (.cv y) (syn_cdm F))
      (.classEq (.cv z) (syn_c0)) p0019
  have p0021_e00_recanon :
    Nominal.NPrf (.imp (.objMem w z) (.neg (.classEq (.cv z) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0021 :=
    @g_mpan9 (.objMem w z) (.neg (.classEq (.cv z) (syn_c0)))
      (.classEq (syn_cfv F (.cv y)) (.cv z)) (.classMem (.cv y) (syn_cdm F))
      p0021_e00_recanon p0020
  have p0022 := @g_funbrfvb (.cv y) (.cv z) F
  have p0023 :=
    @g_sylan2 (syn_wa (.objMem w z) (.classEq (syn_cfv F (.cv y)) (.cv z))) (syn_wfun F)
      (.classMem (.cv y) (syn_cdm F))
      (syn_wb (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wbr (.cv y) F (.cv z))) p0021
      p0022
  have p0024 :=
    @g_expr (syn_wfun F) (.objMem w z) (.classEq (syn_cfv F (.cv y)) (.cv z))
      (syn_wb (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wbr (.cv y) F (.cv z))) p0023
  have p0025 :=
    @g_pm5_21ndd (syn_wa (syn_wfun F) (.objMem w z))
      (.classEq (syn_cfv F (.cv y)) (.cv z)) (.classEq (syn_cfv F (.cv y)) (.cv z))
      (syn_wbr (.cv y) F (.cv z)) p0013 p0015 p0024
  have p0026 :=
    @g_syl5bb (.classEq (.cv z) (syn_cfv F (.cv y)))
      (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wa (syn_wfun F) (.objMem w z))
      (syn_wbr (.cv y) F (.cv z)) p0012 p0025
  have p0027 :=
    @g_rexbidv (syn_wa (syn_wfun F) (.objMem w z)) (.classEq (.cv z) (syn_cfv F (.cv y)))
      (syn_wbr (.cv y) F (.cv z)) y A dv_cache_0011 p0026
  have p0028 :=
    @g_pm5_32da (syn_wfun F) (.objMem w z)
      (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))
      (syn_wrex y A (syn_wbr (.cv y) F (.cv z))) p0027
  have p0029 :=
    @g_exbidv (syn_wfun F)
      (syn_wa (.objMem w z) (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))))
      (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z)))) z dv_cache_0012
      p0028
  have p0030 :=
    @g_eluniab (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))) z (.cv w)
      dv_cache_0013
  have p0031 := @g_eluni z (.cv w) (syn_cima F A) dv_cache_0013 dv_cache_0014
  have p0032 := @g_elima y (.cv z) F A dv_cache_0015 dv_cache_0016 dv_cache_0006
  have p0033 :=
    @g_anbi2i (.classMem (.cv z) (syn_cima F A))
      (syn_wrex y A (syn_wbr (.cv y) F (.cv z))) (.objMem w z) p0032
  have p0034 :=
    @g_exbii (syn_wa (.objMem w z) (.classMem (.cv z) (syn_cima F A)))
      (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z)))) z p0033
  have p0035_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv w) (syn_cuni (syn_cima F A)))
        (syn_wex z (syn_wa (.objMem w z) (.classMem (.cv z) (syn_cima F A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_cima syn_wrex syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl
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
    @g_bitri (.classMem (.cv w) (syn_cuni (syn_cima F A)))
      (syn_wex z (syn_wa (.objMem w z) (.classMem (.cv z) (syn_cima F A))))
      (syn_wex z (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z)))))
      p0035_e00_recanon p0034
  have p0036_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv w)
          (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))) (syn_wex z
          (syn_wa (.objMem w z) (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_wrex syn_cfv syn_cio syn_wbr syn_cop
          syn_cun syn_cnin syn_wnan syn_ccompl
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
    @g_n_3bitr4g (syn_wfun F)
      (syn_wex z (syn_wa (.objMem w z) (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))
      (syn_wex z (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z)))))
      (.classMem (.cv w)
        (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))))))
      (.classMem (.cv w) (syn_cuni (syn_cima F A))) p0029 p0036_e01_recanon p0035
  have p0037 :=
    @g_eqrdv (syn_wfun F) w
      (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))
      (syn_cuni (syn_cima F A)) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0036
  have p0038 :=
    @g_syl5eq (syn_wfun F)
      (syn_cuni (syn_crn (syn_copab y z
            (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))))
      (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))
      (syn_cuni (syn_cima F A)) p0011 p0037
  have p0039 :=
    @g_syl5eq (syn_wfun F) (syn_ciun x A (syn_cfv F (.cv x)))
      (syn_cuni (syn_crn (syn_copab y z
            (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))))
      (syn_cuni (syn_cima F A)) p0009 p0038
  exact p0039

@[expose]
noncomputable def g_eluniima (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wfun F) (syn_wb (.classMem B (syn_cuni (syn_cima F A)))
          (syn_wrex x A (.classMem B (syn_cfv F (.cv x)))))) :=
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
  have p0000 := @g_eliun x B A (syn_cfv F (.cv x)) dv_cache_0001
  have p0001 := @g_funiunfv x A F dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_eleq2d (syn_wfun F) (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_cima F A)) B
      p0001
  have p0003 :=
    @g_syl5rbbr (syn_wrex x A (.classMem B (syn_cfv F (.cv x))))
      (.classMem B (syn_ciun x A (syn_cfv F (.cv x)))) (syn_wfun F)
      (.classMem B (syn_cuni (syn_cima F A))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_elunirn (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wfun F) (syn_wb (.classMem A (syn_cuni (syn_crn F)))
          (syn_wrex x (syn_cdm F) (.classMem A (syn_cfv F (.cv x)))))) :=
  by
  have dv_cache_0001 : x ∉ ((syn_cdm F)).fv := by
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
  have p0000 := @g_imadmrn F
  have p0001 := @g_unieqi (syn_cima F (syn_cdm F)) (syn_crn F) p0000
  have p0002 :=
    @g_eleq2i (syn_cuni (syn_cima F (syn_cdm F))) (syn_cuni (syn_crn F)) A p0001
  have p0003 := @g_eluniima x (syn_cdm F) A F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_syl5bbr (.classMem A (syn_cuni (syn_crn F)))
      (.classMem A (syn_cuni (syn_cima F (syn_cdm F)))) (syn_wfun F)
      (syn_wrex x (syn_cdm F) (.classMem A (syn_cfv F (.cv x)))) p0002 p0003
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

@[expose]
noncomputable def g_dff13 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A
              (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))))) :=
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
  have dv_cache_0004 : z ∉ ((syn_wfn F A)).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))).fv :=
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
  have dv_cache_0007 : z ∉ ((syn_cfv F (.cv x))).fv :=
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
  have dv_cache_0008 : z ∉ ((syn_cfv F (.cv y))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_wfn F A)).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_wfn F A)).fv :=
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
  have dv_cache_0011 : y ∉ ((syn_wbr (.cv x) F (.cv z))).fv :=
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
  have dv_cache_0012 : x ∉ ((syn_wbr (.cv y) F (.cv z))).fv :=
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
  have p0000 := @g_dff12 x z A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_ffn A B F
  have p0002 := @g_breldm (.cv x) (.cv z) F
  have p0003 := @g_fndm A F
  have p0004 := @g_eleq2d (syn_wfn F A) (syn_cdm F) A (.cv x) p0003
  have p0005 :=
    @g_syl5ib (syn_wbr (.cv x) F (.cv z)) (.classMem (.cv x) (syn_cdm F)) (syn_wfn F A)
      (.classMem (.cv x) A) p0002 p0004
  have p0006 := @g_breldm (.cv y) (.cv z) F
  have p0007 := @g_eleq2d (syn_wfn F A) (syn_cdm F) A (.cv y) p0003
  have p0008 :=
    @g_syl5ib (syn_wbr (.cv y) F (.cv z)) (.classMem (.cv y) (syn_cdm F)) (syn_wfn F A)
      (.classMem (.cv y) A) p0006 p0007
  have p0009 :=
    @g_anim12d (syn_wfn F A) (syn_wbr (.cv x) F (.cv z)) (.classMem (.cv x) A)
      (syn_wbr (.cv y) F (.cv z)) (.classMem (.cv y) A) p0005 p0008
  have p0010 :=
    @g_pm4_71rd (syn_wfn F A)
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) p0009
  have p0011 := @g_eqcom (.cv z) (syn_cfv F (.cv x))
  have p0012 := @g_fnbrfvb A (.cv x) (.cv z) F
  have p0013 :=
    @g_syl5bb (.classEq (.cv z) (syn_cfv F (.cv x)))
      (.classEq (syn_cfv F (.cv x)) (.cv z)) (syn_wa (syn_wfn F A) (.classMem (.cv x) A))
      (syn_wbr (.cv x) F (.cv z)) p0011 p0012
  have p0014 := @g_eqcom (.cv z) (syn_cfv F (.cv y))
  have p0015 := @g_fnbrfvb A (.cv y) (.cv z) F
  have p0016 :=
    @g_syl5bb (.classEq (.cv z) (syn_cfv F (.cv y)))
      (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wa (syn_wfn F A) (.classMem (.cv y) A))
      (syn_wbr (.cv y) F (.cv z)) p0014 p0015
  have p0017 :=
    @g_bi2anan9 (syn_wa (syn_wfn F A) (.classMem (.cv x) A))
      (.classEq (.cv z) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv z))
      (syn_wa (syn_wfn F A) (.classMem (.cv y) A)) (.classEq (.cv z) (syn_cfv F (.cv y)))
      (syn_wbr (.cv y) F (.cv z)) p0013 p0016
  have p0018 :=
    @g_anandis (syn_wfn F A) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (syn_wb (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
          (.classEq (.cv z) (syn_cfv F (.cv y))))
        (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))))
      p0017
  have p0019 :=
    @g_pm5_32da (syn_wfn F A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) p0018
  have p0020 :=
    @g_bitr4d (syn_wfn F A)
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))))
      p0010 p0019
  have p0021 :=
    @g_imbi1d (syn_wfn F A)
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))))
      (.objEq x y) p0020
  have p0022 :=
    @g_impexp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))
      (.objEq x y)
  have p0023 :=
    @g_syl6bb (syn_wfn F A)
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))
      (.imp (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
          (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
            (.classEq (.cv z) (syn_cfv F (.cv y))))) (.objEq x y))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
          (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))
          (.objEq x y)))
      p0021 p0022
  have p0024 :=
    @g_albidv (syn_wfn F A)
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
          (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))
          (.objEq x y)))
      z dv_cache_0004 p0023
  have p0025 :=
    @g_n_19_21v (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
          (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))
      z dv_cache_0005
  have p0026 :=
    @g_n_19_23v
      (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))
      (.objEq x y) z dv_cache_0006
  have p0027 := @g_fvex (.cv x) F
  have p0028 :=
    @g_eqvinc z (syn_cfv F (.cv x)) (syn_cfv F (.cv y)) dv_cache_0007 dv_cache_0008 p0027
  have p0029 :=
    @g_imbi1i (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
          (.classEq (.cv z) (syn_cfv F (.cv y)))))
      (.objEq x y) p0028
  have p0030 :=
    @g_bitr4i
      (.all z (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
            (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y)))
      (.imp (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
            (.classEq (.cv z) (syn_cfv F (.cv y))))) (.objEq x y))
      (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)) p0026 p0029
  have p0031 :=
    @g_imbi2i
      (.all z (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
            (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y)))
      (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) p0030
  have p0032 :=
    @g_bitri
      (.all z (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
            (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
              (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.all z (.imp
            (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
              (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))
      p0025 p0031
  have p0033 :=
    @g_syl6bb (syn_wfn F A)
      (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
          (.objEq x y)))
      (.all z (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp
            (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x)))
              (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))
      p0024 p0032
  have p0034 :=
    @g_n_2albidv (syn_wfn F A)
      (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
          (.objEq x y)))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))
      x y dv_cache_0009 dv_cache_0010 p0033
  have p0035 := @g_breq1 (.cv x) (.cv y) (.cv z) F
  have p0036_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))) :=
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
    @g_mo4 (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)) x y dv_cache_0011
      dv_cache_0012 dv_cache_0013 p0036_e00_recanon
  have p0037 :=
    @g_albii (syn_wmo x (syn_wbr (.cv x) F (.cv z)))
      (.all x (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
            (.objEq x y))))
      z p0036
  have p0038 :=
    @g_alcom
      (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
          (.objEq x y)))
      z x
  have p0039 :=
    @g_alcom
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))
      z y
  have p0040 :=
    @g_albii
      (.all z (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
            (.objEq x y))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
            (.objEq x y))))
      x p0039
  have p0041 :=
    @g_n_3bitri (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z))))
      (.all z (.all x (.all y
            (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      (.all x (.all z (.all y
            (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      p0037 p0038 p0040
  have p0042 :=
    @g_r2al (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)) x y A A
      dv_cache_0014 dv_cache_0013
  have p0043 :=
    @g_n_3bitr4g (syn_wfn F A)
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))
              (.objEq x y)))))
      (.all x (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
            (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))))
      (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z))))
      (syn_wral x A (syn_wral y A
          (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))))
      p0034 p0041 p0042
  have p0044 :=
    @g_syl (syn_wf F A B) (syn_wfn F A)
      (syn_wb (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z)))) (syn_wral x A (syn_wral y A
            (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))))
      p0001 p0043
  have p0045 :=
    @g_pm5_32i (syn_wf F A B) (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z))))
      (syn_wral x A (syn_wral y A
          (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))))
      p0044
  have p0046 :=
    @g_bitri (syn_wf1 F A B)
      (syn_wa (syn_wf F A B) (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z)))))
      (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A
            (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))))
      p0000 p0045
  exact p0046

@[expose]
noncomputable def g_f1fveq (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1 F A B) (syn_wa (.classMem C A) (.classMem D A)))
        (syn_wb (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D))) :=
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
      ((Wff.imp (syn_wf1 F A B)
          (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D)))).fv :=
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
      ((Wff.imp (syn_wf1 F A B)
          (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y))))).fv :=
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
  have p0000 := @g_fveq2 (.cv x) C F
  have p0001 :=
    @g_eqeq1d (.classEq (.cv x) C) (syn_cfv F (.cv x)) (syn_cfv F C) (syn_cfv F (.cv y))
      p0000
  have p0002 := @g_eqeq1 (.cv x) C (.cv y)
  have p0003 :=
    @g_imbi12d (.classEq (.cv x) C) (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
      (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))
      (.classEq C (.cv y)) p0001 p0002
  have p0004 :=
    @g_imbi2d (.classEq (.cv x) C)
      (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))
      (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y)))
      (syn_wf1 F A B) p0003
  have p0005 := @g_fveq2 (.cv y) D F
  have p0006 :=
    @g_eqeq2d (.classEq (.cv y) D) (syn_cfv F (.cv y)) (syn_cfv F D) (syn_cfv F C) p0005
  have p0007 := @g_eqeq2 (.cv y) D C
  have p0008 :=
    @g_imbi12d (.classEq (.cv y) D) (.classEq (syn_cfv F C) (syn_cfv F (.cv y)))
      (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C (.cv y)) (.classEq C D) p0006
      p0007
  have p0009 :=
    @g_imbi2d (.classEq (.cv y) D)
      (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y)))
      (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D)) (syn_wf1 F A B) p0008
  have p0010 :=
    @g_dff13 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0011_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A
              (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
                (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid
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
    @g_simprbi (syn_wf1 F A B) (syn_wf F A B)
      (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      p0011_e00_recanon
  have p0012 :=
    @g_rsp2
      (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))
      x y A A
  have p0013 :=
    @g_syl (syn_wf1 F A B)
      (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
        (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))
      p0011 p0012
  have p0014 :=
    @g_com12 (syn_wf1 F A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))
      p0013
  have p0015 :=
    @g_vtocl2ga
      (.imp (syn_wf1 F A B) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
          (.classEq (.cv x) (.cv y))))
      (.imp (syn_wf1 F A B)
        (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y))))
      (.imp (syn_wf1 F A B) (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D)))
      x y C D A A dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0001 dv_cache_0002
      dv_cache_0001 dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0005 p0004 p0009
      p0014
  have p0016 :=
    @g_impcom (syn_wa (.classMem C A) (.classMem D A)) (syn_wf1 F A B)
      (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D)) p0015
  have p0017 := @g_fveq2 C D F
  have p0018 :=
    @g_impbid1 (syn_wa (syn_wf1 F A B) (syn_wa (.classMem C A) (.classMem D A)))
      (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D) p0016 p0017
  exact p0018

@[expose]
noncomputable def g_f1elima (A : Class) (B : Class) (F : Class) (X : Class) (Y : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wf1 F A B) (.classMem X A) (syn_wss Y A))
        (syn_wb (.classMem (syn_cfv F X) (syn_cima F Y)) (.classMem X Y))) :=
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
  have dv_cache_0002 : z ∉ ((syn_cfv F X)).fv :=
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
    z ∉ ((syn_wa (syn_wa (syn_wf1 F A B) (.classMem X A)) (syn_wss Y A))).fv :=
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
  have dv_cache_0007 : z ∉ ((Wff.classEq (syn_cfv F X) (syn_cfv F X))).fv :=
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
  have p0000 := @g_f1fn A B F
  have p0001 :=
    @g_fvelimab z A Y (syn_cfv F X) F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_sylan (syn_wf1 F A B) (syn_wfn F A) (syn_wss Y A)
      (syn_wb (.classMem (syn_cfv F X) (syn_cima F Y))
        (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))))
      p0000 p0001
  have p0003 :=
    @g_n_3adant2 (syn_wf1 F A B) (syn_wss Y A)
      (syn_wb (.classMem (syn_cfv F X) (syn_cima F Y))
        (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))))
      (.classMem X A) p0002
  have p0004 := @g_ssel Y A (.cv z)
  have p0005 := @g_impac (syn_wss Y A) (.classMem (.cv z) Y) (.classMem (.cv z) A) p0004
  have p0006 := @g_f1fveq A B (.cv z) X F
  have p0007 :=
    @g_ancom2s (syn_wf1 F A B) (.classMem (.cv z) A) (.classMem X A)
      (syn_wb (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X)) p0006
  have p0008 :=
    @g_biimpd (syn_wa (syn_wf1 F A B) (syn_wa (.classMem X A) (.classMem (.cv z) A)))
      (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X) p0007
  have p0009 :=
    @g_anassrs (syn_wf1 F A B) (.classMem X A) (.classMem (.cv z) A)
      (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X)) p0008
  have p0010 := @g_eleq1 (.cv z) X Y
  have p0011 :=
    @g_biimpcd (.classEq (.cv z) X) (.classMem (.cv z) Y) (.classMem X Y) p0010
  have p0012 :=
    @g_sylan9 (syn_wa (syn_wa (syn_wf1 F A B) (.classMem X A)) (.classMem (.cv z) A))
      (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X)
      (.classMem (.cv z) Y) (.classMem X Y) p0009 p0011
  have p0013 :=
    @g_anasss (syn_wa (syn_wf1 F A B) (.classMem X A)) (.classMem (.cv z) A)
      (.classMem (.cv z) Y)
      (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y)) p0012
  have p0014 :=
    @g_sylan2 (syn_wa (syn_wss Y A) (.classMem (.cv z) Y))
      (syn_wa (syn_wf1 F A B) (.classMem X A))
      (syn_wa (.classMem (.cv z) A) (.classMem (.cv z) Y))
      (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y)) p0005 p0013
  have p0015 :=
    @g_anassrs (syn_wa (syn_wf1 F A B) (.classMem X A)) (syn_wss Y A)
      (.classMem (.cv z) Y)
      (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y)) p0014
  have p0016 :=
    @g_rexlimdva (syn_wa (syn_wa (syn_wf1 F A B) (.classMem X A)) (syn_wss Y A))
      (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y) z Y dv_cache_0004
      dv_cache_0005 p0015
  have p0017 :=
    @g_n_3impa (syn_wf1 F A B) (.classMem X A) (syn_wss Y A)
      (.imp (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) (.classMem X Y))
      p0016
  have p0018 := @g_eqid (syn_cfv F X)
  have p0019 := @g_fveq2 (.cv z) X F
  have p0020 :=
    @g_eqeq1d (.classEq (.cv z) X) (syn_cfv F (.cv z)) (syn_cfv F X) (syn_cfv F X) p0019
  have p0021 :=
    @g_rspcev (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))
      (.classEq (syn_cfv F X) (syn_cfv F X)) z X Y dv_cache_0006 dv_cache_0001
      dv_cache_0007 p0020
  have p0022 :=
    @g_mpan2 (.classMem X Y) (.classEq (syn_cfv F X) (syn_cfv F X))
      (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) p0018 p0021
  have p0023 :=
    @g_impbid1 (syn_w3a (syn_wf1 F A B) (.classMem X A) (syn_wss Y A))
      (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) (.classMem X Y) p0017
      p0022
  have p0024 :=
    @g_bitrd (syn_w3a (syn_wf1 F A B) (.classMem X A) (syn_wss Y A))
      (.classMem (syn_cfv F X) (syn_cima F Y))
      (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) (.classMem X Y) p0003
      p0023
  exact p0024

@[expose]
noncomputable def g_dff1o6 (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wf1o F A B) (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A
            (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
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
  have p0000 := (Nominal.biimpRefl (syn_wf1o F A B))
  have p0001 :=
    @g_dff13 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0002 := (Nominal.biimpRefl (syn_wfo F A B))
  have p0003_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A
              (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
                (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid
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
    @g_anbi12i (syn_wf1 F A B)
      (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A
            (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) p0003_e00_recanon
      p0002
  have p0004 :=
    (Nominal.biimpRefl (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A
          (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
              (.classEq (.cv x) (.cv y)))))))
  have p0005 := @g_eqimss (syn_crn F) B
  have p0006 :=
    @g_anim2i (.classEq (syn_crn F) B) (syn_wss (syn_crn F) B) (syn_wfn F A) p0005
  have p0007 := (Nominal.biimpRefl (syn_wf F A B))
  have p0008 :=
    @g_sylibr (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
      (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wf F A B) p0006 p0007
  have p0009 :=
    @g_pm4_71ri (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wf F A B) p0008
  have p0010 :=
    @g_anbi1i (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
      (syn_wa (syn_wf F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
      (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      p0009
  have p0011 :=
    @g_an32 (syn_wf F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
      (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
            (.classEq (.cv x) (.cv y)))))
  have p0012 :=
    @g_n_3bitrri
      (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A (syn_wral y A
            (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (syn_wa (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wral x A (syn_wral y A
            (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (syn_wa (syn_wa (syn_wf F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
        (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      (syn_wa (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A
              (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
                (.classEq (.cv x) (.cv y)))))) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
      p0004 p0010 p0011
  have p0013 :=
    @g_n_3bitri (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (syn_wfo F A B))
      (syn_wa (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A
              (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
                (.classEq (.cv x) (.cv y)))))) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
      (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A (syn_wral y A
            (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      p0000 p0003 p0012
  exact p0013

@[expose]
noncomputable def g_f1ocnvfv1 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o F A B) (.classMem C A))
        (.classEq (syn_cfv (syn_ccnv F) (syn_cfv F C)) C)) :=
  by
  have p0000 := @g_f1ococnv1 A B F
  have p0001 :=
    @g_fveq1d (syn_wf1o F A B) C (syn_ccom (syn_ccnv F) F) (syn_cres (syn_cid) A) p0000
  have p0002 :=
    @g_adantr (syn_wf1o F A B)
      (.classEq (syn_cfv (syn_ccom (syn_ccnv F) F) C) (syn_cfv (syn_cres (syn_cid) A) C))
      (.classMem C A) p0001
  have p0003 := @g_f1of A B F
  have p0004 := @g_fvco3 A B C (syn_ccnv F) F
  have p0005 :=
    @g_sylan (syn_wf1o F A B) (syn_wf F A B) (.classMem C A)
      (.classEq (syn_cfv (syn_ccom (syn_ccnv F) F) C) (syn_cfv (syn_ccnv F) (syn_cfv F C)))
      p0003 p0004
  have p0006 := @g_fvresi A C
  have p0007 :=
    @g_adantl (.classMem C A) (.classEq (syn_cfv (syn_cres (syn_cid) A) C) C)
      (syn_wf1o F A B) p0006
  have p0008 :=
    @g_n_3eqtr3d (syn_wa (syn_wf1o F A B) (.classMem C A))
      (syn_cfv (syn_ccom (syn_ccnv F) F) C) (syn_cfv (syn_cres (syn_cid) A) C)
      (syn_cfv (syn_ccnv F) (syn_cfv F C)) C p0002 p0005 p0007
  exact p0008

@[expose]
noncomputable def g_f1ocnvfv2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o F A B) (.classMem C B))
        (.classEq (syn_cfv F (syn_cfv (syn_ccnv F) C)) C)) :=
  by
  have p0000 := @g_cnvcnv F
  have p0001 := @g_fveq1i (syn_cfv (syn_ccnv F) C) (syn_ccnv (syn_ccnv F)) F p0000
  have p0002 := @g_f1ocnv A B F
  have p0003 := @g_f1ocnvfv1 B A C (syn_ccnv F)
  have p0004 :=
    @g_sylan (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) (.classMem C B)
      (.classEq (syn_cfv (syn_ccnv (syn_ccnv F)) (syn_cfv (syn_ccnv F) C)) C) p0002 p0003
  have p0005 :=
    @g_syl5eqr (syn_wa (syn_wf1o F A B) (.classMem C B))
      (syn_cfv F (syn_cfv (syn_ccnv F) C))
      (syn_cfv (syn_ccnv (syn_ccnv F)) (syn_cfv (syn_ccnv F) C)) C p0001 p0004
  exact p0005

@[expose]
noncomputable def g_f1ocnvfv (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o F A B) (.classMem C A))
        (.imp (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C))) :=
  by
  have p0000 := @g_fveq2 D (syn_cfv F C) (syn_ccnv F)
  have p0001 :=
    @g_eqcoms (.classEq (syn_cfv (syn_ccnv F) D) (syn_cfv (syn_ccnv F) (syn_cfv F C))) D
      (syn_cfv F C) p0000
  have p0002 := @g_f1ocnvfv1 A B C F
  have p0003 :=
    @g_eqeq2d (syn_wa (syn_wf1o F A B) (.classMem C A))
      (syn_cfv (syn_ccnv F) (syn_cfv F C)) C (syn_cfv (syn_ccnv F) D) p0002
  have p0004 :=
    @g_syl5ib (.classEq (syn_cfv F C) D)
      (.classEq (syn_cfv (syn_ccnv F) D) (syn_cfv (syn_ccnv F) (syn_cfv F C)))
      (syn_wa (syn_wf1o F A B) (.classMem C A)) (.classEq (syn_cfv (syn_ccnv F) D) C)
      p0001 p0003
  exact p0004

@[expose]
noncomputable def g_f1ocnvfvb (A : Class) (B : Class) (C : Class) (D : Class)
    (F : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wf1o F A B) (.classMem C A) (.classMem D B))
        (syn_wb (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C))) :=
  by
  have p0000 := @g_f1ocnvfv A B C D F
  have p0001 :=
    @g_n_3adant3 (syn_wf1o F A B) (.classMem C A)
      (.imp (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C))
      (.classMem D B) p0000
  have p0002 := @g_fveq2 C (syn_cfv (syn_ccnv F) D) F
  have p0003 :=
    @g_eqcoms (.classEq (syn_cfv F C) (syn_cfv F (syn_cfv (syn_ccnv F) D))) C
      (syn_cfv (syn_ccnv F) D) p0002
  have p0004 := @g_f1ocnvfv2 A B D F
  have p0005 :=
    @g_eqeq2d (syn_wa (syn_wf1o F A B) (.classMem D B))
      (syn_cfv F (syn_cfv (syn_ccnv F) D)) D (syn_cfv F C) p0004
  have p0006 :=
    @g_syl5ib (.classEq (syn_cfv (syn_ccnv F) D) C)
      (.classEq (syn_cfv F C) (syn_cfv F (syn_cfv (syn_ccnv F) D)))
      (syn_wa (syn_wf1o F A B) (.classMem D B)) (.classEq (syn_cfv F C) D) p0003 p0005
  have p0007 :=
    @g_n_3adant2 (syn_wf1o F A B) (.classMem D B)
      (.imp (.classEq (syn_cfv (syn_ccnv F) D) C) (.classEq (syn_cfv F C) D))
      (.classMem C A) p0006
  have p0008 :=
    @g_impbid (syn_w3a (syn_wf1o F A B) (.classMem C A) (.classMem D B))
      (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C) p0001 p0007
  exact p0008

@[expose]
noncomputable def g_f1ocnvdm (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o F A B) (.classMem C B)) (.classMem (syn_cfv (syn_ccnv F) C) A)) :=
  by
  have p0000 := @g_f1ocnv A B F
  have p0001 := @g_f1of B A (syn_ccnv F)
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) (syn_wf (syn_ccnv F) B A) p0000
      p0001
  have p0003 := @g_ffvelrn B A C (syn_ccnv F)
  have p0004 :=
    @g_sylan (syn_wf1o F A B) (syn_wf (syn_ccnv F) B A) (.classMem C B)
      (.classMem (syn_cfv (syn_ccnv F) C) A) p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end
