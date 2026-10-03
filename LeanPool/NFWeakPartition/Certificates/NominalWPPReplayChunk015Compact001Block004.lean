/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_frecdomfv (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cdm F))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0001 := @g_eqid (syn_cfrec F I)
  have p0002 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0005 :=
    @g_fnfrec
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_cfrec F I) F I p0001 p0002 p0003 p0004
  have p0007 := @g_elex F (syn_cfuns)
  have p0008 :=
    @g_syl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem F (syn_cfuns)) (.classMem F (syn_cvv)) p0002 p0007
  have p0010 := @g_frecxpg (syn_cfrec F I) F I (syn_cvv) p0001
  have p0011 :=
    @g_syl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem F (syn_cvv))
      (syn_wss (syn_cfrec F I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I))))
      p0008 p0010
  have p0012 :=
    @g_rnss (syn_cfrec F I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I)))
  have p0013 :=
    @g_syl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wss (syn_cfrec F I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I))))
      (syn_wss (syn_crn (syn_cfrec F I))
        (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I)))))
      p0011 p0012
  have p0014 := @g_rnxpss (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I))
  have p0015 :=
    @g_syl6ss
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_crn (syn_cfrec F I))
      (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I))))
      (syn_cun (syn_crn F) (syn_csn I)) p0013 p0014
  have p0018 :=
    @g_snssd
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      I (syn_cdm F) p0003
  have p0019 :=
    @g_unssd
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_crn F) (syn_csn I) (syn_cdm F) p0004 p0018
  have p0020 :=
    @g_sstrd
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_crn (syn_cfrec F I)) (syn_cun (syn_crn F) (syn_csn I)) (syn_cdm F) p0015 p0019
  have p0021 :=
    @g_jca
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wfn (syn_cfrec F I) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec F I)) (syn_cdm F))
      p0005 p0020
  have p0022 := (Nominal.biimpRefl (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)))
  have p0023 :=
    @g_biimpri (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F))
      (syn_wa (syn_wfn (syn_cfrec F I) (syn_cnnc))
        (syn_wss (syn_crn (syn_cfrec F I)) (syn_cdm F)))
      p0022
  have p0024 :=
    @g_syl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wa (syn_wfn (syn_cfrec F I) (syn_cnnc))
        (syn_wss (syn_crn (syn_cfrec F I)) (syn_cdm F)))
      (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) p0021 p0023
  have p0025 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) p0000 p0024
  have p0026 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0027 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) (.classMem N (syn_cnnc)) p0025 p0026
  have p0028 := @g_ffvelrn (syn_cnnc) (syn_cdm F) N (syn_cfrec F I)
  have p0029 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_wa (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) (.classMem N (syn_cnnc)))
      (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cdm F)) p0027 p0028
  exact p0029

@[expose]
noncomputable def g_funeqfix (A : Class) (P : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun P) (syn_wfun Q)
          (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
        (syn_wb (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q)))
          (.classEq (syn_cfv P A) (syn_cfv Q A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ P.fv ∪ Q.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_P : z ∉ P.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_Q : z ∉ Q.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_ccnv P)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_z_not_P,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ (Q).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_Q, not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((syn_w3a (syn_wfun P) (syn_wfun Q)
          (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_P, fresh_z_not_Q, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cfv Q A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_Q, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cfv P A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_P, or_false, not_false_eq_true])
  have p0000 := @g_elfix A (syn_ccom (syn_ccnv P) Q)
  have p0001 :=
    @g_brco z A A (syn_ccnv P) Q dv_cache_0001 dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_bitri (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q)))
      (syn_wbr A (syn_ccom (syn_ccnv P) Q) A)
      (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A))) p0000
      p0001
  have p0003 :=
    @g_a1i
      (syn_wb (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q)))
        (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A))))
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      p0002
  have p0004 :=
    @g_simp2 (syn_wfun P) (syn_wfun Q)
      (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
  have p0005 :=
    @g_simp3 (syn_wfun P) (syn_wfun Q)
      (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
  have p0006 := @g_simpr (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))
  have p0007 :=
    @g_syl
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
      (.classMem A (syn_cdm Q)) p0005 p0006
  have p0008 :=
    @g_jca
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wfun Q) (.classMem A (syn_cdm Q)) p0004 p0007
  have p0009 := @g_funbrfvb A (.cv z) Q
  have p0010 :=
    @g_syl
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wa (syn_wfun Q) (.classMem A (syn_cdm Q)))
      (syn_wb (.classEq (syn_cfv Q A) (.cv z)) (syn_wbr A Q (.cv z))) p0008 p0009
  have p0011 :=
    @g_bicomd
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (.classEq (syn_cfv Q A) (.cv z)) (syn_wbr A Q (.cv z)) p0010
  have p0012 := @g_brcnv (.cv z) A P
  have p0013 :=
    @g_a1i (syn_wb (syn_wbr (.cv z) (syn_ccnv P) A) (syn_wbr A P (.cv z)))
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      p0012
  have p0014 :=
    @g_simp1 (syn_wfun P) (syn_wfun Q)
      (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
  have p0016 := @g_simpl (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))
  have p0017 :=
    @g_syl
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
      (.classMem A (syn_cdm P)) p0005 p0016
  have p0018 :=
    @g_jca
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wfun P) (.classMem A (syn_cdm P)) p0014 p0017
  have p0019 := @g_funbrfvb A (.cv z) P
  have p0020 :=
    @g_syl
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wa (syn_wfun P) (.classMem A (syn_cdm P)))
      (syn_wb (.classEq (syn_cfv P A) (.cv z)) (syn_wbr A P (.cv z))) p0018 p0019
  have p0021 :=
    @g_bicomd
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (.classEq (syn_cfv P A) (.cv z)) (syn_wbr A P (.cv z)) p0020
  have p0022 :=
    @g_bitrd
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wbr (.cv z) (syn_ccnv P) A) (syn_wbr A P (.cv z))
      (.classEq (syn_cfv P A) (.cv z)) p0013 p0021
  have p0023 :=
    @g_anbi12d
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wbr A Q (.cv z)) (.classEq (syn_cfv Q A) (.cv z))
      (syn_wbr (.cv z) (syn_ccnv P) A) (.classEq (syn_cfv P A) (.cv z)) p0011 p0022
  have p0024 :=
    @g_exbidv
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A))
      (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z))) z
      dv_cache_0004 p0023
  have p0025 := @g_eqcom (syn_cfv Q A) (.cv z)
  have p0026 := @g_eqcom (syn_cfv P A) (.cv z)
  have p0027 :=
    @g_anbi12i (.classEq (syn_cfv Q A) (.cv z)) (.classEq (.cv z) (syn_cfv Q A))
      (.classEq (syn_cfv P A) (.cv z)) (.classEq (.cv z) (syn_cfv P A)) p0025 p0026
  have p0028 :=
    @g_exbii (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z)))
      (syn_wa (.classEq (.cv z) (syn_cfv Q A)) (.classEq (.cv z) (syn_cfv P A))) z p0027
  have p0029 := @g_fvex A Q
  have p0030 := @g_eqvinc z (syn_cfv Q A) (syn_cfv P A) dv_cache_0005 dv_cache_0006 p0029
  have p0031 :=
    @g_bicomi (.classEq (syn_cfv Q A) (syn_cfv P A))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv Q A)) (.classEq (.cv z) (syn_cfv P A))))
      p0030
  have p0032 :=
    @g_bitri
      (syn_wex z (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z))))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv Q A)) (.classEq (.cv z) (syn_cfv P A))))
      (.classEq (syn_cfv Q A) (syn_cfv P A)) p0028 p0031
  have p0033 := @g_eqcom (syn_cfv Q A) (syn_cfv P A)
  have p0034 :=
    @g_bitri
      (syn_wex z (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z))))
      (.classEq (syn_cfv Q A) (syn_cfv P A)) (.classEq (syn_cfv P A) (syn_cfv Q A)) p0032
      p0033
  have p0035 :=
    @g_a1i
      (syn_wb (syn_wex z
          (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z))))
        (.classEq (syn_cfv P A) (syn_cfv Q A)))
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      p0034
  have p0036 :=
    @g_bitrd
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A)))
      (syn_wex z (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z))))
      (.classEq (syn_cfv P A) (syn_cfv Q A)) p0024 p0035
  have p0037 :=
    @g_bitrd
      (syn_w3a (syn_wfun P) (syn_wfun Q)
        (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))
      (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q)))
      (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A)))
      (.classEq (syn_cfv P A) (syn_cfv Q A)) p0003 p0036
  exact p0037

@[expose]
noncomputable def g_frecteqex (F : Class) (G : Class) (I : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
        (.classMem (syn_cfrecteq F G I) (syn_cvv))) :=
  by
  have p0000 := @g_tcfnex
  have p0001 :=
    @g_a1i (.classMem (syn_ctcfn) (syn_cvv))
      (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) p0000
  have p0002 := @g_simpl (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0003 := @g_eqid (syn_cfrec F I)
  have p0004 := @g_frecexg (syn_cfrec F I) F I (syn_cvv) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem F (syn_cvv)) (.classMem (syn_cfrec F I) (syn_cvv)) p0002 p0004
  have p0006 := @g_siexg (syn_cfrec F I) (syn_cvv)
  have p0007 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_cfrec F I) (syn_cvv))
      (.classMem (syn_csi (syn_cfrec F I)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_jca (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_ctcfn) (syn_cvv)) (.classMem (syn_csi (syn_cfrec F I)) (syn_cvv))
      p0001 p0007
  have p0009 := @g_coexg (syn_ctcfn) (syn_csi (syn_cfrec F I)) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (syn_wa (.classMem (syn_ctcfn) (syn_cvv)) (.classMem (syn_csi (syn_cfrec F I)) (syn_cvv)))
      (.classMem (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_cvv)) p0008 p0009
  have p0011 := @g_cnvexg (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_cvv)
  have p0012 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_cvv))
      (.classMem (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_cvv))
      p0010 p0011
  have p0013 := @g_simpr (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0014 := @g_eqid (syn_cfrec G (syn_ctc I))
  have p0015 := @g_frecexg (syn_cfrec G (syn_ctc I)) G (syn_ctc I) (syn_cvv) p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem G (syn_cvv)) (.classMem (syn_cfrec G (syn_ctc I)) (syn_cvv)) p0013 p0015
  have p0019 :=
    @g_jca (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_cfrec G (syn_ctc I)) (syn_cvv)) (.classMem (syn_ctcfn) (syn_cvv))
      p0016 p0001
  have p0020 := @g_coexg (syn_cfrec G (syn_ctc I)) (syn_ctcfn) (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (syn_wa (.classMem (syn_cfrec G (syn_ctc I)) (syn_cvv)) (.classMem (syn_ctcfn) (syn_cvv)))
      (.classMem (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_cvv))
      (.classMem (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv)) p0012 p0021
  have p0023 :=
    @g_coexg (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
      (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (syn_wa (.classMem (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_cvv))
        (.classMem (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv)))
      (.classMem (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
          (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_cvv))
      p0022 p0023
  have p0025 :=
    @g_fixexg
      (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
        (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))
      (syn_cvv)
  have p0026 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
          (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_cvv))
      (.classMem (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
            (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) (syn_cvv))
      p0024 p0025
  have p0027 :=
    @g_uni1exg
      (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
          (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))
      (syn_cvv)
  have p0028 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
            (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) (syn_cvv))
      (.classMem (syn_cuni1 (syn_cfix
            (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
              (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (syn_cvv))
      p0026 p0027
  have p0029 := (Nominal.classEqRefl (syn_cfrecteq F G I))
  have p0030 :=
    @g_eleq1i (syn_cfrecteq F G I)
      (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
            (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))
      (syn_cvv) p0029
  have p0031 :=
    @g_sylibr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv)))
      (.classMem (syn_cuni1 (syn_cfix
            (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
              (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (syn_cvv))
      (.classMem (syn_cfrecteq F G I) (syn_cvv)) p0028 p0030
  exact p0031

@[expose]
noncomputable def g_sifnvalv (x : Var) (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem (.cv x) A))
        (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv x))) (syn_csn (syn_cfv F (.cv x))))) :=
  by
  have p0000 := @g_eqid (syn_cfv F (.cv x))
  have p0001 :=
    @g_a1i (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x)))
      (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) p0000
  have p0002 := @g_fnopfvb A (.cv x) (syn_cfv F (.cv x)) F
  have p0003 :=
    @g_mpbid (syn_wa (syn_wfn F A) (.classMem (.cv x) A))
      (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x)))
      (.classMem (syn_cop (.cv x) (syn_cfv F (.cv x))) F) p0001 p0002
  have p0004 := @g_vex x
  have p0005 := @g_fvex (.cv x) F
  have p0006 := @g_opsnelsi (.cv x) (syn_cfv F (.cv x)) F p0004 p0005
  have p0007 :=
    @g_sylibr (syn_wa (syn_wfn F A) (.classMem (.cv x) A))
      (.classMem (syn_cop (.cv x) (syn_cfv F (.cv x))) F)
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x)))) (syn_csi F))
      p0003 p0006
  have p0008 := @g_simpl (syn_wfn F A) (.classMem (.cv x) A)
  have p0009 := @g_fnfun A F
  have p0010 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wfn F A) (syn_wfun F) p0008
      p0009
  have p0011 := @g_funsi F
  have p0012 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wfun F)
      (syn_wfun (syn_csi F)) p0010 p0011
  have p0013 := @g_funopfv (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x))) (syn_csi F)
  have p0014 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wfun (syn_csi F))
      (.imp (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x)))) (syn_csi F))
        (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv x))) (syn_csn (syn_cfv F (.cv x)))))
      p0012 p0013
  have p0015 :=
    @g_mpd (syn_wa (syn_wfn F A) (.classMem (.cv x) A))
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x)))) (syn_csi F))
      (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv x))) (syn_csn (syn_cfv F (.cv x))))
      p0007 p0014
  exact p0015

@[expose]
noncomputable def g_tcfnfv (A : Class)
    (hyp_tcfnfv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) (syn_ctc A)) :=
  by
  have p0000 := @g_eqid (syn_ctc A)
  have p0001 := @g_brtcfn A (syn_ctc A) hyp_tcfnfv_1
  have p0002 :=
    @g_mpbir (syn_wbr (syn_csn A) (syn_ctcfn) (syn_ctc A))
      (.classEq (syn_ctc A) (syn_ctc A)) p0000 p0001
  have p0003 := @g_fntcfn
  have p0004 := @g_snel1c A hyp_tcfnfv_1
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c)) p0003
      p0004
  have p0006 := @g_fnbrfvb (syn_c1c) (syn_csn A) (syn_ctc A) (syn_ctcfn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_mpbir (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) (syn_ctc A))
      (syn_wbr (syn_csn A) (syn_ctcfn) (syn_ctc A)) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_frecteqval (n : Var) (F : Class) (G : Class) (I : Class)
    (hyp_frecteqval_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_frecteqval_2 : Nominal.NPrf (.classMem I (syn_cdm F)))
    (hyp_frecteqval_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_frecteqval_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_frecteqval_5 : Nominal.NPrf (.classMem (syn_ctc I) (syn_cdm G)))
    (hyp_frecteqval_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I))
          (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
            (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfrecteq F G I))
  have p0001 :=
    @g_eleq2i (syn_cfrecteq F G I)
      (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
            (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))
      (.cv n) p0000
  have p0002 := @g_vex n
  have p0003 :=
    @g_eluni1 (.cv n)
      (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
          (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))
      p0002
  have p0004 :=
    @g_bitri (.classMem (.cv n) (syn_cfrecteq F G I))
      (.classMem (.cv n) (syn_cuni1 (syn_cfix
            (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
              (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))))
      (.classMem (syn_csn (.cv n)) (syn_cfix
          (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
            (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))
      p0001 p0003
  have p0005 :=
    @g_a1i
      (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I)) (.classMem (syn_csn (.cv n)) (syn_cfix
            (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
              (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))))
      (.classMem (.cv n) (syn_cnnc)) p0004
  have p0006 := @g_fntcfn
  have p0007 := @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0010 := @g_eqid (syn_cfrec F I)
  have p0011 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0012 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0013 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0014 :=
    @g_fnfrec
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_cfrec F I) F I p0010 p0011 p0012 p0013
  have p0015 := Nominal.mp p0009 p0014
  have p0016 := @g_fnfun (syn_cnnc) (syn_cfrec F I)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @g_funsi (syn_cfrec F I)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (syn_wfun (syn_csi (syn_cfrec F I))) p0008 p0019
  have p0021 := @g_funco (syn_ctcfn) (syn_csi (syn_cfrec F I))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_a1i (syn_wfun (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
      (.classMem (.cv n) (syn_cnnc)) p0022
  have p0024 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G)) hyp_frecteqval_4 hyp_frecteqval_5 hyp_frecteqval_6
  have p0025 := @g_eqid (syn_cfrec G (syn_ctc I))
  have p0026 :=
    @g_simp1 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G))
  have p0027 :=
    @g_simp2 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G))
  have p0028 :=
    @g_simp3 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G))
  have p0029 :=
    @g_fnfrec
      (syn_w3a (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
        (syn_wss (syn_crn G) (syn_cdm G)))
      (syn_cfrec G (syn_ctc I)) G (syn_ctc I) p0025 p0026 p0027 p0028
  have p0030 := Nominal.mp p0024 p0029
  have p0031 := @g_fnfun (syn_cnnc) (syn_cfrec G (syn_ctc I))
  have p0032 := Nominal.mp p0030 p0031
  have p0036 :=
    @g_pm3_2i (syn_wfun (syn_cfrec G (syn_ctc I))) (syn_wfun (syn_ctcfn)) p0032 p0008
  have p0037 := @g_funco (syn_cfrec G (syn_ctc I)) (syn_ctcfn)
  have p0038 := Nominal.mp p0036 p0037
  have p0039 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))
      (.classMem (.cv n) (syn_cnnc)) p0038
  have p0040 := @g_fvex (.cv n) (syn_cfrec F I)
  have p0041 := @g_snel1c (syn_cfv (syn_cfrec F I) (.cv n)) p0040
  have p0043 := @g_fndm (syn_c1c) (syn_ctcfn)
  have p0044 := Nominal.mp p0006 p0043
  have p0045 :=
    @g_eleq2i (syn_cdm (syn_ctcfn)) (syn_c1c) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n)))
      p0044
  have p0046 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn)))
      (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_c1c)) p0041 p0045
  have p0047 :=
    @g_a1i (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn)))
      (.classMem (.cv n) (syn_cnnc)) p0046
  have p0055 := @g_sifnvalv n (syn_cnnc) (syn_cfrec F I)
  have p0056 :=
    @g_mpan (syn_wfn (syn_cfrec F I) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n)))
        (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))))
      p0015 p0055
  have p0057 :=
    @g_eleq1d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n)))
      (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn)) p0056
  have p0058 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_cdm (syn_ctcfn)))
      (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn))) p0047
      p0057
  have p0070 :=
    @g_a1i (syn_wfun (syn_csi (syn_cfrec F I))) (.classMem (.cv n) (syn_cnnc)) p0019
  have p0071 := @g_snelpw1 (.cv n) (syn_cnnc)
  have p0072 :=
    @g_biimpri (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc)))
      (.classMem (.cv n) (syn_cnnc)) p0071
  have p0073 := @g_dmsi (syn_cfrec F I)
  have p0081 := @g_fndm (syn_cnnc) (syn_cfrec F I)
  have p0082 := Nominal.mp p0015 p0081
  have p0083 := @g_pw1eq (syn_cdm (syn_cfrec F I)) (syn_cnnc)
  have p0084 := Nominal.mp p0082 p0083
  have p0085 :=
    @g_eqtri (syn_cdm (syn_csi (syn_cfrec F I))) (syn_cpw1 (syn_cdm (syn_cfrec F I)))
      (syn_cpw1 (syn_cnnc)) p0073 p0084
  have p0086 :=
    @g_eleq2i (syn_cdm (syn_csi (syn_cfrec F I))) (syn_cpw1 (syn_cnnc)) (syn_csn (.cv n))
      p0085
  have p0087 :=
    @g_sylibr (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc)))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))) p0072 p0086
  have p0088 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_csi (syn_cfrec F I)))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))) p0070 p0087
  have p0089 := @g_dmfco (syn_csn (.cv n)) (syn_ctcfn) (syn_csi (syn_cfrec F I))
  have p0090 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (syn_wfun (syn_csi (syn_cfrec F I)))
        (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))))
      (syn_wb (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))))
        (.classMem (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_cdm (syn_ctcfn))))
      p0088 p0089
  have p0091 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))))
      (.classMem (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_cdm (syn_ctcfn)))
      p0058 p0090
  have p0092 := @g_nntccl (.cv n)
  have p0094 := @g_tcfnfv (.cv n) p0002
  have p0095 :=
    @g_eleq1i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n))
      (syn_cdm (syn_cfrec G (syn_ctc I))) p0094
  have p0103 := @g_fndm (syn_cnnc) (syn_cfrec G (syn_ctc I))
  have p0104 := Nominal.mp p0030 p0103
  have p0105 :=
    @g_eleq2i (syn_cdm (syn_cfrec G (syn_ctc I))) (syn_cnnc) (syn_ctc (.cv n)) p0104
  have p0106 :=
    @g_bitri
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec G (syn_ctc I))))
      (.classMem (syn_ctc (.cv n)) (syn_cdm (syn_cfrec G (syn_ctc I))))
      (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0095 p0105
  have p0107 :=
    @g_sylibr (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec G (syn_ctc I))))
      p0092 p0106
  have p0112 := @g_snel1c (.cv n) p0002
  have p0116 := @g_eleq2i (syn_cdm (syn_ctcfn)) (syn_c1c) (syn_csn (.cv n)) p0044
  have p0117 :=
    @g_mpbir (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn)))
      (.classMem (syn_csn (.cv n)) (syn_c1c)) p0112 p0116
  have p0118 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn)))
      p0008 p0117
  have p0119 := @g_dmfco (syn_csn (.cv n)) (syn_cfrec G (syn_ctc I)) (syn_ctcfn)
  have p0120 := Nominal.mp p0118 p0119
  have p0121 :=
    @g_sylibr (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec G (syn_ctc I))))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))
      p0107 p0120
  have p0122 :=
    @g_jca (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))
      p0091 p0121
  have p0123 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc))
      (syn_wfun (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
      (syn_wfun (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))
      (syn_wa (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))))
        (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))
      p0023 p0039 p0122
  have p0124 :=
    @g_funeqfix (syn_csn (.cv n)) (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))
      (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))
  have p0125 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_w3a (syn_wfun (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
        (syn_wfun (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_wa
          (.classMem (syn_csn (.cv n))
            (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))))
          (.classMem (syn_csn (.cv n))
            (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))))
      (syn_wb (.classMem (syn_csn (.cv n)) (syn_cfix
            (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
              (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (.classEq
          (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n)))
          (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n)))))
      p0123 p0124
  have p0126 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cfrecteq F G I))
      (.classMem (syn_csn (.cv n)) (syn_cfix
          (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
            (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))
      (.classEq (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n)))
        (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n))))
      p0005 p0125
  have p0157 := @g_fvco (syn_csn (.cv n)) (syn_ctcfn) (syn_csi (syn_cfrec F I))
  have p0158 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (syn_wfun (syn_csi (syn_cfrec F I)))
        (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))))
      (.classEq (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n)))
        (syn_cfv (syn_ctcfn) (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n)))))
      p0088 p0157
  have p0168 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n)))
      (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_ctcfn) p0056
  have p0169 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n)))
      (syn_cfv (syn_ctcfn) (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n)))) p0158 p0168
  have p0171 := @g_tcfnfv (syn_cfv (syn_cfrec F I) (.cv n)) p0040
  have p0172 :=
    @g_a1i
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))))
        (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0171
  have p0173 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n)))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))))
      (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) p0169 p0172
  have p0185 := @g_fvco (syn_csn (.cv n)) (syn_cfrec G (syn_ctc I)) (syn_ctcfn)
  have p0186 := Nominal.mp p0118 p0185
  have p0189 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n))
      (syn_cfrec G (syn_ctc I)) p0094
  have p0190 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n)))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n))))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))) p0186 p0189
  have p0191 :=
    @g_a1i
      (.classEq (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0190
  have p0192 :=
    @g_eqeq12d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n)))
      (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
      (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n)))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))) p0173 p0191
  have p0193 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cfrecteq F G I))
      (.classEq (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n)))
        (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))))
      p0126 p0192
  exact p0193

@[expose]
noncomputable def g_frecteqvalcl (B : Class) (F : Class) (G : Class) (I : Class)
    (hyp_frecteqvalcl_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_frecteqvalcl_2 : Nominal.NPrf (.classMem I (syn_cdm F)))
    (hyp_frecteqvalcl_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_frecteqvalcl_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_frecteqvalcl_5 : Nominal.NPrf (.classMem (syn_ctc I) (syn_cdm G)))
    (hyp_frecteqvalcl_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cfrecteq F G I))
          (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B))
            (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B))))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_B, not_false_eq_true])
  have dv_cache_0002 :
    n ∉
      ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cfrecteq F G I))
            (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B))
              (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union,
          fresh_n_not_B, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_id (.classEq (.cv n) B)
  have p0002 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0004 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cfrecteq F G I) p0001
  have p0006 := @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F I) p0001
  have p0007 := @g_tceq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec F I) B)
  have p0008 :=
    @g_syl (.classEq (.cv n) B)
      (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec F I) B))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
        (syn_ctc (syn_cfv (syn_cfrec F I) B)))
      p0006 p0007
  have p0010 := @g_tceq (.cv n) B
  have p0011 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0001 p0010
  have p0012 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B) (syn_cfrec G (syn_ctc I))
      p0011
  have p0013 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
      (syn_ctc (syn_cfv (syn_cfrec F I) B))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)) p0008 p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cfrecteq F G I))
      (.classMem B (syn_cfrecteq F G I))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)))
      p0004 p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc))
      (.classMem B (syn_cnnc))
      (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))))
      (syn_wb (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B))))
      p0002 p0014
  have p0016 :=
    @g_frecteqval n F G I hyp_frecteqvalcl_1 hyp_frecteqvalcl_2 hyp_frecteqvalcl_3
      hyp_frecteqvalcl_4 hyp_frecteqvalcl_5 hyp_frecteqvalcl_6
  have p0017 :=
    @g_vtoclg
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I))
          (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))
            (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))))))
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cfrecteq F G I))
          (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B))
            (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)))))
      n B (syn_cnnc) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wb (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B))))
      p0000 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part017`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_frectchom0 (x : Var) (F : Class) (G : Class) (I : Class) (N : Class)
    (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) (dv_I_x : x ∉ I.fv)
    (hyp_frectchom0_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_frectchom0_2 : Nominal.NPrf (.classMem I (syn_cdm F)))
    (hyp_frectchom0_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_frectchom0_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_frectchom0_5 : Nominal.NPrf (.classMem (syn_ctc I) (syn_cdm G)))
    (hyp_frectchom0_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_frectchom0_7 : Nominal.NPrf (syn_wral x (syn_cdm F)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) N))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc N)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_ne_x : m ≠ x := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_m_not_G : m ∉ G.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_not_I : m ∉ I.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have dv_cache_0001 : n ∉ ((syn_cfrecteq F G I)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq,
          Finset.mem_union, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, or_false,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cfv (syn_cfrec F I) (.cv m))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_m, dv_F_x, dv_I_x, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cdm F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, dv_F_x,
          not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
          (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_m, dv_F_x, dv_I_x, dv_G_x, or_false,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : n ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.classMem (.cv m) (syn_cfrecteq F G I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I,
          or_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((Wff.classMem (.cv n) (syn_cfrecteq F G I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_F, fresh_m_not_G, fresh_m_not_I,
          or_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.classMem (syn_c0c) (syn_cfrecteq F G I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union,
          fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Wff.classMem N (syn_cfrecteq F G I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union,
          fresh_n_not_N, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : n ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_frectchom0_1 p0000
  have p0002 := @g_elex G (syn_cfuns)
  have p0003 := Nominal.mp hyp_frectchom0_4 p0002
  have p0004 := @g_pm3_2i (.classMem F (syn_cvv)) (.classMem G (syn_cvv)) p0001 p0003
  have p0005 := @g_frecteqex F G I
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_abid2 n (syn_cfrecteq F G I) dv_cache_0001
  have p0008 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cfrecteq F G I))) (syn_cfrecteq F G I)
      (syn_cvv) p0007
  have p0009 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cfrecteq F G I))) (syn_cvv))
      (.classMem (syn_cfrecteq F G I) (syn_cvv)) p0006 p0008
  have p0010 := @g_id (.classEq (.cv n) (syn_c0c))
  have p0011 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cfrecteq F G I) p0010
  have p0012 := @g_id (.classEq (.cv n) (.cv m))
  have p0013 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cfrecteq F G I) p0012
  have p0014 := @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0015 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n)
      (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I) p0014
  have p0016 := @g_id (.classEq (.cv n) N)
  have p0017 := @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cfrecteq F G I) p0016
  have p0018 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F)) hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
  have p0019 := @g_eqid (syn_cfrec F I)
  have p0020 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0021 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0022 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0023 :=
    @g_frec0
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_cfrec F I) F I p0019 p0020 p0021 p0022
  have p0024 := Nominal.mp p0018 p0023
  have p0025 := @g_tceq (syn_cfv (syn_cfrec F I) (syn_c0c)) I
  have p0026 := Nominal.mp p0024 p0025
  have p0027 := @g_tc0c
  have p0028 := @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c) (syn_cfrec G (syn_ctc I)) p0027
  have p0029 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G)) hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0030 := @g_eqid (syn_cfrec G (syn_ctc I))
  have p0031 :=
    @g_simp1 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G))
  have p0032 :=
    @g_simp2 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G))
  have p0033 :=
    @g_simp3 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G))
  have p0034 :=
    @g_frec0
      (syn_w3a (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G))
        (syn_wss (syn_crn G) (syn_cdm G)))
      (syn_cfrec G (syn_ctc I)) G (syn_ctc I) p0030 p0031 p0032 p0033
  have p0035 := Nominal.mp p0029 p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c)))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_c0c)) (syn_ctc I) p0028 p0035
  have p0037 :=
    @g_eqcomi (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c))) (syn_ctc I) p0036
  have p0038 :=
    @g_eqtri (syn_ctc (syn_cfv (syn_cfrec F I) (syn_c0c))) (syn_ctc I)
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c))) p0026 p0037
  have p0039 := @g_peano1
  have p0040 :=
    @g_frecteqvalcl (syn_c0c) F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
      hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cfrecteq F G I))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_c0c)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c))))
      p0038 p0041
  have p0044 :=
    @g_a1i (.classMem F (syn_cfuns)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_1
  have p0045 :=
    @g_a1i (.classMem I (syn_cdm F)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_2
  have p0046 :=
    @g_a1i (syn_wss (syn_crn F) (syn_cdm F)) (.classMem (.cv m) (syn_cnnc))
      hyp_frectchom0_3
  have p0047 := @g_id (.classMem (.cv m) (syn_cnnc))
  have p0048 :=
    @g_frecsuc (.classMem (.cv m) (syn_cnnc)) (syn_cfrec F I) F I (.cv m) p0019 p0044
      p0045 p0046 p0047
  have p0049 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      p0048
  have p0050 :=
    @g_tceq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))
      (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))
  have p0051 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
        (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))
      p0049 p0050
  have p0053 := @g_frecdomfv F I (.cv m)
  have p0054 :=
    @g_mpan
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cdm F)) p0018 p0053
  have p0055 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc))
      (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))
  have p0056 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))))
      (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)) F p0055
  have p0057 := @g_tceq (syn_cfv F (.cv x)) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))
  have p0058 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))))
      (.classEq (syn_cfv F (.cv x)) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
      (.classEq (syn_ctc (syn_cfv F (.cv x)))
        (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))
      p0056 p0057
  have p0060 := @g_tceq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))
  have p0061 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))))
      (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))
      (.classEq (syn_ctc (.cv x)) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))) p0055 p0060
  have p0062 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))))
      (syn_ctc (.cv x)) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) G p0061
  have p0063 :=
    @g_eqeq12d
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))))
      (syn_ctc (syn_cfv F (.cv x)))
      (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
      (syn_cfv G (syn_ctc (.cv x)))
      (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))) p0058 p0062
  have p0064 :=
    @g_rspcdv (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x))))
      (.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
        (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))))
      x (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cdm F) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0054 p0063
  have p0065 :=
    @g_mpi (.classMem (.cv m) (syn_cnnc))
      (syn_wral x (syn_cdm F)
        (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))
      (.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
        (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))))
      hyp_frectchom0_7 p0064
  have p0066 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
        (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      p0065
  have p0067 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
      (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
      (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))) p0051 p0066
  have p0068 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
  have p0069 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))) G p0068
  have p0070 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
      (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))))
      (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0067 p0069
  have p0072 :=
    @g_a1i (.classMem G (syn_cfuns)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_4
  have p0073 :=
    @g_a1i (.classMem (syn_ctc I) (syn_cdm G)) (.classMem (.cv m) (syn_cnnc))
      hyp_frectchom0_5
  have p0074 :=
    @g_a1i (syn_wss (syn_crn G) (syn_cdm G)) (.classMem (.cv m) (syn_cnnc))
      hyp_frectchom0_6
  have p0076 := @g_nntccl (.cv m)
  have p0077 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0047 p0076
  have p0078 :=
    @g_frecsuc (.classMem (.cv m) (syn_cnnc)) (syn_cfrec G (syn_ctc I)) G (syn_ctc I)
      (syn_ctc (.cv m)) p0030 p0072 p0073 p0074 p0077
  have p0079 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
        (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      p0078
  have p0080 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
      (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0079
  have p0081 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
      (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0070
      p0080
  have p0083 := @g_nnnc (.cv m)
  have p0084 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))
      (.classMem (.cv m) (syn_cncs)) p0047 p0083
  have p0085 := @g_n_1cnc
  have p0086 :=
    @g_a1i (.classMem (syn_c1c) (syn_cncs)) (.classMem (.cv m) (syn_cnnc)) p0085
  have p0087 :=
    @g_jca (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cncs))
      (.classMem (syn_c1c) (syn_cncs)) p0084 p0086
  have p0088 := @g_tcdi (.cv m) (syn_c1c)
  have p0089 :=
    @g_syl (.classMem (.cv m) (syn_cnnc))
      (syn_wa (.classMem (.cv m) (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)))
      (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_ctc (.cv m)) (syn_ctc (syn_c1c))))
      p0087 p0088
  have p0090 := @g_tc1c
  have p0091 :=
    @g_a1i (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) (.classMem (.cv m) (syn_cnnc)) p0090
  have p0092 :=
    @g_addceq2d (.classMem (.cv m) (syn_cnnc)) (syn_ctc (syn_c1c)) (syn_c1c)
      (syn_ctc (.cv m)) p0091
  have p0093 :=
    @g_eqtrd (.classMem (.cv m) (syn_cnnc)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_ctc (.cv m)) (syn_ctc (syn_c1c)))
      (syn_cplc (syn_ctc (.cv m)) (syn_c1c)) p0089 p0092
  have p0094 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      p0093
  have p0095 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))
      (syn_cfrec G (syn_ctc I)) p0094
  have p0096 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0095
  have p0097 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))))
      (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
      (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) p0081
      p0096
  have p0098 :=
    @g_ex (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))
      p0097
  have p0099 :=
    @g_frecteqval m F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
      hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0100 :=
    @g_bicomd (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cfrecteq F G I))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      p0099
  have p0102 := @g_peano2 (.cv m)
  have p0103 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) p0047 p0102
  have p0104 :=
    @g_frecteqvalcl (syn_cplc (.cv m) (syn_c1c)) F G I hyp_frectchom0_1 hyp_frectchom0_2
      hyp_frectchom0_3 hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0105 :=
    @g_syl (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I))
        (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
          (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))))
      p0103 p0104
  have p0106 :=
    @g_bicomd (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))
      p0105
  have p0107 :=
    @g_n_3imtr3d (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))
      (.classMem (.cv m) (syn_cfrecteq F G I))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I)) p0098 p0100 p0106
  have p0108_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I))
          (.classMem (.cv m) (syn_cfrecteq F G I)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfrecteq syn_cuni1 syn_cuni syn_wex syn_wa syn_cin syn_ccompl
          syn_cnin syn_wnan syn_c1c syn_cfix syn_crn syn_cima syn_wrex syn_wbr syn_cop
          syn_cun syn_cvv syn_ccom syn_copab syn_ccnv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0108 :=
    @g_finds (.classMem (.cv n) (syn_cfrecteq F G I))
      (.classMem (syn_c0c) (syn_cfrecteq F G I)) (.classMem (.cv m) (syn_cfrecteq F G I))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I))
      (.classMem N (syn_cfrecteq F G I)) n m N dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0009 p0011
      p0108_e02_recanon p0015 p0017 p0042 p0107
  have p0109 :=
    @g_frecteqvalcl N F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
      hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0110 :=
    @g_mpbid (.classMem N (syn_cnnc)) (.classMem N (syn_cfrecteq F G I))
      (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) N))
        (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc N)))
      p0108 p0109
  exact p0110

@[expose]
noncomputable def g_f1pwexd (ph : Wff) (A : Class) (B : Class) (g : Var) (F : Class)
    (dv_A_g : g ∉ A.fv) (_dv_B_g : g ∉ B.fv) (dv_F_g : g ∉ F.fv) (dv_g_ph : g ∉ ph.fv)
    (hyp_f1pwexd_1 : Nominal.NPrf (.imp ph (.classMem F (syn_cvv))))
    (hyp_f1pwexd_2 : Nominal.NPrf (.imp ph (syn_wf1 F A B))) :
    Nominal.NPrf (.imp ph (syn_wex g (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)))) :=
  by
  have dv_cache_0001 : g ∉ ((syn_cpw A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, dv_A_g,
          not_false_eq_true])
  have dv_cache_0002 : g ∉ ((syn_cpw (syn_crn F))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, dv_F_g,
          not_false_eq_true])
  have dv_cache_0003 : g ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_g_ph, not_false_eq_true])
  have p0000 := @g_f1f1orn A B F
  have p0001 := @g_syl ph (syn_wf1 F A B) (syn_wf1o F A (syn_crn F)) hyp_f1pwexd_2 p0000
  have p0002 :=
    @g_jca ph (.classMem F (syn_cvv)) (syn_wf1o F A (syn_crn F)) hyp_f1pwexd_1 p0001
  have p0003 := @g_f1oeng A (syn_crn F) (syn_cvv) F
  have p0004 :=
    @g_syl ph (syn_wa (.classMem F (syn_cvv)) (syn_wf1o F A (syn_crn F)))
      (syn_wbr A (syn_cen) (syn_crn F)) p0002 p0003
  have p0005 := @g_enpw A (syn_crn F)
  have p0006 :=
    @g_syl ph (syn_wbr A (syn_cen) (syn_crn F))
      (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (syn_crn F))) p0004 p0005
  have p0007 := @g_bren (syn_cpw A) (syn_cpw (syn_crn F)) g dv_cache_0001 dv_cache_0002
  have p0008 :=
    @g_biimpi (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (syn_crn F)))
      (syn_wex g (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))) p0007
  have p0009 :=
    @g_syl ph (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (syn_crn F)))
      (syn_wex g (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))) p0006 p0008
  have p0010 := @g_f1of1 (syn_cpw A) (syn_cpw (syn_crn F)) (.cv g)
  have p0011 :=
    @g_a1i
      (.imp (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))
        (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))))
      ph p0010
  have p0012 := @g_f1f A B F
  have p0013 := @g_syl ph (syn_wf1 F A B) (syn_wf F A B) hyp_f1pwexd_2 p0012
  have p0014 := @g_frn A B F
  have p0015 := @g_syl ph (syn_wf F A B) (syn_wss (syn_crn F) B) p0013 p0014
  have p0016 := @g_sspwb (syn_crn F) B
  have p0017 :=
    @g_biimpi (syn_wss (syn_crn F) B) (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)) p0016
  have p0018 :=
    @g_syl ph (syn_wss (syn_crn F) B) (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)) p0015
      p0017
  have p0019 :=
    @g_a1d ph (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B))
      (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) p0018
  have p0020 :=
    @g_jcad ph (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))
      (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))
      (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)) p0011 p0019
  have p0021 := @g_f1ss (syn_cpw A) (syn_cpw (syn_crn F)) (syn_cpw B) (.cv g)
  have p0022 :=
    @g_syl6 ph (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))
      (syn_wa (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))
        (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)))
      (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) p0020 p0021
  have p0023 :=
    @g_eximdv ph (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))
      (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) g dv_cache_0003 p0022
  have p0024 :=
    @g_mpd ph (syn_wex g (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))))
      (syn_wex g (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))) p0009 p0023
  exact p0024

@[expose]
noncomputable def g_f1pwpwexd (ph : Wff) (A : Class) (B : Class) (h : Var) (F : Class)
    (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv)
    (hyp_f1pwpwexd_1 : Nominal.NPrf (.imp ph (.classMem F (syn_cvv))))
    (hyp_f1pwpwexd_2 : Nominal.NPrf (.imp ph (syn_wf1 F A B))) :
    Nominal.NPrf
      (.imp ph (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ ({ h } : Finset Var) ∪ F.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_ph : g ∉ ph.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_ne_h : g ≠ h := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have fresh_g_not_F : g ∉ F.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : g ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_A, not_false_eq_true])
  have dv_cache_0002 : g ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_B, not_false_eq_true])
  have dv_cache_0003 : g ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_F, not_false_eq_true])
  have dv_cache_0004 : g ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_ph, not_false_eq_true])
  have dv_cache_0005 : h ∉ ((syn_cpw A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, dv_A_h,
          not_false_eq_true])
  have dv_cache_0006 : h ∉ ((syn_cpw B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, dv_B_h,
          not_false_eq_true])
  have dv_cache_0007 : h ∉ ((Class.cv g)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_g, not_false_eq_true])
  have dv_cache_0008 : h ∉ ((syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, dv_A_h, dv_B_h, fresh_h_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    g ∉ ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B,
          fresh_g_ne_h, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1pwexd ph A B g F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_f1pwpwexd_1 hyp_f1pwpwexd_2
  have p0001 := @g_vex g
  have p0002 :=
    @g_a1i (.classMem (.cv g) (syn_cvv)) (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) p0001
  have p0003 := @g_id (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))
  have p0004 :=
    @g_f1pwexd (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) (syn_cpw A) (syn_cpw B) h (.cv g)
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0002 p0003
  have p0005 :=
    @g_a1i
      (.imp (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))
        (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))))
      ph p0004
  have p0006 :=
    @g_exlimdv ph (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))
      (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) g
      dv_cache_0009 dv_cache_0004 p0005
  have p0007 :=
    @g_mpd ph (syn_wex g (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)))
      (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) p0000
      p0006
  exact p0007

@[expose]
noncomputable def g_f1pw2exim (A : Class) (B : Class) (f : Var) (h : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_h : h ∉ A.fv) (dv_B_f : f ∉ B.fv) (dv_B_h : h ∉ B.fv)
    (dv_f_h : f ≠ h) :
    Nominal.NPrf
      (.imp (syn_wex f (syn_wf1 (.cv f) A B))
        (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))) :=
  by
  have dv_cache_0001 : h ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_h, not_false_eq_true])
  have dv_cache_0002 : h ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_h, not_false_eq_true])
  have dv_cache_0003 :
    f ∉ ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_f, dv_B_f, dv_f_h, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_vex f
  have p0001 := @g_a1i (.classMem (.cv f) (syn_cvv)) (syn_wf1 (.cv f) A B) p0000
  have p0002 := @g_id (syn_wf1 (.cv f) A B)
  have p0003 :=
    @g_f1pwpwexd (syn_wf1 (.cv f) A B) A B h (.cv f) dv_cache_0001 dv_cache_0002 p0001
      p0002
  have p0004 :=
    @g_exlimiv (syn_wf1 (.cv f) A B)
      (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) f
      dv_cache_0003 p0003
  exact p0004

@[expose]
noncomputable def g_ncpw2le (A : Class) (B : Class)
    (hyp_ncpw2le_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ncpw2le_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))
        (syn_wbr (syn_cnc (syn_cpw (syn_cpw A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw B))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let h : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (h))
  have fresh_h_not_B : h ∉ B.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_h_ne_f : h ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_h : f ≠ h := Ne.symm fresh_h_ne_f
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0004 : h ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_B, not_false_eq_true])
  have dv_cache_0005 : f ≠ h :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ h from (by exact fresh_f_ne_h))
  have dv_cache_0006 : h ∉ ((syn_cpw (syn_cpw A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_h_not_A,
          not_false_eq_true])
  have dv_cache_0007 : h ∉ ((syn_cpw (syn_cpw B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_h_not_B,
          not_false_eq_true])
  have p0000 := @g_nclenc A B f dv_cache_0001 dv_cache_0002 hyp_ncpw2le_1 hyp_ncpw2le_2
  have p0001 :=
    @g_biimpi (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))
      (syn_wex f (syn_wf1 (.cv f) A B)) p0000
  have p0002 :=
    @g_f1pw2exim A B f h dv_cache_0001 dv_cache_0003 dv_cache_0002 dv_cache_0004
      dv_cache_0005
  have p0003 :=
    @g_syl (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B))
      (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) p0001
      p0002
  have p0004 := @g_pwex A hyp_ncpw2le_1
  have p0005 := @g_pwex (syn_cpw A) p0004
  have p0006 := @g_pwex B hyp_ncpw2le_2
  have p0007 := @g_pwex (syn_cpw B) p0006
  have p0008 :=
    @g_nclenc (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)) h dv_cache_0006 dv_cache_0007
      p0005 p0007
  have p0009 :=
    @g_biimpri
      (syn_wbr (syn_cnc (syn_cpw (syn_cpw A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw B))))
      (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) p0008
  have p0010 :=
    @g_syl (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))
      (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))
      (syn_wbr (syn_cnc (syn_cpw (syn_cpw A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw B))))
      p0003 p0009
  exact p0010

@[expose]
noncomputable def g_hwnisobaseext (v : Var) (u : Var) (A : Class) (D : Class)
    (dv_u_v : u ≠ v) (hyp_hwnisobaseext_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (.imp (syn_wbr (.cv u) (syn_chwniso D) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))) :=
  by
  let proofSupport : Finset Var :=
    ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ D.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_v : h ≠ v := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ≠ v := by exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : h ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_D, not_false_eq_true])
  have dv_cache_0003 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0004 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0005 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have p0000 := @g_hwcnssbase A D hyp_hwnisobaseext_1
  have p0001 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))
  have p0002 :=
    @g_sseldi (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_chwcn D) (syn_chwcn A) (.cv u) p0000 p0001
  have p0004 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))
  have p0005 :=
    @g_sseldi (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_chwcn D) (syn_chwcn A) (.cv v) p0000 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0002 p0005
  have p0007 :=
    @g_adantr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) p0006
  have p0011 := @g_hwcnraw u A
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) p0002 p0011
  have p0016 := @g_hwcnraw v A
  have p0017 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcodes A)) p0005 p0016
  have p0018 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)) p0012
      p0017
  have p0019 :=
    @g_adantr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) p0018
  have p0020 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wbr (.cv u) (syn_chwniso D) (.cv v))
  have p0021 := @g_hwnisohwisob v u D dv_cache_0001
  have p0022 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso D) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwiso D) (.cv v)))
      p0021
  have p0023 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso D) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wbr (.cv u) (syn_chwiso D) (.cv v))
      p0020 p0023
  have p0025 := @g_brhwisoany v u D h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0026 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))
      (syn_wbr (.cv u) (syn_chwiso D) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0024 p0025
  have p0027 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0026
  have p0028 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0019 p0027
  have p0029 := @g_brhwisoany v u A h dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0030 :=
    @g_sylibr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0028 p0029
  have p0031 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0007 p0030
  have p0032 := @g_hwnisohwisob v u A dv_cache_0001
  have p0033 :=
    @g_sylibr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0031 p0032
  have p0034 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      p0033
  exact p0034


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwnisobaseextcl (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_hwnisobaseextcl_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
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
  have fresh_x_not_D : x ∉ D.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
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
  have dv_cache_0005 :
    y ∉
      ((Wff.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
          (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((Wff.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
          (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_A,
          or_false, not_false_eq_true])
  have p0000 := @g_simpl (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))
  have p0001 := @g_elex B (syn_chwcn D)
  have p0002 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (.classMem B (syn_chwcn D)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 := @g_simpr (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))
  have p0004 := @g_elex C (syn_chwcn D)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (.classMem C (syn_chwcn D)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002 p0005
  have p0007 := @g_eleq1 (.cv x) B (syn_chwcn D)
  have p0008 := @g_biid (.classMem (.cv y) (syn_chwcn D))
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
      (.classEq (.cv x) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) (syn_chwcn D))
      (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))
      (.classMem (.cv y) (syn_chwcn D)) p0007 p0009
  have p0011 := @g_breq1 (.cv x) B (.cv y) (syn_chwniso D)
  have p0012 := @g_breq1 (.cv x) B (.cv y) (syn_chwniso A)
  have p0013 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wbr (.cv x) (syn_chwniso D) (.cv y))
      (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
      (syn_wbr B (syn_chwniso A) (.cv y)) p0011 p0012
  have p0014 :=
    @g_imbi12d (.classEq (.cv x) B)
      (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
      (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
      (.imp (syn_wbr (.cv x) (syn_chwniso D) (.cv y)) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)))
      (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y))) p0010
      p0013
  have p0015 := @g_biid (.classMem B (syn_chwcn D))
  have p0016 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn D)) (.classMem B (syn_chwcn D)))
      (.classEq (.cv y) C) p0015
  have p0017 := @g_eleq1 (.cv y) C (syn_chwcn D)
  have p0018 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B (syn_chwcn D))
      (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))
      (.classMem C (syn_chwcn D)) p0016 p0017
  have p0019 := @g_breq2 (.cv y) C B (syn_chwniso D)
  have p0020 := @g_breq2 (.cv y) C B (syn_chwniso A)
  have p0021 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wbr B (syn_chwniso D) (.cv y))
      (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) (.cv y))
      (syn_wbr B (syn_chwniso A) C) p0019 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv y) C)
      (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
      (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y)))
      (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)) p0018 p0021
  have p0023 := @g_hwnisobaseext y x A D dv_cache_0001 hyp_hwnisobaseextcl_1
  have p0024 :=
    @g_vtocl2g
      (.imp (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
        (.imp (syn_wbr (.cv x) (syn_chwniso D) (.cv y))
          (syn_wbr (.cv x) (syn_chwniso A) (.cv y))))
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y))))
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)))
      x y B C (syn_cvv) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0014 p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)))
      p0006 p0024
  have p0026 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)) p0025
  exact p0026

@[expose]
noncomputable def g_hwnisobasebicl (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_hwnisobasebicl_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
        (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C))) :=
  by
  have p0000 := @g_hwnisobaserestrcl A B C D
  have p0001 := @g_hwnisobaseextcl A B C D hyp_hwnisobasebicl_1
  have p0002 :=
    @g_impbid (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hnqmap1basecompat (A : Class) (D : Class) (q : Var) (p : Var)
    (hyp_hnqmap1basecompat_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqmap1basecompat_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqmap1basecompat_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.imp
          (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
          (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))) :=
  by
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0001 := @g_hnwpw1argcl (syn_chwcn D) p
  have p0002 :=
    @g_simprd (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0001
  have p0003 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0000 p0002
  have p0004 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 A) p0003
  have p0005 := @g_hwcnssbase A D hyp_hnqmap1basecompat_1
  have p0008 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0001
  have p0009 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0000 p0008
  have p0010 :=
    @g_sseldi
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv p)) p0005 p0009
  have p0011 := @g_hnqmap1valcl A (syn_cuni (.cv p)) hyp_hnqmap1basecompat_3
  have p0012 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)))
      p0010 p0011
  have p0013 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 A) (.cv p))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) p0004 p0012
  have p0014 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0013
  have p0019 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 D) p0003
  have p0024 := @g_hnqmap1valcl D (syn_cuni (.cv p)) hyp_hnqmap1basecompat_2
  have p0025 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)))
      p0009 p0024
  have p0026 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 D) (.cv p))
      (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) p0019 p0025
  have p0027 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0026
  have p0028 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
      p0027
  have p0029 :=
    @g_simpr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
  have p0030 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cfv (syn_chnqmap1 D) (.cv p))
      (syn_cfv (syn_chnqmap1 D) (.cv q)) p0028 p0029
  have p0031 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0032 := @g_hnwpw1argcl (syn_chwcn D) q
  have p0033 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0032
  have p0034 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0031 p0033
  have p0035 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 D) p0034
  have p0038 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0032
  have p0039 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0031 p0038
  have p0040 := @g_hnqmap1valcl D (syn_cuni (.cv q)) hyp_hnqmap1basecompat_2
  have p0041 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      p0039 p0040
  have p0042 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 D) (.cv q))
      (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q))))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0035 p0041
  have p0043 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0042
  have p0044 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cfv (syn_chnqmap1 D) (.cv q))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0030 p0043
  have p0053 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0009 p0039
  have p0054 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn D)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0053
  have p0055 :=
    @g_hwnisoclasseqbcl D (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basecompat_2
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn D)))
      (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
          (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))))
      p0054 p0055
  have p0057 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0056
  have p0058 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0044 p0057
  have p0069 :=
    @g_hwnisobaseextcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) D hyp_hnqmap1basecompat_1
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn D)))
      (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))))
      p0054 p0069
  have p0071 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0058 p0070
  have p0083 :=
    @g_sseldi
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv q)) p0005 p0039
  have p0084 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0010 p0083
  have p0085 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0084
  have p0086 :=
    @g_hwnisoclasseqbcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basecompat_3
  have p0087 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
          (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))))
      p0085 p0086
  have p0088 :=
    @g_biimprd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0087
  have p0089 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q)))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      p0071 p0088
  have p0090 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0014 p0089
  have p0095 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 A) p0034
  have p0102 := @g_hnqmap1valcl A (syn_cuni (.cv q)) hyp_hnqmap1basecompat_3
  have p0103 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      p0083 p0102
  have p0104 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 A) (.cv q))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q))))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0095 p0103
  have p0105 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0104
  have p0106 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))
      p0105
  have p0107 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))
      (syn_cfv (syn_chnqmap1 A) (.cv q)) p0090 p0106
  have p0108 :=
    @g_ex
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0107
  exact p0108

@[expose]
noncomputable def g_hnqmap1basereflect (A : Class) (D : Class) (q : Var) (p : Var)
    (hyp_hnqmap1basereflect_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqmap1basereflect_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqmap1basereflect_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.imp
          (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
          (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))) :=
  by
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0001 := @g_hnwpw1argcl (syn_chwcn D) p
  have p0002 :=
    @g_simprd (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0001
  have p0003 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0000 p0002
  have p0004 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 D) p0003
  have p0007 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0001
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0000 p0007
  have p0009 := @g_hnqmap1valcl D (syn_cuni (.cv p)) hyp_hnqmap1basereflect_2
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)))
      p0008 p0009
  have p0011 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 D) (.cv p))
      (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) p0004 p0010
  have p0012 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0011
  have p0017 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 A) p0003
  have p0018 := @g_hwcnssbase A D hyp_hnqmap1basereflect_1
  have p0023 :=
    @g_sseldi
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv p)) p0018 p0008
  have p0024 := @g_hnqmap1valcl A (syn_cuni (.cv p)) hyp_hnqmap1basereflect_3
  have p0025 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)))
      p0023 p0024
  have p0026 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 A) (.cv p))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) p0017 p0025
  have p0027 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0026
  have p0028 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
      p0027
  have p0029 :=
    @g_simpr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
  have p0030 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cfv (syn_chnqmap1 A) (.cv p))
      (syn_cfv (syn_chnqmap1 A) (.cv q)) p0028 p0029
  have p0031 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0032 := @g_hnwpw1argcl (syn_chwcn D) q
  have p0033 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0032
  have p0034 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0031 p0033
  have p0035 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 A) p0034
  have p0039 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0032
  have p0040 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0031 p0039
  have p0041 :=
    @g_sseldi
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv q)) p0018 p0040
  have p0042 := @g_hnqmap1valcl A (syn_cuni (.cv q)) hyp_hnqmap1basereflect_3
  have p0043 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      p0041 p0042
  have p0044 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 A) (.cv q))
      (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q))))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0035 p0043
  have p0045 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0044
  have p0046 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cfv (syn_chnqmap1 A) (.cv q))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0030 p0045
  have p0059 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0023 p0041
  have p0060 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0059
  have p0061 :=
    @g_hwnisoclasseqbcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basereflect_3
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
          (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))))
      p0060 p0061
  have p0063 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0062
  have p0064 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0046 p0063
  have p0073 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0008 p0040
  have p0074 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn D)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0073
  have p0075 := @g_hwnisobaserestrcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) D
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn D)))
      (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))))
      p0074 p0075
  have p0077 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0064 p0076
  have p0088 :=
    @g_hwnisoclasseqbcl D (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basereflect_2
  have p0089 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn D)))
      (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
          (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))))
      p0074 p0088
  have p0090 :=
    @g_biimprd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0089
  have p0091 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q)))
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      p0077 p0090
  have p0092 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0012 p0091
  have p0097 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 D) p0034
  have p0102 := @g_hnqmap1valcl D (syn_cuni (.cv q)) hyp_hnqmap1basereflect_2
  have p0103 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      p0040 p0102
  have p0104 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (syn_cfv (syn_chnqmap1 D) (.cv q))
      (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q))))
      (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0097 p0103
  have p0105 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0104
  have p0106 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))
      p0105
  have p0107 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
          (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))
      (syn_cfv (syn_chnqmap1 D) (.cv q)) p0092 p0106
  have p0108 :=
    @g_ex
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0107
  exact p0108

@[expose]
noncomputable def g_hnqincexg (A : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv)))
        (.classMem (syn_chnqinc D A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnqinc D A))
  have p0001 := @g_simpr (.classMem D (syn_cvv)) (.classMem A (syn_cvv))
  have p0002 := @g_hnqmap1exg A
  have p0003 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv)))
      (.classMem A (syn_cvv)) (.classMem (syn_chnqmap1 A) (syn_cvv)) p0001 p0002
  have p0004 := @g_simpl (.classMem D (syn_cvv)) (.classMem A (syn_cvv))
  have p0005 := @g_hnqmap1exg D
  have p0006 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv)))
      (.classMem D (syn_cvv)) (.classMem (syn_chnqmap1 D) (syn_cvv)) p0004 p0005
  have p0007 := @g_cnvexg (syn_chnqmap1 D) (syn_cvv)
  have p0008 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv)))
      (.classMem (syn_chnqmap1 D) (syn_cvv))
      (.classMem (syn_ccnv (syn_chnqmap1 D)) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_jca (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv)))
      (.classMem (syn_chnqmap1 A) (syn_cvv))
      (.classMem (syn_ccnv (syn_chnqmap1 D)) (syn_cvv)) p0003 p0008
  have p0010 := @g_coexg (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wa (.classMem (syn_chnqmap1 A) (syn_cvv))
        (.classMem (syn_ccnv (syn_chnqmap1 D)) (syn_cvv)))
      (.classMem (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cvv)) p0009
      p0010
  have p0012 :=
    @g_syl5eqel (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (syn_chnqinc D A)
      (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cvv) p0000 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnqincfun (A : Class) (D : Class)
    (hyp_hnqincfun_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqincfun_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqincfun_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfun (syn_chnqinc D A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_z_ne_p : z ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_y, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_chnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_p_not_A, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_ccnv (syn_chnqmap1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0005 : q ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_x, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_z, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_ccnv (syn_chnqmap1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0009 : q ∉ ((Wff.classEq (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_y, fresh_q_ne_z, or_false, not_false_eq_true])
  have dv_cache_0010 :
    q ∉
      ((syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
              (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
              (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_A, fresh_q_not_D,
          fresh_q_ne_z, fresh_q_ne_p, or_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((Wff.classEq (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_z, or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
          (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_A, fresh_p_not_D,
          fresh_p_ne_z, or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_D, or_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_D, or_false, not_false_eq_true])
  have dv_cache_0016 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0017 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0018 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_simpl
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))
  have p0001 :=
    @g_brco p (.cv x) (.cv y) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_sylib
      (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
        (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
      (syn_wex p (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
      p0000 p0001
  have p0003 :=
    @g_simpl
      (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
        (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
  have p0004 :=
    @g_simpr
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))
  have p0005 :=
    @g_brco q (.cv x) (.cv z) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0006 :=
    @g_sylib
      (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
        (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))
      (syn_wex q (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      p0004 p0005
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
        (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
      (syn_wex q (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      p0003 p0006
  have p0008 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0009 :=
    @g_simpr
      (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
        (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
      p0008 p0009
  have p0011 :=
    @g_simpr (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)) p0010 p0011
  have p0013 := @g_hnqmap1fn A hyp_hnqincfun_3
  have p0014 := @g_fnfun (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_funbrfv (.cv p) (.cv y) (syn_chnqmap1 A)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (.cv y)) p0012 p0017
  have p0019 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_cfv (syn_chnqmap1 A) (.cv p)) (.cv y) p0018
  have p0023 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) p0010 p0023
  have p0025 := @g_brcnv (.cv x) (.cv p) (syn_chnqmap1 D)
  have p0026 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
      (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) p0024 p0025
  have p0027 := @g_hnqmap1fn D hyp_hnqincfun_2
  have p0028 := @g_fnfun (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @g_funbrfv (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x)) p0026 p0031
  have p0033 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0034 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) p0033 p0034
  have p0036 := @g_brcnv (.cv x) (.cv q) (syn_chnqmap1 D)
  have p0037 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
      (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv x)) p0035 p0036
  have p0041 := @g_funbrfv (.cv q) (.cv x) (syn_chnqmap1 D)
  have p0042 := Nominal.mp p0029 p0041
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv x))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (.cv x)) p0037 p0042
  have p0044 :=
    @g_eqtr4d
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x) (syn_cfv (syn_chnqmap1 D) (.cv q)) p0032
      p0043
  have p0052 := @g_breldm (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x))
      (.classMem (.cv p) (syn_cdm (syn_chnqmap1 D))) p0026 p0052
  have p0055 := @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0056 := Nominal.mp p0027 p0055
  have p0057 :=
    @g_syl6eleq
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (.cv p) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0053 p0056
  have p0063 := @g_breldm (.cv q) (.cv x) (syn_chnqmap1 D)
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv x))
      (.classMem (.cv q) (syn_cdm (syn_chnqmap1 D))) p0037 p0063
  have p0068 :=
    @g_syl6eleq
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (.cv q) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0064 p0056
  have p0069 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) p0057 p0068
  have p0070 :=
    @g_hnqmap1basecompat A D q p hyp_hnqincfun_1 hyp_hnqincfun_2 hyp_hnqincfun_3
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.imp (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
        (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))
      p0069 p0070
  have p0072 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      p0044 p0071
  have p0073 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (.cv y) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)) p0019
      p0072
  have p0075 :=
    @g_simpr (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)) p0033 p0075
  have p0080 := @g_funbrfv (.cv q) (.cv z) (syn_chnqmap1 A)
  have p0081 := Nominal.mp p0015 p0080
  have p0082 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (.cv z)) p0076 p0081
  have p0083 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))))
      (.cv y) (syn_cfv (syn_chnqmap1 A) (.cv q)) (.cv z) p0073 p0082
  have p0084 :=
    @g_exlimddv
      (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
            (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
      (.classEq (.cv y) (.cv z)) q dv_cache_0009 dv_cache_0010 p0007 p0083
  have p0085 :=
    @g_exlimddv
      (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y))
        (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
      (.classEq (.cv y) (.cv z)) p dv_cache_0011 dv_cache_0012 p0002 p0084
  have p0086 := Nominal.gen p0085 z
  have p0087 := Nominal.gen p0086 y
  have p0088 := Nominal.gen p0087 x
  have p0089 :=
    @g_dffun2 x y z (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0090_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wfun (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (.all x (.all y
            (.all z (.imp (syn_wa
                  (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
                    (.cv y))
                  (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
                    (.cv z))) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0089
  have p0090 :=
    @g_mpbir (syn_wfun (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))))
      (.all x (.all y (.all z (.imp (syn_wa
                (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
                  (.cv y))
                (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
                  (.cv z))) (.classEq (.cv y) (.cv z))))))
      p0088 p0090_e01_recanon
  have p0091 := (Nominal.classEqRefl (syn_chnqinc D A))
  have p0092 :=
    @g_funeq (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
  have p0093 := Nominal.mp p0091 p0092
  have p0094 :=
    @g_mpbir (syn_wfun (syn_chnqinc D A))
      (syn_wfun (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) p0090 p0093
  exact p0094

@[expose]
noncomputable def g_hnqincdm (A : Class) (D : Class)
    (hyp_hnqincdm_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqincdm_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqincdm_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cdm (syn_chnqinc D A)) (syn_chnord D)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnqinc D A))
  have p0001 :=
    @g_dmeqi (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
      p0000
  have p0002 := @g_hwcnssbase A D hyp_hnqincdm_1
  have p0003 := @g_pw1ss (syn_chwcn D) (syn_chwcn A)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cdm (syn_chnqmap1 D)))
  have p0006 :=
    @g_eqcomi (syn_cdm (syn_chnqmap1 D)) (syn_crn (syn_ccnv (syn_chnqmap1 D))) p0005
  have p0007 := @g_hnqmap1fn D hyp_hnqincdm_2
  have p0008 := @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_eqtri (syn_crn (syn_ccnv (syn_chnqmap1 D))) (syn_cdm (syn_chnqmap1 D))
      (syn_cpw1 (syn_chwcn D)) p0006 p0009
  have p0011 := @g_hnqmap1fn A hyp_hnqincdm_3
  have p0012 := @g_fndm (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_n_3sstr4i (syn_cpw1 (syn_chwcn D)) (syn_cpw1 (syn_chwcn A))
      (syn_crn (syn_ccnv (syn_chnqmap1 D))) (syn_cdm (syn_chnqmap1 A)) p0004 p0010 p0013
  have p0015 := @g_dmcosseq (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_dfrn4 (syn_chnqmap1 D)
  have p0018 :=
    @g_eqtr4i (syn_cdm (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))))
      (syn_cdm (syn_ccnv (syn_chnqmap1 D))) (syn_crn (syn_chnqmap1 D)) p0016 p0017
  have p0019 := @g_hnqmap1rn D hyp_hnqincdm_2
  have p0020 :=
    @g_eqtri (syn_cdm (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))))
      (syn_crn (syn_chnqmap1 D)) (syn_chnord D) p0018 p0019
  have p0021 :=
    @g_eqtri (syn_cdm (syn_chnqinc D A))
      (syn_cdm (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (syn_chnord D)
      p0001 p0020
  exact p0021

@[expose]
noncomputable def g_hnqincfn (A : Class) (D : Class)
    (hyp_hnqincfn_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqincfn_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqincfn_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_chnqinc D A) (syn_chnord D)) :=
  by
  have p0000 := @g_hnqincfun A D hyp_hnqincfn_1 hyp_hnqincfn_2 hyp_hnqincfn_3
  have p0001 := @g_hnqincdm A D hyp_hnqincfn_1 hyp_hnqincfn_2 hyp_hnqincfn_3
  have p0002 :=
    @g_pm3_2i (syn_wfun (syn_chnqinc D A))
      (.classEq (syn_cdm (syn_chnqinc D A)) (syn_chnord D)) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wfn (syn_chnqinc D A) (syn_chnord D)))
  have p0004 :=
    @g_mpbir (syn_wfn (syn_chnqinc D A) (syn_chnord D))
      (syn_wa (syn_wfun (syn_chnqinc D A))
        (.classEq (syn_cdm (syn_chnqinc D A)) (syn_chnord D)))
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_hnqincf (A : Class) (D : Class)
    (hyp_hnqincf_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqincf_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqincf_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) :=
  by
  have p0000 := @g_hnqincfn A D hyp_hnqincf_1 hyp_hnqincf_2 hyp_hnqincf_3
  have p0001 := @g_rncoss (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))
  have p0002 := (Nominal.classEqRefl (syn_chnqinc D A))
  have p0003 :=
    @g_rneqi (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
      p0002
  have p0004 := @g_hnqmap1rn A hyp_hnqincf_3
  have p0005 := @g_eqcomi (syn_crn (syn_chnqmap1 A)) (syn_chnord A) p0004
  have p0006 :=
    @g_n_3sstr4i (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))))
      (syn_crn (syn_chnqmap1 A)) (syn_crn (syn_chnqinc D A)) (syn_chnord A) p0001 p0003
      p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_chnqinc D A) (syn_chnord D))
      (syn_wss (syn_crn (syn_chnqinc D A)) (syn_chnord A)) p0000 p0006
  have p0008 :=
    (Nominal.biimpRefl (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)))
  have p0009 :=
    @g_mpbir (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))
      (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D))
        (syn_wss (syn_crn (syn_chnqinc D A)) (syn_chnord A)))
      p0007 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnqincf1 (A : Class) (D : Class)
    (hyp_hnqincf1_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqincf1_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqincf1_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let q : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cfv (syn_chnqinc D A) (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_not_A, fresh_p_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_chnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_p_not_A, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_ccnv (syn_chnqmap1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0005 : q ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_y, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_cfv (syn_chnqinc D A) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_y, fresh_q_not_A, fresh_q_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_ccnv (syn_chnqmap1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0009 : q ∉ ((Wff.classEq (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, or_false, not_false_eq_true])
  have dv_cache_0010 :
    q ∉
      ((syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_D, fresh_q_ne_y, fresh_q_not_A,
          fresh_q_ne_p, or_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((Wff.classEq (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
          (.classEq (syn_cfv (syn_chnqinc D A) (.cv x))
            (syn_cfv (syn_chnqinc D A) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_not_D, fresh_p_ne_y, fresh_p_not_A,
          or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_chnord D)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_y_not_D, not_false_eq_true])
  have dv_cache_0014 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0015 : x ∉ ((syn_chnord D)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_x_not_D, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_chnqinc D A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_chnqinc D A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_D, or_false, not_false_eq_true])
  have p0000 := @g_hnqincf A D hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0001 :=
    @g_simpl
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0002 := @g_eqid (syn_cfv (syn_chnqinc D A) (.cv x))
  have p0003 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv x)))
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) p0002
  have p0004 := @g_hnqincfn A D hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0005 :=
    @g_a1i (syn_wfn (syn_chnqinc D A) (syn_chnord D))
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) p0004
  have p0006 :=
    @g_simpl (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))
  have p0007 :=
    @g_jca (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv x) (syn_chnord D)) p0005
      p0006
  have p0008 :=
    @g_fnbrfvb (syn_chnord D) (.cv x) (syn_cfv (syn_chnqinc D A) (.cv x))
      (syn_chnqinc D A)
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv x) (syn_chnord D)))
      (syn_wb (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv x)))
        (syn_wbr (.cv x) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv x))))
      p0007 p0008
  have p0010 :=
    @g_mpbid
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv x)))
      (syn_wbr (.cv x) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv x))) p0003 p0009
  have p0011 := (Nominal.classEqRefl (syn_chnqinc D A))
  have p0012 :=
    @g_breqi (.cv x) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_chnqinc D A)
      (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0011
  have p0013 :=
    @g_sylib
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wbr (.cv x) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv x)))
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
        (syn_cfv (syn_chnqinc D A) (.cv x)))
      p0010 p0012
  have p0014 :=
    @g_brco p (.cv x) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_chnqmap1 A)
      (syn_ccnv (syn_chnqmap1 D)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0015 :=
    @g_sylib
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
        (syn_cfv (syn_chnqinc D A) (.cv x)))
      (syn_wex p (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      p0013 p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wex p (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      p0001 p0015
  have p0017 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
  have p0019 := @g_eqid (syn_cfv (syn_chnqinc D A) (.cv y))
  have p0020 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_cfv (syn_chnqinc D A) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) p0019
  have p0023 :=
    @g_simpr (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))
  have p0024 :=
    @g_jca (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)) p0005
      p0023
  have p0025 :=
    @g_fnbrfvb (syn_chnord D) (.cv y) (syn_cfv (syn_chnqinc D A) (.cv y))
      (syn_chnqinc D A)
  have p0026 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wb (.classEq (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_cfv (syn_chnqinc D A) (.cv y)))
        (syn_wbr (.cv y) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv y))))
      p0024 p0025
  have p0027 :=
    @g_mpbid
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_cfv (syn_chnqinc D A) (.cv y)))
      (syn_wbr (.cv y) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv y))) p0020 p0026
  have p0029 :=
    @g_breqi (.cv y) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_chnqinc D A)
      (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0011
  have p0030 :=
    @g_sylib
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wbr (.cv y) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv y)))
      (syn_wbr (.cv y) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
        (syn_cfv (syn_chnqinc D A) (.cv y)))
      p0027 p0029
  have p0031 :=
    @g_brco q (.cv y) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_chnqmap1 A)
      (syn_ccnv (syn_chnqmap1 D)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0032 :=
    @g_sylib
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wbr (.cv y) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
        (syn_cfv (syn_chnqinc D A) (.cv y)))
      (syn_wex q (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      p0030 p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (syn_wex q (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      p0001 p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
          (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wex q (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      p0017 p0033
  have p0035 :=
    @g_simpl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
          (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0036 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
          (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
      p0035 p0036
  have p0038 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) p0037 p0038
  have p0040 := @g_brcnv (.cv x) (.cv p) (syn_chnqmap1 D)
  have p0041 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
      (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) p0039 p0040
  have p0042 := @g_hnqmap1fn D hyp_hnqincf1_2
  have p0043 := @g_fnfun (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0044 := Nominal.mp p0042 p0043
  have p0045 := @g_funbrfv (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0046 := Nominal.mp p0044 p0045
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x)) p0041 p0046
  have p0048 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x) p0047
  have p0052 :=
    @g_simpr (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))) p0037 p0052
  have p0054 := @g_hnqmap1fn A hyp_hnqincf1_3
  have p0055 := @g_fnfun (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0056 := Nominal.mp p0054 p0055
  have p0057 := @g_funbrfv (.cv p) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_chnqmap1 A)
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqinc D A) (.cv x)))
      p0053 p0058
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
          (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      p0035 p0017
  have p0063 :=
    @g_simpr
      (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
      p0062 p0063
  have p0065 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqinc D A) (.cv x))
      (syn_cfv (syn_chnqinc D A) (.cv y)) p0059 p0064
  have p0066 :=
    @g_simpr
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
          (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0067 :=
    @g_simpr (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))) p0066 p0067
  have p0072 := @g_funbrfv (.cv q) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_chnqmap1 A)
  have p0073 := Nominal.mp p0056 p0072
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqinc D A) (.cv y)))
      p0068 p0073
  have p0075 :=
    @g_eqtr4d
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqinc D A) (.cv y))
      (syn_cfv (syn_chnqmap1 A) (.cv q)) p0065 p0074
  have p0083 := @g_breldm (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0084 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x))
      (.classMem (.cv p) (syn_cdm (syn_chnqmap1 D))) p0041 p0083
  have p0086 := @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0087 := Nominal.mp p0042 p0086
  have p0088 :=
    @g_syl6eleq
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (.cv p) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0084 p0087
  have p0090 :=
    @g_simpl (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
      (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) p0066 p0090
  have p0092 := @g_brcnv (.cv y) (.cv q) (syn_chnqmap1 D)
  have p0093 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
      (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv y)) p0091 p0092
  have p0094 := @g_breldm (.cv q) (.cv y) (syn_chnqmap1 D)
  have p0095 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv y))
      (.classMem (.cv q) (syn_cdm (syn_chnqmap1 D))) p0093 p0094
  have p0099 :=
    @g_syl6eleq
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (.cv q) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0095 p0087
  have p0100 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) p0088 p0099
  have p0101 := @g_hnqmap1basereflect A D q p hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0102 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))))
      (.imp (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
        (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))
      p0100 p0101
  have p0103 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
      p0075 p0102
  have p0104 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (.cv x) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)) p0048
      p0103
  have p0113 := @g_funbrfv (.cv q) (.cv y) (syn_chnqmap1 D)
  have p0114 := Nominal.mp p0044 p0113
  have p0115 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv y))
      (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (.cv y)) p0093 p0114
  have p0116 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
          (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
            (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
        (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
          (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))))
      (.cv x) (syn_cfv (syn_chnqmap1 D) (.cv q)) (.cv y) p0104 p0115
  have p0117 :=
    @g_exlimddv
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
          (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
          (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (.classEq (.cv x) (.cv y)) q dv_cache_0009 dv_cache_0010 p0034 p0116
  have p0118 :=
    @g_exlimddv
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
        (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
      (.classEq (.cv x) (.cv y)) p dv_cache_0011 dv_cache_0012 p0016 p0117
  have p0119 :=
    @g_ex (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)))
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
      (.classEq (.cv x) (.cv y)) p0118
  have p0120 :=
    @g_rgen2
      (.imp (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
        (.classEq (.cv x) (.cv y)))
      x y (syn_chnord D) (syn_chnord D) dv_cache_0013 dv_cache_0014 p0119
  have p0121 :=
    @g_pm3_2i (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))
      (syn_wral x (syn_chnord D) (syn_wral y (syn_chnord D) (.imp
            (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      p0000 p0120
  have p0122 :=
    @g_dff13 x y (syn_chnord D) (syn_chnord A) (syn_chnqinc D A) dv_cache_0015
      dv_cache_0013 dv_cache_0016 dv_cache_0017 dv_cache_0014
  have p0123_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))
        (syn_wa (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))
          (syn_wral x (syn_chnord D) (syn_wral y (syn_chnord D) (.imp
                (.classEq (syn_cfv (syn_chnqinc D A) (.cv x))
                  (syn_cfv (syn_chnqinc D A) (.cv y))) (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnqinc syn_chnord
          syn_cqs syn_wrex syn_cec syn_cima syn_csn syn_chwcn syn_chwniso
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0122
  have p0123 :=
    @g_mpbir (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))
      (syn_wa (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))
        (syn_wral x (syn_chnord D) (syn_wral y (syn_chnord D) (.imp
              (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      p0121 p0123_e01_recanon
  exact p0123


end NFChoice.DirectNominalPrf.WPPReplay

end
