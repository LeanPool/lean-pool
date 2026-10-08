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

/-- Checked nominal proof certificate identified upstream as `g_frecdomfv`. -/
@[expose]
noncomputable def gFrecdomfv (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.classMem (synCfv (synCfrec F I) N) (synCdm F))) :=
  by
  have p0000 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0001 := @gEqid (synCfrec F I)
  have p0002 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0003 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0004 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0005 :=
    @gFnfrec
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCfrec F I) F I p0001 p0002 p0003 p0004
  have p0007 := @gElex F (synCfuns)
  have p0008 :=
    @gSyl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem F (synCfuns)) (.classMem F (synCvv)) p0002 p0007
  have p0010 := @gFrecxpg (synCfrec F I) F I (synCvv) p0001
  have p0011 :=
    @gSyl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem F (synCvv))
      (synWss (synCfrec F I) (synCxp (synCnnc) (synCun (synCrn F) (synCsn I))))
      p0008 p0010
  have p0012 :=
    @gRnss (synCfrec F I) (synCxp (synCnnc) (synCun (synCrn F) (synCsn I)))
  have p0013 :=
    @gSyl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWss (synCfrec F I) (synCxp (synCnnc) (synCun (synCrn F) (synCsn I))))
      (synWss (synCrn (synCfrec F I))
        (synCrn (synCxp (synCnnc) (synCun (synCrn F) (synCsn I)))))
      p0011 p0012
  have p0014 := @gRnxpss (synCnnc) (synCun (synCrn F) (synCsn I))
  have p0015 :=
    @gSyl6ss
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCrn (synCfrec F I))
      (synCrn (synCxp (synCnnc) (synCun (synCrn F) (synCsn I))))
      (synCun (synCrn F) (synCsn I)) p0013 p0014
  have p0018 :=
    @gSnssd
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      I (synCdm F) p0003
  have p0019 :=
    @gUnssd
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCrn F) (synCsn I) (synCdm F) p0004 p0018
  have p0020 :=
    @gSstrd
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCrn (synCfrec F I)) (synCun (synCrn F) (synCsn I)) (synCdm F) p0015 p0019
  have p0021 :=
    @gJca
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWfn (synCfrec F I) (synCnnc)) (synWss (synCrn (synCfrec F I)) (synCdm F))
      p0005 p0020
  have p0022 := (Nominal.biimpRefl (synWf (synCfrec F I) (synCnnc) (synCdm F)))
  have p0023 :=
    @gBiimpri (synWf (synCfrec F I) (synCnnc) (synCdm F))
      (synWa (synWfn (synCfrec F I) (synCnnc))
        (synWss (synCrn (synCfrec F I)) (synCdm F)))
      p0022
  have p0024 :=
    @gSyl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWa (synWfn (synCfrec F I) (synCnnc))
        (synWss (synCrn (synCfrec F I)) (synCdm F)))
      (synWf (synCfrec F I) (synCnnc) (synCdm F)) p0021 p0023
  have p0025 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWf (synCfrec F I) (synCnnc) (synCdm F)) p0000 p0024
  have p0026 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0027 :=
    @gJca
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synWf (synCfrec F I) (synCnnc) (synCdm F)) (.classMem N (synCnnc)) p0025 p0026
  have p0028 := @gFfvelrn (synCnnc) (synCdm F) N (synCfrec F I)
  have p0029 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synWa (synWf (synCfrec F I) (synCnnc) (synCdm F)) (.classMem N (synCnnc)))
      (.classMem (synCfv (synCfrec F I) N) (synCdm F)) p0027 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_funeqfix`. -/
@[expose]
noncomputable def gFuneqfix (A : Class) (P : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWfun P) (synWfun Q)
          (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
        (synWb (.classMem A (synCfix (synCcom (synCcnv P) Q)))
          (.classEq (synCfv P A) (synCfv Q A)))) :=
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
  have dv_cache_0002 : z ∉ ((synCcnv P)).fv :=
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
      ((synW3a (synWfun P) (synWfun Q)
          (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))).fv :=
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
  have dv_cache_0005 : z ∉ ((synCfv Q A)).fv :=
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
  have dv_cache_0006 : z ∉ ((synCfv P A)).fv :=
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
  have p0000 := @gElfix A (synCcom (synCcnv P) Q)
  have p0001 :=
    @gBrco z A A (synCcnv P) Q dv_cache_0001 dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gBitri (.classMem A (synCfix (synCcom (synCcnv P) Q)))
      (synWbr A (synCcom (synCcnv P) Q) A)
      (synWex z (synWa (synWbr A Q (.cv z)) (synWbr (.cv z) (synCcnv P) A))) p0000
      p0001
  have p0003 :=
    @gA1i
      (synWb (.classMem A (synCfix (synCcom (synCcnv P) Q)))
        (synWex z (synWa (synWbr A Q (.cv z)) (synWbr (.cv z) (synCcnv P) A))))
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      p0002
  have p0004 :=
    @gSimp2 (synWfun P) (synWfun Q)
      (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q)))
  have p0005 :=
    @gSimp3 (synWfun P) (synWfun Q)
      (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q)))
  have p0006 := @gSimpr (.classMem A (synCdm P)) (.classMem A (synCdm Q))
  have p0007 :=
    @gSyl
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q)))
      (.classMem A (synCdm Q)) p0005 p0006
  have p0008 :=
    @gJca
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWfun Q) (.classMem A (synCdm Q)) p0004 p0007
  have p0009 := @gFunbrfvb A (.cv z) Q
  have p0010 :=
    @gSyl
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWa (synWfun Q) (.classMem A (synCdm Q)))
      (synWb (.classEq (synCfv Q A) (.cv z)) (synWbr A Q (.cv z))) p0008 p0009
  have p0011 :=
    @gBicomd
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (.classEq (synCfv Q A) (.cv z)) (synWbr A Q (.cv z)) p0010
  have p0012 := @gBrcnv (.cv z) A P
  have p0013 :=
    @gA1i (synWb (synWbr (.cv z) (synCcnv P) A) (synWbr A P (.cv z)))
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      p0012
  have p0014 :=
    @gSimp1 (synWfun P) (synWfun Q)
      (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q)))
  have p0016 := @gSimpl (.classMem A (synCdm P)) (.classMem A (synCdm Q))
  have p0017 :=
    @gSyl
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q)))
      (.classMem A (synCdm P)) p0005 p0016
  have p0018 :=
    @gJca
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWfun P) (.classMem A (synCdm P)) p0014 p0017
  have p0019 := @gFunbrfvb A (.cv z) P
  have p0020 :=
    @gSyl
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWa (synWfun P) (.classMem A (synCdm P)))
      (synWb (.classEq (synCfv P A) (.cv z)) (synWbr A P (.cv z))) p0018 p0019
  have p0021 :=
    @gBicomd
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (.classEq (synCfv P A) (.cv z)) (synWbr A P (.cv z)) p0020
  have p0022 :=
    @gBitrd
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWbr (.cv z) (synCcnv P) A) (synWbr A P (.cv z))
      (.classEq (synCfv P A) (.cv z)) p0013 p0021
  have p0023 :=
    @gAnbi12d
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWbr A Q (.cv z)) (.classEq (synCfv Q A) (.cv z))
      (synWbr (.cv z) (synCcnv P) A) (.classEq (synCfv P A) (.cv z)) p0011 p0022
  have p0024 :=
    @gExbidv
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWa (synWbr A Q (.cv z)) (synWbr (.cv z) (synCcnv P) A))
      (synWa (.classEq (synCfv Q A) (.cv z)) (.classEq (synCfv P A) (.cv z))) z
      dv_cache_0004 p0023
  have p0025 := @gEqcom (synCfv Q A) (.cv z)
  have p0026 := @gEqcom (synCfv P A) (.cv z)
  have p0027 :=
    @gAnbi12i (.classEq (synCfv Q A) (.cv z)) (.classEq (.cv z) (synCfv Q A))
      (.classEq (synCfv P A) (.cv z)) (.classEq (.cv z) (synCfv P A)) p0025 p0026
  have p0028 :=
    @gExbii (synWa (.classEq (synCfv Q A) (.cv z)) (.classEq (synCfv P A) (.cv z)))
      (synWa (.classEq (.cv z) (synCfv Q A)) (.classEq (.cv z) (synCfv P A))) z p0027
  have p0029 := @gFvex A Q
  have p0030 := @gEqvinc z (synCfv Q A) (synCfv P A) dv_cache_0005 dv_cache_0006 p0029
  have p0031 :=
    @gBicomi (.classEq (synCfv Q A) (synCfv P A))
      (synWex z (synWa (.classEq (.cv z) (synCfv Q A)) (.classEq (.cv z) (synCfv P A))))
      p0030
  have p0032 :=
    @gBitri
      (synWex z (synWa (.classEq (synCfv Q A) (.cv z)) (.classEq (synCfv P A) (.cv z))))
      (synWex z (synWa (.classEq (.cv z) (synCfv Q A)) (.classEq (.cv z) (synCfv P A))))
      (.classEq (synCfv Q A) (synCfv P A)) p0028 p0031
  have p0033 := @gEqcom (synCfv Q A) (synCfv P A)
  have p0034 :=
    @gBitri
      (synWex z (synWa (.classEq (synCfv Q A) (.cv z)) (.classEq (synCfv P A) (.cv z))))
      (.classEq (synCfv Q A) (synCfv P A)) (.classEq (synCfv P A) (synCfv Q A)) p0032
      p0033
  have p0035 :=
    @gA1i
      (synWb (synWex z
          (synWa (.classEq (synCfv Q A) (.cv z)) (.classEq (synCfv P A) (.cv z))))
        (.classEq (synCfv P A) (synCfv Q A)))
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      p0034
  have p0036 :=
    @gBitrd
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (synWex z (synWa (synWbr A Q (.cv z)) (synWbr (.cv z) (synCcnv P) A)))
      (synWex z (synWa (.classEq (synCfv Q A) (.cv z)) (.classEq (synCfv P A) (.cv z))))
      (.classEq (synCfv P A) (synCfv Q A)) p0024 p0035
  have p0037 :=
    @gBitrd
      (synW3a (synWfun P) (synWfun Q)
        (synWa (.classMem A (synCdm P)) (.classMem A (synCdm Q))))
      (.classMem A (synCfix (synCcom (synCcnv P) Q)))
      (synWex z (synWa (synWbr A Q (.cv z)) (synWbr (.cv z) (synCcnv P) A)))
      (.classEq (synCfv P A) (synCfv Q A)) p0003 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_frecteqex`. -/
@[expose]
noncomputable def gFrecteqex (F : Class) (G : Class) (I : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
        (.classMem (synCfrecteq F G I) (synCvv))) :=
  by
  have p0000 := @gTcfnex
  have p0001 :=
    @gA1i (.classMem (synCtcfn) (synCvv))
      (synWa (.classMem F (synCvv)) (.classMem G (synCvv))) p0000
  have p0002 := @gSimpl (.classMem F (synCvv)) (.classMem G (synCvv))
  have p0003 := @gEqid (synCfrec F I)
  have p0004 := @gFrecexg (synCfrec F I) F I (synCvv) p0003
  have p0005 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem F (synCvv)) (.classMem (synCfrec F I) (synCvv)) p0002 p0004
  have p0006 := @gSiexg (synCfrec F I) (synCvv)
  have p0007 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCfrec F I) (synCvv))
      (.classMem (synCsi (synCfrec F I)) (synCvv)) p0005 p0006
  have p0008 :=
    @gJca (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCtcfn) (synCvv)) (.classMem (synCsi (synCfrec F I)) (synCvv))
      p0001 p0007
  have p0009 := @gCoexg (synCtcfn) (synCsi (synCfrec F I)) (synCvv) (synCvv)
  have p0010 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (synWa (.classMem (synCtcfn) (synCvv)) (.classMem (synCsi (synCfrec F I)) (synCvv)))
      (.classMem (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCvv)) p0008 p0009
  have p0011 := @gCnvexg (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCvv)
  have p0012 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCvv))
      (.classMem (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I)))) (synCvv))
      p0010 p0011
  have p0013 := @gSimpr (.classMem F (synCvv)) (.classMem G (synCvv))
  have p0014 := @gEqid (synCfrec G (synCtc I))
  have p0015 := @gFrecexg (synCfrec G (synCtc I)) G (synCtc I) (synCvv) p0014
  have p0016 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem G (synCvv)) (.classMem (synCfrec G (synCtc I)) (synCvv)) p0013 p0015
  have p0019 :=
    @gJca (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCfrec G (synCtc I)) (synCvv)) (.classMem (synCtcfn) (synCvv))
      p0016 p0001
  have p0020 := @gCoexg (synCfrec G (synCtc I)) (synCtcfn) (synCvv) (synCvv)
  have p0021 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (synWa (.classMem (synCfrec G (synCtc I)) (synCvv)) (.classMem (synCtcfn) (synCvv)))
      (.classMem (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCvv)) p0019 p0020
  have p0022 :=
    @gJca (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I)))) (synCvv))
      (.classMem (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCvv)) p0012 p0021
  have p0023 :=
    @gCoexg (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
      (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCvv) (synCvv)
  have p0024 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (synWa (.classMem (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I)))) (synCvv))
        (.classMem (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCvv)))
      (.classMem (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
          (synCcom (synCfrec G (synCtc I)) (synCtcfn))) (synCvv))
      p0022 p0023
  have p0025 :=
    @gFixexg
      (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
        (synCcom (synCfrec G (synCtc I)) (synCtcfn)))
      (synCvv)
  have p0026 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
          (synCcom (synCfrec G (synCtc I)) (synCtcfn))) (synCvv))
      (.classMem (synCfix (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
            (synCcom (synCfrec G (synCtc I)) (synCtcfn)))) (synCvv))
      p0024 p0025
  have p0027 :=
    @gUni1exg
      (synCfix (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
          (synCcom (synCfrec G (synCtc I)) (synCtcfn))))
      (synCvv)
  have p0028 :=
    @gSyl (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCfix (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
            (synCcom (synCfrec G (synCtc I)) (synCtcfn)))) (synCvv))
      (.classMem (synCuni1 (synCfix
            (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
              (synCcom (synCfrec G (synCtc I)) (synCtcfn))))) (synCvv))
      p0026 p0027
  have p0029 := (Nominal.classEqRefl (synCfrecteq F G I))
  have p0030 :=
    @gEleq1i (synCfrecteq F G I)
      (synCuni1 (synCfix (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
            (synCcom (synCfrec G (synCtc I)) (synCtcfn)))))
      (synCvv) p0029
  have p0031 :=
    @gSylibr (synWa (.classMem F (synCvv)) (.classMem G (synCvv)))
      (.classMem (synCuni1 (synCfix
            (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
              (synCcom (synCfrec G (synCtc I)) (synCtcfn))))) (synCvv))
      (.classMem (synCfrecteq F G I) (synCvv)) p0028 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_sifnvalv`. -/
@[expose]
noncomputable def gSifnvalv (x : Var) (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem (.cv x) A))
        (.classEq (synCfv (synCsi F) (synCsn (.cv x))) (synCsn (synCfv F (.cv x))))) :=
  by
  have p0000 := @gEqid (synCfv F (.cv x))
  have p0001 :=
    @gA1i (.classEq (synCfv F (.cv x)) (synCfv F (.cv x)))
      (synWa (synWfn F A) (.classMem (.cv x) A)) p0000
  have p0002 := @gFnopfvb A (.cv x) (synCfv F (.cv x)) F
  have p0003 :=
    @gMpbid (synWa (synWfn F A) (.classMem (.cv x) A))
      (.classEq (synCfv F (.cv x)) (synCfv F (.cv x)))
      (.classMem (synCop (.cv x) (synCfv F (.cv x))) F) p0001 p0002
  have p0004 := @gVex x
  have p0005 := @gFvex (.cv x) F
  have p0006 := @gOpsnelsi (.cv x) (synCfv F (.cv x)) F p0004 p0005
  have p0007 :=
    @gSylibr (synWa (synWfn F A) (.classMem (.cv x) A))
      (.classMem (synCop (.cv x) (synCfv F (.cv x))) F)
      (.classMem (synCop (synCsn (.cv x)) (synCsn (synCfv F (.cv x)))) (synCsi F))
      p0003 p0006
  have p0008 := @gSimpl (synWfn F A) (.classMem (.cv x) A)
  have p0009 := @gFnfun A F
  have p0010 :=
    @gSyl (synWa (synWfn F A) (.classMem (.cv x) A)) (synWfn F A) (synWfun F) p0008
      p0009
  have p0011 := @gFunsi F
  have p0012 :=
    @gSyl (synWa (synWfn F A) (.classMem (.cv x) A)) (synWfun F)
      (synWfun (synCsi F)) p0010 p0011
  have p0013 := @gFunopfv (synCsn (.cv x)) (synCsn (synCfv F (.cv x))) (synCsi F)
  have p0014 :=
    @gSyl (synWa (synWfn F A) (.classMem (.cv x) A)) (synWfun (synCsi F))
      (.imp (.classMem (synCop (synCsn (.cv x)) (synCsn (synCfv F (.cv x)))) (synCsi F))
        (.classEq (synCfv (synCsi F) (synCsn (.cv x))) (synCsn (synCfv F (.cv x)))))
      p0012 p0013
  have p0015 :=
    @gMpd (synWa (synWfn F A) (.classMem (.cv x) A))
      (.classMem (synCop (synCsn (.cv x)) (synCsn (synCfv F (.cv x)))) (synCsi F))
      (.classEq (synCfv (synCsi F) (synCsn (.cv x))) (synCsn (synCfv F (.cv x))))
      p0007 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_tcfnfv`. -/
@[expose]
noncomputable def gTcfnfv (A : Class)
    (hyp_tcfnfv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCtcfn) (synCsn A)) (synCtc A)) :=
  by
  have p0000 := @gEqid (synCtc A)
  have p0001 := @gBrtcfn A (synCtc A) hyp_tcfnfv_1
  have p0002 :=
    @gMpbir (synWbr (synCsn A) (synCtcfn) (synCtc A))
      (.classEq (synCtc A) (synCtc A)) p0000 p0001
  have p0003 := @gFntcfn
  have p0004 := @gSnel1c A hyp_tcfnfv_1
  have p0005 :=
    @gPm32i (synWfn (synCtcfn) (synC1c)) (.classMem (synCsn A) (synC1c)) p0003
      p0004
  have p0006 := @gFnbrfvb (synC1c) (synCsn A) (synCtc A) (synCtcfn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gMpbir (.classEq (synCfv (synCtcfn) (synCsn A)) (synCtc A))
      (synWbr (synCsn A) (synCtcfn) (synCtc A)) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_frecteqval`. -/
@[expose]
noncomputable def gFrecteqval (n : Var) (F : Class) (G : Class) (I : Class)
    (hyp_frecteqval_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_frecteqval_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_frecteqval_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_frecteqval_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_frecteqval_5 : Nominal.NPrf (.classMem (synCtc I) (synCdm G)))
    (hyp_frecteqval_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCfrecteq F G I))
          (.classEq (synCtc (synCfv (synCfrec F I) (.cv n)))
            (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfrecteq F G I))
  have p0001 :=
    @gEleq2i (synCfrecteq F G I)
      (synCuni1 (synCfix (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
            (synCcom (synCfrec G (synCtc I)) (synCtcfn)))))
      (.cv n) p0000
  have p0002 := @gVex n
  have p0003 :=
    @gEluni1 (.cv n)
      (synCfix (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
          (synCcom (synCfrec G (synCtc I)) (synCtcfn))))
      p0002
  have p0004 :=
    @gBitri (.classMem (.cv n) (synCfrecteq F G I))
      (.classMem (.cv n) (synCuni1 (synCfix
            (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
              (synCcom (synCfrec G (synCtc I)) (synCtcfn))))))
      (.classMem (synCsn (.cv n)) (synCfix
          (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
            (synCcom (synCfrec G (synCtc I)) (synCtcfn)))))
      p0001 p0003
  have p0005 :=
    @gA1i
      (synWb (.classMem (.cv n) (synCfrecteq F G I)) (.classMem (synCsn (.cv n)) (synCfix
            (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
              (synCcom (synCfrec G (synCtc I)) (synCtcfn))))))
      (.classMem (.cv n) (synCnnc)) p0004
  have p0006 := @gFntcfn
  have p0007 := @gFnfun (synC1c) (synCtcfn)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0010 := @gEqid (synCfrec F I)
  have p0011 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0012 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0013 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0014 :=
    @gFnfrec
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCfrec F I) F I p0010 p0011 p0012 p0013
  have p0015 := Nominal.mp p0009 p0014
  have p0016 := @gFnfun (synCnnc) (synCfrec F I)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @gFunsi (synCfrec F I)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gPm32i (synWfun (synCtcfn)) (synWfun (synCsi (synCfrec F I))) p0008 p0019
  have p0021 := @gFunco (synCtcfn) (synCsi (synCfrec F I))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gA1i (synWfun (synCcom (synCtcfn) (synCsi (synCfrec F I))))
      (.classMem (.cv n) (synCnnc)) p0022
  have p0024 :=
    @gN3pm32i (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G)) hyp_frecteqval_4 hyp_frecteqval_5 hyp_frecteqval_6
  have p0025 := @gEqid (synCfrec G (synCtc I))
  have p0026 :=
    @gSimp1 (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G))
  have p0027 :=
    @gSimp2 (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G))
  have p0028 :=
    @gSimp3 (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G))
  have p0029 :=
    @gFnfrec
      (synW3a (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
        (synWss (synCrn G) (synCdm G)))
      (synCfrec G (synCtc I)) G (synCtc I) p0025 p0026 p0027 p0028
  have p0030 := Nominal.mp p0024 p0029
  have p0031 := @gFnfun (synCnnc) (synCfrec G (synCtc I))
  have p0032 := Nominal.mp p0030 p0031
  have p0036 :=
    @gPm32i (synWfun (synCfrec G (synCtc I))) (synWfun (synCtcfn)) p0032 p0008
  have p0037 := @gFunco (synCfrec G (synCtc I)) (synCtcfn)
  have p0038 := Nominal.mp p0036 p0037
  have p0039 :=
    @gA1i (synWfun (synCcom (synCfrec G (synCtc I)) (synCtcfn)))
      (.classMem (.cv n) (synCnnc)) p0038
  have p0040 := @gFvex (.cv n) (synCfrec F I)
  have p0041 := @gSnel1c (synCfv (synCfrec F I) (.cv n)) p0040
  have p0043 := @gFndm (synC1c) (synCtcfn)
  have p0044 := Nominal.mp p0006 p0043
  have p0045 :=
    @gEleq2i (synCdm (synCtcfn)) (synC1c) (synCsn (synCfv (synCfrec F I) (.cv n)))
      p0044
  have p0046 :=
    @gMpbir (.classMem (synCsn (synCfv (synCfrec F I) (.cv n))) (synCdm (synCtcfn)))
      (.classMem (synCsn (synCfv (synCfrec F I) (.cv n))) (synC1c)) p0041 p0045
  have p0047 :=
    @gA1i (.classMem (synCsn (synCfv (synCfrec F I) (.cv n))) (synCdm (synCtcfn)))
      (.classMem (.cv n) (synCnnc)) p0046
  have p0055 := @gSifnvalv n (synCnnc) (synCfrec F I)
  have p0056 :=
    @gMpan (synWfn (synCfrec F I) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.classEq (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n)))
        (synCsn (synCfv (synCfrec F I) (.cv n))))
      p0015 p0055
  have p0057 :=
    @gEleq1d (.classMem (.cv n) (synCnnc))
      (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n)))
      (synCsn (synCfv (synCfrec F I) (.cv n))) (synCdm (synCtcfn)) p0056
  have p0058 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n))) (synCdm (synCtcfn)))
      (.classMem (synCsn (synCfv (synCfrec F I) (.cv n))) (synCdm (synCtcfn))) p0047
      p0057
  have p0070 :=
    @gA1i (synWfun (synCsi (synCfrec F I))) (.classMem (.cv n) (synCnnc)) p0019
  have p0071 := @gSnelpw1 (.cv n) (synCnnc)
  have p0072 :=
    @gBiimpri (.classMem (synCsn (.cv n)) (synCpw1 (synCnnc)))
      (.classMem (.cv n) (synCnnc)) p0071
  have p0073 := @gDmsi (synCfrec F I)
  have p0081 := @gFndm (synCnnc) (synCfrec F I)
  have p0082 := Nominal.mp p0015 p0081
  have p0083 := @gPw1eq (synCdm (synCfrec F I)) (synCnnc)
  have p0084 := Nominal.mp p0082 p0083
  have p0085 :=
    @gEqtri (synCdm (synCsi (synCfrec F I))) (synCpw1 (synCdm (synCfrec F I)))
      (synCpw1 (synCnnc)) p0073 p0084
  have p0086 :=
    @gEleq2i (synCdm (synCsi (synCfrec F I))) (synCpw1 (synCnnc)) (synCsn (.cv n))
      p0085
  have p0087 :=
    @gSylibr (.classMem (.cv n) (synCnnc))
      (.classMem (synCsn (.cv n)) (synCpw1 (synCnnc)))
      (.classMem (synCsn (.cv n)) (synCdm (synCsi (synCfrec F I)))) p0072 p0086
  have p0088 :=
    @gJca (.classMem (.cv n) (synCnnc)) (synWfun (synCsi (synCfrec F I)))
      (.classMem (synCsn (.cv n)) (synCdm (synCsi (synCfrec F I)))) p0070 p0087
  have p0089 := @gDmfco (synCsn (.cv n)) (synCtcfn) (synCsi (synCfrec F I))
  have p0090 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (synWfun (synCsi (synCfrec F I)))
        (.classMem (synCsn (.cv n)) (synCdm (synCsi (synCfrec F I)))))
      (synWb (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCtcfn) (synCsi (synCfrec F I)))))
        (.classMem (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n))) (synCdm (synCtcfn))))
      p0088 p0089
  have p0091 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCtcfn) (synCsi (synCfrec F I)))))
      (.classMem (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n))) (synCdm (synCtcfn)))
      p0058 p0090
  have p0092 := @gNntccl (.cv n)
  have p0094 := @gTcfnfv (.cv n) p0002
  have p0095 :=
    @gEleq1i (synCfv (synCtcfn) (synCsn (.cv n))) (synCtc (.cv n))
      (synCdm (synCfrec G (synCtc I))) p0094
  have p0103 := @gFndm (synCnnc) (synCfrec G (synCtc I))
  have p0104 := Nominal.mp p0030 p0103
  have p0105 :=
    @gEleq2i (synCdm (synCfrec G (synCtc I))) (synCnnc) (synCtc (.cv n)) p0104
  have p0106 :=
    @gBitri
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCdm (synCfrec G (synCtc I))))
      (.classMem (synCtc (.cv n)) (synCdm (synCfrec G (synCtc I))))
      (.classMem (synCtc (.cv n)) (synCnnc)) p0095 p0105
  have p0107 :=
    @gSylibr (.classMem (.cv n) (synCnnc)) (.classMem (synCtc (.cv n)) (synCnnc))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCdm (synCfrec G (synCtc I))))
      p0092 p0106
  have p0112 := @gSnel1c (.cv n) p0002
  have p0116 := @gEleq2i (synCdm (synCtcfn)) (synC1c) (synCsn (.cv n)) p0044
  have p0117 :=
    @gMpbir (.classMem (synCsn (.cv n)) (synCdm (synCtcfn)))
      (.classMem (synCsn (.cv n)) (synC1c)) p0112 p0116
  have p0118 :=
    @gPm32i (synWfun (synCtcfn)) (.classMem (synCsn (.cv n)) (synCdm (synCtcfn)))
      p0008 p0117
  have p0119 := @gDmfco (synCsn (.cv n)) (synCfrec G (synCtc I)) (synCtcfn)
  have p0120 := Nominal.mp p0118 p0119
  have p0121 :=
    @gSylibr (.classMem (.cv n) (synCnnc))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCdm (synCfrec G (synCtc I))))
      (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCfrec G (synCtc I)) (synCtcfn))))
      p0107 p0120
  have p0122 :=
    @gJca (.classMem (.cv n) (synCnnc))
      (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCtcfn) (synCsi (synCfrec F I)))))
      (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCfrec G (synCtc I)) (synCtcfn))))
      p0091 p0121
  have p0123 :=
    @gN3jca (.classMem (.cv n) (synCnnc))
      (synWfun (synCcom (synCtcfn) (synCsi (synCfrec F I))))
      (synWfun (synCcom (synCfrec G (synCtc I)) (synCtcfn)))
      (synWa (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCtcfn) (synCsi (synCfrec F I)))))
        (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCfrec G (synCtc I)) (synCtcfn)))))
      p0023 p0039 p0122
  have p0124 :=
    @gFuneqfix (synCsn (.cv n)) (synCcom (synCtcfn) (synCsi (synCfrec F I)))
      (synCcom (synCfrec G (synCtc I)) (synCtcfn))
  have p0125 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synW3a (synWfun (synCcom (synCtcfn) (synCsi (synCfrec F I))))
        (synWfun (synCcom (synCfrec G (synCtc I)) (synCtcfn))) (synWa
          (.classMem (synCsn (.cv n))
            (synCdm (synCcom (synCtcfn) (synCsi (synCfrec F I)))))
          (.classMem (synCsn (.cv n))
            (synCdm (synCcom (synCfrec G (synCtc I)) (synCtcfn))))))
      (synWb (.classMem (synCsn (.cv n)) (synCfix
            (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
              (synCcom (synCfrec G (synCtc I)) (synCtcfn))))) (.classEq
          (synCfv (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCsn (.cv n)))
          (synCfv (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCsn (.cv n)))))
      p0123 p0124
  have p0126 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCfrecteq F G I))
      (.classMem (synCsn (.cv n)) (synCfix
          (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
            (synCcom (synCfrec G (synCtc I)) (synCtcfn)))))
      (.classEq (synCfv (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCsn (.cv n)))
        (synCfv (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCsn (.cv n))))
      p0005 p0125
  have p0157 := @gFvco (synCsn (.cv n)) (synCtcfn) (synCsi (synCfrec F I))
  have p0158 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (synWfun (synCsi (synCfrec F I)))
        (.classMem (synCsn (.cv n)) (synCdm (synCsi (synCfrec F I)))))
      (.classEq (synCfv (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCsn (.cv n)))
        (synCfv (synCtcfn) (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n)))))
      p0088 p0157
  have p0168 :=
    @gFveq2d (.classMem (.cv n) (synCnnc))
      (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n)))
      (synCsn (synCfv (synCfrec F I) (.cv n))) (synCtcfn) p0056
  have p0169 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCsn (.cv n)))
      (synCfv (synCtcfn) (synCfv (synCsi (synCfrec F I)) (synCsn (.cv n))))
      (synCfv (synCtcfn) (synCsn (synCfv (synCfrec F I) (.cv n)))) p0158 p0168
  have p0171 := @gTcfnfv (synCfv (synCfrec F I) (.cv n)) p0040
  have p0172 :=
    @gA1i
      (.classEq (synCfv (synCtcfn) (synCsn (synCfv (synCfrec F I) (.cv n))))
        (synCtc (synCfv (synCfrec F I) (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0171
  have p0173 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCsn (.cv n)))
      (synCfv (synCtcfn) (synCsn (synCfv (synCfrec F I) (.cv n))))
      (synCtc (synCfv (synCfrec F I) (.cv n))) p0169 p0172
  have p0185 := @gFvco (synCsn (.cv n)) (synCfrec G (synCtc I)) (synCtcfn)
  have p0186 := Nominal.mp p0118 p0185
  have p0189 :=
    @gFveq2i (synCfv (synCtcfn) (synCsn (.cv n))) (synCtc (.cv n))
      (synCfrec G (synCtc I)) p0094
  have p0190 :=
    @gEqtri (synCfv (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCsn (.cv n)))
      (synCfv (synCfrec G (synCtc I)) (synCfv (synCtcfn) (synCsn (.cv n))))
      (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n))) p0186 p0189
  have p0191 :=
    @gA1i
      (.classEq (synCfv (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCsn (.cv n)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0190
  have p0192 :=
    @gEqeq12d (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCsn (.cv n)))
      (synCtc (synCfv (synCfrec F I) (.cv n)))
      (synCfv (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCsn (.cv n)))
      (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n))) p0173 p0191
  have p0193 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCfrecteq F G I))
      (.classEq (synCfv (synCcom (synCtcfn) (synCsi (synCfrec F I))) (synCsn (.cv n)))
        (synCfv (synCcom (synCfrec G (synCtc I)) (synCtcfn)) (synCsn (.cv n))))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv n)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n))))
      p0126 p0192
  exact p0193

/-- Checked nominal proof certificate identified upstream as `g_frecteqvalcl`. -/
@[expose]
noncomputable def gFrecteqvalcl (B : Class) (F : Class) (G : Class) (I : Class)
    (hyp_frecteqvalcl_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_frecteqvalcl_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_frecteqvalcl_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_frecteqvalcl_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_frecteqvalcl_5 : Nominal.NPrf (.classMem (synCtc I) (synCdm G)))
    (hyp_frecteqvalcl_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCfrecteq F G I))
          (.classEq (synCtc (synCfv (synCfrec F I) B))
            (synCfv (synCfrec G (synCtc I)) (synCtc B))))) :=
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
      ((Wff.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCfrecteq F G I))
            (.classEq (synCtc (synCfv (synCfrec F I) B))
              (synCfv (synCfrec G (synCtc I)) (synCtc B)))))).fv :=
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
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gId (.classEq (.cv n) B)
  have p0002 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCnnc) p0001
  have p0004 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCfrecteq F G I) p0001
  have p0006 := @gFveq2d (.classEq (.cv n) B) (.cv n) B (synCfrec F I) p0001
  have p0007 := @gTceq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec F I) B)
  have p0008 :=
    @gSyl (.classEq (.cv n) B)
      (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec F I) B))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv n)))
        (synCtc (synCfv (synCfrec F I) B)))
      p0006 p0007
  have p0010 := @gTceq (.cv n) B
  have p0011 :=
    @gSyl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (synCtc (.cv n)) (synCtc B)) p0001 p0010
  have p0012 :=
    @gFveq2d (.classEq (.cv n) B) (synCtc (.cv n)) (synCtc B) (synCfrec G (synCtc I))
      p0011
  have p0013 :=
    @gEqeq12d (.classEq (.cv n) B) (synCtc (synCfv (synCfrec F I) (.cv n)))
      (synCtc (synCfv (synCfrec F I) B))
      (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n)))
      (synCfv (synCfrec G (synCtc I)) (synCtc B)) p0008 p0012
  have p0014 :=
    @gBibi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCfrecteq F G I))
      (.classMem B (synCfrecteq F G I))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv n)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n))))
      (.classEq (synCtc (synCfv (synCfrec F I) B))
        (synCfv (synCfrec G (synCtc I)) (synCtc B)))
      p0004 p0013
  have p0015 :=
    @gImbi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCnnc))
      (.classMem B (synCnnc))
      (synWb (.classMem (.cv n) (synCfrecteq F G I))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv n)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n)))))
      (synWb (.classMem B (synCfrecteq F G I)) (.classEq (synCtc (synCfv (synCfrec F I) B))
          (synCfv (synCfrec G (synCtc I)) (synCtc B))))
      p0002 p0014
  have p0016 :=
    @gFrecteqval n F G I hyp_frecteqvalcl_1 hyp_frecteqvalcl_2 hyp_frecteqvalcl_3
      hyp_frecteqvalcl_4 hyp_frecteqvalcl_5 hyp_frecteqvalcl_6
  have p0017 :=
    @gVtoclg
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCfrecteq F G I))
          (.classEq (synCtc (synCfv (synCfrec F I) (.cv n)))
            (synCfv (synCfrec G (synCtc I)) (synCtc (.cv n))))))
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCfrecteq F G I))
          (.classEq (synCtc (synCfv (synCfrec F I) B))
            (synCfv (synCfrec G (synCtc I)) (synCtc B)))))
      n B (synCnnc) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 :=
    @gMpd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (synWb (.classMem B (synCfrecteq F G I)) (.classEq (synCtc (synCfv (synCfrec F I) B))
          (synCfv (synCfrec G (synCtc I)) (synCtc B))))
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

/-- Checked nominal proof certificate identified upstream as `g_frectchom0`. -/
@[expose]
noncomputable def gFrectchom0 (x : Var) (F : Class) (G : Class) (I : Class) (N : Class)
    (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) (dv_I_x : x ∉ I.fv)
    (hyp_frectchom0_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_frectchom0_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_frectchom0_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_frectchom0_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_frectchom0_5 : Nominal.NPrf (.classMem (synCtc I) (synCdm G)))
    (hyp_frectchom0_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_frectchom0_7 : Nominal.NPrf (synWral x (synCdm F)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x)))))) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (.classEq (synCtc (synCfv (synCfrec F I) N))
          (synCfv (synCfrec G (synCtc I)) (synCtc N)))) :=
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
  have dv_cache_0001 : n ∉ ((synCfrecteq F G I)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq,
          Finset.mem_union, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, or_false,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCfv (synCfrec F I) (.cv m))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCdm F)).fv :=
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
      ((Wff.classEq (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m))))
          (synCfv G (synCtc (synCfv (synCfrec F I) (.cv m)))))).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv m) (synCnnc))).fv :=
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
  have dv_cache_0007 : n ∉ ((Wff.classMem (.cv m) (synCfrecteq F G I))).fv :=
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
  have dv_cache_0008 : m ∉ ((Wff.classMem (.cv n) (synCfrecteq F G I))).fv :=
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
  have dv_cache_0009 : n ∉ ((Wff.classMem (synC0c) (synCfrecteq F G I))).fv :=
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
  have dv_cache_0010 : n ∉ ((Wff.classMem N (synCfrecteq F G I))).fv :=
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
    n ∉ ((Wff.classMem (synCplc (.cv m) (synC1c)) (synCfrecteq F G I))).fv :=
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
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_frectchom0_1 p0000
  have p0002 := @gElex G (synCfuns)
  have p0003 := Nominal.mp hyp_frectchom0_4 p0002
  have p0004 := @gPm32i (.classMem F (synCvv)) (.classMem G (synCvv)) p0001 p0003
  have p0005 := @gFrecteqex F G I
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gAbid2 n (synCfrecteq F G I) dv_cache_0001
  have p0008 :=
    @gEleq1i (.cab n (.classMem (.cv n) (synCfrecteq F G I))) (synCfrecteq F G I)
      (synCvv) p0007
  have p0009 :=
    @gMpbir (.classMem (.cab n (.classMem (.cv n) (synCfrecteq F G I))) (synCvv))
      (.classMem (synCfrecteq F G I) (synCvv)) p0006 p0008
  have p0010 := @gId (.classEq (.cv n) (synC0c))
  have p0011 :=
    @gEleq1d (.classEq (.cv n) (synC0c)) (.cv n) (synC0c) (synCfrecteq F G I) p0010
  have p0012 := @gId (.classEq (.cv n) (.cv m))
  have p0013 :=
    @gEleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (synCfrecteq F G I) p0012
  have p0014 := @gId (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
  have p0015 :=
    @gEleq1d (.classEq (.cv n) (synCplc (.cv m) (synC1c))) (.cv n)
      (synCplc (.cv m) (synC1c)) (synCfrecteq F G I) p0014
  have p0016 := @gId (.classEq (.cv n) N)
  have p0017 := @gEleq1d (.classEq (.cv n) N) (.cv n) N (synCfrecteq F G I) p0016
  have p0018 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
  have p0019 := @gEqid (synCfrec F I)
  have p0020 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0021 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0022 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0023 :=
    @gFrec0
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCfrec F I) F I p0019 p0020 p0021 p0022
  have p0024 := Nominal.mp p0018 p0023
  have p0025 := @gTceq (synCfv (synCfrec F I) (synC0c)) I
  have p0026 := Nominal.mp p0024 p0025
  have p0027 := @gTc0c
  have p0028 := @gFveq2i (synCtc (synC0c)) (synC0c) (synCfrec G (synCtc I)) p0027
  have p0029 :=
    @gN3pm32i (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G)) hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0030 := @gEqid (synCfrec G (synCtc I))
  have p0031 :=
    @gSimp1 (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G))
  have p0032 :=
    @gSimp2 (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G))
  have p0033 :=
    @gSimp3 (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
      (synWss (synCrn G) (synCdm G))
  have p0034 :=
    @gFrec0
      (synW3a (.classMem G (synCfuns)) (.classMem (synCtc I) (synCdm G))
        (synWss (synCrn G) (synCdm G)))
      (synCfrec G (synCtc I)) G (synCtc I) p0030 p0031 p0032 p0033
  have p0035 := Nominal.mp p0029 p0034
  have p0036 :=
    @gEqtri (synCfv (synCfrec G (synCtc I)) (synCtc (synC0c)))
      (synCfv (synCfrec G (synCtc I)) (synC0c)) (synCtc I) p0028 p0035
  have p0037 :=
    @gEqcomi (synCfv (synCfrec G (synCtc I)) (synCtc (synC0c))) (synCtc I) p0036
  have p0038 :=
    @gEqtri (synCtc (synCfv (synCfrec F I) (synC0c))) (synCtc I)
      (synCfv (synCfrec G (synCtc I)) (synCtc (synC0c))) p0026 p0037
  have p0039 := @gPeano1
  have p0040 :=
    @gFrecteqvalcl (synC0c) F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
      hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @gMpbir (.classMem (synC0c) (synCfrecteq F G I))
      (.classEq (synCtc (synCfv (synCfrec F I) (synC0c)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (synC0c))))
      p0038 p0041
  have p0044 :=
    @gA1i (.classMem F (synCfuns)) (.classMem (.cv m) (synCnnc)) hyp_frectchom0_1
  have p0045 :=
    @gA1i (.classMem I (synCdm F)) (.classMem (.cv m) (synCnnc)) hyp_frectchom0_2
  have p0046 :=
    @gA1i (synWss (synCrn F) (synCdm F)) (.classMem (.cv m) (synCnnc))
      hyp_frectchom0_3
  have p0047 := @gId (.classMem (.cv m) (synCnnc))
  have p0048 :=
    @gFrecsuc (.classMem (.cv m) (synCnnc)) (synCfrec F I) F I (.cv m) p0019 p0044
      p0045 p0046 p0047
  have p0049 :=
    @gAdantr (.classMem (.cv m) (synCnnc))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c)))
        (synCfv F (synCfv (synCfrec F I) (.cv m))))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      p0048
  have p0050 :=
    @gTceq (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c)))
      (synCfv F (synCfv (synCfrec F I) (.cv m)))
  have p0051 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c)))
        (synCfv F (synCfv (synCfrec F I) (.cv m))))
      (.classEq (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
        (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m)))))
      p0049 p0050
  have p0053 := @gFrecdomfv F I (.cv m)
  have p0054 :=
    @gMpan
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem (.cv m) (synCnnc))
      (.classMem (synCfv (synCfrec F I) (.cv m)) (synCdm F)) p0018 p0053
  have p0055 :=
    @gSimpr (.classMem (.cv m) (synCnnc))
      (.classEq (.cv x) (synCfv (synCfrec F I) (.cv m)))
  have p0056 :=
    @gFveq2d
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (.cv x) (synCfv (synCfrec F I) (.cv m))))
      (.cv x) (synCfv (synCfrec F I) (.cv m)) F p0055
  have p0057 := @gTceq (synCfv F (.cv x)) (synCfv F (synCfv (synCfrec F I) (.cv m)))
  have p0058 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (.cv x) (synCfv (synCfrec F I) (.cv m))))
      (.classEq (synCfv F (.cv x)) (synCfv F (synCfv (synCfrec F I) (.cv m))))
      (.classEq (synCtc (synCfv F (.cv x)))
        (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m)))))
      p0056 p0057
  have p0060 := @gTceq (.cv x) (synCfv (synCfrec F I) (.cv m))
  have p0061 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (.cv x) (synCfv (synCfrec F I) (.cv m))))
      (.classEq (.cv x) (synCfv (synCfrec F I) (.cv m)))
      (.classEq (synCtc (.cv x)) (synCtc (synCfv (synCfrec F I) (.cv m)))) p0055 p0060
  have p0062 :=
    @gFveq2d
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (.cv x) (synCfv (synCfrec F I) (.cv m))))
      (synCtc (.cv x)) (synCtc (synCfv (synCfrec F I) (.cv m))) G p0061
  have p0063 :=
    @gEqeq12d
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (.cv x) (synCfv (synCfrec F I) (.cv m))))
      (synCtc (synCfv F (.cv x)))
      (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m))))
      (synCfv G (synCtc (.cv x)))
      (synCfv G (synCtc (synCfv (synCfrec F I) (.cv m)))) p0058 p0062
  have p0064 :=
    @gRspcdv (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x))))
      (.classEq (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m))))
        (synCfv G (synCtc (synCfv (synCfrec F I) (.cv m)))))
      x (synCfv (synCfrec F I) (.cv m)) (synCdm F) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0054 p0063
  have p0065 :=
    @gMpi (.classMem (.cv m) (synCnnc))
      (synWral x (synCdm F)
        (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x)))))
      (.classEq (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m))))
        (synCfv G (synCtc (synCfv (synCfrec F I) (.cv m)))))
      hyp_frectchom0_7 p0064
  have p0066 :=
    @gAdantr (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m))))
        (synCfv G (synCtc (synCfv (synCfrec F I) (.cv m)))))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      p0065
  have p0067 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
      (synCtc (synCfv F (synCfv (synCfrec F I) (.cv m))))
      (synCfv G (synCtc (synCfv (synCfrec F I) (.cv m)))) p0051 p0066
  have p0068 :=
    @gSimpr (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
  have p0069 :=
    @gFveq2d
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCtc (synCfv (synCfrec F I) (.cv m)))
      (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))) G p0068
  have p0070 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
      (synCfv G (synCtc (synCfv (synCfrec F I) (.cv m))))
      (synCfv G (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))) p0067 p0069
  have p0072 :=
    @gA1i (.classMem G (synCfuns)) (.classMem (.cv m) (synCnnc)) hyp_frectchom0_4
  have p0073 :=
    @gA1i (.classMem (synCtc I) (synCdm G)) (.classMem (.cv m) (synCnnc))
      hyp_frectchom0_5
  have p0074 :=
    @gA1i (synWss (synCrn G) (synCdm G)) (.classMem (.cv m) (synCnnc))
      hyp_frectchom0_6
  have p0076 := @gNntccl (.cv m)
  have p0077 :=
    @gSyl (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCnnc))
      (.classMem (synCtc (.cv m)) (synCnnc)) p0047 p0076
  have p0078 :=
    @gFrecsuc (.classMem (.cv m) (synCnnc)) (synCfrec G (synCtc I)) G (synCtc I)
      (synCtc (.cv m)) p0030 p0072 p0073 p0074 p0077
  have p0079 :=
    @gAdantr (.classMem (.cv m) (synCnnc))
      (.classEq (synCfv (synCfrec G (synCtc I)) (synCplc (synCtc (.cv m)) (synC1c)))
        (synCfv G (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      p0078
  have p0080 :=
    @gEqcomd
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCfv (synCfrec G (synCtc I)) (synCplc (synCtc (.cv m)) (synC1c)))
      (synCfv G (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))) p0079
  have p0081 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
      (synCfv G (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      (synCfv (synCfrec G (synCtc I)) (synCplc (synCtc (.cv m)) (synC1c))) p0070
      p0080
  have p0083 := @gNnnc (.cv m)
  have p0084 :=
    @gSyl (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCnnc))
      (.classMem (.cv m) (synCncs)) p0047 p0083
  have p0085 := @gN1cnc
  have p0086 :=
    @gA1i (.classMem (synC1c) (synCncs)) (.classMem (.cv m) (synCnnc)) p0085
  have p0087 :=
    @gJca (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCncs))
      (.classMem (synC1c) (synCncs)) p0084 p0086
  have p0088 := @gTcdi (.cv m) (synC1c)
  have p0089 :=
    @gSyl (.classMem (.cv m) (synCnnc))
      (synWa (.classMem (.cv m) (synCncs)) (.classMem (synC1c) (synCncs)))
      (.classEq (synCtc (synCplc (.cv m) (synC1c)))
        (synCplc (synCtc (.cv m)) (synCtc (synC1c))))
      p0087 p0088
  have p0090 := @gTc1c
  have p0091 :=
    @gA1i (.classEq (synCtc (synC1c)) (synC1c)) (.classMem (.cv m) (synCnnc)) p0090
  have p0092 :=
    @gAddceq2d (.classMem (.cv m) (synCnnc)) (synCtc (synC1c)) (synC1c)
      (synCtc (.cv m)) p0091
  have p0093 :=
    @gEqtrd (.classMem (.cv m) (synCnnc)) (synCtc (synCplc (.cv m) (synC1c)))
      (synCplc (synCtc (.cv m)) (synCtc (synC1c)))
      (synCplc (synCtc (.cv m)) (synC1c)) p0089 p0092
  have p0094 :=
    @gAdantr (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCplc (.cv m) (synC1c))) (synCplc (synCtc (.cv m)) (synC1c)))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      p0093
  have p0095 :=
    @gFveq2d
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCtc (synCplc (.cv m) (synC1c))) (synCplc (synCtc (.cv m)) (synC1c))
      (synCfrec G (synCtc I)) p0094
  have p0096 :=
    @gEqcomd
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCfv (synCfrec G (synCtc I)) (synCtc (synCplc (.cv m) (synC1c))))
      (synCfv (synCfrec G (synCtc I)) (synCplc (synCtc (.cv m)) (synC1c))) p0095
  have p0097 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc))
        (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
          (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m)))))
      (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
      (synCfv (synCfrec G (synCtc I)) (synCplc (synCtc (.cv m)) (synC1c)))
      (synCfv (synCfrec G (synCtc I)) (synCtc (synCplc (.cv m) (synC1c)))) p0081
      p0096
  have p0098 :=
    @gEx (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      (.classEq (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
        (synCfv (synCfrec G (synCtc I)) (synCtc (synCplc (.cv m) (synC1c)))))
      p0097
  have p0099 :=
    @gFrecteqval m F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
      hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0100 :=
    @gBicomd (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCfrecteq F G I))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      p0099
  have p0102 := @gPeano2 (.cv m)
  have p0103 :=
    @gSyl (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc)) p0047 p0102
  have p0104 :=
    @gFrecteqvalcl (synCplc (.cv m) (synC1c)) F G I hyp_frectchom0_1 hyp_frectchom0_2
      hyp_frectchom0_3 hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0105 :=
    @gSyl (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (synWb (.classMem (synCplc (.cv m) (synC1c)) (synCfrecteq F G I))
        (.classEq (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
          (synCfv (synCfrec G (synCtc I)) (synCtc (synCplc (.cv m) (synC1c))))))
      p0103 p0104
  have p0106 :=
    @gBicomd (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (synC1c)) (synCfrecteq F G I))
      (.classEq (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
        (synCfv (synCfrec G (synCtc I)) (synCtc (synCplc (.cv m) (synC1c)))))
      p0105
  have p0107 :=
    @gN3imtr3d (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCfv (synCfrec F I) (.cv m)))
        (synCfv (synCfrec G (synCtc I)) (synCtc (.cv m))))
      (.classEq (synCtc (synCfv (synCfrec F I) (synCplc (.cv m) (synC1c))))
        (synCfv (synCfrec G (synCtc I)) (synCtc (synCplc (.cv m) (synC1c)))))
      (.classMem (.cv m) (synCfrecteq F G I))
      (.classMem (synCplc (.cv m) (synC1c)) (synCfrecteq F G I)) p0098 p0100 p0106
  have p0108_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (synWb (.classMem (.cv n) (synCfrecteq F G I))
          (.classMem (.cv m) (synCfrecteq F G I)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfrecteq synCuni1 synCuni synWex synWa synCin synCcompl
          synCnin synWnan synC1c synCfix synCrn synCima synWrex synWbr synCop
          synCun synCvv synCcom synCopab synCcnv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0108 :=
    @gFinds (.classMem (.cv n) (synCfrecteq F G I))
      (.classMem (synC0c) (synCfrecteq F G I)) (.classMem (.cv m) (synCfrecteq F G I))
      (.classMem (synCplc (.cv m) (synC1c)) (synCfrecteq F G I))
      (.classMem N (synCfrecteq F G I)) n m N dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0009 p0011
      p0108_e02_recanon p0015 p0017 p0042 p0107
  have p0109 :=
    @gFrecteqvalcl N F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
      hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0110 :=
    @gMpbid (.classMem N (synCnnc)) (.classMem N (synCfrecteq F G I))
      (.classEq (synCtc (synCfv (synCfrec F I) N))
        (synCfv (synCfrec G (synCtc I)) (synCtc N)))
      p0108 p0109
  exact p0110

/-- Checked nominal proof certificate identified upstream as `g_f1pwexd`. -/
@[expose]
noncomputable def gF1pwexd (ph : Wff) (A : Class) (B : Class) (g : Var) (F : Class)
    (dv_A_g : g ∉ A.fv) (_dv_B_g : g ∉ B.fv) (dv_F_g : g ∉ F.fv) (dv_g_ph : g ∉ ph.fv)
    (hyp_f1pwexd_1 : Nominal.NPrf (.imp ph (.classMem F (synCvv))))
    (hyp_f1pwexd_2 : Nominal.NPrf (.imp ph (synWf1 F A B))) :
    Nominal.NPrf (.imp ph (synWex g (synWf1 (.cv g) (synCpw A) (synCpw B)))) :=
  by
  have dv_cache_0001 : g ∉ ((synCpw A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, dv_A_g,
          not_false_eq_true])
  have dv_cache_0002 : g ∉ ((synCpw (synCrn F))).fv :=
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
  have p0000 := @gF1f1orn A B F
  have p0001 := @gSyl ph (synWf1 F A B) (synWf1o F A (synCrn F)) hyp_f1pwexd_2 p0000
  have p0002 :=
    @gJca ph (.classMem F (synCvv)) (synWf1o F A (synCrn F)) hyp_f1pwexd_1 p0001
  have p0003 := @gF1oeng A (synCrn F) (synCvv) F
  have p0004 :=
    @gSyl ph (synWa (.classMem F (synCvv)) (synWf1o F A (synCrn F)))
      (synWbr A (synCen) (synCrn F)) p0002 p0003
  have p0005 := @gEnpw A (synCrn F)
  have p0006 :=
    @gSyl ph (synWbr A (synCen) (synCrn F))
      (synWbr (synCpw A) (synCen) (synCpw (synCrn F))) p0004 p0005
  have p0007 := @gBren (synCpw A) (synCpw (synCrn F)) g dv_cache_0001 dv_cache_0002
  have p0008 :=
    @gBiimpi (synWbr (synCpw A) (synCen) (synCpw (synCrn F)))
      (synWex g (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F)))) p0007
  have p0009 :=
    @gSyl ph (synWbr (synCpw A) (synCen) (synCpw (synCrn F)))
      (synWex g (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F)))) p0006 p0008
  have p0010 := @gF1of1 (synCpw A) (synCpw (synCrn F)) (.cv g)
  have p0011 :=
    @gA1i
      (.imp (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F)))
        (synWf1 (.cv g) (synCpw A) (synCpw (synCrn F))))
      ph p0010
  have p0012 := @gF1f A B F
  have p0013 := @gSyl ph (synWf1 F A B) (synWf F A B) hyp_f1pwexd_2 p0012
  have p0014 := @gFrn A B F
  have p0015 := @gSyl ph (synWf F A B) (synWss (synCrn F) B) p0013 p0014
  have p0016 := @gSspwb (synCrn F) B
  have p0017 :=
    @gBiimpi (synWss (synCrn F) B) (synWss (synCpw (synCrn F)) (synCpw B)) p0016
  have p0018 :=
    @gSyl ph (synWss (synCrn F) B) (synWss (synCpw (synCrn F)) (synCpw B)) p0015
      p0017
  have p0019 :=
    @gA1d ph (synWss (synCpw (synCrn F)) (synCpw B))
      (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F))) p0018
  have p0020 :=
    @gJcad ph (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F)))
      (synWf1 (.cv g) (synCpw A) (synCpw (synCrn F)))
      (synWss (synCpw (synCrn F)) (synCpw B)) p0011 p0019
  have p0021 := @gF1ss (synCpw A) (synCpw (synCrn F)) (synCpw B) (.cv g)
  have p0022 :=
    @gSyl6 ph (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F)))
      (synWa (synWf1 (.cv g) (synCpw A) (synCpw (synCrn F)))
        (synWss (synCpw (synCrn F)) (synCpw B)))
      (synWf1 (.cv g) (synCpw A) (synCpw B)) p0020 p0021
  have p0023 :=
    @gEximdv ph (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F)))
      (synWf1 (.cv g) (synCpw A) (synCpw B)) g dv_cache_0003 p0022
  have p0024 :=
    @gMpd ph (synWex g (synWf1o (.cv g) (synCpw A) (synCpw (synCrn F))))
      (synWex g (synWf1 (.cv g) (synCpw A) (synCpw B))) p0009 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_f1pwpwexd`. -/
@[expose]
noncomputable def gF1pwpwexd (ph : Wff) (A : Class) (B : Class) (h : Var) (F : Class)
    (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv)
    (hyp_f1pwpwexd_1 : Nominal.NPrf (.imp ph (.classMem F (synCvv))))
    (hyp_f1pwpwexd_2 : Nominal.NPrf (.imp ph (synWf1 F A B))) :
    Nominal.NPrf
      (.imp ph (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B))))) :=
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
  have dv_cache_0005 : h ∉ ((synCpw A)).fv :=
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
  have dv_cache_0006 : h ∉ ((synCpw B)).fv :=
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
  have dv_cache_0008 : h ∉ ((synWf1 (.cv g) (synCpw A) (synCpw B))).fv :=
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
    g ∉ ((synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B))))).fv :=
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
    @gF1pwexd ph A B g F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_f1pwpwexd_1 hyp_f1pwpwexd_2
  have p0001 := @gVex g
  have p0002 :=
    @gA1i (.classMem (.cv g) (synCvv)) (synWf1 (.cv g) (synCpw A) (synCpw B)) p0001
  have p0003 := @gId (synWf1 (.cv g) (synCpw A) (synCpw B))
  have p0004 :=
    @gF1pwexd (synWf1 (.cv g) (synCpw A) (synCpw B)) (synCpw A) (synCpw B) h (.cv g)
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0002 p0003
  have p0005 :=
    @gA1i
      (.imp (synWf1 (.cv g) (synCpw A) (synCpw B))
        (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B)))))
      ph p0004
  have p0006 :=
    @gExlimdv ph (synWf1 (.cv g) (synCpw A) (synCpw B))
      (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B)))) g
      dv_cache_0009 dv_cache_0004 p0005
  have p0007 :=
    @gMpd ph (synWex g (synWf1 (.cv g) (synCpw A) (synCpw B)))
      (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B)))) p0000
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_f1pw2exim`. -/
@[expose]
noncomputable def gF1pw2exim (A : Class) (B : Class) (f : Var) (h : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_h : h ∉ A.fv) (dv_B_f : f ∉ B.fv) (dv_B_h : h ∉ B.fv)
    (dv_f_h : f ≠ h) :
    Nominal.NPrf
      (.imp (synWex f (synWf1 (.cv f) A B))
        (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B))))) :=
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
    f ∉ ((synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B))))).fv :=
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
  have p0000 := @gVex f
  have p0001 := @gA1i (.classMem (.cv f) (synCvv)) (synWf1 (.cv f) A B) p0000
  have p0002 := @gId (synWf1 (.cv f) A B)
  have p0003 :=
    @gF1pwpwexd (synWf1 (.cv f) A B) A B h (.cv f) dv_cache_0001 dv_cache_0002 p0001
      p0002
  have p0004 :=
    @gExlimiv (synWf1 (.cv f) A B)
      (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B)))) f
      dv_cache_0003 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ncpw2le`. -/
@[expose]
noncomputable def gNcpw2le (A : Class) (B : Class)
    (hyp_ncpw2le_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ncpw2le_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr (synCnc A) (synClec) (synCnc B))
        (synWbr (synCnc (synCpw (synCpw A))) (synClec) (synCnc (synCpw (synCpw B))))) :=
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
  have dv_cache_0006 : h ∉ ((synCpw (synCpw A))).fv :=
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
  have dv_cache_0007 : h ∉ ((synCpw (synCpw B))).fv :=
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
  have p0000 := @gNclenc A B f dv_cache_0001 dv_cache_0002 hyp_ncpw2le_1 hyp_ncpw2le_2
  have p0001 :=
    @gBiimpi (synWbr (synCnc A) (synClec) (synCnc B))
      (synWex f (synWf1 (.cv f) A B)) p0000
  have p0002 :=
    @gF1pw2exim A B f h dv_cache_0001 dv_cache_0003 dv_cache_0002 dv_cache_0004
      dv_cache_0005
  have p0003 :=
    @gSyl (synWbr (synCnc A) (synClec) (synCnc B)) (synWex f (synWf1 (.cv f) A B))
      (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B)))) p0001
      p0002
  have p0004 := @gPwex A hyp_ncpw2le_1
  have p0005 := @gPwex (synCpw A) p0004
  have p0006 := @gPwex B hyp_ncpw2le_2
  have p0007 := @gPwex (synCpw B) p0006
  have p0008 :=
    @gNclenc (synCpw (synCpw A)) (synCpw (synCpw B)) h dv_cache_0006 dv_cache_0007
      p0005 p0007
  have p0009 :=
    @gBiimpri
      (synWbr (synCnc (synCpw (synCpw A))) (synClec) (synCnc (synCpw (synCpw B))))
      (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B)))) p0008
  have p0010 :=
    @gSyl (synWbr (synCnc A) (synClec) (synCnc B))
      (synWex h (synWf1 (.cv h) (synCpw (synCpw A)) (synCpw (synCpw B))))
      (synWbr (synCnc (synCpw (synCpw A))) (synClec) (synCnc (synCpw (synCpw B))))
      p0003 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hwnisobaseext`. -/
@[expose]
noncomputable def gHwnisobaseext (v : Var) (u : Var) (A : Class) (D : Class)
    (dv_u_v : u ≠ v) (hyp_hwnisobaseext_1 : Nominal.NPrf (synWss D A)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (.imp (synWbr (.cv u) (synChwniso D) (.cv v))
          (synWbr (.cv u) (synChwniso A) (.cv v)))) :=
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
  have p0000 := @gHwcnssbase A D hyp_hwnisobaseext_1
  have p0001 :=
    @gSimpl (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D))
  have p0002 :=
    @gSseldi (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synChwcn D) (synChwcn A) (.cv u) p0000 p0001
  have p0004 :=
    @gSimpr (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D))
  have p0005 :=
    @gSseldi (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synChwcn D) (synChwcn A) (.cv v) p0000 p0004
  have p0006 :=
    @gJca (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0002 p0005
  have p0007 :=
    @gAdantr (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwniso D) (.cv v)) p0006
  have p0011 := @gHwcnraw u A
  have p0012 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A)) p0002 p0011
  have p0016 := @gHwcnraw v A
  have p0017 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synChwcodes A)) p0005 p0016
  have p0018 :=
    @gJca (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)) p0012
      p0017
  have p0019 :=
    @gAdantr (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWbr (.cv u) (synChwniso D) (.cv v)) p0018
  have p0020 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWbr (.cv u) (synChwniso D) (.cv v))
  have p0021 := @gHwnisohwisob v u D dv_cache_0001
  have p0022 :=
    @gBiimpi (synWbr (.cv u) (synChwniso D) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwiso D) (.cv v)))
      p0021
  have p0023 :=
    @gSimprd (synWbr (.cv u) (synChwniso D) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWbr (.cv u) (synChwiso D) (.cv v)) p0022
  have p0024 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso D) (.cv v)))
      (synWbr (.cv u) (synChwniso D) (.cv v)) (synWbr (.cv u) (synChwiso D) (.cv v))
      p0020 p0023
  have p0025 := @gBrhwisoany v u D h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0026 :=
    @gSylib
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso D) (.cv v)))
      (synWbr (.cv u) (synChwiso D) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes D)) (.classMem (.cv v) (synChwcodes D)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0024 p0025
  have p0027 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso D) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcodes D)) (.classMem (.cv v) (synChwcodes D)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0026
  have p0028 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso D) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0019 p0027
  have p0029 := @gBrhwisoany v u A h dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0030 :=
    @gSylibr
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso D) (.cv v)))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0028 p0029
  have p0031 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso D) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0007 p0030
  have p0032 := @gHwnisohwisob v u A dv_cache_0001
  have p0033 :=
    @gSylibr
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso D) (.cv v)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0031 p0032
  have p0034 :=
    @gEx (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWbr (.cv u) (synChwniso D) (.cv v)) (synWbr (.cv u) (synChwniso A) (.cv v))
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

/-- Checked nominal proof certificate identified upstream as `g_hwnisobaseextcl`. -/
@[expose]
noncomputable def gHwnisobaseextcl (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_hwnisobaseextcl_1 : Nominal.NPrf (synWss D A)) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
        (.imp (synWbr B (synChwniso D) C) (synWbr B (synChwniso A) C))) :=
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
      ((Wff.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
          (.imp (synWbr B (synChwniso D) C) (synWbr B (synChwniso A) C)))).fv :=
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
      ((Wff.imp (synWa (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
          (.imp (synWbr B (synChwniso D) (.cv y)) (synWbr B (synChwniso A) (.cv y))))).fv :=
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
  have p0000 := @gSimpl (.classMem B (synChwcn D)) (.classMem C (synChwcn D))
  have p0001 := @gElex B (synChwcn D)
  have p0002 :=
    @gSyl (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (.classMem B (synChwcn D)) (.classMem B (synCvv)) p0000 p0001
  have p0003 := @gSimpr (.classMem B (synChwcn D)) (.classMem C (synChwcn D))
  have p0004 := @gElex C (synChwcn D)
  have p0005 :=
    @gSyl (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (.classMem C (synChwcn D)) (.classMem C (synCvv)) p0003 p0004
  have p0006 :=
    @gJca (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (.classMem B (synCvv)) (.classMem C (synCvv)) p0002 p0005
  have p0007 := @gEleq1 (.cv x) B (synChwcn D)
  have p0008 := @gBiid (.classMem (.cv y) (synChwcn D))
  have p0009 :=
    @gA1i (synWb (.classMem (.cv y) (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
      (.classEq (.cv x) B) p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (.cv x) (synChwcn D))
      (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D))
      (.classMem (.cv y) (synChwcn D)) p0007 p0009
  have p0011 := @gBreq1 (.cv x) B (.cv y) (synChwniso D)
  have p0012 := @gBreq1 (.cv x) B (.cv y) (synChwniso A)
  have p0013 :=
    @gImbi12d (.classEq (.cv x) B) (synWbr (.cv x) (synChwniso D) (.cv y))
      (synWbr B (synChwniso D) (.cv y)) (synWbr (.cv x) (synChwniso A) (.cv y))
      (synWbr B (synChwniso A) (.cv y)) p0011 p0012
  have p0014 :=
    @gImbi12d (.classEq (.cv x) B)
      (synWa (.classMem (.cv x) (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
      (synWa (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
      (.imp (synWbr (.cv x) (synChwniso D) (.cv y)) (synWbr (.cv x) (synChwniso A) (.cv y)))
      (.imp (synWbr B (synChwniso D) (.cv y)) (synWbr B (synChwniso A) (.cv y))) p0010
      p0013
  have p0015 := @gBiid (.classMem B (synChwcn D))
  have p0016 :=
    @gA1i (synWb (.classMem B (synChwcn D)) (.classMem B (synChwcn D)))
      (.classEq (.cv y) C) p0015
  have p0017 := @gEleq1 (.cv y) C (synChwcn D)
  have p0018 :=
    @gAnbi12d (.classEq (.cv y) C) (.classMem B (synChwcn D))
      (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D))
      (.classMem C (synChwcn D)) p0016 p0017
  have p0019 := @gBreq2 (.cv y) C B (synChwniso D)
  have p0020 := @gBreq2 (.cv y) C B (synChwniso A)
  have p0021 :=
    @gImbi12d (.classEq (.cv y) C) (synWbr B (synChwniso D) (.cv y))
      (synWbr B (synChwniso D) C) (synWbr B (synChwniso A) (.cv y))
      (synWbr B (synChwniso A) C) p0019 p0020
  have p0022 :=
    @gImbi12d (.classEq (.cv y) C)
      (synWa (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
      (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (.imp (synWbr B (synChwniso D) (.cv y)) (synWbr B (synChwniso A) (.cv y)))
      (.imp (synWbr B (synChwniso D) C) (synWbr B (synChwniso A) C)) p0018 p0021
  have p0023 := @gHwnisobaseext y x A D dv_cache_0001 hyp_hwnisobaseextcl_1
  have p0024 :=
    @gVtocl2g
      (.imp (synWa (.classMem (.cv x) (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
        (.imp (synWbr (.cv x) (synChwniso D) (.cv y))
          (synWbr (.cv x) (synChwniso A) (.cv y))))
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
        (.imp (synWbr B (synChwniso D) (.cv y)) (synWbr B (synChwniso A) (.cv y))))
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
        (.imp (synWbr B (synChwniso D) C) (synWbr B (synChwniso A) C)))
      x y B C (synCvv) (synCvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0014 p0022 p0023
  have p0025 :=
    @gSyl (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
        (.imp (synWbr B (synChwniso D) C) (synWbr B (synChwniso A) C)))
      p0006 p0024
  have p0026 :=
    @gPm243i (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (.imp (synWbr B (synChwniso D) C) (synWbr B (synChwniso A) C)) p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_hwnisobasebicl`. -/
@[expose]
noncomputable def gHwnisobasebicl (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_hwnisobasebicl_1 : Nominal.NPrf (synWss D A)) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
        (synWb (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C))) :=
  by
  have p0000 := @gHwnisobaserestrcl A B C D
  have p0001 := @gHwnisobaseextcl A B C D hyp_hwnisobasebicl_1
  have p0002 :=
    @gImpbid (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1basecompat`. -/
@[expose]
noncomputable def gHnqmap1basecompat (A : Class) (D : Class) (q : Var) (p : Var)
    (hyp_hnqmap1basecompat_1 : Nominal.NPrf (synWss D A))
    (hyp_hnqmap1basecompat_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqmap1basecompat_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D)))) (.imp
          (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
          (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))) :=
  by
  have p0000 :=
    @gSimpl (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
  have p0001 := @gHnwpw1argcl (synChwcn D) p
  have p0002 :=
    @gSimprd (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0001
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0000 p0002
  have p0004 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv p) (synCsn (synCuni (.cv p))) (synChnqmap1 A) p0003
  have p0005 := @gHwcnssbase A D hyp_hnqmap1basecompat_1
  have p0008 :=
    @gSimpld (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0001
  have p0009 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv p)) (synChwcn D)) p0000 p0008
  have p0010 :=
    @gSseldi
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synChwcn D) (synChwcn A) (synCuni (.cv p)) p0005 p0009
  have p0011 := @gHnqmap1valcl A (synCuni (.cv p)) hyp_hnqmap1basecompat_3
  have p0012 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso A)))
      p0010 p0011
  have p0013 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 A) (.cv p))
      (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv p))))
      (synCec (synCuni (.cv p)) (synChwniso A)) p0004 p0012
  have p0014 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso A)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0013
  have p0019 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv p) (synCsn (synCuni (.cv p))) (synChnqmap1 D) p0003
  have p0024 := @gHnqmap1valcl D (synCuni (.cv p)) hyp_hnqmap1basecompat_2
  have p0025 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso D)))
      p0009 p0024
  have p0026 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 D) (.cv p))
      (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv p))))
      (synCec (synCuni (.cv p)) (synChwniso D)) p0019 p0025
  have p0027 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso D)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0026
  have p0028 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synCfv (synChnqmap1 D) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso D))
      p0027
  have p0029 :=
    @gSimpr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
  have p0030 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synCec (synCuni (.cv p)) (synChwniso D)) (synCfv (synChnqmap1 D) (.cv p))
      (synCfv (synChnqmap1 D) (.cv q)) p0028 p0029
  have p0031 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
  have p0032 := @gHnwpw1argcl (synChwcn D) q
  have p0033 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv q)) (synChwcn D))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0032
  have p0034 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0031 p0033
  have p0035 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv q) (synCsn (synCuni (.cv q))) (synChnqmap1 D) p0034
  have p0038 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv q)) (synChwcn D))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0032
  have p0039 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv q)) (synChwcn D)) p0031 p0038
  have p0040 := @gHnqmap1valcl D (synCuni (.cv q)) hyp_hnqmap1basecompat_2
  have p0041 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv q)) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso D)))
      p0039 p0040
  have p0042 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 D) (.cv q))
      (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv q))))
      (synCec (synCuni (.cv q)) (synChwniso D)) p0035 p0041
  have p0043 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 D) (.cv q)) (synCec (synCuni (.cv q)) (synChwniso D)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0042
  have p0044 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synCec (synCuni (.cv p)) (synChwniso D)) (synCfv (synChnqmap1 D) (.cv q))
      (synCec (synCuni (.cv q)) (synChwniso D)) p0030 p0043
  have p0053 :=
    @gJca
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classMem (synCuni (.cv q)) (synChwcn D)) p0009 p0039
  have p0054 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn D))
        (.classMem (synCuni (.cv q)) (synChwcn D)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0053
  have p0055 :=
    @gHwnisoclasseqbcl D (synCuni (.cv p)) (synCuni (.cv q)) hyp_hnqmap1basecompat_2
  have p0056 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn D))
        (.classMem (synCuni (.cv q)) (synChwcn D)))
      (synWb (.classEq (synCec (synCuni (.cv p)) (synChwniso D))
          (synCec (synCuni (.cv q)) (synChwniso D)))
        (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q))))
      p0054 p0055
  have p0057 :=
    @gBiimpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso D))
        (synCec (synCuni (.cv q)) (synChwniso D)))
      (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q))) p0056
  have p0058 :=
    @gMpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso D))
        (synCec (synCuni (.cv q)) (synChwniso D)))
      (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q))) p0044 p0057
  have p0069 :=
    @gHwnisobaseextcl A (synCuni (.cv p)) (synCuni (.cv q)) D hyp_hnqmap1basecompat_1
  have p0070 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn D))
        (.classMem (synCuni (.cv q)) (synChwcn D)))
      (.imp (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q)))
        (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q))))
      p0054 p0069
  have p0071 :=
    @gMpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q)))
      (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q))) p0058 p0070
  have p0083 :=
    @gSseldi
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synChwcn D) (synChwcn A) (synCuni (.cv q)) p0005 p0039
  have p0084 :=
    @gJca
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn A))
      (.classMem (synCuni (.cv q)) (synChwcn A)) p0010 p0083
  have p0085 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn A))
        (.classMem (synCuni (.cv q)) (synChwcn A)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0084
  have p0086 :=
    @gHwnisoclasseqbcl A (synCuni (.cv p)) (synCuni (.cv q)) hyp_hnqmap1basecompat_3
  have p0087 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn A))
        (.classMem (synCuni (.cv q)) (synChwcn A)))
      (synWb (.classEq (synCec (synCuni (.cv p)) (synChwniso A))
          (synCec (synCuni (.cv q)) (synChwniso A)))
        (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q))))
      p0085 p0086
  have p0088 :=
    @gBiimprd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso A))
        (synCec (synCuni (.cv q)) (synChwniso A)))
      (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q))) p0087
  have p0089 :=
    @gMpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q)))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso A))
        (synCec (synCuni (.cv q)) (synChwniso A)))
      p0071 p0088
  have p0090 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synCfv (synChnqmap1 A) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso A))
      (synCec (synCuni (.cv q)) (synChwniso A)) p0014 p0089
  have p0095 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv q) (synCsn (synCuni (.cv q))) (synChnqmap1 A) p0034
  have p0102 := @gHnqmap1valcl A (synCuni (.cv q)) hyp_hnqmap1basecompat_3
  have p0103 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso A)))
      p0083 p0102
  have p0104 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 A) (.cv q))
      (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv q))))
      (synCec (synCuni (.cv q)) (synChwniso A)) p0095 p0103
  have p0105 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 A) (.cv q)) (synCec (synCuni (.cv q)) (synChwniso A)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0104
  have p0106 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synCfv (synChnqmap1 A) (.cv q)) (synCec (synCuni (.cv q)) (synChwniso A))
      p0105
  have p0107 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      (synCfv (synChnqmap1 A) (.cv p)) (synCec (synCuni (.cv q)) (synChwniso A))
      (synCfv (synChnqmap1 A) (.cv q)) p0090 p0106
  have p0108 :=
    @gEx
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0107
  exact p0108

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1basereflect`. -/
@[expose]
noncomputable def gHnqmap1basereflect (A : Class) (D : Class) (q : Var) (p : Var)
    (hyp_hnqmap1basereflect_1 : Nominal.NPrf (synWss D A))
    (hyp_hnqmap1basereflect_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqmap1basereflect_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D)))) (.imp
          (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
          (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))) :=
  by
  have p0000 :=
    @gSimpl (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
  have p0001 := @gHnwpw1argcl (synChwcn D) p
  have p0002 :=
    @gSimprd (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0001
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0000 p0002
  have p0004 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv p) (synCsn (synCuni (.cv p))) (synChnqmap1 D) p0003
  have p0007 :=
    @gSimpld (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0001
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv p)) (synChwcn D)) p0000 p0007
  have p0009 := @gHnqmap1valcl D (synCuni (.cv p)) hyp_hnqmap1basereflect_2
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso D)))
      p0008 p0009
  have p0011 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 D) (.cv p))
      (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv p))))
      (synCec (synCuni (.cv p)) (synChwniso D)) p0004 p0010
  have p0012 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso D)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0011
  have p0017 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv p) (synCsn (synCuni (.cv p))) (synChnqmap1 A) p0003
  have p0018 := @gHwcnssbase A D hyp_hnqmap1basereflect_1
  have p0023 :=
    @gSseldi
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synChwcn D) (synChwcn A) (synCuni (.cv p)) p0018 p0008
  have p0024 := @gHnqmap1valcl A (synCuni (.cv p)) hyp_hnqmap1basereflect_3
  have p0025 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso A)))
      p0023 p0024
  have p0026 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 A) (.cv p))
      (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv p))))
      (synCec (synCuni (.cv p)) (synChwniso A)) p0017 p0025
  have p0027 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso A)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0026
  have p0028 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synCfv (synChnqmap1 A) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso A))
      p0027
  have p0029 :=
    @gSimpr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
  have p0030 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synCec (synCuni (.cv p)) (synChwniso A)) (synCfv (synChnqmap1 A) (.cv p))
      (synCfv (synChnqmap1 A) (.cv q)) p0028 p0029
  have p0031 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
  have p0032 := @gHnwpw1argcl (synChwcn D) q
  have p0033 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv q)) (synChwcn D))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0032
  have p0034 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0031 p0033
  have p0035 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv q) (synCsn (synCuni (.cv q))) (synChnqmap1 A) p0034
  have p0039 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv q)) (synChwcn D))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0032
  have p0040 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (.cv q) (synCpw1 (synChwcn D)))
      (.classMem (synCuni (.cv q)) (synChwcn D)) p0031 p0039
  have p0041 :=
    @gSseldi
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synChwcn D) (synChwcn A) (synCuni (.cv q)) p0018 p0040
  have p0042 := @gHnqmap1valcl A (synCuni (.cv q)) hyp_hnqmap1basereflect_3
  have p0043 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso A)))
      p0041 p0042
  have p0044 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 A) (.cv q))
      (synCfv (synChnqmap1 A) (synCsn (synCuni (.cv q))))
      (synCec (synCuni (.cv q)) (synChwniso A)) p0035 p0043
  have p0045 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 A) (.cv q)) (synCec (synCuni (.cv q)) (synChwniso A)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0044
  have p0046 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synCec (synCuni (.cv p)) (synChwniso A)) (synCfv (synChnqmap1 A) (.cv q))
      (synCec (synCuni (.cv q)) (synChwniso A)) p0030 p0045
  have p0059 :=
    @gJca
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn A))
      (.classMem (synCuni (.cv q)) (synChwcn A)) p0023 p0041
  have p0060 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn A))
        (.classMem (synCuni (.cv q)) (synChwcn A)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0059
  have p0061 :=
    @gHwnisoclasseqbcl A (synCuni (.cv p)) (synCuni (.cv q)) hyp_hnqmap1basereflect_3
  have p0062 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn A))
        (.classMem (synCuni (.cv q)) (synChwcn A)))
      (synWb (.classEq (synCec (synCuni (.cv p)) (synChwniso A))
          (synCec (synCuni (.cv q)) (synChwniso A)))
        (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q))))
      p0060 p0061
  have p0063 :=
    @gBiimpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso A))
        (synCec (synCuni (.cv q)) (synChwniso A)))
      (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q))) p0062
  have p0064 :=
    @gMpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso A))
        (synCec (synCuni (.cv q)) (synChwniso A)))
      (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q))) p0046 p0063
  have p0073 :=
    @gJca
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv p)) (synChwcn D))
      (.classMem (synCuni (.cv q)) (synChwcn D)) p0008 p0040
  have p0074 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn D))
        (.classMem (synCuni (.cv q)) (synChwcn D)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0073
  have p0075 := @gHwnisobaserestrcl A (synCuni (.cv p)) (synCuni (.cv q)) D
  have p0076 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn D))
        (.classMem (synCuni (.cv q)) (synChwcn D)))
      (.imp (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q)))
        (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q))))
      p0074 p0075
  have p0077 :=
    @gMpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synWbr (synCuni (.cv p)) (synChwniso A) (synCuni (.cv q)))
      (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q))) p0064 p0076
  have p0088 :=
    @gHwnisoclasseqbcl D (synCuni (.cv p)) (synCuni (.cv q)) hyp_hnqmap1basereflect_2
  have p0089 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synChwcn D))
        (.classMem (synCuni (.cv q)) (synChwcn D)))
      (synWb (.classEq (synCec (synCuni (.cv p)) (synChwniso D))
          (synCec (synCuni (.cv q)) (synChwniso D)))
        (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q))))
      p0074 p0088
  have p0090 :=
    @gBiimprd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso D))
        (synCec (synCuni (.cv q)) (synChwniso D)))
      (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q))) p0089
  have p0091 :=
    @gMpd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synWbr (synCuni (.cv p)) (synChwniso D) (synCuni (.cv q)))
      (.classEq (synCec (synCuni (.cv p)) (synChwniso D))
        (synCec (synCuni (.cv q)) (synChwniso D)))
      p0077 p0090
  have p0092 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synCfv (synChnqmap1 D) (.cv p)) (synCec (synCuni (.cv p)) (synChwniso D))
      (synCec (synCuni (.cv q)) (synChwniso D)) p0012 p0091
  have p0097 :=
    @gFveq2d
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.cv q) (synCsn (synCuni (.cv q))) (synChnqmap1 D) p0034
  have p0102 := @gHnqmap1valcl D (synCuni (.cv q)) hyp_hnqmap1basereflect_2
  have p0103 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classMem (synCuni (.cv q)) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso D)))
      p0040 p0102
  have p0104 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (synCfv (synChnqmap1 D) (.cv q))
      (synCfv (synChnqmap1 D) (synCsn (synCuni (.cv q))))
      (synCec (synCuni (.cv q)) (synChwniso D)) p0097 p0103
  have p0105 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 D) (.cv q)) (synCec (synCuni (.cv q)) (synChwniso D)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0104
  have p0106 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synCfv (synChnqmap1 D) (.cv q)) (synCec (synCuni (.cv q)) (synChwniso D))
      p0105
  have p0107 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
          (.classMem (.cv q) (synCpw1 (synChwcn D))))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      (synCfv (synChnqmap1 D) (.cv p)) (synCec (synCuni (.cv q)) (synChwniso D))
      (synCfv (synChnqmap1 D) (.cv q)) p0092 p0106
  have p0108 :=
    @gEx
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0107
  exact p0108

/-- Checked nominal proof certificate identified upstream as `g_hnqincexg`. -/
@[expose]
noncomputable def gHnqincexg (A : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem D (synCvv)) (.classMem A (synCvv)))
        (.classMem (synChnqinc D A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnqinc D A))
  have p0001 := @gSimpr (.classMem D (synCvv)) (.classMem A (synCvv))
  have p0002 := @gHnqmap1exg A
  have p0003 :=
    @gSyl (synWa (.classMem D (synCvv)) (.classMem A (synCvv)))
      (.classMem A (synCvv)) (.classMem (synChnqmap1 A) (synCvv)) p0001 p0002
  have p0004 := @gSimpl (.classMem D (synCvv)) (.classMem A (synCvv))
  have p0005 := @gHnqmap1exg D
  have p0006 :=
    @gSyl (synWa (.classMem D (synCvv)) (.classMem A (synCvv)))
      (.classMem D (synCvv)) (.classMem (synChnqmap1 D) (synCvv)) p0004 p0005
  have p0007 := @gCnvexg (synChnqmap1 D) (synCvv)
  have p0008 :=
    @gSyl (synWa (.classMem D (synCvv)) (.classMem A (synCvv)))
      (.classMem (synChnqmap1 D) (synCvv))
      (.classMem (synCcnv (synChnqmap1 D)) (synCvv)) p0006 p0007
  have p0009 :=
    @gJca (synWa (.classMem D (synCvv)) (.classMem A (synCvv)))
      (.classMem (synChnqmap1 A) (synCvv))
      (.classMem (synCcnv (synChnqmap1 D)) (synCvv)) p0003 p0008
  have p0010 := @gCoexg (synChnqmap1 A) (synCcnv (synChnqmap1 D)) (synCvv) (synCvv)
  have p0011 :=
    @gSyl (synWa (.classMem D (synCvv)) (.classMem A (synCvv)))
      (synWa (.classMem (synChnqmap1 A) (synCvv))
        (.classMem (synCcnv (synChnqmap1 D)) (synCvv)))
      (.classMem (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (synCvv)) p0009
      p0010
  have p0012 :=
    @gSyl5eqel (synWa (.classMem D (synCvv)) (.classMem A (synCvv))) (synChnqinc D A)
      (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (synCvv) p0000 p0011
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

/-- Checked nominal proof certificate identified upstream as `g_hnqincfun`. -/
@[expose]
noncomputable def gHnqincfun (A : Class) (D : Class)
    (hyp_hnqincfun_1 : Nominal.NPrf (synWss D A))
    (hyp_hnqincfun_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqincfun_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWfun (synChnqinc D A)) :=
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
  have dv_cache_0003 : p ∉ ((synChnqmap1 A)).fv :=
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
  have dv_cache_0004 : p ∉ ((synCcnv (synChnqmap1 D))).fv :=
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
  have dv_cache_0007 : q ∉ ((synChnqmap1 A)).fv :=
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
  have dv_cache_0008 : q ∉ ((synCcnv (synChnqmap1 D))).fv :=
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
      ((synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
              (.cv y)) (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
              (.cv z))) (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))).fv :=
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
      ((synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
          (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
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
  have dv_cache_0013 : x ∉ ((synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))).fv :=
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
  have dv_cache_0014 : y ∉ ((synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))).fv :=
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
  have dv_cache_0015 : z ∉ ((synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))).fv :=
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
    @gSimpl
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z))
  have p0001 :=
    @gBrco p (.cv x) (.cv y) (synChnqmap1 A) (synCcnv (synChnqmap1 D)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gSylib
      (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
        (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
      (synWex p (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
      p0000 p0001
  have p0003 :=
    @gSimpl
      (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
        (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (.cv y)))
  have p0004 :=
    @gSimpr
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z))
  have p0005 :=
    @gBrco q (.cv x) (.cv z) (synChnqmap1 A) (synCcnv (synChnqmap1 D)) dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0006 :=
    @gSylib
      (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
        (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z))
      (synWex q (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      p0004 p0005
  have p0007 :=
    @gSyl
      (synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv y)) (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv z))) (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
        (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
      (synWex q (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      p0003 p0006
  have p0008 :=
    @gSimpl
      (synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv y)) (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv z))) (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (.cv z)))
  have p0009 :=
    @gSimpr
      (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
        (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (.cv y)))
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv y)) (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv z))) (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (.cv y)))
      p0008 p0009
  have p0011 :=
    @gSimpr (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
      (synWbr (.cv p) (synChnqmap1 A) (.cv y))
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (.cv y)))
      (synWbr (.cv p) (synChnqmap1 A) (.cv y)) p0010 p0011
  have p0013 := @gHnqmap1fn A hyp_hnqincfun_3
  have p0014 := @gFnfun (synCpw1 (synChwcn A)) (synChnqmap1 A)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gFunbrfv (.cv p) (.cv y) (synChnqmap1 A)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv p) (synChnqmap1 A) (.cv y))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (.cv y)) p0012 p0017
  have p0019 :=
    @gEqcomd
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synCfv (synChnqmap1 A) (.cv p)) (.cv y) p0018
  have p0023 :=
    @gSimpl (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
      (synWbr (.cv p) (synChnqmap1 A) (.cv y))
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (.cv y)))
      (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p)) p0010 p0023
  have p0025 := @gBrcnv (.cv x) (.cv p) (synChnqmap1 D)
  have p0026 :=
    @gSylib
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
      (synWbr (.cv p) (synChnqmap1 D) (.cv x)) p0024 p0025
  have p0027 := @gHnqmap1fn D hyp_hnqincfun_2
  have p0028 := @gFnfun (synCpw1 (synChwcn D)) (synChnqmap1 D)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @gFunbrfv (.cv p) (.cv x) (synChnqmap1 D)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv p) (synChnqmap1 D) (.cv x))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (.cv x)) p0026 p0031
  have p0033 :=
    @gSimpr
      (synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv y)) (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv z))) (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (.cv z)))
  have p0034 :=
    @gSimpl (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
      (synWbr (.cv q) (synChnqmap1 A) (.cv z))
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (.cv z)))
      (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q)) p0033 p0034
  have p0036 := @gBrcnv (.cv x) (.cv q) (synChnqmap1 D)
  have p0037 :=
    @gSylib
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
      (synWbr (.cv q) (synChnqmap1 D) (.cv x)) p0035 p0036
  have p0041 := @gFunbrfv (.cv q) (.cv x) (synChnqmap1 D)
  have p0042 := Nominal.mp p0029 p0041
  have p0043 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv q) (synChnqmap1 D) (.cv x))
      (.classEq (synCfv (synChnqmap1 D) (.cv q)) (.cv x)) p0037 p0042
  have p0044 :=
    @gEqtr4d
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synCfv (synChnqmap1 D) (.cv p)) (.cv x) (synCfv (synChnqmap1 D) (.cv q)) p0032
      p0043
  have p0052 := @gBreldm (.cv p) (.cv x) (synChnqmap1 D)
  have p0053 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv p) (synChnqmap1 D) (.cv x))
      (.classMem (.cv p) (synCdm (synChnqmap1 D))) p0026 p0052
  have p0055 := @gFndm (synCpw1 (synChwcn D)) (synChnqmap1 D)
  have p0056 := Nominal.mp p0027 p0055
  have p0057 :=
    @gSyl6eleq
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (.cv p) (synCdm (synChnqmap1 D)) (synCpw1 (synChwcn D)) p0053 p0056
  have p0063 := @gBreldm (.cv q) (.cv x) (synChnqmap1 D)
  have p0064 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv q) (synChnqmap1 D) (.cv x))
      (.classMem (.cv q) (synCdm (synChnqmap1 D))) p0037 p0063
  have p0068 :=
    @gSyl6eleq
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (.cv q) (synCdm (synChnqmap1 D)) (synCpw1 (synChwcn D)) p0064 p0056
  have p0069 :=
    @gJca
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (.cv q) (synCpw1 (synChwcn D))) p0057 p0068
  have p0070 :=
    @gHnqmap1basecompat A D q p hyp_hnqincfun_1 hyp_hnqincfun_2 hyp_hnqincfun_3
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.imp (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
        (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q))))
      p0069 p0070
  have p0072 :=
    @gMpd
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      p0044 p0071
  have p0073 :=
    @gEqtrd
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (.cv y) (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)) p0019
      p0072
  have p0075 :=
    @gSimpr (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
      (synWbr (.cv q) (synChnqmap1 A) (.cv z))
  have p0076 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (.cv z)))
      (synWbr (.cv q) (synChnqmap1 A) (.cv z)) p0033 p0075
  have p0080 := @gFunbrfv (.cv q) (.cv z) (synChnqmap1 A)
  have p0081 := Nominal.mp p0015 p0080
  have p0082 :=
    @gSyl
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (synWbr (.cv q) (synChnqmap1 A) (.cv z))
      (.classEq (synCfv (synChnqmap1 A) (.cv q)) (.cv z)) p0076 p0081
  have p0083 :=
    @gEqtrd
      (synWa (synWa (synWa
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (.cv z))))
      (.cv y) (synCfv (synChnqmap1 A) (.cv q)) (.cv z) p0073 p0082
  have p0084 :=
    @gExlimddv
      (synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv y)) (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
            (.cv z))) (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (.cv z)))
      (.classEq (.cv y) (.cv z)) q dv_cache_0009 dv_cache_0010 p0007 p0083
  have p0085 :=
    @gExlimddv
      (synWa (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv y))
        (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) (.cv z)))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (.cv y)))
      (.classEq (.cv y) (.cv z)) p dv_cache_0011 dv_cache_0012 p0002 p0084
  have p0086 := Nominal.gen p0085 z
  have p0087 := Nominal.gen p0086 y
  have p0088 := Nominal.gen p0087 x
  have p0089 :=
    @gDffun2 x y z (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0090_e01_recanon :
    Nominal.NPrf
      (synWb (synWfun (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))) (.all x (.all y
            (.all z (.imp (synWa
                  (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
                    (.cv y))
                  (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
                    (.cv z))) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWfun synWss synCin synCcompl synCnin synWnan synWa
          synCcom synCopab synWex synCcnv synCid
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
    @gMpbir (synWfun (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))))
      (.all x (.all y (.all z (.imp (synWa
                (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
                  (.cv y))
                (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
                  (.cv z))) (.classEq (.cv y) (.cv z))))))
      p0088 p0090_e01_recanon
  have p0091 := (Nominal.classEqRefl (synChnqinc D A))
  have p0092 :=
    @gFuneq (synChnqinc D A) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
  have p0093 := Nominal.mp p0091 p0092
  have p0094 :=
    @gMpbir (synWfun (synChnqinc D A))
      (synWfun (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))) p0090 p0093
  exact p0094

/-- Checked nominal proof certificate identified upstream as `g_hnqincdm`. -/
@[expose]
noncomputable def gHnqincdm (A : Class) (D : Class)
    (hyp_hnqincdm_1 : Nominal.NPrf (synWss D A))
    (hyp_hnqincdm_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqincdm_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCdm (synChnqinc D A)) (synChnord D)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnqinc D A))
  have p0001 :=
    @gDmeqi (synChnqinc D A) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
      p0000
  have p0002 := @gHwcnssbase A D hyp_hnqincdm_1
  have p0003 := @gPw1ss (synChwcn D) (synChwcn A)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCdm (synChnqmap1 D)))
  have p0006 :=
    @gEqcomi (synCdm (synChnqmap1 D)) (synCrn (synCcnv (synChnqmap1 D))) p0005
  have p0007 := @gHnqmap1fn D hyp_hnqincdm_2
  have p0008 := @gFndm (synCpw1 (synChwcn D)) (synChnqmap1 D)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gEqtri (synCrn (synCcnv (synChnqmap1 D))) (synCdm (synChnqmap1 D))
      (synCpw1 (synChwcn D)) p0006 p0009
  have p0011 := @gHnqmap1fn A hyp_hnqincdm_3
  have p0012 := @gFndm (synCpw1 (synChwcn A)) (synChnqmap1 A)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gN3sstr4i (synCpw1 (synChwcn D)) (synCpw1 (synChwcn A))
      (synCrn (synCcnv (synChnqmap1 D))) (synCdm (synChnqmap1 A)) p0004 p0010 p0013
  have p0015 := @gDmcosseq (synChnqmap1 A) (synCcnv (synChnqmap1 D))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gDfrn4 (synChnqmap1 D)
  have p0018 :=
    @gEqtr4i (synCdm (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))))
      (synCdm (synCcnv (synChnqmap1 D))) (synCrn (synChnqmap1 D)) p0016 p0017
  have p0019 := @gHnqmap1rn D hyp_hnqincdm_2
  have p0020 :=
    @gEqtri (synCdm (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))))
      (synCrn (synChnqmap1 D)) (synChnord D) p0018 p0019
  have p0021 :=
    @gEqtri (synCdm (synChnqinc D A))
      (synCdm (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))) (synChnord D)
      p0001 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_hnqincfn`. -/
@[expose]
noncomputable def gHnqincfn (A : Class) (D : Class)
    (hyp_hnqincfn_1 : Nominal.NPrf (synWss D A))
    (hyp_hnqincfn_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqincfn_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWfn (synChnqinc D A) (synChnord D)) :=
  by
  have p0000 := @gHnqincfun A D hyp_hnqincfn_1 hyp_hnqincfn_2 hyp_hnqincfn_3
  have p0001 := @gHnqincdm A D hyp_hnqincfn_1 hyp_hnqincfn_2 hyp_hnqincfn_3
  have p0002 :=
    @gPm32i (synWfun (synChnqinc D A))
      (.classEq (synCdm (synChnqinc D A)) (synChnord D)) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWfn (synChnqinc D A) (synChnord D)))
  have p0004 :=
    @gMpbir (synWfn (synChnqinc D A) (synChnord D))
      (synWa (synWfun (synChnqinc D A))
        (.classEq (synCdm (synChnqinc D A)) (synChnord D)))
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnqincf`. -/
@[expose]
noncomputable def gHnqincf (A : Class) (D : Class)
    (hyp_hnqincf_1 : Nominal.NPrf (synWss D A))
    (hyp_hnqincf_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqincf_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWf (synChnqinc D A) (synChnord D) (synChnord A)) :=
  by
  have p0000 := @gHnqincfn A D hyp_hnqincf_1 hyp_hnqincf_2 hyp_hnqincf_3
  have p0001 := @gRncoss (synChnqmap1 A) (synCcnv (synChnqmap1 D))
  have p0002 := (Nominal.classEqRefl (synChnqinc D A))
  have p0003 :=
    @gRneqi (synChnqinc D A) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
      p0002
  have p0004 := @gHnqmap1rn A hyp_hnqincf_3
  have p0005 := @gEqcomi (synCrn (synChnqmap1 A)) (synChnord A) p0004
  have p0006 :=
    @gN3sstr4i (synCrn (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))))
      (synCrn (synChnqmap1 A)) (synCrn (synChnqinc D A)) (synChnord A) p0001 p0003
      p0005
  have p0007 :=
    @gPm32i (synWfn (synChnqinc D A) (synChnord D))
      (synWss (synCrn (synChnqinc D A)) (synChnord A)) p0000 p0006
  have p0008 :=
    (Nominal.biimpRefl (synWf (synChnqinc D A) (synChnord D) (synChnord A)))
  have p0009 :=
    @gMpbir (synWf (synChnqinc D A) (synChnord D) (synChnord A))
      (synWa (synWfn (synChnqinc D A) (synChnord D))
        (synWss (synCrn (synChnqinc D A)) (synChnord A)))
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

/-- Checked nominal proof certificate identified upstream as `g_hnqincf1`. -/
@[expose]
noncomputable def gHnqincf1 (A : Class) (D : Class)
    (hyp_hnqincf1_1 : Nominal.NPrf (synWss D A))
    (hyp_hnqincf1_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqincf1_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWf1 (synChnqinc D A) (synChnord D) (synChnord A)) :=
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
  have dv_cache_0002 : p ∉ ((synCfv (synChnqinc D A) (.cv x))).fv :=
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
  have dv_cache_0003 : p ∉ ((synChnqmap1 A)).fv :=
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
  have dv_cache_0004 : p ∉ ((synCcnv (synChnqmap1 D))).fv :=
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
  have dv_cache_0006 : q ∉ ((synCfv (synChnqinc D A) (.cv y))).fv :=
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
  have dv_cache_0007 : q ∉ ((synChnqmap1 A)).fv :=
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
  have dv_cache_0008 : q ∉ ((synCcnv (synChnqmap1 D))).fv :=
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
      ((synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))).fv :=
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
      ((synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
          (.classEq (synCfv (synChnqinc D A) (.cv x))
            (synCfv (synChnqinc D A) (.cv y))))).fv :=
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
  have dv_cache_0013 : y ∉ ((synChnord D)).fv :=
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
  have dv_cache_0015 : x ∉ ((synChnord D)).fv :=
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
  have dv_cache_0016 : x ∉ ((synChnqinc D A)).fv :=
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
  have dv_cache_0017 : y ∉ ((synChnqinc D A)).fv :=
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
  have p0000 := @gHnqincf A D hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0001 :=
    @gSimpl
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y)))
  have p0002 := @gEqid (synCfv (synChnqinc D A) (.cv x))
  have p0003 :=
    @gA1i
      (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv x)))
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D))) p0002
  have p0004 := @gHnqincfn A D hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0005 :=
    @gA1i (synWfn (synChnqinc D A) (synChnord D))
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D))) p0004
  have p0006 :=
    @gSimpl (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D))
  have p0007 :=
    @gJca (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWfn (synChnqinc D A) (synChnord D)) (.classMem (.cv x) (synChnord D)) p0005
      p0006
  have p0008 :=
    @gFnbrfvb (synChnord D) (.cv x) (synCfv (synChnqinc D A) (.cv x))
      (synChnqinc D A)
  have p0009 :=
    @gSyl (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWa (synWfn (synChnqinc D A) (synChnord D)) (.classMem (.cv x) (synChnord D)))
      (synWb (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv x)))
        (synWbr (.cv x) (synChnqinc D A) (synCfv (synChnqinc D A) (.cv x))))
      p0007 p0008
  have p0010 :=
    @gMpbid
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv x)))
      (synWbr (.cv x) (synChnqinc D A) (synCfv (synChnqinc D A) (.cv x))) p0003 p0009
  have p0011 := (Nominal.classEqRefl (synChnqinc D A))
  have p0012 :=
    @gBreqi (.cv x) (synCfv (synChnqinc D A) (.cv x)) (synChnqinc D A)
      (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) p0011
  have p0013 :=
    @gSylib
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWbr (.cv x) (synChnqinc D A) (synCfv (synChnqinc D A) (.cv x)))
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
        (synCfv (synChnqinc D A) (.cv x)))
      p0010 p0012
  have p0014 :=
    @gBrco p (.cv x) (synCfv (synChnqinc D A) (.cv x)) (synChnqmap1 A)
      (synCcnv (synChnqmap1 D)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0015 :=
    @gSylib
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWbr (.cv x) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
        (synCfv (synChnqinc D A) (.cv x)))
      (synWex p (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      p0013 p0014
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWex p (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      p0001 p0015
  have p0017 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x))))
  have p0019 := @gEqid (synCfv (synChnqinc D A) (.cv y))
  have p0020 :=
    @gA1i
      (.classEq (synCfv (synChnqinc D A) (.cv y)) (synCfv (synChnqinc D A) (.cv y)))
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D))) p0019
  have p0023 :=
    @gSimpr (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D))
  have p0024 :=
    @gJca (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWfn (synChnqinc D A) (synChnord D)) (.classMem (.cv y) (synChnord D)) p0005
      p0023
  have p0025 :=
    @gFnbrfvb (synChnord D) (.cv y) (synCfv (synChnqinc D A) (.cv y))
      (synChnqinc D A)
  have p0026 :=
    @gSyl (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWa (synWfn (synChnqinc D A) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWb (.classEq (synCfv (synChnqinc D A) (.cv y)) (synCfv (synChnqinc D A) (.cv y)))
        (synWbr (.cv y) (synChnqinc D A) (synCfv (synChnqinc D A) (.cv y))))
      p0024 p0025
  have p0027 :=
    @gMpbid
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (.classEq (synCfv (synChnqinc D A) (.cv y)) (synCfv (synChnqinc D A) (.cv y)))
      (synWbr (.cv y) (synChnqinc D A) (synCfv (synChnqinc D A) (.cv y))) p0020 p0026
  have p0029 :=
    @gBreqi (.cv y) (synCfv (synChnqinc D A) (.cv y)) (synChnqinc D A)
      (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) p0011
  have p0030 :=
    @gSylib
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWbr (.cv y) (synChnqinc D A) (synCfv (synChnqinc D A) (.cv y)))
      (synWbr (.cv y) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
        (synCfv (synChnqinc D A) (.cv y)))
      p0027 p0029
  have p0031 :=
    @gBrco q (.cv y) (synCfv (synChnqinc D A) (.cv y)) (synChnqmap1 A)
      (synCcnv (synChnqmap1 D)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0032 :=
    @gSylib
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWbr (.cv y) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
        (synCfv (synChnqinc D A) (.cv y)))
      (synWex q (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      p0030 p0031
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (synWex q (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      p0001 p0032
  have p0034 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
          (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      (synWex q (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      p0017 p0033
  have p0035 :=
    @gSimpl
      (synWa (synWa
          (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
          (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y))))
  have p0036 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x))))
  have p0037 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (synWa
          (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
          (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x))))
      p0035 p0036
  have p0038 :=
    @gSimpl (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
      (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x))))
      (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p)) p0037 p0038
  have p0040 := @gBrcnv (.cv x) (.cv p) (synChnqmap1 D)
  have p0041 :=
    @gSylib
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
      (synWbr (.cv p) (synChnqmap1 D) (.cv x)) p0039 p0040
  have p0042 := @gHnqmap1fn D hyp_hnqincf1_2
  have p0043 := @gFnfun (synCpw1 (synChwcn D)) (synChnqmap1 D)
  have p0044 := Nominal.mp p0042 p0043
  have p0045 := @gFunbrfv (.cv p) (.cv x) (synChnqmap1 D)
  have p0046 := Nominal.mp p0044 p0045
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv p) (synChnqmap1 D) (.cv x))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (.cv x)) p0041 p0046
  have p0048 :=
    @gEqcomd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synCfv (synChnqmap1 D) (.cv p)) (.cv x) p0047
  have p0052 :=
    @gSimpr (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
      (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))
  have p0053 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x))))
      (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x))) p0037 p0052
  have p0054 := @gHnqmap1fn A hyp_hnqincf1_3
  have p0055 := @gFnfun (synCpw1 (synChwcn A)) (synChnqmap1 A)
  have p0056 := Nominal.mp p0054 p0055
  have p0057 := @gFunbrfv (.cv p) (synCfv (synChnqinc D A) (.cv x)) (synChnqmap1 A)
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqinc D A) (.cv x)))
      p0053 p0058
  have p0062 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (synWa
          (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
          (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      p0035 p0017
  have p0063 :=
    @gSimpr
      (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y)))
  have p0064 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y)))
      p0062 p0063
  have p0065 :=
    @gEqtrd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqinc D A) (.cv x))
      (synCfv (synChnqinc D A) (.cv y)) p0059 p0064
  have p0066 :=
    @gSimpr
      (synWa (synWa
          (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
          (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y))))
  have p0067 :=
    @gSimpr (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
      (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))
  have p0068 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y))))
      (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y))) p0066 p0067
  have p0072 := @gFunbrfv (.cv q) (synCfv (synChnqinc D A) (.cv y)) (synChnqmap1 A)
  have p0073 := Nominal.mp p0056 p0072
  have p0074 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))
      (.classEq (synCfv (synChnqmap1 A) (.cv q)) (synCfv (synChnqinc D A) (.cv y)))
      p0068 p0073
  have p0075 :=
    @gEqtr4d
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqinc D A) (.cv y))
      (synCfv (synChnqmap1 A) (.cv q)) p0065 p0074
  have p0083 := @gBreldm (.cv p) (.cv x) (synChnqmap1 D)
  have p0084 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv p) (synChnqmap1 D) (.cv x))
      (.classMem (.cv p) (synCdm (synChnqmap1 D))) p0041 p0083
  have p0086 := @gFndm (synCpw1 (synChwcn D)) (synChnqmap1 D)
  have p0087 := Nominal.mp p0042 p0086
  have p0088 :=
    @gSyl6eleq
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (.cv p) (synCdm (synChnqmap1 D)) (synCpw1 (synChwcn D)) p0084 p0087
  have p0090 :=
    @gSimpl (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
      (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))
  have p0091 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y))))
      (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q)) p0066 p0090
  have p0092 := @gBrcnv (.cv y) (.cv q) (synChnqmap1 D)
  have p0093 :=
    @gSylib
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
      (synWbr (.cv q) (synChnqmap1 D) (.cv y)) p0091 p0092
  have p0094 := @gBreldm (.cv q) (.cv y) (synChnqmap1 D)
  have p0095 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv q) (synChnqmap1 D) (.cv y))
      (.classMem (.cv q) (synCdm (synChnqmap1 D))) p0093 p0094
  have p0099 :=
    @gSyl6eleq
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (.cv q) (synCdm (synChnqmap1 D)) (synCpw1 (synChwcn D)) p0095 p0087
  have p0100 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (.classMem (.cv p) (synCpw1 (synChwcn D)))
      (.classMem (.cv q) (synCpw1 (synChwcn D))) p0088 p0099
  have p0101 := @gHnqmap1basereflect A D q p hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0102 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn D)))
        (.classMem (.cv q) (synCpw1 (synChwcn D))))
      (.imp (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
        (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q))))
      p0100 p0101
  have p0103 :=
    @gMpd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (.classEq (synCfv (synChnqmap1 A) (.cv p)) (synCfv (synChnqmap1 A) (.cv q)))
      (.classEq (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)))
      p0075 p0102
  have p0104 :=
    @gEqtrd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (.cv x) (synCfv (synChnqmap1 D) (.cv p)) (synCfv (synChnqmap1 D) (.cv q)) p0048
      p0103
  have p0113 := @gFunbrfv (.cv q) (.cv y) (synChnqmap1 D)
  have p0114 := Nominal.mp p0044 p0113
  have p0115 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (synWbr (.cv q) (synChnqmap1 D) (.cv y))
      (.classEq (synCfv (synChnqmap1 D) (.cv q)) (.cv y)) p0093 p0114
  have p0116 :=
    @gEqtrd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
          (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
            (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
        (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
          (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y)))))
      (.cv x) (synCfv (synChnqmap1 D) (.cv q)) (.cv y) p0104 p0115
  have p0117 :=
    @gExlimddv
      (synWa (synWa
          (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
          (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
        (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
          (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x)))))
      (synWa (synWbr (.cv y) (synCcnv (synChnqmap1 D)) (.cv q))
        (synWbr (.cv q) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv y))))
      (.classEq (.cv x) (.cv y)) q dv_cache_0009 dv_cache_0010 p0034 p0116
  have p0118 :=
    @gExlimddv
      (synWa (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
        (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y))))
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 D)) (.cv p))
        (synWbr (.cv p) (synChnqmap1 A) (synCfv (synChnqinc D A) (.cv x))))
      (.classEq (.cv x) (.cv y)) p dv_cache_0011 dv_cache_0012 p0016 p0117
  have p0119 :=
    @gEx (synWa (.classMem (.cv x) (synChnord D)) (.classMem (.cv y) (synChnord D)))
      (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y)))
      (.classEq (.cv x) (.cv y)) p0118
  have p0120 :=
    @gRgen2
      (.imp (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y)))
        (.classEq (.cv x) (.cv y)))
      x y (synChnord D) (synChnord D) dv_cache_0013 dv_cache_0014 p0119
  have p0121 :=
    @gPm32i (synWf (synChnqinc D A) (synChnord D) (synChnord A))
      (synWral x (synChnord D) (synWral y (synChnord D) (.imp
            (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y)))
            (.classEq (.cv x) (.cv y)))))
      p0000 p0120
  have p0122 :=
    @gDff13 x y (synChnord D) (synChnord A) (synChnqinc D A) dv_cache_0015
      dv_cache_0013 dv_cache_0016 dv_cache_0017 dv_cache_0014
  have p0123_e01_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synChnqinc D A) (synChnord D) (synChnord A))
        (synWa (synWf (synChnqinc D A) (synChnord D) (synChnord A))
          (synWral x (synChnord D) (synWral y (synChnord D) (.imp
                (.classEq (synCfv (synChnqinc D A) (.cv x))
                  (synCfv (synChnqinc D A) (.cv y))) (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synChnqinc synChnord
          synCqs synWrex synCec synCima synCsn synChwcn synChwniso
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
    @gMpbir (synWf1 (synChnqinc D A) (synChnord D) (synChnord A))
      (synWa (synWf (synChnqinc D A) (synChnord D) (synChnord A))
        (synWral x (synChnord D) (synWral y (synChnord D) (.imp
              (.classEq (synCfv (synChnqinc D A) (.cv x)) (synCfv (synChnqinc D A) (.cv y)))
              (.classEq (.cv x) (.cv y))))))
      p0121 p0123_e01_recanon
  exact p0123


end NFChoice.DirectNominalPrf.WPPReplay

end
