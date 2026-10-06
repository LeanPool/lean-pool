/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_kqfinantinn`. -/
@[expose]
noncomputable def gKqfinantinn (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.imp
          (synWa (synWbr A (synCkqrel (synClefin)) B)
            (synWbr B (synCkqrel (synClefin)) A)) (.classEq A B))) :=
  by
  have p0000 := @gKqlefinbr A B (synCnnc) (synCnnc)
  have p0001 := @gSimpr (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0002 := @gSimpl (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0003 :=
    @gJca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCnnc)) (.classMem A (synCnnc)) p0001 p0002
  have p0004 := @gKqlefinbr B A (synCnnc) (synCnnc)
  have p0005 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem B (synCnnc)) (.classMem A (synCnnc)))
      (synWb (synWbr B (synCkqrel (synClefin)) A) (.classMem (synCopk B A) (synClefin)))
      p0003 p0004
  have p0006 :=
    @gAnbi12d (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWbr A (synCkqrel (synClefin)) B) (.classMem (synCopk A B) (synClefin))
      (synWbr B (synCkqrel (synClefin)) A) (.classMem (synCopk B A) (synClefin))
      p0000 p0005
  have p0007 :=
    @gBiimpd (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (synWbr A (synCkqrel (synClefin)) B) (synWbr B (synCkqrel (synClefin)) A))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      p0006
  have p0008 := @gLefinantinn A B
  have p0009 :=
    @gSyld (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (synWbr A (synCkqrel (synClefin)) B) (synWbr B (synCkqrel (synClefin)) A))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      (.classEq A B) p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_nntctfin`. -/
@[expose]
noncomputable def gNntctfin (N : Class) :
    Nominal.NPrf (.imp (.classMem N (synCnnc)) (.classEq (synCtc N) (synCtfin N))) :=
  by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have dv_cache_0001 : a ∉ (N).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Wff.classEq (synCtc N) (synCtfin N))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          fresh_a_not_N, or_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Wff.classMem N (synCnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_a_not_N, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gId (.classMem N (synCnnc))
  have p0001 := @gNulnnn
  have p0002 := @gEleq1 N (synC0) (synCnnc)
  have p0003 :=
    @gMtbiri (.classEq N (synC0)) (.classMem N (synCnnc))
      (.classMem (synC0) (synCnnc)) p0001 p0002
  have p0004 := @gNecon2ai (.classMem N (synCnnc)) N (synC0) p0003
  have p0005 :=
    @gJca (.classMem N (synCnnc)) (.classMem N (synCnnc)) (synWne N (synC0)) p0000
      p0004
  have p0006 := @gTfinprop N a dv_cache_0001
  have p0007 :=
    @gSyl (.classMem N (synCnnc)) (synWa (.classMem N (synCnnc)) (synWne N (synC0)))
      (synWa (.classMem (synCtfin N) (synCnnc))
        (synWrex a N (.classMem (synCpw1 (.cv a)) (synCtfin N))))
      p0005 p0006
  have p0008 :=
    @gSimprd (.classMem N (synCnnc)) (.classMem (synCtfin N) (synCnnc))
      (synWrex a N (.classMem (synCpw1 (.cv a)) (synCtfin N))) p0007
  have p0009 :=
    @gSimpl (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem (synCpw1 (.cv a)) (synCtfin N))
  have p0010 := @gSimpl (.classMem N (synCnnc)) (.classMem (.cv a) N)
  have p0011 :=
    @gSyl
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N)) (.classMem N (synCnnc))
      p0009 p0010
  have p0012 := @gNntccl N
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (.classMem N (synCnnc)) (.classMem (synCtc N) (synCnnc)) p0011 p0012
  have p0017 := @gTfincl N
  have p0018 :=
    @gSyl
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (.classMem N (synCnnc)) (.classMem (synCtfin N) (synCnnc)) p0011 p0017
  have p0019 :=
    @gJca
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (.classMem (synCtc N) (synCnnc)) (.classMem (synCtfin N) (synCnnc)) p0013 p0018
  have p0022 := @gNnnc N
  have p0023 :=
    @gSyl (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem N (synCnnc)) (.classMem N (synCncs)) p0010 p0022
  have p0024 := @gSimpr (.classMem N (synCnnc)) (.classMem (.cv a) N)
  have p0025 :=
    @gJca (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem N (synCncs)) (.classMem (.cv a) N) p0023 p0024
  have p0026 := @gPw1eltc N (.cv a)
  have p0027 :=
    @gSyl (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (synWa (.classMem N (synCncs)) (.classMem (.cv a) N))
      (.classMem (synCpw1 (.cv a)) (synCtc N)) p0025 p0026
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem (synCpw1 (.cv a)) (synCtc N)) p0009 p0027
  have p0029 :=
    @gSimpr (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem (synCpw1 (.cv a)) (synCtfin N))
  have p0030 :=
    @gJca
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (.classMem (synCpw1 (.cv a)) (synCtc N))
      (.classMem (synCpw1 (.cv a)) (synCtfin N)) p0028 p0029
  have p0031 :=
    @gJca
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (synWa (.classMem (synCtc N) (synCnnc)) (.classMem (synCtfin N) (synCnnc)))
      (synWa (.classMem (synCpw1 (.cv a)) (synCtc N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      p0019 p0030
  have p0032 := @gNnceleq (synCpw1 (.cv a)) (synCtc N) (synCtfin N)
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
        (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (synWa (synWa (.classMem (synCtc N) (synCnnc)) (.classMem (synCtfin N) (synCnnc)))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtc N))
          (.classMem (synCpw1 (.cv a)) (synCtfin N))))
      (.classEq (synCtc N) (synCtfin N)) p0031 p0032
  have p0034 :=
    @gEx (synWa (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem (synCpw1 (.cv a)) (synCtfin N)) (.classEq (synCtc N) (synCtfin N))
      p0033
  have p0035 :=
    @gRexlimdva (.classMem N (synCnnc)) (.classMem (synCpw1 (.cv a)) (synCtfin N))
      (.classEq (synCtc N) (synCtfin N)) a N dv_cache_0002 dv_cache_0003 p0034
  have p0036 :=
    @gMpd (.classMem N (synCnnc))
      (synWrex a N (.classMem (synCpw1 (.cv a)) (synCtfin N)))
      (.classEq (synCtc N) (synCtfin N)) p0008 p0035
  exact p0036

/-- Checked nominal proof certificate identified upstream as `g_tc6lecan`. -/
@[expose]
noncomputable def gTc6lecan (M : Class) (N : Class)
    (hyp_tc6lecb_1 : Nominal.NPrf (.classMem M (synCncs)))
    (hyp_tc6lecb_2 : Nominal.NPrf (.classMem N (synCncs))) :
    Nominal.NPrf
      (.imp (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc M)))))) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
        (synWbr M (synClec) N)) :=
  by
  have p0000 := @gTlecg M N
  have p0001 :=
    @gMp2an (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWb (synWbr M (synClec) N) (synWbr (synCtc M) (synClec) (synCtc N)))
      hyp_tc6lecb_1 hyp_tc6lecb_2 p0000
  have p0002 := @gTccl M
  have p0003 := Nominal.mp hyp_tc6lecb_1 p0002
  have p0004 := @gTccl N
  have p0005 := Nominal.mp hyp_tc6lecb_2 p0004
  have p0006 := @gTlecg (synCtc M) (synCtc N)
  have p0007 :=
    @gMp2an (.classMem (synCtc M) (synCncs)) (.classMem (synCtc N) (synCncs))
      (synWb (synWbr (synCtc M) (synClec) (synCtc N))
        (synWbr (synCtc (synCtc M)) (synClec) (synCtc (synCtc N))))
      p0003 p0005 p0006
  have p0008 :=
    @gBitri (synWbr M (synClec) N) (synWbr (synCtc M) (synClec) (synCtc N))
      (synWbr (synCtc (synCtc M)) (synClec) (synCtc (synCtc N))) p0001 p0007
  have p0011 := @gTccl (synCtc M)
  have p0012 := Nominal.mp p0003 p0011
  have p0015 := @gTccl (synCtc N)
  have p0016 := Nominal.mp p0005 p0015
  have p0017 := @gTlecg (synCtc (synCtc M)) (synCtc (synCtc N))
  have p0018 :=
    @gMp2an (.classMem (synCtc (synCtc M)) (synCncs))
      (.classMem (synCtc (synCtc N)) (synCncs))
      (synWb (synWbr (synCtc (synCtc M)) (synClec) (synCtc (synCtc N)))
        (synWbr (synCtc (synCtc (synCtc M))) (synClec) (synCtc (synCtc (synCtc N)))))
      p0012 p0016 p0017
  have p0019 :=
    @gBitri (synWbr M (synClec) N)
      (synWbr (synCtc (synCtc M)) (synClec) (synCtc (synCtc N)))
      (synWbr (synCtc (synCtc (synCtc M))) (synClec) (synCtc (synCtc (synCtc N))))
      p0008 p0018
  have p0024 := @gTccl (synCtc (synCtc M))
  have p0025 := Nominal.mp p0012 p0024
  have p0030 := @gTccl (synCtc (synCtc N))
  have p0031 := Nominal.mp p0016 p0030
  have p0032 := @gTlecg (synCtc (synCtc (synCtc M))) (synCtc (synCtc (synCtc N)))
  have p0033 :=
    @gMp2an (.classMem (synCtc (synCtc (synCtc M))) (synCncs))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs))
      (synWb (synWbr (synCtc (synCtc (synCtc M))) (synClec)
          (synCtc (synCtc (synCtc N))))
        (synWbr (synCtc (synCtc (synCtc (synCtc M)))) (synClec)
          (synCtc (synCtc (synCtc (synCtc N))))))
      p0025 p0031 p0032
  have p0034 :=
    @gBitri (synWbr M (synClec) N)
      (synWbr (synCtc (synCtc (synCtc M))) (synClec) (synCtc (synCtc (synCtc N))))
      (synWbr (synCtc (synCtc (synCtc (synCtc M)))) (synClec)
        (synCtc (synCtc (synCtc (synCtc N)))))
      p0019 p0033
  have p0041 := @gTccl (synCtc (synCtc (synCtc M)))
  have p0042 := Nominal.mp p0025 p0041
  have p0049 := @gTccl (synCtc (synCtc (synCtc N)))
  have p0050 := Nominal.mp p0031 p0049
  have p0051 :=
    @gTlecg (synCtc (synCtc (synCtc (synCtc M))))
      (synCtc (synCtc (synCtc (synCtc N))))
  have p0052 :=
    @gMp2an (.classMem (synCtc (synCtc (synCtc (synCtc M)))) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs))
      (synWb (synWbr (synCtc (synCtc (synCtc (synCtc M)))) (synClec)
          (synCtc (synCtc (synCtc (synCtc N)))))
        (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc M))))) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0042 p0050 p0051
  have p0053 :=
    @gBitri (synWbr M (synClec) N)
      (synWbr (synCtc (synCtc (synCtc (synCtc M)))) (synClec)
        (synCtc (synCtc (synCtc (synCtc N)))))
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc M))))) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      p0034 p0052
  have p0062 := @gTccl (synCtc (synCtc (synCtc (synCtc M))))
  have p0063 := Nominal.mp p0042 p0062
  have p0072 := @gTccl (synCtc (synCtc (synCtc (synCtc N))))
  have p0073 := Nominal.mp p0050 p0072
  have p0074 :=
    @gTlecg (synCtc (synCtc (synCtc (synCtc (synCtc M)))))
      (synCtc (synCtc (synCtc (synCtc (synCtc N)))))
  have p0075 :=
    @gMp2an (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc M))))) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synCncs))
      (synWb (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc M))))) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
        (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc M)))))) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      p0063 p0073 p0074
  have p0076 :=
    @gBitri (synWbr M (synClec) N)
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc M))))) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc M)))))) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0053 p0075
  have p0077 :=
    @gBiimpri (synWbr M (synClec) N)
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc M)))))) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0076
  exact p0077

/-- Checked nominal proof certificate identified upstream as `g_tc2nc`. -/
@[expose]
noncomputable def gTc2nc (A : Class)
    (hyp_tc2nc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synCnc A))) (synCnc (synCpw1 (synCpw1 A)))) :=
  by
  have p0000 := @gTcnc A hyp_tc2nc_1
  have p0001 := @gTceq (synCtc (synCnc A)) (synCnc (synCpw1 A))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gPw1ex A hyp_tc2nc_1
  have p0004 := @gTcnc (synCpw1 A) p0003
  have p0005 :=
    @gEqtri (synCtc (synCtc (synCnc A))) (synCtc (synCnc (synCpw1 A)))
      (synCnc (synCpw1 (synCpw1 A))) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_resiidima`. -/
@[expose]
noncomputable def gResiidima (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCima (synCres (synCid) A) B) (synCin A B)) :=
  by
  have p0000 := @gCnvresid A
  have p0001 := @gEqcomi (synCcnv (synCres (synCid) A)) (synCres (synCid) A) p0000
  have p0002 :=
    @gImaeq1i (synCres (synCid) A) (synCcnv (synCres (synCid) A)) B p0001
  have p0003 := @gCnvresima A B (synCid)
  have p0004 :=
    @gEqtri (synCima (synCres (synCid) A) B)
      (synCima (synCcnv (synCres (synCid) A)) B)
      (synCin (synCima (synCcnv (synCid)) B) A) p0002 p0003
  have p0005 := @gCnvi
  have p0006 := @gImaeq1i (synCcnv (synCid)) (synCid) B p0005
  have p0007 := @gImai B
  have p0008 :=
    @gEqtri (synCima (synCcnv (synCid)) B) (synCima (synCid) B) B p0006 p0007
  have p0009 := @gIneq1i (synCima (synCcnv (synCid)) B) B A p0008
  have p0010 :=
    @gEqtri (synCima (synCres (synCid) A) B)
      (synCin (synCima (synCcnv (synCid)) B) A) (synCin B A) p0004 p0009
  have p0011 := @gIncom B A
  have p0012 :=
    @gEqtri (synCima (synCres (synCid) A) B) (synCin B A) (synCin A B) p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_hnwsegfnex`. -/
@[expose]
noncomputable def gHnwsegfnex (D : Class) (R : Class)
    (hyp_hnwsegfnex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synChnwsegfn R D) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwsegfn R D))
  have p0001 := @gIdex
  have p0002 := @gBrex R D (synCwe)
  have p0003 := Nominal.mp hyp_hnwsegfnex_1 p0002
  have p0004 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0003
  have p0005 := @gResex (synCid) D p0001 p0004
  have p0006 := @gImageex (synCres (synCid) D) p0005
  have p0009 := @gSimpli (.classMem R (synCvv)) (.classMem D (synCvv)) p0003
  have p0011 := @gDifex R (synCid) p0009 p0001
  have p0012 := @gCnvex (synCdif R (synCid)) p0011
  have p0013 := @gImageex (synCcnv (synCdif R (synCid))) p0012
  have p0014 :=
    @gCoex (synCimage (synCres (synCid) D))
      (synCimage (synCcnv (synCdif R (synCid)))) p0006 p0013
  have p0015 :=
    @gEqeltri (synChnwsegfn R D)
      (synCcom (synCimage (synCres (synCid) D))
        (synCimage (synCcnv (synCdif R (synCid)))))
      (synCvv) p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hnwcodefnex`. -/
@[expose]
noncomputable def gHnwcodefnex (D : Class) (R : Class)
    (hyp_hnwcodefnex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synChnwcodefn R) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcodefn R))
  have p0001 := @gIdex
  have p0002 := @gBrex R D (synCwe)
  have p0003 := Nominal.mp hyp_hnwcodefnex_1 p0002
  have p0004 := @gSimpli (.classMem R (synCvv)) (.classMem D (synCvv)) p0003
  have p0005 := @gResex (synCid) R p0001 p0004
  have p0006 := @gImageex (synCres (synCid) R) p0005
  have p0007 := @gCrossex
  have p0010 := @gTxpex (synCid) (synCid) p0001 p0001
  have p0011 := @gCoex (synCcross) (synCtxp (synCid) (synCid)) p0007 p0010
  have p0012 :=
    @gCoex (synCimage (synCres (synCid) R))
      (synCcom (synCcross) (synCtxp (synCid) (synCid))) p0006 p0011
  have p0014 :=
    @gTxpex
      (synCcom (synCimage (synCres (synCid) R))
        (synCcom (synCcross) (synCtxp (synCid) (synCid))))
      (synCid) p0012 p0001
  have p0015 :=
    @gEqeltri (synChnwcodefn R)
      (synCtxp (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
      (synCvv) p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hnwcutfnex`. -/
@[expose]
noncomputable def gHnwcutfnex (D : Class) (R : Class)
    (hyp_hnwcutfnex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synChnwcutfn R D) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcutfn R D))
  have p0001 := @gHnwcodefnex D R hyp_hnwcutfnex_1
  have p0002 := @gHnwsegfnex D R hyp_hnwcutfnex_1
  have p0003 := @gCoex (synChnwcodefn R) (synChnwsegfn R D) p0001 p0002
  have p0004 :=
    @gEqeltri (synChnwcutfn R D) (synCcom (synChnwcodefn R) (synChnwsegfn R D))
      (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fvimagecl`. -/
@[expose]
noncomputable def gFvimagecl (B : Class) (F : Class)
    (hyp_fvimagecl_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_fvimagecl_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCimage F) B) (synCima F B)) :=
  by
  have p0000 := @gEqid (synCima F B)
  have p0001 := @gImaex F B hyp_fvimagecl_1 hyp_fvimagecl_2
  have p0002 := @gBrimage B (synCima F B) F hyp_fvimagecl_2 p0001
  have p0003 :=
    @gMpbir (synWbr B (synCimage F) (synCima F B))
      (.classEq (synCima F B) (synCima F B)) p0000 p0002
  have p0004 := @gWppimagefn F hyp_fvimagecl_1
  have p0005 :=
    @gPm32i (synWfn (synCimage F) (synCvv)) (.classMem B (synCvv)) p0004
      hyp_fvimagecl_2
  have p0006 := @gFnbrfvb (synCvv) B (synCima F B) (synCimage F)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gMpbir (.classEq (synCfv (synCimage F) B) (synCima F B))
      (synWbr B (synCimage F) (synCima F B)) p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fncovv`. -/
@[expose]
noncomputable def gFncovv (F : Class) (G : Class)
    (hyp_fncovv_1 : Nominal.NPrf (synWfn F (synCvv)))
    (hyp_fncovv_2 : Nominal.NPrf (synWfn G (synCvv))) :
    Nominal.NPrf (synWfn (synCcom F G) (synCvv)) :=
  by
  have p0000 := @gSsv (synCrn G)
  have p0001 :=
    @gN3pm32i (synWfn F (synCvv)) (synWfn G (synCvv))
      (synWss (synCrn G) (synCvv)) hyp_fncovv_1 hyp_fncovv_2 p0000
  have p0002 := @gFnco (synCvv) (synCvv) F G
  have p0003 := Nominal.mp p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fvtxpvv`. -/
@[expose]
noncomputable def gFvtxpvv (A : Class) (F : Class) (G : Class)
    (hyp_fvtxpvv_1 : Nominal.NPrf (synWfn F (synCvv)))
    (hyp_fvtxpvv_2 : Nominal.NPrf (synWfn G (synCvv)))
    (hyp_fvtxpvv_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCtxp F G) A) (synCop (synCfv F A) (synCfv G A))) :=
  by
  have p0000 := @gEqid (synCfv F A)
  have p0001 :=
    @gPm32i (synWfn F (synCvv)) (.classMem A (synCvv)) hyp_fvtxpvv_1 hyp_fvtxpvv_3
  have p0002 := @gFnbrfvb (synCvv) A (synCfv F A) F
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gMpbi (.classEq (synCfv F A) (synCfv F A)) (synWbr A F (synCfv F A)) p0000 p0003
  have p0005 := @gEqid (synCfv G A)
  have p0006 :=
    @gPm32i (synWfn G (synCvv)) (.classMem A (synCvv)) hyp_fvtxpvv_2 hyp_fvtxpvv_3
  have p0007 := @gFnbrfvb (synCvv) A (synCfv G A) G
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gMpbi (.classEq (synCfv G A) (synCfv G A)) (synWbr A G (synCfv G A)) p0005 p0008
  have p0010 :=
    @gPm32i (synWbr A F (synCfv F A)) (synWbr A G (synCfv G A)) p0004 p0009
  have p0011 := @gTrtxp A (synCfv F A) (synCfv G A) F G
  have p0012 :=
    @gMpbir (synWbr A (synCtxp F G) (synCop (synCfv F A) (synCfv G A)))
      (synWa (synWbr A F (synCfv F A)) (synWbr A G (synCfv G A))) p0010 p0011
  have p0013 :=
    @gPm32i (synWfn F (synCvv)) (synWfn G (synCvv)) hyp_fvtxpvv_1 hyp_fvtxpvv_2
  have p0014 := @gFntxp (synCvv) (synCvv) F G
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gInidm (synCvv)
  have p0017 := @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp F G) p0016
  have p0018 :=
    @gMpbi (synWfn (synCtxp F G) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp F G) (synCvv)) p0015 p0017
  have p0019 :=
    @gPm32i (synWfn (synCtxp F G) (synCvv)) (.classMem A (synCvv)) p0018
      hyp_fvtxpvv_3
  have p0020 :=
    @gFnbrfvb (synCvv) A (synCop (synCfv F A) (synCfv G A)) (synCtxp F G)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @gMpbir (.classEq (synCfv (synCtxp F G) A) (synCop (synCfv F A) (synCfv G A)))
      (synWbr A (synCtxp F G) (synCop (synCfv F A) (synCfv G A))) p0012 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_hnwsegfnfn`. -/
@[expose]
noncomputable def gHnwsegfnfn (D : Class) (R : Class)
    (hyp_hnwsegfnfn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWfn (synChnwsegfn R D) (synCvv)) :=
  by
  have p0000 := @gIdex
  have p0001 := @gBrex R D (synCwe)
  have p0002 := Nominal.mp hyp_hnwsegfnfn_1 p0001
  have p0003 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0002
  have p0004 := @gResex (synCid) D p0000 p0003
  have p0005 := @gWppimagefn (synCres (synCid) D) p0004
  have p0008 := @gSimpli (.classMem R (synCvv)) (.classMem D (synCvv)) p0002
  have p0010 := @gDifex R (synCid) p0008 p0000
  have p0011 := @gCnvex (synCdif R (synCid)) p0010
  have p0012 := @gWppimagefn (synCcnv (synCdif R (synCid))) p0011
  have p0013 :=
    @gFncovv (synCimage (synCres (synCid) D))
      (synCimage (synCcnv (synCdif R (synCid)))) p0005 p0012
  have p0014 := (Nominal.classEqRefl (synChnwsegfn R D))
  have p0015 :=
    @gFneq1i (synCvv) (synChnwsegfn R D)
      (synCcom (synCimage (synCres (synCid) D))
        (synCimage (synCcnv (synCdif R (synCid)))))
      p0014
  have p0016 :=
    @gMpbir (synWfn (synChnwsegfn R D) (synCvv))
      (synWfn (synCcom (synCimage (synCres (synCid) D))
          (synCimage (synCcnv (synCdif R (synCid))))) (synCvv))
      p0013 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_hnwcodefnfn`. -/
@[expose]
noncomputable def gHnwcodefnfn (D : Class) (R : Class)
    (hyp_hnwcodefnfn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWfn (synChnwcodefn R) (synCvv)) :=
  by
  have p0000 := @gIdex
  have p0001 := @gBrex R D (synCwe)
  have p0002 := Nominal.mp hyp_hnwcodefnfn_1 p0001
  have p0003 := @gSimpli (.classMem R (synCvv)) (.classMem D (synCvv)) p0002
  have p0004 := @gResex (synCid) R p0000 p0003
  have p0005 := @gWppimagefn (synCres (synCid) R) p0004
  have p0006 := @gFncross
  have p0007 := @gFnresi (synCvv)
  have p0008 := @gResid (synCid)
  have p0009 := @gFneq1i (synCvv) (synCres (synCid) (synCvv)) (synCid) p0008
  have p0010 :=
    @gMpbi (synWfn (synCres (synCid) (synCvv)) (synCvv))
      (synWfn (synCid) (synCvv)) p0007 p0009
  have p0015 :=
    @gPm32i (synWfn (synCid) (synCvv)) (synWfn (synCid) (synCvv)) p0010 p0010
  have p0016 := @gFntxp (synCvv) (synCvv) (synCid) (synCid)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @gInidm (synCvv)
  have p0019 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synCid) (synCid)) p0018
  have p0020 :=
    @gMpbi (synWfn (synCtxp (synCid) (synCid)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synCid)) (synCvv)) p0017 p0019
  have p0021 := @gFncovv (synCcross) (synCtxp (synCid) (synCid)) p0006 p0020
  have p0022 :=
    @gFncovv (synCimage (synCres (synCid) R))
      (synCcom (synCcross) (synCtxp (synCid) (synCid))) p0005 p0021
  have p0027 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCvv))
      (synWfn (synCid) (synCvv)) p0022 p0010
  have p0028 :=
    @gFntxp (synCvv) (synCvv)
      (synCcom (synCimage (synCres (synCid) R))
        (synCcom (synCcross) (synCtxp (synCid) (synCid))))
      (synCid)
  have p0029 := Nominal.mp p0027 p0028
  have p0031 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
      p0018
  have p0032 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synCimage (synCres (synCid) R))
            (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synCimage (synCres (synCid) R))
            (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid)) (synCvv))
      p0029 p0031
  have p0033 := (Nominal.classEqRefl (synChnwcodefn R))
  have p0034 :=
    @gFneq1i (synCvv) (synChnwcodefn R)
      (synCtxp (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
      p0033
  have p0035 :=
    @gMpbir (synWfn (synChnwcodefn R) (synCvv))
      (synWfn (synCtxp (synCcom (synCimage (synCres (synCid) R))
            (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid)) (synCvv))
      p0032 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_hnwcutfnfn`. -/
@[expose]
noncomputable def gHnwcutfnfn (D : Class) (R : Class)
    (hyp_hnwcutfnfn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWfn (synChnwcutfn R D) (synCvv)) :=
  by
  have p0000 := @gHnwcodefnfn D R hyp_hnwcutfnfn_1
  have p0001 := @gHnwsegfnfn D R hyp_hnwcutfnfn_1
  have p0002 := @gFncovv (synChnwcodefn R) (synChnwsegfn R D) p0000 p0001
  have p0003 := (Nominal.classEqRefl (synChnwcutfn R D))
  have p0004 :=
    @gFneq1i (synCvv) (synChnwcutfn R D)
      (synCcom (synChnwcodefn R) (synChnwsegfn R D)) p0003
  have p0005 :=
    @gMpbir (synWfn (synChnwcutfn R D) (synCvv))
      (synWfn (synCcom (synChnwcodefn R) (synChnwsegfn R D)) (synCvv)) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hnwsegfnval`. -/
@[expose]
noncomputable def gHnwsegfnval (B : Class) (D : Class) (R : Class)
    (hyp_hnwsegfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hnwsegfnval_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnwsegfnval_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChnwsegfn R D) B)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) B))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwsegfn R D))
  have p0001 :=
    @gFveq1i B (synChnwsegfn R D)
      (synCcom (synCimage (synCres (synCid) D))
        (synCimage (synCcnv (synCdif R (synCid)))))
      p0000
  have p0002 := @gIdex
  have p0003 := @gDifex R (synCid) hyp_hnwsegfnval_1 p0002
  have p0004 := @gCnvex (synCdif R (synCid)) p0003
  have p0005 := @gWppimagefn (synCcnv (synCdif R (synCid))) p0004
  have p0006 :=
    @gPm32i (synWfn (synCimage (synCcnv (synCdif R (synCid)))) (synCvv))
      (.classMem B (synCvv)) p0005 hyp_hnwsegfnval_3
  have p0007 :=
    @gFvco2 (synCvv) B (synCimage (synCres (synCid) D))
      (synCimage (synCcnv (synCdif R (synCid))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gEqtri (synCfv (synChnwsegfn R D) B)
      (synCfv (synCcom (synCimage (synCres (synCid) D))
          (synCimage (synCcnv (synCdif R (synCid))))) B)
      (synCfv (synCimage (synCres (synCid) D))
        (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B))
      p0001 p0008
  have p0011 := @gResex (synCid) D p0002 hyp_hnwsegfnval_2
  have p0012 := @gFvex B (synCimage (synCcnv (synCdif R (synCid))))
  have p0013 :=
    @gFvimagecl (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B)
      (synCres (synCid) D) p0011 p0012
  have p0014 :=
    @gEqtri (synCfv (synChnwsegfn R D) B)
      (synCfv (synCimage (synCres (synCid) D))
        (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B))
      (synCima (synCres (synCid) D)
        (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B))
      p0009 p0013
  have p0015 := @gResiidima D (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B)
  have p0016 :=
    @gEqtri (synCfv (synChnwsegfn R D) B)
      (synCima (synCres (synCid) D)
        (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B))
      (synCin D (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B)) p0014 p0015
  have p0020 := @gFvimagecl B (synCcnv (synCdif R (synCid))) p0004 hyp_hnwsegfnval_3
  have p0021 :=
    @gIneq2i (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B)
      (synCima (synCcnv (synCdif R (synCid))) B) D p0020
  have p0022 :=
    @gEqtri (synCfv (synChnwsegfn R D) B)
      (synCin D (synCfv (synCimage (synCcnv (synCdif R (synCid)))) B))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) B)) p0016 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_hnwcodefnval`. -/
@[expose]
noncomputable def gHnwcodefnval (B : Class) (R : Class)
    (hyp_hnwcodefnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hnwcodefnval_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChnwcodefn R) B) (synCop (synCin R (synCxp B B)) B)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcodefn R))
  have p0001 :=
    @gFveq1i B (synChnwcodefn R)
      (synCtxp (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
      p0000
  have p0002 := @gIdex
  have p0003 := @gResex (synCid) R p0002 hyp_hnwcodefnval_1
  have p0004 := @gWppimagefn (synCres (synCid) R) p0003
  have p0005 := @gFncross
  have p0006 := @gFnresi (synCvv)
  have p0007 := @gResid (synCid)
  have p0008 := @gFneq1i (synCvv) (synCres (synCid) (synCvv)) (synCid) p0007
  have p0009 :=
    @gMpbi (synWfn (synCres (synCid) (synCvv)) (synCvv))
      (synWfn (synCid) (synCvv)) p0006 p0008
  have p0014 :=
    @gPm32i (synWfn (synCid) (synCvv)) (synWfn (synCid) (synCvv)) p0009 p0009
  have p0015 := @gFntxp (synCvv) (synCvv) (synCid) (synCid)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gInidm (synCvv)
  have p0018 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synCid) (synCid)) p0017
  have p0019 :=
    @gMpbi (synWfn (synCtxp (synCid) (synCid)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synCid)) (synCvv)) p0016 p0018
  have p0020 := @gFncovv (synCcross) (synCtxp (synCid) (synCid)) p0005 p0019
  have p0021 :=
    @gFncovv (synCimage (synCres (synCid) R))
      (synCcom (synCcross) (synCtxp (synCid) (synCid))) p0004 p0020
  have p0026 :=
    @gFvtxpvv B
      (synCcom (synCimage (synCres (synCid) R))
        (synCcom (synCcross) (synCtxp (synCid) (synCid))))
      (synCid) p0021 p0009 hyp_hnwcodefnval_2
  have p0043 :=
    @gPm32i (synWfn (synCcom (synCcross) (synCtxp (synCid) (synCid))) (synCvv))
      (.classMem B (synCvv)) p0020 hyp_hnwcodefnval_2
  have p0044 :=
    @gFvco2 (synCvv) B (synCimage (synCres (synCid) R))
      (synCcom (synCcross) (synCtxp (synCid) (synCid)))
  have p0045 := Nominal.mp p0043 p0044
  have p0060 :=
    @gPm32i (synWfn (synCtxp (synCid) (synCid)) (synCvv)) (.classMem B (synCvv))
      p0019 hyp_hnwcodefnval_2
  have p0061 := @gFvco2 (synCvv) B (synCcross) (synCtxp (synCid) (synCid))
  have p0062 := Nominal.mp p0060 p0061
  have p0071 := @gFvtxpvv B (synCid) (synCid) p0009 p0009 hyp_hnwcodefnval_2
  have p0072 := @gFvi B (synCvv)
  have p0073 := Nominal.mp hyp_hnwcodefnval_2 p0072
  have p0076 := @gOpeq12i (synCfv (synCid) B) B (synCfv (synCid) B) B p0073 p0073
  have p0077 :=
    @gEqtri (synCfv (synCtxp (synCid) (synCid)) B)
      (synCop (synCfv (synCid) B) (synCfv (synCid) B)) (synCop B B) p0071 p0076
  have p0078 :=
    @gFveq2i (synCfv (synCtxp (synCid) (synCid)) B) (synCop B B) (synCcross) p0077
  have p0079 :=
    @gEqtri (synCfv (synCcom (synCcross) (synCtxp (synCid) (synCid))) B)
      (synCfv (synCcross) (synCfv (synCtxp (synCid) (synCid)) B))
      (synCfv (synCcross) (synCop B B)) p0062 p0078
  have p0080 := (Nominal.classEqRefl (synCo B (synCcross) B))
  have p0081 :=
    @gEqcomi (synCo B (synCcross) B) (synCfv (synCcross) (synCop B B)) p0080
  have p0082 :=
    @gEqtri (synCfv (synCcom (synCcross) (synCtxp (synCid) (synCid))) B)
      (synCfv (synCcross) (synCop B B)) (synCo B (synCcross) B) p0079 p0081
  have p0083 :=
    @gPm32i (.classMem B (synCvv)) (.classMem B (synCvv)) hyp_hnwcodefnval_2
      hyp_hnwcodefnval_2
  have p0084 := @gOvcross B B (synCvv) (synCvv)
  have p0085 := Nominal.mp p0083 p0084
  have p0086 :=
    @gEqtri (synCfv (synCcom (synCcross) (synCtxp (synCid) (synCid))) B)
      (synCo B (synCcross) B) (synCxp B B) p0082 p0085
  have p0087 :=
    @gFveq2i (synCfv (synCcom (synCcross) (synCtxp (synCid) (synCid))) B)
      (synCxp B B) (synCimage (synCres (synCid) R)) p0086
  have p0088 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) B)
      (synCfv (synCimage (synCres (synCid) R))
        (synCfv (synCcom (synCcross) (synCtxp (synCid) (synCid))) B))
      (synCfv (synCimage (synCres (synCid) R)) (synCxp B B)) p0045 p0087
  have p0091 := @gXpex B B hyp_hnwcodefnval_2 hyp_hnwcodefnval_2
  have p0092 := @gFvimagecl (synCxp B B) (synCres (synCid) R) p0003 p0091
  have p0093 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) B)
      (synCfv (synCimage (synCres (synCid) R)) (synCxp B B))
      (synCima (synCres (synCid) R) (synCxp B B)) p0088 p0092
  have p0094 := @gResiidima R (synCxp B B)
  have p0095 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) B)
      (synCima (synCres (synCid) R) (synCxp B B)) (synCin R (synCxp B B)) p0093
      p0094
  have p0098 :=
    @gOpeq12i
      (synCfv (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) B)
      (synCin R (synCxp B B)) (synCfv (synCid) B) B p0095 p0073
  have p0099 :=
    @gEqtri
      (synCfv (synCtxp (synCcom (synCimage (synCres (synCid) R))
            (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid)) B)
      (synCop (synCfv (synCcom (synCimage (synCres (synCid) R))
            (synCcom (synCcross) (synCtxp (synCid) (synCid)))) B) (synCfv (synCid) B))
      (synCop (synCin R (synCxp B B)) B) p0026 p0098
  have p0100 :=
    @gEqtri (synCfv (synChnwcodefn R) B)
      (synCfv (synCtxp (synCcom (synCimage (synCres (synCid) R))
            (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid)) B)
      (synCop (synCin R (synCxp B B)) B) p0001 p0099
  exact p0100

/-- Checked nominal proof certificate identified upstream as `g_hnwcutfnvalg`. -/
@[expose]
noncomputable def gHnwcutfnvalg (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutfnvalg_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hnwcutfnvalg_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnwcutfnvalg_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChnwcutfn R D) B) (synCop (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) B))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) B))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) B)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcutfn R D))
  have p0001 :=
    @gFveq1i B (synChnwcutfn R D) (synCcom (synChnwcodefn R) (synChnwsegfn R D))
      p0000
  have p0002 := @gIdex
  have p0003 := @gResex (synCid) D p0002 hyp_hnwcutfnvalg_2
  have p0004 := @gWppimagefn (synCres (synCid) D) p0003
  have p0006 := @gDifex R (synCid) hyp_hnwcutfnvalg_1 p0002
  have p0007 := @gCnvex (synCdif R (synCid)) p0006
  have p0008 := @gWppimagefn (synCcnv (synCdif R (synCid))) p0007
  have p0009 :=
    @gFncovv (synCimage (synCres (synCid) D))
      (synCimage (synCcnv (synCdif R (synCid)))) p0004 p0008
  have p0010 := (Nominal.classEqRefl (synChnwsegfn R D))
  have p0011 :=
    @gFneq1i (synCvv) (synChnwsegfn R D)
      (synCcom (synCimage (synCres (synCid) D))
        (synCimage (synCcnv (synCdif R (synCid)))))
      p0010
  have p0012 :=
    @gMpbir (synWfn (synChnwsegfn R D) (synCvv))
      (synWfn (synCcom (synCimage (synCres (synCid) D))
          (synCimage (synCcnv (synCdif R (synCid))))) (synCvv))
      p0009 p0011
  have p0013 :=
    @gPm32i (synWfn (synChnwsegfn R D) (synCvv)) (.classMem B (synCvv)) p0012
      hyp_hnwcutfnvalg_3
  have p0014 := @gFvco2 (synCvv) B (synChnwcodefn R) (synChnwsegfn R D)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @gEqtri (synCfv (synChnwcutfn R D) B)
      (synCfv (synCcom (synChnwcodefn R) (synChnwsegfn R D)) B)
      (synCfv (synChnwcodefn R) (synCfv (synChnwsegfn R D) B)) p0001 p0015
  have p0017 :=
    @gHnwsegfnval B D R hyp_hnwcutfnvalg_1 hyp_hnwcutfnvalg_2 hyp_hnwcutfnvalg_3
  have p0018 :=
    @gFveq2i (synCfv (synChnwsegfn R D) B)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) B)) (synChnwcodefn R) p0017
  have p0019 :=
    @gEqtri (synCfv (synChnwcutfn R D) B)
      (synCfv (synChnwcodefn R) (synCfv (synChnwsegfn R D) B))
      (synCfv (synChnwcodefn R) (synCin D (synCima (synCcnv (synCdif R (synCid))) B)))
      p0016 p0018
  have p0023 := @gImaex (synCcnv (synCdif R (synCid))) B p0007 hyp_hnwcutfnvalg_3
  have p0024 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) B) hyp_hnwcutfnvalg_2 p0023
  have p0025 :=
    @gHnwcodefnval (synCin D (synCima (synCcnv (synCdif R (synCid))) B)) R
      hyp_hnwcutfnvalg_1 p0024
  have p0026 :=
    @gEqtri (synCfv (synChnwcutfn R D) B)
      (synCfv (synChnwcodefn R) (synCin D (synCima (synCcnv (synCdif R (synCid))) B)))
      (synCop (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) B))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) B))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) B)))
      p0019 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_hnwcutfnvalcl`. -/
@[expose]
noncomputable def gHnwcutfnvalcl (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutfnvalcl_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (_hyp_hnwcutfnvalcl_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChnwcutfn R D) (synCsn B)) (synChnwcutcode R D B)) :=
  by
  have p0000 := @gBrex R D (synCwe)
  have p0001 := Nominal.mp hyp_hnwcutfnvalcl_1 p0000
  have p0002 := @gSimpli (.classMem R (synCvv)) (.classMem D (synCvv)) p0001
  have p0005 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0001
  have p0006 := @gSnex B
  have p0007 := @gHnwcutfnvalg (synCsn B) D R p0002 p0005 p0006
  have p0008 := (Nominal.classEqRefl (synChnwcutcode R D B))
  have p0009 :=
    @gEqcomi (synChnwcutcode R D B)
      (synCop (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      p0008
  have p0010 :=
    @gEqtri (synCfv (synChnwcutfn R D) (synCsn B))
      (synCop (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      (synChnwcutcode R D B) p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnwcutrelex`. -/
@[expose]
noncomputable def gHnwcutrelex (D : Class) (R : Class)
    (hyp_hnwcutrelex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synChnwcutrel R D) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcutrel R D))
  have p0001 := @gHnwcutfnex D R hyp_hnwcutrelex_1
  have p0002 := @gBrex R D (synCwe)
  have p0003 := Nominal.mp hyp_hnwcutrelex_1 p0002
  have p0004 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0003
  have p0005 := @gPw1ex D p0004
  have p0006 := @gResex (synChnwcutfn R D) (synCpw1 D) p0001 p0005
  have p0007 :=
    @gEqeltri (synChnwcutrel R D) (synCres (synChnwcutfn R D) (synCpw1 D)) (synCvv)
      p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnwcutrelfn`. -/
@[expose]
noncomputable def gHnwcutrelfn (D : Class) (R : Class)
    (hyp_hnwcutrelfn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWfn (synChnwcutrel R D) (synCpw1 D)) :=
  by
  have p0000 := @gHnwcutfnfn D R hyp_hnwcutrelfn_1
  have p0001 := @gSsv (synCpw1 D)
  have p0002 :=
    @gPm32i (synWfn (synChnwcutfn R D) (synCvv)) (synWss (synCpw1 D) (synCvv))
      p0000 p0001
  have p0003 := @gFnssres (synCvv) (synCpw1 D) (synChnwcutfn R D)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (synChnwcutrel R D))
  have p0006 :=
    @gFneq1i (synCpw1 D) (synChnwcutrel R D)
      (synCres (synChnwcutfn R D) (synCpw1 D)) p0005
  have p0007 :=
    @gMpbir (synWfn (synChnwcutrel R D) (synCpw1 D))
      (synWfn (synCres (synChnwcutfn R D) (synCpw1 D)) (synCpw1 D)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnwpw1argcl`. -/
@[expose]
noncomputable def gHnwpw1argcl (D : Class) (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 D)) (synWa (.classMem (synCuni (.cv q)) D)
          (.classEq (.cv q) (synCsn (synCuni (.cv q)))))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ ({ q } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_q : x ≠ q := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : x ∉ ((Class.cv q)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_q, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 :
    x ∉
      ((synWa (.classMem (synCuni (.cv q)) D)
          (.classEq (.cv q) (synCsn (synCuni (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_D, or_false, not_false_eq_true])
  have p0000 := @gElpw1 x (.cv q) D dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpi (.classMem (.cv q) (synCpw1 D))
      (synWrex x D (.classEq (.cv q) (synCsn (.cv x)))) p0000
  have p0002 := @gSimpr (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x)))
  have p0003 := @gId (.classEq (.cv q) (synCsn (.cv x)))
  have p0004 :=
    @gUnieqd (.classEq (.cv q) (synCsn (.cv x))) (.cv q) (synCsn (.cv x)) p0003
  have p0005 := @gVex x
  have p0006 := @gUnisn (.cv x) p0005
  have p0007 :=
    @gA1i (.classEq (synCuni (synCsn (.cv x))) (.cv x))
      (.classEq (.cv q) (synCsn (.cv x))) p0006
  have p0008 :=
    @gEqtrd (.classEq (.cv q) (synCsn (.cv x))) (synCuni (.cv q))
      (synCuni (synCsn (.cv x))) (.cv x) p0004 p0007
  have p0009 :=
    @gSyl (synWa (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x))))
      (.classEq (.cv q) (synCsn (.cv x))) (.classEq (synCuni (.cv q)) (.cv x)) p0002
      p0008
  have p0010 := @gSimpl (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x)))
  have p0011 :=
    @gEqeltrd (synWa (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x))))
      (synCuni (.cv q)) (.cv x) D p0009 p0010
  have p0021 :=
    @gSneqd (synWa (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x))))
      (synCuni (.cv q)) (.cv x) p0009
  have p0022 :=
    @gEqcomd (synWa (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x))))
      (synCsn (synCuni (.cv q))) (synCsn (.cv x)) p0021
  have p0023 :=
    @gEqtrd (synWa (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x)))) (.cv q)
      (synCsn (.cv x)) (synCsn (synCuni (.cv q))) p0002 p0022
  have p0024 :=
    @gJca (synWa (.classMem (.cv x) D) (.classEq (.cv q) (synCsn (.cv x))))
      (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q))))
      p0011 p0023
  have p0025 :=
    @gRexlimiva (.classEq (.cv q) (synCsn (.cv x)))
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      x D dv_cache_0003 p0024
  have p0026 :=
    @gSyl (.classMem (.cv q) (synCpw1 D))
      (synWrex x D (.classEq (.cv q) (synCsn (.cv x))))
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0001 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_hnwcutrelval`. -/
@[expose]
noncomputable def gHnwcutrelval (D : Class) (R : Class) (q : Var)
    (hyp_hnwcutrelval_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 D)) (.classEq (synCfv (synChnwcutrel R D) (.cv q))
          (synChnwcutcode R D (synCuni (.cv q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcutrel R D))
  have p0001 :=
    @gFveq1i (.cv q) (synChnwcutrel R D) (synCres (synChnwcutfn R D) (synCpw1 D))
      p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synChnwcutrel R D) (.cv q))
        (synCfv (synCres (synChnwcutfn R D) (synCpw1 D)) (.cv q)))
      (.classMem (.cv q) (synCpw1 D)) p0001
  have p0003 := @gFvres (.cv q) (synCpw1 D) (synChnwcutfn R D)
  have p0004 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 D)) (synCfv (synChnwcutrel R D) (.cv q))
      (synCfv (synCres (synChnwcutfn R D) (synCpw1 D)) (.cv q))
      (synCfv (synChnwcutfn R D) (.cv q)) p0002 p0003
  have p0005 := @gHnwpw1argcl D q
  have p0006 :=
    @gSimprd (.classMem (.cv q) (synCpw1 D)) (.classMem (synCuni (.cv q)) D)
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0005
  have p0007 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 D)) (.cv q) (synCsn (synCuni (.cv q)))
      (synChnwcutfn R D) p0006
  have p0008 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 D)) (synCfv (synChnwcutrel R D) (.cv q))
      (synCfv (synChnwcutfn R D) (.cv q))
      (synCfv (synChnwcutfn R D) (synCsn (synCuni (.cv q)))) p0004 p0007
  have p0009 := @gVex q
  have p0010 := @gUniex (.cv q) p0009
  have p0011 := @gHnwcutfnvalcl (synCuni (.cv q)) D R hyp_hnwcutrelval_1 p0010
  have p0012 :=
    @gA1i
      (.classEq (synCfv (synChnwcutfn R D) (synCsn (synCuni (.cv q))))
        (synChnwcutcode R D (synCuni (.cv q))))
      (.classMem (.cv q) (synCpw1 D)) p0011
  have p0013 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 D)) (synCfv (synChnwcutrel R D) (.cv q))
      (synCfv (synChnwcutfn R D) (synCsn (synCuni (.cv q))))
      (synChnwcutcode R D (synCuni (.cv q))) p0008 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutrelf`. -/
@[expose]
noncomputable def gHnwcutrelf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutrelf_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : q ∉ ((synCpw1 D)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synChwcn D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_q_not_D, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((synChnwcutrel R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have p0000 := @gHnwcutrelfn D R hyp_hnwcutrelf_1
  have p0001 := @gHnwpw1argcl D q
  have p0002 :=
    @gSimpld (.classMem (.cv q) (synCpw1 D)) (.classMem (synCuni (.cv q)) D)
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0001
  have p0003 := @gHnwcutcodecncl (synCuni (.cv q)) D R dv_cache_0001 hyp_hnwcutrelf_1
  have p0004 :=
    @gSyl (.classMem (.cv q) (synCpw1 D)) (.classMem (synCuni (.cv q)) D)
      (.classMem (synChnwcutcode R D (synCuni (.cv q))) (synChwcn D)) p0002 p0003
  have p0005 := @gHnwcutrelval D R q hyp_hnwcutrelf_1
  have p0006 :=
    @gEleq1d (.classMem (.cv q) (synCpw1 D)) (synCfv (synChnwcutrel R D) (.cv q))
      (synChnwcutcode R D (synCuni (.cv q))) (synChwcn D) p0005
  have p0007 :=
    @gMpbird (.classMem (.cv q) (synCpw1 D))
      (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D))
      (.classMem (synChnwcutcode R D (synCuni (.cv q))) (synChwcn D)) p0004 p0006
  have p0008 :=
    @gRgen (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D)) q
      (synCpw1 D) p0007
  have p0009 :=
    @gPm32i (synWfn (synChnwcutrel R D) (synCpw1 D))
      (synWral q (synCpw1 D) (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D)))
      p0000 p0008
  have p0010 :=
    @gFfnfv q (synCpw1 D) (synChwcn D) (synChnwcutrel R D) dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0011 :=
    @gMpbir (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWa (synWfn (synChnwcutrel R D) (synCpw1 D)) (synWral q (synCpw1 D)
          (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D))))
      p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_sifmap`. -/
@[expose]
noncomputable def gSifmap (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf F A B) (synWf (synCsi F) (synCpw1 A) (synCpw1 B))) :=
  by
  have p0000 := @gFfn A B F
  have p0001 := @gFnfun A F
  have p0002 := @gSyl (synWf F A B) (synWfn F A) (synWfun F) p0000 p0001
  have p0003 := @gFunsi F
  have p0004 := @gSyl (synWf F A B) (synWfun F) (synWfun (synCsi F)) p0002 p0003
  have p0005 := @gFunfn (synCsi F)
  have p0006 :=
    @gBiimpi (synWfun (synCsi F)) (synWfn (synCsi F) (synCdm (synCsi F))) p0005
  have p0007 :=
    @gSyl (synWf F A B) (synWfun (synCsi F))
      (synWfn (synCsi F) (synCdm (synCsi F))) p0004 p0006
  have p0008 := @gDmsi F
  have p0009 :=
    @gA1i (.classEq (synCdm (synCsi F)) (synCpw1 (synCdm F))) (synWf F A B) p0008
  have p0011 := @gFndm A F
  have p0012 := @gSyl (synWf F A B) (synWfn F A) (.classEq (synCdm F) A) p0000 p0011
  have p0013 := @gPw1eq (synCdm F) A
  have p0014 :=
    @gSyl (synWf F A B) (.classEq (synCdm F) A)
      (.classEq (synCpw1 (synCdm F)) (synCpw1 A)) p0012 p0013
  have p0015 :=
    @gEqtrd (synWf F A B) (synCdm (synCsi F)) (synCpw1 (synCdm F)) (synCpw1 A)
      p0009 p0014
  have p0016 :=
    @gFneq2d (synWf F A B) (synCdm (synCsi F)) (synCpw1 A) (synCsi F) p0015
  have p0017 :=
    @gMpbid (synWf F A B) (synWfn (synCsi F) (synCdm (synCsi F)))
      (synWfn (synCsi F) (synCpw1 A)) p0007 p0016
  have p0018 := @gFrn A B F
  have p0019 := @gPw1ss (synCrn F) B
  have p0020 :=
    @gSyl (synWf F A B) (synWss (synCrn F) B)
      (synWss (synCpw1 (synCrn F)) (synCpw1 B)) p0018 p0019
  have p0021 := @gRnsi F
  have p0022 :=
    @gA1i (.classEq (synCrn (synCsi F)) (synCpw1 (synCrn F))) (synWf F A B) p0021
  have p0023 :=
    @gSseq1d (synWf F A B) (synCrn (synCsi F)) (synCpw1 (synCrn F)) (synCpw1 B)
      p0022
  have p0024 :=
    @gMpbird (synWf F A B) (synWss (synCrn (synCsi F)) (synCpw1 B))
      (synWss (synCpw1 (synCrn F)) (synCpw1 B)) p0020 p0023
  have p0025 :=
    @gJca (synWf F A B) (synWfn (synCsi F) (synCpw1 A))
      (synWss (synCrn (synCsi F)) (synCpw1 B)) p0017 p0024
  have p0026 := (Nominal.biimpRefl (synWf (synCsi F) (synCpw1 A) (synCpw1 B)))
  have p0027 :=
    @gSylibr (synWf F A B)
      (synWa (synWfn (synCsi F) (synCpw1 A)) (synWss (synCrn (synCsi F)) (synCpw1 B)))
      (synWf (synCsi F) (synCpw1 A) (synCpw1 B)) p0025 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_sifvaldv`. -/
@[expose]
noncomputable def gSifvaldv (A : Class) (B : Class) (F : Class) (c : Var)
    (_dv_A_c : c ∉ A.fv) (_dv_B_c : c ∉ B.fv) (_dv_F_c : c ∉ F.fv)
    (hyp_sifvaldv_1 : Nominal.NPrf (synWf F A B)) :
    Nominal.NPrf
      (.imp (.classMem (.cv c) A) (.classEq (synCfv (synCsi F) (synCsn (.cv c)))
          (synCsn (synCfv F (.cv c))))) :=
  by
  have p0000 := @gEqid (synCfv F (.cv c))
  have p0001 :=
    @gA1i (.classEq (synCfv F (.cv c)) (synCfv F (.cv c))) (.classMem (.cv c) A) p0000
  have p0002 := @gFfn A B F
  have p0003 := Nominal.mp hyp_sifvaldv_1 p0002
  have p0004 := @gA1i (synWfn F A) (.classMem (.cv c) A) p0003
  have p0005 := @gId (.classMem (.cv c) A)
  have p0006 :=
    @gJca (.classMem (.cv c) A) (synWfn F A) (.classMem (.cv c) A) p0004 p0005
  have p0007 := @gFnbrfvb A (.cv c) (synCfv F (.cv c)) F
  have p0008 :=
    @gSyl (.classMem (.cv c) A) (synWa (synWfn F A) (.classMem (.cv c) A))
      (synWb (.classEq (synCfv F (.cv c)) (synCfv F (.cv c)))
        (synWbr (.cv c) F (synCfv F (.cv c))))
      p0006 p0007
  have p0009 :=
    @gMpbid (.classMem (.cv c) A) (.classEq (synCfv F (.cv c)) (synCfv F (.cv c)))
      (synWbr (.cv c) F (synCfv F (.cv c))) p0001 p0008
  have p0010 := @gVex c
  have p0011 := @gFvex (.cv c) F
  have p0012 := @gBrsnsi (.cv c) (synCfv F (.cv c)) F p0010 p0011
  have p0013 :=
    @gA1i
      (synWb (synWbr (synCsn (.cv c)) (synCsi F) (synCsn (synCfv F (.cv c))))
        (synWbr (.cv c) F (synCfv F (.cv c))))
      (.classMem (.cv c) A) p0012
  have p0014 :=
    @gMpbird (.classMem (.cv c) A)
      (synWbr (synCsn (.cv c)) (synCsi F) (synCsn (synCfv F (.cv c))))
      (synWbr (.cv c) F (synCfv F (.cv c))) p0009 p0013
  have p0015 := @gSifmap A B F
  have p0016 := Nominal.mp hyp_sifvaldv_1 p0015
  have p0017 := @gFfn (synCpw1 A) (synCpw1 B) (synCsi F)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gA1i (synWfn (synCsi F) (synCpw1 A)) (.classMem (.cv c) A) p0018
  have p0020 := @gSnelpw1 (.cv c) A
  have p0021 :=
    @gBiimpri (.classMem (synCsn (.cv c)) (synCpw1 A)) (.classMem (.cv c) A) p0020
  have p0022 :=
    @gJca (.classMem (.cv c) A) (synWfn (synCsi F) (synCpw1 A))
      (.classMem (synCsn (.cv c)) (synCpw1 A)) p0019 p0021
  have p0023 :=
    @gFnbrfvb (synCpw1 A) (synCsn (.cv c)) (synCsn (synCfv F (.cv c))) (synCsi F)
  have p0024 :=
    @gSyl (.classMem (.cv c) A)
      (synWa (synWfn (synCsi F) (synCpw1 A)) (.classMem (synCsn (.cv c)) (synCpw1 A)))
      (synWb (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c))))
        (synWbr (synCsn (.cv c)) (synCsi F) (synCsn (synCfv F (.cv c)))))
      p0022 p0023
  have p0025 :=
    @gMpbird (.classMem (.cv c) A)
      (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c))))
      (synWbr (synCsn (.cv c)) (synCsi F) (synCsn (synCfv F (.cv c)))) p0014 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_sifvald`. -/
@[expose]
noncomputable def gSifvald (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_sifvald_1 : Nominal.NPrf (synWf F A B)) :
    Nominal.NPrf
      (.imp (.classMem C A)
        (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have dv_cache_0001 : c ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0002 : c ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_B, not_false_eq_true])
  have dv_cache_0003 : c ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_F, not_false_eq_true])
  have dv_cache_0004 : c ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_C, not_false_eq_true])
  have dv_cache_0005 :
    c ∉
      ((Wff.imp (.classMem C A)
          (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_c_not_C, fresh_c_not_A, fresh_c_not_F, or_false, not_false_eq_true])
  have p0000 := @gElex C A
  have p0001 := @gEleq1 (.cv c) C A
  have p0002 := @gSneq (.cv c) C
  have p0003 :=
    @gFveq2d (.classEq (.cv c) C) (synCsn (.cv c)) (synCsn C) (synCsi F) p0002
  have p0004 := @gFveq2 (.cv c) C F
  have p0005 := @gSneqd (.classEq (.cv c) C) (synCfv F (.cv c)) (synCfv F C) p0004
  have p0006 :=
    @gEqeq12d (.classEq (.cv c) C) (synCfv (synCsi F) (synCsn (.cv c)))
      (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F (.cv c)))
      (synCsn (synCfv F C)) p0003 p0005
  have p0007 :=
    @gImbi12d (.classEq (.cv c) C) (.classMem (.cv c) A) (.classMem C A)
      (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c))))
      (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))) p0001 p0006
  have p0008 :=
    @gSifvaldv A B F c dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_sifvald_1
  have p0009 :=
    @gVtoclg
      (.imp (.classMem (.cv c) A)
        (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c)))))
      (.imp (.classMem C A)
        (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))))
      c C (synCvv) dv_cache_0004 dv_cache_0005 p0007 p0008
  have p0010 :=
    @gMpcom (.classMem C (synCvv)) (.classMem C A)
      (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1valcl`. -/
@[expose]
noncomputable def gHnqmap1valcl (A : Class) (B : Class)
    (hyp_hnqmap1valcl_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synChwcn A))
        (.classEq (synCfv (synChnqmap1 A) (synCsn B)) (synCec B (synChwniso A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0003 :
    u ∉
      ((Wff.imp (.classMem B (synChwcn A)) (.classEq (synCfv (synChnqmap1 A) (synCsn B))
            (synCec B (synChwniso A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, or_false, not_false_eq_true])
  have p0000 := @gElex B (synChwcn A)
  have p0001 := @gEleq1 (.cv u) B (synChwcn A)
  have p0002 := @gSneq (.cv u) B
  have p0003 :=
    @gFveq2d (.classEq (.cv u) B) (synCsn (.cv u)) (synCsn B) (synChnqmap1 A) p0002
  have p0004 := @gEceq1 (.cv u) B (synChwniso A)
  have p0005 :=
    @gEqeq12d (.classEq (.cv u) B) (synCfv (synChnqmap1 A) (synCsn (.cv u)))
      (synCfv (synChnqmap1 A) (synCsn B)) (synCec (.cv u) (synChwniso A))
      (synCec B (synChwniso A)) p0003 p0004
  have p0006 :=
    @gImbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (.cv u))) (synCec (.cv u) (synChwniso A)))
      (.classEq (synCfv (synChnqmap1 A) (synCsn B)) (synCec B (synChwniso A))) p0001
      p0005
  have p0007 := @gHnqmap1val u A dv_cache_0001 hyp_hnqmap1valcl_1
  have p0008 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classEq (synCfv (synChnqmap1 A) (synCsn (.cv u)))
          (synCec (.cv u) (synChwniso A))))
      (.imp (.classMem B (synChwcn A))
        (.classEq (synCfv (synChnqmap1 A) (synCsn B)) (synCec B (synChwniso A))))
      u B (synCvv) dv_cache_0002 dv_cache_0003 p0006 p0007
  have p0009 :=
    @gMpcom (.classMem B (synCvv)) (.classMem B (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn B)) (synCec B (synChwniso A))) p0000
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_qmapcompvald`. -/
@[expose]
noncomputable def gQmapcompvald (ph : Wff) (A : Class) (B : Class) (G : Class)
    (X : Class) (p : Var) (hyp_qmapcompvald_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_qmapcompvald_2 : Nominal.NPrf (synWf G X (synCpw1 (synChwcn A))))
    (hyp_qmapcompvald_3 : Nominal.NPrf (.imp ph (.classMem (.cv p) X)))
    (hyp_qmapcompvald_4 : Nominal.NPrf (.imp ph (.classEq (synCfv G (.cv p)) (synCsn B))))
    (hyp_qmapcompvald_5 : Nominal.NPrf (.imp ph (.classMem B (synChwcn A)))) :
    Nominal.NPrf
      (.imp ph (.classEq (synCfv (synCcom (synChnqmap1 A) G) (.cv p))
          (synCec B (synChwniso A)))) :=
  by
  have p0000 := @gFfn X (synCpw1 (synChwcn A)) G
  have p0001 := Nominal.mp hyp_qmapcompvald_2 p0000
  have p0002 := @gA1i (synWfn G X) ph p0001
  have p0003 := @gJca ph (synWfn G X) (.classMem (.cv p) X) p0002 hyp_qmapcompvald_3
  have p0004 := @gFvco2 X (.cv p) (synChnqmap1 A) G
  have p0005 :=
    @gSyl ph (synWa (synWfn G X) (.classMem (.cv p) X))
      (.classEq (synCfv (synCcom (synChnqmap1 A) G) (.cv p))
        (synCfv (synChnqmap1 A) (synCfv G (.cv p))))
      p0003 p0004
  have p0006 :=
    @gFveq2d ph (synCfv G (.cv p)) (synCsn B) (synChnqmap1 A) hyp_qmapcompvald_4
  have p0007 :=
    @gEqtrd ph (synCfv (synCcom (synChnqmap1 A) G) (.cv p))
      (synCfv (synChnqmap1 A) (synCfv G (.cv p)))
      (synCfv (synChnqmap1 A) (synCsn B)) p0005 p0006
  have p0008 := @gHnqmap1valcl A B hyp_qmapcompvald_1
  have p0009 :=
    @gSyl ph (.classMem B (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn B)) (synCec B (synChwniso A)))
      hyp_qmapcompvald_5 p0008
  have p0010 :=
    @gEqtrd ph (synCfv (synCcom (synChnqmap1 A) G) (.cv p))
      (synCfv (synChnqmap1 A) (synCsn B)) (synCec B (synChwniso A)) p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnwcutsirelf`. -/
@[expose]
noncomputable def gHnwcutsirelf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutsirelf_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (synWf (synCsi (synChnwcutrel R D)) (synCpw1 (synCpw1 D))
        (synCpw1 (synChwcn D))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gHnwcutrelf D R dv_cache_0001 hyp_hnwcutsirelf_1
  have p0001 := @gSifmap (synCpw1 D) (synChwcn D) (synChnwcutrel R D)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hnwcutsirelex`. -/
@[expose]
noncomputable def gHnwcutsirelex (D : Class) (R : Class)
    (hyp_hnwcutsirelex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synCsi (synChnwcutrel R D)) (synCvv)) :=
  by
  have p0000 := @gHnwcutrelex D R hyp_hnwcutsirelex_1
  have p0001 := @gSiex (synChnwcutrel R D) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_hnwcutfactorf`. -/
@[expose]
noncomputable def gHnwcutfactorf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutfactorf_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (synWf (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D)))
        (synCpw1 (synCpw1 D)) (synChnord D)) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gBrex R D (synCwe)
  have p0001 := Nominal.mp hyp_hnwcutfactorf_1 p0000
  have p0002 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0001
  have p0003 := @gHnqmap1f D p0002
  have p0004 := @gHnwcutsirelf D R dv_cache_0001 hyp_hnwcutfactorf_1
  have p0005 :=
    @gPm32i (synWf (synChnqmap1 D) (synCpw1 (synChwcn D)) (synChnord D))
      (synWf (synCsi (synChnwcutrel R D)) (synCpw1 (synCpw1 D)) (synCpw1 (synChwcn D)))
      p0003 p0004
  have p0006 :=
    @gFco (synCpw1 (synCpw1 D)) (synCpw1 (synChwcn D)) (synChnord D)
      (synChnqmap1 D) (synCsi (synChnwcutrel R D))
  have p0007 := Nominal.mp p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnwcutrelvalcld`. -/
@[expose]
noncomputable def gHnwcutrelvalcld (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutrelvalcld_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D)
        (.classEq (synCfv (synChnwcutrel R D) (synCsn B)) (synChnwcutcode R D B))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((synCuni (.cv x))).fv (R).fv := by
    exact
      (show Disjoint ((synCuni (.cv x))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((Class.cv x)).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ x } : Finset Var)) ((R).fv) from
                    (Finset.disjoint_singleton_left.mpr
                      (show x ∉ (R).fv from (by exact fresh_x_not_R))))))))
  have dv_cache_0002 : x ∉ ((synCsn B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_B,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_D,
          not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.classEq (synCfv (synChnwcutrel R D) (synCsn B)) (synChnwcutcode R D B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          Finset.mem_union, fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem B D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, or_false, not_false_eq_true])
  have p0000 := @gHnwcutrelval D R x hyp_hnwcutrelvalcld_1
  have p0001 :=
    @gRgen
      (.classEq (synCfv (synChnwcutrel R D) (.cv x)) (synChnwcutcode R D (synCuni (.cv x))))
      x (synCpw1 D) p0000
  have p0002 := @gSnelpw1 B D
  have p0003 := @gBiimpri (.classMem (synCsn B) (synCpw1 D)) (.classMem B D) p0002
  have p0004 := @gSimpr (.classMem B D) (.classEq (.cv x) (synCsn B))
  have p0005 :=
    @gFveq2d (synWa (.classMem B D) (.classEq (.cv x) (synCsn B))) (.cv x) (synCsn B)
      (synChnwcutrel R D) p0004
  have p0007 :=
    @gUnieqd (synWa (.classMem B D) (.classEq (.cv x) (synCsn B))) (.cv x) (synCsn B)
      p0004
  have p0008 := @gSimpl (.classMem B D) (.classEq (.cv x) (synCsn B))
  have p0009 := @gUnisng B D
  have p0010 :=
    @gSyl (synWa (.classMem B D) (.classEq (.cv x) (synCsn B))) (.classMem B D)
      (.classEq (synCuni (synCsn B)) B) p0008 p0009
  have p0011 :=
    @gEqtrd (synWa (.classMem B D) (.classEq (.cv x) (synCsn B))) (synCuni (.cv x))
      (synCuni (synCsn B)) B p0007 p0010
  have p0012 := @gHnwcutcodeeq3 (synCuni (.cv x)) B D R dv_cache_0001
  have p0013 :=
    @gSyl (synWa (.classMem B D) (.classEq (.cv x) (synCsn B)))
      (.classEq (synCuni (.cv x)) B)
      (.classEq (synChnwcutcode R D (synCuni (.cv x))) (synChnwcutcode R D B)) p0011
      p0012
  have p0014 :=
    @gEqeq12d (synWa (.classMem B D) (.classEq (.cv x) (synCsn B)))
      (synCfv (synChnwcutrel R D) (.cv x)) (synCfv (synChnwcutrel R D) (synCsn B))
      (synChnwcutcode R D (synCuni (.cv x))) (synChnwcutcode R D B) p0005 p0013
  have p0015 :=
    @gRspcdv (.classMem B D)
      (.classEq (synCfv (synChnwcutrel R D) (.cv x)) (synChnwcutcode R D (synCuni (.cv x))))
      (.classEq (synCfv (synChnwcutrel R D) (synCsn B)) (synChnwcutcode R D B)) x
      (synCsn B) (synCpw1 D) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0003 p0014
  have p0016 :=
    @gMpi (.classMem B D)
      (synWral x (synCpw1 D) (.classEq (synCfv (synChnwcutrel R D) (.cv x))
          (synChnwcutcode R D (synCuni (.cv x)))))
      (.classEq (synCfv (synChnwcutrel R D) (synCsn B)) (synChnwcutcode R D B)) p0001
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_hnwcutsirelval`. -/
@[expose]
noncomputable def gHnwcutsirelval (D : Class) (R : Class) (q : Var)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutsirelval_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classEq (synCfv (synCsi (synChnwcutrel R D)) (.cv q))
          (synCsn (synChnwcutcode R D (synCuni (synCuni (.cv q))))))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gPw12argcl (.cv q) D
  have p0001 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0000
  have p0002 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.cv q)
      (synCsn (synCsn (synCuni (synCuni (.cv q))))) (synCsi (synChnwcutrel R D))
      p0001
  have p0004 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0000
  have p0005 := @gSnelpw1 (synCuni (synCuni (.cv q))) D
  have p0006 :=
    @gBiimpri (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D))
      (.classMem (synCuni (synCuni (.cv q))) D) p0005
  have p0007 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D)) p0004 p0006
  have p0008 := @gHnwcutrelf D R dv_cache_0001 hyp_hnwcutsirelval_1
  have p0009 :=
    @gSifvald (synCpw1 D) (synChwcn D) (synCsn (synCuni (synCuni (.cv q))))
      (synChnwcutrel R D) p0008
  have p0010 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D))
      (.classEq (synCfv (synCsi (synChnwcutrel R D))
          (synCsn (synCsn (synCuni (synCuni (.cv q))))))
        (synCsn (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))))
      p0007 p0009
  have p0011 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCsi (synChnwcutrel R D)) (.cv q))
      (synCfv (synCsi (synChnwcutrel R D)) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
      (synCsn (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q))))))
      p0002 p0010
  have p0014 := @gHnwcutrelvalcld (synCuni (synCuni (.cv q))) D R hyp_hnwcutsirelval_1
  have p0015 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))
        (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
      p0004 p0014
  have p0016 :=
    @gSneqd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))
      (synChnwcutcode R D (synCuni (synCuni (.cv q)))) p0015
  have p0017 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCsi (synChnwcutrel R D)) (.cv q))
      (synCsn (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q))))))
      (synCsn (synChnwcutcode R D (synCuni (synCuni (.cv q))))) p0011 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_hnwcutfactorval`. -/
@[expose]
noncomputable def gHnwcutfactorval (D : Class) (R : Class) (q : Var)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutfactorval_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq
          (synCfv (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gBrex R D (synCwe)
  have p0001 := Nominal.mp hyp_hnwcutfactorval_1 p0000
  have p0002 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0001
  have p0003 := @gHnwcutsirelf D R dv_cache_0001 hyp_hnwcutfactorval_1
  have p0004 := @gId (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0005 := @gHnwcutsirelval D R q dv_cache_0001 hyp_hnwcutfactorval_1
  have p0006 := @gPw12argcl (.cv q) D
  have p0007 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0006
  have p0008 :=
    @gHnwcutcodecncl (synCuni (synCuni (.cv q))) D R dv_cache_0001
      hyp_hnwcutfactorval_1
  have p0009 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwcn D)) p0007
      p0008
  have p0010 :=
    @gQmapcompvald (.classMem (.cv q) (synCpw1 (synCpw1 D))) D
      (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synCsi (synChnwcutrel R D))
      (synCpw1 (synCpw1 D)) q p0002 p0003 p0004 p0005 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnwcutmapfactor`. -/
@[expose]
noncomputable def gHnwcutmapfactor (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapfactor_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.classEq (synChnwcutmap R D)
        (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D)))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synChnwcutmap R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 :
    q ∉ ((synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have p0000 := @gHnwcutmapval D R q dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0001 := @gHnwcutfactorval D R q dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0002 :=
    @gEqcomd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))) (.cv q))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)) p0001
  have p0003 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synChnwcutmap R D) (.cv q))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
      (synCfv (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))) (.cv q)) p0000
      p0002
  have p0004 :=
    @gRgen
      (.classEq (synCfv (synChnwcutmap R D) (.cv q))
        (synCfv (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))) (.cv q)))
      q (synCpw1 (synCpw1 D)) p0003
  have p0005 := @gHnwcutmapf D R dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0006 := @gFfn (synCpw1 (synCpw1 D)) (synChnord D) (synChnwcutmap R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gHnwcutfactorf D R dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0009 :=
    @gFfn (synCpw1 (synCpw1 D)) (synChnord D)
      (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gPm32i (synWfn (synChnwcutmap R D) (synCpw1 (synCpw1 D)))
      (synWfn (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D)))
        (synCpw1 (synCpw1 D)))
      p0007 p0010
  have p0012 :=
    @gEqfnfv q (synCpw1 (synCpw1 D)) (synChnwcutmap R D)
      (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))) dv_cache_0002
      dv_cache_0003 dv_cache_0004
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gMpbir
      (.classEq (synChnwcutmap R D) (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))))
      (synWral q (synCpw1 (synCpw1 D)) (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))) (.cv q))))
      p0004 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_hnwcutmapex`. -/
@[expose]
noncomputable def gHnwcutmapex (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapex_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (.classMem (synChnwcutmap R D) (synCvv)) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gHnwcutmapfactor D R dv_cache_0001 hyp_hnwcutmapex_1
  have p0001 := @gBrex R D (synCwe)
  have p0002 := Nominal.mp hyp_hnwcutmapex_1 p0001
  have p0003 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0002
  have p0004 := @gHnqmap1exg D
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gHnwcutsirelex D R hyp_hnwcutmapex_1
  have p0007 := @gCoex (synChnqmap1 D) (synCsi (synChnwcutrel R D)) p0005 p0006
  have p0008 :=
    @gEqeltri (synChnwcutmap R D)
      (synCcom (synChnqmap1 D) (synCsi (synChnwcutrel R D))) (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hnwcutmapcardle`. -/
@[expose]
noncomputable def gHnwcutmapcardle (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapcardle_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWbr (synCnc (synCpw1 (synCpw1 D))) (synClec) (synChncard D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : f ∉ ((synChnwcutmap R D)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_R, or_false, not_false_eq_true])
  have dv_cache_0003 :
    f ∉ ((synWf1 (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          fresh_f_not_D, fresh_f_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((synCpw1 (synCpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_f_not_D,
          not_false_eq_true])
  have dv_cache_0005 : f ∉ ((synChnord D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_f_not_D, not_false_eq_true])
  have p0000 := @gHnwcutmapf1 D R dv_cache_0001 hyp_hnwcutmapcardle_1
  have p0001 := @gHnwcutmapex D R dv_cache_0001 hyp_hnwcutmapcardle_1
  have p0002 :=
    @gF1eq1 (synCpw1 (synCpw1 D)) (synChnord D) (.cv f) (synChnwcutmap R D)
  have p0003 :=
    @gSpcegv (synWf1 (.cv f) (synCpw1 (synCpw1 D)) (synChnord D))
      (synWf1 (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D)) f
      (synChnwcutmap R D) (synCvv) dv_cache_0002 dv_cache_0003 p0002
  have p0004 := Nominal.mp p0001 p0003
  have p0005 := Nominal.mp p0000 p0004
  have p0006 := @gBrex R D (synCwe)
  have p0007 := Nominal.mp hyp_hnwcutmapcardle_1 p0006
  have p0008 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0007
  have p0009 := @gPw1ex D p0008
  have p0010 := @gPw1ex (synCpw1 D) p0009
  have p0014 := @gHnordex D p0008
  have p0015 :=
    @gNclenc (synCpw1 (synCpw1 D)) (synChnord D) f dv_cache_0004 dv_cache_0005 p0010
      p0014
  have p0016 :=
    @gMpbir
      (synWbr (synCnc (synCpw1 (synCpw1 D))) (synClec) (synCnc (synChnord D)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCpw1 D)) (synChnord D))) p0005 p0015
  have p0017 := (Nominal.classEqRefl (synChncard D))
  have p0018 := @gEqcomi (synChncard D) (synCnc (synChnord D)) p0017
  have p0019 :=
    @gBreq2i (synCnc (synChnord D)) (synChncard D) (synCnc (synCpw1 (synCpw1 D)))
      (synClec) p0018
  have p0020 :=
    @gMpbi
      (synWbr (synCnc (synCpw1 (synCpw1 D))) (synClec) (synCnc (synChnord D)))
      (synWbr (synCnc (synCpw1 (synCpw1 D))) (synClec) (synChncard D)) p0016 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_hnwcutmaptc2le`. -/
@[expose]
noncomputable def gHnwcutmaptc2le (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmaptc2le_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWbr (synCtc (synCtc (synCnc D))) (synClec) (synChncard D)) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gHnwcutmapcardle D R dv_cache_0001 hyp_hnwcutmaptc2le_1
  have p0001 := @gBrex R D (synCwe)
  have p0002 := Nominal.mp hyp_hnwcutmaptc2le_1 p0001
  have p0003 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0002
  have p0004 := @gTc2nc D p0003
  have p0005 :=
    @gBreq1i (synCtc (synCtc (synCnc D))) (synCnc (synCpw1 (synCpw1 D)))
      (synChncard D) (synClec) p0004
  have p0006 :=
    @gMpbir (synWbr (synCtc (synCtc (synCnc D))) (synClec) (synChncard D))
      (synWbr (synCnc (synCpw1 (synCpw1 D))) (synClec) (synChncard D)) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_hwcnssbase`. -/
@[expose]
noncomputable def gHwcnssbase (A : Class) (D : Class)
    (hyp_hwcnssbase_1 : Nominal.NPrf (synWss D A)) :
    Nominal.NPrf (synWss (synChwcn D) (synChwcn A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv ((synCfv (synC1st) (.cv u))).fv := by
    exact
      (show Disjoint (D).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((D).fv) ((((Class.cv u)).fv) ∪ (((synC1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((D).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((D).fv) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show u ∉ (D).fv from (by exact fresh_u_not_D)))))),
                  (show Disjoint ((D).fv) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((D).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0002 : Disjoint (A).fv ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((synC1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show u ∉ (A).fv from (by exact fresh_u_not_A)))))),
                  (show Disjoint ((A).fv) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0003 : u ∉ ((synChwcn D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_D, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have p0000 := @gHwcnraw u D
  have p0001 := @gHwcnpair u D
  have p0002 :=
    @gEleq1d (.classMem (.cv u) (synChwcn D)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (synChwcodes D)
      p0001
  have p0003 :=
    @gMpbid (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcodes D))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes D))
      p0000 p0002
  have p0004 := @gFvex (.cv u) (synC1st)
  have p0005 := @gFvex (.cv u) (synC2nd)
  have p0006 :=
    @gElhwcodes D (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) dv_cache_0001
      p0004 p0005
  have p0007 :=
    @gBiimpi
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      p0006
  have p0008 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      p0003 p0007
  have p0009 :=
    @gSimpld (.classMem (.cv u) (synChwcn D))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) D) p0008
  have p0019 :=
    @gSimprd (.classMem (.cv u) (synChwcn D))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) D) p0008
  have p0020 := @gA1i (synWss D A) (.classMem (.cv u) (synChwcn D)) hyp_hwcnssbase_1
  have p0021 :=
    @gSstrd (.classMem (.cv u) (synChwcn D)) (synCfv (synC2nd) (.cv u)) D A p0019
      p0020
  have p0022 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) A) p0009 p0021
  have p0025 :=
    @gElhwcodes A (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) dv_cache_0002
      p0004 p0005
  have p0026 :=
    @gBiimpri
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) A))
      p0025
  have p0027 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) A))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      p0022 p0026
  have p0029 :=
    @gEleq1d (.classMem (.cv u) (synChwcn D)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (synChwcodes A)
      p0001
  have p0030 :=
    @gMpbird (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcodes A))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      p0027 p0029
  have p0031 := @gHwcnsupp u D
  have p0032 :=
    @gJca (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcodes A))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0030 p0031
  have p0033 := @gElhwcn u A
  have p0034 :=
    @gBiimpri (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0033
  have p0035 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) p0032 p0034
  have p0036 := @gSsriv u (synChwcn D) (synChwcn A) dv_cache_0003 dv_cache_0004 p0035
  exact p0036


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwnisobaserestr`. -/
@[expose]
noncomputable def gHwnisobaserestr (v : Var) (u : Var) (A : Class) (D : Class)
    (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (.imp (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWbr (.cv u) (synChwniso D) (.cv v)))) :=
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
  have dv_cache_0002 : h ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0003 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0004 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0005 : h ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_D, not_false_eq_true])
  have p0000 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0002 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)) p0000
  have p0003 := @gHwcnraw u D
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcodes D)) p0002 p0003
  have p0006 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)) p0000
  have p0007 := @gHwcnraw v D
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv v) (synChwcn D)) (.classMem (.cv v) (synChwcodes D)) p0006 p0007
  have p0009 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcodes D)) (.classMem (.cv v) (synChwcodes D)) p0004
      p0008
  have p0010 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0011 := @gHwnisohwisob v u A dv_cache_0001
  have p0012 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0011
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0010 p0012
  have p0014 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0013
  have p0015 := @gBrhwisoany v u A h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0016 :=
    @gBiimpi (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0014 p0016
  have p0018 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0017
  have p0019 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcodes D)) (.classMem (.cv v) (synChwcodes D)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0009 p0018
  have p0020 := @gBrhwisoany v u D h dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0021 :=
    @gBiimpri (synWbr (.cv u) (synChwiso D) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes D)) (.classMem (.cv v) (synChwcodes D)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0020
  have p0022 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (synWa (.classMem (.cv u) (synChwcodes D)) (.classMem (.cv v) (synChwcodes D)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWbr (.cv u) (synChwiso D) (.cv v)) p0019 p0021
  have p0023 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWbr (.cv u) (synChwiso D) (.cv v)) p0000 p0022
  have p0024 := @gHwnisohwisob v u D dv_cache_0001
  have p0025 :=
    @gBiimpri (synWbr (.cv u) (synChwniso D) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwiso D) (.cv v)))
      p0024
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
        (synWbr (.cv u) (synChwiso D) (.cv v)))
      (synWbr (.cv u) (synChwniso D) (.cv v)) p0023 p0025
  have p0027 :=
    @gEx (synWa (.classMem (.cv u) (synChwcn D)) (.classMem (.cv v) (synChwcn D)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) (synWbr (.cv u) (synChwniso D) (.cv v))
      p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_hwnisobaserestrcl`. -/
@[expose]
noncomputable def gHwnisobaserestrcl (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
        (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C))) :=
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
          (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C)))).fv :=
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
          (.imp (synWbr B (synChwniso A) (.cv y)) (synWbr B (synChwniso D) (.cv y))))).fv :=
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
  have p0011 := @gBreq1 (.cv x) B (.cv y) (synChwniso A)
  have p0012 := @gBreq1 (.cv x) B (.cv y) (synChwniso D)
  have p0013 :=
    @gImbi12d (.classEq (.cv x) B) (synWbr (.cv x) (synChwniso A) (.cv y))
      (synWbr B (synChwniso A) (.cv y)) (synWbr (.cv x) (synChwniso D) (.cv y))
      (synWbr B (synChwniso D) (.cv y)) p0011 p0012
  have p0014 :=
    @gImbi12d (.classEq (.cv x) B)
      (synWa (.classMem (.cv x) (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
      (synWa (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
      (.imp (synWbr (.cv x) (synChwniso A) (.cv y)) (synWbr (.cv x) (synChwniso D) (.cv y)))
      (.imp (synWbr B (synChwniso A) (.cv y)) (synWbr B (synChwniso D) (.cv y))) p0010
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
  have p0019 := @gBreq2 (.cv y) C B (synChwniso A)
  have p0020 := @gBreq2 (.cv y) C B (synChwniso D)
  have p0021 :=
    @gImbi12d (.classEq (.cv y) C) (synWbr B (synChwniso A) (.cv y))
      (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) (.cv y))
      (synWbr B (synChwniso D) C) p0019 p0020
  have p0022 :=
    @gImbi12d (.classEq (.cv y) C)
      (synWa (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
      (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (.imp (synWbr B (synChwniso A) (.cv y)) (synWbr B (synChwniso D) (.cv y)))
      (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C)) p0018 p0021
  have p0023 := @gHwnisobaserestr y x A D dv_cache_0001
  have p0024 :=
    @gVtocl2g
      (.imp (synWa (.classMem (.cv x) (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
        (.imp (synWbr (.cv x) (synChwniso A) (.cv y))
          (synWbr (.cv x) (synChwniso D) (.cv y))))
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem (.cv y) (synChwcn D)))
        (.imp (synWbr B (synChwniso A) (.cv y)) (synWbr B (synChwniso D) (.cv y))))
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
        (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C)))
      x y B C (synCvv) (synCvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0014 p0022 p0023
  have p0025 :=
    @gSyl (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.imp (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
        (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C)))
      p0006 p0024
  have p0026 :=
    @gPm243i (synWa (.classMem B (synChwcn D)) (.classMem C (synChwcn D)))
      (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwniso D) C)) p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_brlnqrelg`. -/
@[expose]
noncomputable def gBrlnqrelg (x : Var) (y : Var) (C : Class) (D : Class) (R : Class)
    (V : Class) (W : Class) (dv_C_x : x ∉ C.fv) (_dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (.classMem C V) (.classMem D W)) (synWb (synWbr C (synClnqrel R) D)
          (synWrex x C (synWrex y D (synWbr (.cv x) R (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let b : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_a : b ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv b) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_b, dv_D_x, or_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0007 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
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
  have dv_cache_0010 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0013 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0014 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0016 : a ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_C, not_false_eq_true])
  have dv_cache_0017 : b ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_C, not_false_eq_true])
  have dv_cache_0018 : a ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_D, not_false_eq_true])
  have dv_cache_0019 : b ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_D, not_false_eq_true])
  have dv_cache_0020 :
    a ∉ ((synWrex x C (synWrex y D (synWbr (.cv x) R (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_C, fresh_a_not_D, fresh_a_ne_x, fresh_a_ne_y,
          fresh_a_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0021 :
    b ∉ ((synWrex x C (synWrex y D (synWbr (.cv x) R (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_not_C, fresh_b_not_D, fresh_b_ne_x, fresh_b_ne_y,
          fresh_b_not_R, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gRexeq (synWrex y (.cv b) (synWbr (.cv x) R (.cv y))) x (.cv a) C dv_cache_0001
      dv_cache_0002
  have p0001 :=
    @gRexeq (synWbr (.cv x) R (.cv y)) y (.cv b) D dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gRexbidv (.classEq (.cv b) D) (synWrex y (.cv b) (synWbr (.cv x) R (.cv y)))
      (synWrex y D (synWbr (.cv x) R (.cv y))) x C dv_cache_0005 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLnqrel x y R a b
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0004 :=
    @gBrabg (synWrex x (.cv a) (synWrex y (.cv b) (synWbr (.cv x) R (.cv y))))
      (synWrex x C (synWrex y (.cv b) (synWbr (.cv x) R (.cv y))))
      (synWrex x C (synWrex y D (synWbr (.cv x) R (.cv y)))) a b C D V W
      (synClnqrel R) dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0010 p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ellnkerec`. -/
@[expose]
noncomputable def gEllnkerec (u : Var) (R : Class) (X : Class) :
    Nominal.NPrf
      (synWb (.classMem (.cv u) (synCec X (synClnker R)))
        (synWa (synWbr X R (.cv u)) (synWbr (.cv u) R X))) :=
  by
  have p0000 := @gElec (.cv u) X (synClnker R)
  have p0001 := @gBrlnker R X (.cv u)
  have p0002 :=
    @gBitri (.classMem (.cv u) (synCec X (synClnker R)))
      (synWbr X (synClnker R) (.cv u))
      (synWa (synWbr X R (.cv u)) (synWbr (.cv u) R X)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ellnkerecg`. -/
@[expose]
noncomputable def gEllnkerecg (B : Class) (C : Class) (R : Class) :
    Nominal.NPrf
      (synWb (.classMem B (synCec C (synClnker R)))
        (synWa (synWbr C R B) (synWbr B R C))) :=
  by
  have p0000 := @gElec B C (synClnker R)
  have p0001 := @gBrlnker R C B
  have p0002 :=
    @gBitri (.classMem B (synCec C (synClnker R))) (synWbr C (synClnker R) B)
      (synWa (synWbr C R B) (synWbr B R C)) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_lnqrelreps`. -/
@[expose]
noncomputable def gLnqrelreps (v : Var) (u : Var) (C : Class) (R : Class) (X : Class)
    (Y : Class) (dv_C_u : u ∉ C.fv) (dv_C_v : v ∉ C.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_v : v ∉ R.fv) (dv_X_u : u ∉ X.fv) (dv_X_v : v ∉ X.fv) (dv_Y_u : u ∉ Y.fv)
    (dv_Y_v : v ∉ Y.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))) (synWb
          (synWrex u (synCec X (synClnker R))
            (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v))))
          (synWbr X R Y))) :=
  by
  have dv_cache_0001 : v ∉ ((synCec X (synClnker R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          dv_X_v, dv_R_v, or_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synWbr X R Y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          dv_X_u, dv_Y_u, dv_R_u, or_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((synWbr X R Y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          dv_X_v, dv_Y_v, dv_R_v, or_false, not_false_eq_true])
  have dv_cache_0004 :
    u ∉
      ((synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_R_u, dv_C_u,
          dv_X_u, dv_Y_u, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    v ∉
      ((synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_R_v, dv_C_v,
          dv_X_v, dv_Y_v, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0007 : v ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_Y_v, not_false_eq_true])
  have dv_cache_0008 : v ∉ ((synCec Y (synClnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          dv_Y_v, dv_R_v, or_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((Wff.classEq (.cv u) X)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_v), dv_X_v, or_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_u, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((synCec X (synClnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          dv_X_u, dv_R_u, or_false, not_false_eq_true])
  have dv_cache_0012 :
    u ∉ ((synWrex v (synCec Y (synClnker R)) (synWbr X R (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_Y_u, dv_R_u, dv_X_u, dv_u_v, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv u) R (.cv v))
  have p0001 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem (.cv u) (synCec X (synClnker R)))
        (.classMem (.cv v) (synCec Y (synClnker R))))
  have p0002 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem X C) (.classMem Y C))
  have p0003 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0002
  have p0004 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr R (synCref) C) (synWbr R (synCtrans) C) p0003
  have p0005 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr R (synCtrans) C) p0001 p0004
  have p0006 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr R (synCtrans) C) p0000 p0005
  have p0009 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem X C) (.classMem Y C))
  have p0010 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (.classMem X C) (.classMem Y C) p0009
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (.classMem X C) p0001 p0010
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem X C) p0000 p0011
  have p0014 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem (.cv u) (synCec X (synClnker R)))
        (.classMem (.cv v) (synCec Y (synClnker R))))
  have p0015 :=
    @gSimprd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv u) (synCec X (synClnker R)))
      (.classMem (.cv v) (synCec Y (synClnker R))) p0014
  have p0016 := @gEllnkerec v R Y
  have p0017 :=
    @gBiimpi (.classMem (.cv v) (synCec Y (synClnker R)))
      (synWa (synWbr Y R (.cv v)) (synWbr (.cv v) R Y)) p0016
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv v) (synCec Y (synClnker R)))
      (synWa (synWbr Y R (.cv v)) (synWbr (.cv v) R Y)) p0015 p0017
  have p0019 :=
    @gSimprd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr Y R (.cv v)) (synWbr (.cv v) R Y) p0018
  have p0022 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0002
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWss R (synCxp C C)) p0001 p0022
  have p0024 :=
    @gSsbrd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      R (synCxp C C) (.cv v) Y p0023
  have p0025 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv v) R Y) (synWbr (.cv v) (synCxp C C) Y) p0019 p0024
  have p0026 := @gBrxp (.cv v) Y C C
  have p0027 :=
    @gBiimpi (synWbr (.cv v) (synCxp C C) Y)
      (synWa (.classMem (.cv v) C) (.classMem Y C)) p0026
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv v) (synCxp C C) Y) (synWa (.classMem (.cv v) C) (.classMem Y C))
      p0025 p0027
  have p0029 :=
    @gSimpld
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv v) C) (.classMem Y C) p0028
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv v) C) p0000 p0029
  have p0034 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (.classMem X C) (.classMem Y C) p0009
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (.classMem Y C) p0001 p0034
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem Y C) p0000 p0035
  have p0052 :=
    @gSimpld
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv u) (synCec X (synClnker R)))
      (.classMem (.cv v) (synCec Y (synClnker R))) p0014
  have p0053 := @gEllnkerec u R X
  have p0054 :=
    @gBiimpi (.classMem (.cv u) (synCec X (synClnker R)))
      (synWa (synWbr X R (.cv u)) (synWbr (.cv u) R X)) p0053
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv u) (synCec X (synClnker R)))
      (synWa (synWbr X R (.cv u)) (synWbr (.cv u) R X)) p0052 p0054
  have p0056 :=
    @gSimpld
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X R (.cv u)) (synWbr (.cv u) R X) p0055
  have p0061 :=
    @gSsbrd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      R (synCxp C C) X (.cv u) p0023
  have p0062 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X R (.cv u)) (synWbr X (synCxp C C) (.cv u)) p0056 p0061
  have p0063 := @gBrxp X (.cv u) C C
  have p0064 :=
    @gBiimpi (synWbr X (synCxp C C) (.cv u))
      (synWa (.classMem X C) (.classMem (.cv u) C)) p0063
  have p0065 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X (synCxp C C) (.cv u)) (synWa (.classMem X C) (.classMem (.cv u) C))
      p0062 p0064
  have p0066 :=
    @gSimprd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem X C) (.classMem (.cv u) C) p0065
  have p0067 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv u) C) p0000 p0066
  have p0093 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X R (.cv u)) p0000 p0056
  have p0094 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv u) R (.cv v))
  have p0095 :=
    @gTrd
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      C R X (.cv u) (.cv v) p0006 p0012 p0067 p0030 p0093 p0094
  have p0103 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv v) R Y) p0000 p0019
  have p0104 :=
    @gTrd
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr (.cv u) R (.cv v)))
      C R X (.cv v) Y p0006 p0012 p0030 p0036 p0095 p0103
  have p0105 :=
    @gEx
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv u) R (.cv v)) (synWbr X R Y) p0104
  have p0106 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X R Y)
  have p0112 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr R (synCtrans) C) p0106 p0005
  have p0130 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv u) C) p0106 p0066
  have p0136 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem Y C) p0106 p0035
  have p0154 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem (.cv v) C) p0106 p0029
  have p0185 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (.classMem X C) p0106 p0011
  have p0198 :=
    @gSimprd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X R (.cv u)) (synWbr (.cv u) R X) p0055
  have p0199 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv u) R X) p0106 p0198
  have p0200 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X R Y)
  have p0201 :=
    @gTrd
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      C R (.cv u) X Y p0112 p0130 p0185 p0136 p0199 p0200
  have p0208 :=
    @gSimpld
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr Y R (.cv v)) (synWbr (.cv v) R Y) p0018
  have p0209 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr Y R (.cv v)) p0106 p0208
  have p0210 :=
    @gTrd
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
          (synWa (.classMem (.cv u) (synCec X (synClnker R)))
            (.classMem (.cv v) (synCec Y (synClnker R))))) (synWbr X R Y))
      C R (.cv u) Y (.cv v) p0112 p0130 p0136 p0154 p0201 p0209
  have p0211 :=
    @gEx
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr X R Y) (synWbr (.cv u) R (.cv v)) p0210
  have p0212 :=
    @gImpbid
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv u) R (.cv v)) (synWbr X R Y) p0105 p0211
  have p0213 :=
    @gBiimpd
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWa (.classMem (.cv u) (synCec X (synClnker R)))
          (.classMem (.cv v) (synCec Y (synClnker R)))))
      (synWbr (.cv u) R (.cv v)) (synWbr X R Y) p0212
  have p0214 :=
    @gRexlimdvva
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr (.cv u) R (.cv v)) (synWbr X R Y) u v (synCec X (synClnker R))
      (synCec Y (synClnker R)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0213
  have p0215 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr X R Y)
  have p0218 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr R (synCref) C) (synWbr R (synCtrans) C) p0003
  have p0221 :=
    @gRefd
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      C R X p0218 p0010
  have p0228 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr X R X) (synWbr X R X) p0221 p0221
  have p0229 := @gElec X X (synClnker R)
  have p0230 := @gBrlnker R X X
  have p0231 :=
    @gBitri (.classMem X (synCec X (synClnker R))) (synWbr X (synClnker R) X)
      (synWa (synWbr X R X) (synWbr X R X)) p0229 p0230
  have p0232 :=
    @gBiimpri (.classMem X (synCec X (synClnker R)))
      (synWa (synWbr X R X) (synWbr X R X)) p0231
  have p0233 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr X R X) (synWbr X R X)) (.classMem X (synCec X (synClnker R)))
      p0228 p0232
  have p0234 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWbr X R Y))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (.classMem X (synCec X (synClnker R))) p0215 p0233
  have p0241 :=
    @gRefd
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      C R Y p0218 p0034
  have p0248 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr Y R Y) (synWbr Y R Y) p0241 p0241
  have p0249 := @gElec Y Y (synClnker R)
  have p0250 := @gBrlnker R Y Y
  have p0251 :=
    @gBitri (.classMem Y (synCec Y (synClnker R))) (synWbr Y (synClnker R) Y)
      (synWa (synWbr Y R Y) (synWbr Y R Y)) p0249 p0250
  have p0252 :=
    @gBiimpri (.classMem Y (synCec Y (synClnker R)))
      (synWa (synWbr Y R Y) (synWbr Y R Y)) p0251
  have p0253 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr Y R Y) (synWbr Y R Y)) (.classMem Y (synCec Y (synClnker R)))
      p0248 p0252
  have p0254 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWbr X R Y))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (.classMem Y (synCec Y (synClnker R))) p0215 p0253
  have p0255 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr X R Y)
  have p0256 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWbr X R Y))
      (.classMem Y (synCec Y (synClnker R))) (synWbr X R Y) p0254 p0255
  have p0257 := @gBreq2 (.cv v) Y X R
  have p0258 :=
    @gRspcev (synWbr X R (.cv v)) (synWbr X R Y) v Y (synCec Y (synClnker R))
      dv_cache_0007 dv_cache_0008 dv_cache_0003 p0257
  have p0259 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWbr X R Y))
      (synWa (.classMem Y (synCec Y (synClnker R))) (synWbr X R Y))
      (synWrex v (synCec Y (synClnker R)) (synWbr X R (.cv v))) p0256 p0258
  have p0260 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWbr X R Y))
      (.classMem X (synCec X (synClnker R)))
      (synWrex v (synCec Y (synClnker R)) (synWbr X R (.cv v))) p0234 p0259
  have p0261 := @gBreq1 (.cv u) X (.cv v) R
  have p0262 :=
    @gRexbidv (.classEq (.cv u) X) (synWbr (.cv u) R (.cv v)) (synWbr X R (.cv v)) v
      (synCec Y (synClnker R)) dv_cache_0009 p0261
  have p0263 :=
    @gRspcev (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v)))
      (synWrex v (synCec Y (synClnker R)) (synWbr X R (.cv v))) u X
      (synCec X (synClnker R)) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0262
  have p0264 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
        (synWbr X R Y))
      (synWa (.classMem X (synCec X (synClnker R)))
        (synWrex v (synCec Y (synClnker R)) (synWbr X R (.cv v))))
      (synWrex u (synCec X (synClnker R))
        (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v))))
      p0260 p0263
  have p0265 :=
    @gEx
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWbr X R Y)
      (synWrex u (synCec X (synClnker R))
        (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v))))
      p0264
  have p0266 :=
    @gImpbid
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWrex u (synCec X (synClnker R))
        (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v))))
      (synWbr X R Y) p0214 p0265
  exact p0266


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_lnkerexg`. -/
@[expose]
noncomputable def gLnkerexg (R : Class) :
    Nominal.NPrf (.imp (.classMem R (synCvv)) (.classMem (synClnker R) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnker R))
  have p0001 := @gId (.classMem R (synCvv))
  have p0002 := @gCnvexg R (synCvv)
  have p0003 :=
    @gJca (.classMem R (synCvv)) (.classMem R (synCvv))
      (.classMem (synCcnv R) (synCvv)) p0001 p0002
  have p0004 := @gInexg R (synCcnv R) (synCvv) (synCvv)
  have p0005 :=
    @gSyl (.classMem R (synCvv))
      (synWa (.classMem R (synCvv)) (.classMem (synCcnv R) (synCvv)))
      (.classMem (synCin R (synCcnv R)) (synCvv)) p0003 p0004
  have p0006 :=
    @gSyl5eqel (.classMem R (synCvv)) (synClnker R) (synCin R (synCcnv R)) (synCvv)
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_brlnqrelkern`. -/
@[expose]
noncomputable def gBrlnqrelkern (C : Class) (R : Class) (X : Class) (Y : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem R (synCvv)) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))) (synWb
          (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
          (synWbr X R Y))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_Y : u ∉ Y.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_X : v ∉ X.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_Y : v ∉ Y.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : u ∉ ((synCec X (synClnker R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          fresh_u_not_X, fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((synCec X (synClnker R))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          fresh_v_not_X, fresh_v_not_R, or_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((synCec Y (synClnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          fresh_u_not_Y, fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((synCec Y (synClnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          fresh_v_not_Y, fresh_v_not_R, or_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0006 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0007 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0008 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0009 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0010 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_X, not_false_eq_true])
  have dv_cache_0011 : v ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_X, not_false_eq_true])
  have dv_cache_0012 : u ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_Y, not_false_eq_true])
  have dv_cache_0013 : v ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_Y, not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
  have p0001 := (Nominal.classEqRefl (synClnker R))
  have p0002 := @gId (.classMem R (synCvv))
  have p0003 := @gCnvexg R (synCvv)
  have p0004 :=
    @gJca (.classMem R (synCvv)) (.classMem R (synCvv))
      (.classMem (synCcnv R) (synCvv)) p0002 p0003
  have p0005 := @gInexg R (synCcnv R) (synCvv) (synCvv)
  have p0006 :=
    @gSyl (.classMem R (synCvv))
      (synWa (.classMem R (synCvv)) (.classMem (synCcnv R) (synCvv)))
      (.classMem (synCin R (synCcnv R)) (synCvv)) p0004 p0005
  have p0007 :=
    @gSyl5eqel (.classMem R (synCvv)) (synClnker R) (synCin R (synCcnv R)) (synCvv)
      p0001 p0006
  have p0008 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem R (synCvv)) (.classMem (synClnker R) (synCvv)) p0000 p0007
  have p0009 := @gEcexg X (synCvv) (synClnker R)
  have p0010 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem (synClnker R) (synCvv))
      (.classMem (synCec X (synClnker R)) (synCvv)) p0008 p0009
  have p0020 := @gEcexg Y (synCvv) (synClnker R)
  have p0021 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem (synClnker R) (synCvv))
      (.classMem (synCec Y (synClnker R)) (synCvv)) p0008 p0020
  have p0022 :=
    @gJca
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem (synCec X (synClnker R)) (synCvv))
      (.classMem (synCec Y (synClnker R)) (synCvv)) p0010 p0021
  have p0023 :=
    @gBrlnqrelg u v (synCec X (synClnker R)) (synCec Y (synClnker R)) R (synCvv)
      (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0024 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (.classMem (synCec X (synClnker R)) (synCvv))
        (.classMem (synCec Y (synClnker R)) (synCvv)))
      (synWb (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
        (synWrex u (synCec X (synClnker R))
          (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v)))))
      p0022 p0023
  have p0025 :=
    @gSimpr (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
  have p0026 :=
    @gLnqrelreps v u C R X Y dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0007
  have p0027 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWb (synWrex u (synCec X (synClnker R))
          (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v)))) (synWbr X R Y))
      p0025 p0026
  have p0028 :=
    @gBitrd
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
      (synWrex u (synCec X (synClnker R))
        (synWrex v (synCec Y (synClnker R)) (synWbr (.cv u) R (.cv v))))
      (synWbr X R Y) p0024 p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_lnqrelexg`. -/
@[expose]
noncomputable def gLnqrelexg (R : Class) :
    Nominal.NPrf (.imp (.classMem R (synCvv)) (.classMem (synClnqrel R) (synCvv))) :=
  by
  let proofSupport : Finset Var := R.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (h)
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_u : a ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have fresh_b_ne_u : b ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_b : u ≠ b := Ne.symm fresh_b_ne_u
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have dv_cache_0001 : y ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0003 : t ∉ ((synWbr (.cv x) R (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0004 : u ∉ ((synWbr (.cv x) R (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0005 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0006 : u ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_x,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ ((synCsn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0008 : u ∉ ((synCsn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_y,
          not_false_eq_true])
  have dv_cache_0009 :
    u ∉
      ((synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
          (synWbr (synCsn (.cv y)) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_a, fresh_u_ne_y, fresh_u_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    t ∉
      ((synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, fresh_t_ne_u, fresh_t_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0012 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0015 : x ∉ (R).fv :=
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
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0016 : y ∉ (R).fv :=
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
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_b, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((synCcom (synCsset) (synCsi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          fresh_t_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : t ∉ ((synCcnv (synCsset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0021 : u ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_t, not_false_eq_true])
  have dv_cache_0022 : u ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_b, not_false_eq_true])
  have dv_cache_0023 : u ∉ ((synCsset)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0024 : u ∉ ((synCsi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_u_not_R,
          not_false_eq_true])
  have dv_cache_0025 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Class.cv t)).fv :=
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
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((Class.cv u)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0029 : u ∉ ((synWbr (.cv t) (synCsset) (.cv a))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_t, fresh_u_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0030 :
    x ∉
      ((synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_a, fresh_x_ne_u, fresh_x_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 :
    y ∉
      ((synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_a, fresh_y_ne_u, fresh_y_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0032 : a ∉ ((synClnqrel R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqrel,
          fresh_a_not_R, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((synClnqrel R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqrel,
          fresh_b_not_R, not_false_eq_true])
  have dv_cache_0034 :
    a ∉ ((synCcom (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_a_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0035 :
    b ∉ ((synCcom (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_b_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0036 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @gR2ex (synWbr (.cv x) R (.cv y)) x y (.cv a) (.cv b) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gN1941vv
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classEq (.cv u) (synCsn (.cv y)))))
      (synWbr (.cv x) R (.cv y)) t u dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gAnass
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
      (synWbr (.cv x) R (.cv y))
  have p0003 :=
    @gN2exbii
      (synWa (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
            (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classEq (.cv u) (synCsn (.cv y))))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa
          (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
          (synWbr (.cv x) R (.cv y))))
      t u p0002
  have p0004 :=
    @gAncom
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
  have p0005 :=
    (Nominal.biimpRefl
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))))
  have p0006 :=
    @gBitr4i
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classEq (.cv u) (synCsn (.cv y)))))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))))
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))))
      p0004 p0005
  have p0007 :=
    @gN2exbii
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classEq (.cv u) (synCsn (.cv y)))))
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))))
      t u p0006
  have p0008 := @gSnex (.cv x)
  have p0009 := @gSnex (.cv y)
  have p0010 := @gBreq1 (.cv t) (synCsn (.cv x)) (.cv a) (synCsset)
  have p0011 :=
    @gAnbi1d (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) (synCsset) (.cv a))
      (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
      (synWbr (.cv u) (synCsset) (.cv b)) p0010
  have p0012 := @gBreq1 (.cv u) (synCsn (.cv y)) (.cv b) (synCsset)
  have p0013 :=
    @gAnbi2d (.classEq (.cv u) (synCsn (.cv y))) (synWbr (.cv u) (synCsset) (.cv b))
      (synWbr (synCsn (.cv y)) (synCsset) (.cv b))
      (synWbr (synCsn (.cv x)) (synCsset) (.cv a)) p0012
  have p0014 :=
    @gCeqsex2v
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
        (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
        (synWbr (synCsn (.cv y)) (synCsset) (.cv b)))
      t u (synCsn (.cv x)) (synCsn (.cv y)) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0008 p0009 p0011 p0013
  have p0015 := @gVex x
  have p0016 := @gVex a
  have p0017 := @gBrssetsn (.cv x) (.cv a) p0015 p0016
  have p0018 := @gVex y
  have p0019 := @gVex b
  have p0020 := @gBrssetsn (.cv y) (.cv b) p0018 p0019
  have p0021 :=
    @gAnbi12i (synWbr (synCsn (.cv x)) (synCsset) (.cv a)) (.classMem (.cv x) (.cv a))
      (synWbr (synCsn (.cv y)) (synCsset) (.cv b)) (.classMem (.cv y) (.cv b)) p0017
      p0020
  have p0022 :=
    @gN3bitri
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b)))
            (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))))))
      (synWex t (synWex u (synW3a (.classEq (.cv t) (synCsn (.cv x)))
            (.classEq (.cv u) (synCsn (.cv y))) (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))))))
      (synWa (synWbr (synCsn (.cv x)) (synCsset) (.cv a))
        (synWbr (synCsn (.cv y)) (synCsset) (.cv b)))
      (synWa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b))) p0007 p0014 p0021
  have p0023 :=
    @gAnbi1i
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b)))
            (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))))))
      (synWa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
      (synWbr (.cv x) R (.cv y)) p0022
  have p0024 :=
    @gN3bitr3i
      (synWex t (synWex u (synWa (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b)))
              (synWa (.classEq (.cv t) (synCsn (.cv x)))
                (.classEq (.cv u) (synCsn (.cv y))))) (synWbr (.cv x) R (.cv y)))))
      (synWa (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b)))
              (synWa (.classEq (.cv t) (synCsn (.cv x)))
                (.classEq (.cv u) (synCsn (.cv y))))))) (synWbr (.cv x) R (.cv y)))
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWbr (.cv x) R (.cv y))))))
      (synWa (synWa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
        (synWbr (.cv x) R (.cv y)))
      p0001 p0003 p0023
  have p0025 :=
    @gN2exbii
      (synWex t (synWex u (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWbr (.cv x) R (.cv y))))))
      (synWa (synWa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
        (synWbr (.cv x) R (.cv y)))
      x y p0024
  have p0026 :=
    @gBitr4i (synWrex x (.cv a) (synWrex y (.cv b) (synWbr (.cv x) R (.cv y))))
      (synWex x (synWex y
          (synWa (synWa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
            (synWbr (.cv x) R (.cv y)))))
      (synWex x (synWex y (synWex t (synWex u (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      p0000 p0025
  have p0029 :=
    @gBrlnqrelg x y (.cv a) (.cv b) R (synCvv) (synCvv) dv_cache_0012 dv_cache_0001
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0002
  have p0030 :=
    @gMp2an (.classMem (.cv a) (synCvv)) (.classMem (.cv b) (synCvv))
      (synWb (synWbr (.cv a) (synClnqrel R) (.cv b))
        (synWrex x (.cv a) (synWrex y (.cv b) (synWbr (.cv x) R (.cv y)))))
      p0016 p0019 p0029
  have p0031 :=
    @gBrco t (.cv a) (.cv b) (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0032 := @gBrcnv (.cv a) (.cv t) (synCsset)
  have p0033 :=
    @gBrco u (.cv t) (.cv b) (synCsset) (synCsi R) dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024
  have p0034 :=
    @gBrsi x y (.cv t) (.cv u) R dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
      dv_cache_0015 dv_cache_0016 dv_cache_0002
  have p0035 :=
    (Nominal.biimpRefl
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y))))
  have p0036 :=
    @gN2exbii
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWbr (.cv x) R (.cv y)))
      x y p0035
  have p0037 :=
    @gBitri (synWbr (.cv t) (synCsi R) (.cv u))
      (synWex x (synWex y (synW3a (.classEq (.cv t) (synCsn (.cv x)))
            (.classEq (.cv u) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      p0034 p0036
  have p0038 :=
    @gAnbi2ci (synWbr (.cv t) (synCsi R) (.cv u))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))
      (synWbr (.cv u) (synCsset) (.cv b)) p0037
  have p0039 :=
    @gExbii
      (synWa (synWbr (.cv t) (synCsi R) (.cv u)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWbr (.cv x) R (.cv y))))))
      u p0038
  have p0040 :=
    @gBitri (synWbr (.cv t) (synCcom (synCsset) (synCsi R)) (.cv b))
      (synWex u (synWa (synWbr (.cv t) (synCsi R) (.cv u))
          (synWbr (.cv u) (synCsset) (.cv b))))
      (synWex u (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      p0033 p0039
  have p0041 :=
    @gAnbi12i (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
      (synWbr (.cv t) (synCsset) (.cv a))
      (synWbr (.cv t) (synCcom (synCsset) (synCsi R)) (.cv b))
      (synWex u (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      p0032 p0040
  have p0042 :=
    @gN1942v (synWbr (.cv t) (synCsset) (.cv a))
      (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWbr (.cv x) R (.cv y))))))
      u dv_cache_0029
  have p0043 :=
    @gN1942vv
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b)))
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
        (synWbr (.cv x) R (.cv y)))
      x y dv_cache_0030 dv_cache_0031
  have p0044 :=
    @gAnass (synWbr (.cv t) (synCsset) (.cv a)) (synWbr (.cv u) (synCsset) (.cv b))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))
  have p0045 :=
    @gBitr2i
      (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWbr (.cv x) R (.cv y))))))
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWex x (synWex y (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWbr (.cv x) R (.cv y))))))
      (synWa (synWbr (.cv t) (synCsset) (.cv a))
        (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      p0043 p0044
  have p0046 :=
    @gExbii
      (synWa (synWbr (.cv t) (synCsset) (.cv a))
        (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
              (synWbr (.cv u) (synCsset) (.cv b))) (synWa
              (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
              (synWbr (.cv x) R (.cv y))))))
      u p0045
  have p0047 :=
    @gN3bitr2i
      (synWa (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
        (synWbr (.cv t) (synCcom (synCsset) (synCsi R)) (.cv b)))
      (synWa (synWbr (.cv t) (synCsset) (.cv a)) (synWex u
          (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      (synWex u (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWa (synWbr (.cv u) (synCsset) (.cv b)) (synWex x (synWex y (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      (synWex u (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      p0041 p0042 p0046
  have p0048 :=
    @gExbii
      (synWa (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
        (synWbr (.cv t) (synCcom (synCsset) (synCsi R)) (.cv b)))
      (synWex u (synWex x (synWex y (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
                (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                (synWa (.classEq (.cv t) (synCsn (.cv x)))
                  (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y)))))))
      t p0047
  have p0049 :=
    @gExrot4
      (synWa (synWa (synWbr (.cv t) (synCsset) (.cv a))
          (synWbr (.cv u) (synCsset) (.cv b))) (synWa
          (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y))))
          (synWbr (.cv x) R (.cv y))))
      t u x y
  have p0050 :=
    @gN3bitri
      (synWbr (.cv a)
        (synCcom (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset))) (.cv b))
      (synWex t (synWa (synWbr (.cv a) (synCcnv (synCsset)) (.cv t))
          (synWbr (.cv t) (synCcom (synCsset) (synCsi R)) (.cv b))))
      (synWex t (synWex u (synWex x (synWex y (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      (synWex x (synWex y (synWex t (synWex u (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      p0031 p0048 p0049
  have p0051 :=
    @gN3bitr4i (synWrex x (.cv a) (synWrex y (.cv b) (synWbr (.cv x) R (.cv y))))
      (synWex x (synWex y (synWex t (synWex u (synWa
                (synWa (synWbr (.cv t) (synCsset) (.cv a))
                  (synWbr (.cv u) (synCsset) (.cv b))) (synWa
                  (synWa (.classEq (.cv t) (synCsn (.cv x)))
                    (.classEq (.cv u) (synCsn (.cv y)))) (synWbr (.cv x) R (.cv y))))))))
      (synWbr (.cv a) (synClnqrel R) (.cv b))
      (synWbr (.cv a)
        (synCcom (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset))) (.cv b))
      p0026 p0030 p0050
  have p0052 :=
    @gEqbrriv a b (synClnqrel R)
      (synCcom (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset))) dv_cache_0032
      dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 p0051
  have p0053 := @gSsetex
  have p0054 := @gA1i (.classMem (synCsset) (synCvv)) (.classMem R (synCvv)) p0053
  have p0055 := @gSiexg R (synCvv)
  have p0056 :=
    @gJca (.classMem R (synCvv)) (.classMem (synCsset) (synCvv))
      (.classMem (synCsi R) (synCvv)) p0054 p0055
  have p0057 := @gCoexg (synCsset) (synCsi R) (synCvv) (synCvv)
  have p0058 :=
    @gSyl (.classMem R (synCvv))
      (synWa (.classMem (synCsset) (synCvv)) (.classMem (synCsi R) (synCvv)))
      (.classMem (synCcom (synCsset) (synCsi R)) (synCvv)) p0056 p0057
  have p0060 := @gCnvexg (synCsset) (synCvv)
  have p0061 := Nominal.mp p0053 p0060
  have p0062 :=
    @gA1i (.classMem (synCcnv (synCsset)) (synCvv)) (.classMem R (synCvv)) p0061
  have p0063 :=
    @gJca (.classMem R (synCvv))
      (.classMem (synCcom (synCsset) (synCsi R)) (synCvv))
      (.classMem (synCcnv (synCsset)) (synCvv)) p0058 p0062
  have p0064 :=
    @gCoexg (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset)) (synCvv) (synCvv)
  have p0065 :=
    @gSyl (.classMem R (synCvv))
      (synWa (.classMem (synCcom (synCsset) (synCsi R)) (synCvv))
        (.classMem (synCcnv (synCsset)) (synCvv)))
      (.classMem (synCcom (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset))) (synCvv))
      p0063 p0064
  have p0066 :=
    @gSyl5eqel (.classMem R (synCvv)) (synClnqrel R)
      (synCcom (synCcom (synCsset) (synCsi R)) (synCcnv (synCsset))) (synCvv) p0052
      p0065
  exact p0066

/-- Checked nominal proof certificate identified upstream as `g_lnquoexg`. -/
@[expose]
noncomputable def gLnquoexg (C : Class) (R : Class) (_dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
        (.classMem (synClnquo R C) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnquo R C))
  have p0001 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0002 := @gLnkerexg R
  have p0003 :=
    @gSyl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem R (synCvv)) (.classMem (synClnker R) (synCvv)) p0001 p0002
  have p0004 := @gSimpr (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0005 :=
    @gJca (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnker R) (synCvv)) (.classMem C (synCvv)) p0003 p0004
  have p0006 := @gQsexg C (synClnker R) (synCvv) (synCvv)
  have p0007 :=
    @gSyl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (.classMem (synClnker R) (synCvv)) (.classMem C (synCvv)))
      (.classMem (synCqs C (synClnker R)) (synCvv)) p0005 p0006
  have p0008 :=
    @gSyl5eqel (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synClnquo R C)
      (synCqs C (synClnker R)) (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_lnqordexg`. -/
@[expose]
noncomputable def gLnqordexg (C : Class) (R : Class) (_dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
        (.classMem (synClnqord R C) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnqord R C))
  have p0001 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0002 := @gLnqrelexg R
  have p0003 :=
    @gSyl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem R (synCvv)) (.classMem (synClnqrel R) (synCvv)) p0001 p0002
  have p0004 := (Nominal.classEqRefl (synClnquo R C))
  have p0006 := @gLnkerexg R
  have p0007 :=
    @gSyl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem R (synCvv)) (.classMem (synClnker R) (synCvv)) p0001 p0006
  have p0008 := @gSimpr (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0009 :=
    @gJca (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnker R) (synCvv)) (.classMem C (synCvv)) p0007 p0008
  have p0010 := @gQsexg C (synClnker R) (synCvv) (synCvv)
  have p0011 :=
    @gSyl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (.classMem (synClnker R) (synCvv)) (.classMem C (synCvv)))
      (.classMem (synCqs C (synClnker R)) (synCvv)) p0009 p0010
  have p0012 :=
    @gSyl5eqel (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synClnquo R C)
      (synCqs C (synClnker R)) (synCvv) p0004 p0011
  have p0022 :=
    @gJca (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnquo R C) (synCvv)) (.classMem (synClnquo R C) (synCvv)) p0012
      p0012
  have p0023 := @gXpexg (synClnquo R C) (synClnquo R C) (synCvv) (synCvv)
  have p0024 :=
    @gSyl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (.classMem (synClnquo R C) (synCvv)) (.classMem (synClnquo R C) (synCvv)))
      (.classMem (synCxp (synClnquo R C) (synClnquo R C)) (synCvv)) p0022 p0023
  have p0025 :=
    @gJca (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnqrel R) (synCvv))
      (.classMem (synCxp (synClnquo R C) (synClnquo R C)) (synCvv)) p0003 p0024
  have p0026 :=
    @gInexg (synClnqrel R) (synCxp (synClnquo R C) (synClnquo R C)) (synCvv)
      (synCvv)
  have p0027 :=
    @gSyl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (.classMem (synClnqrel R) (synCvv))
        (.classMem (synCxp (synClnquo R C) (synClnquo R C)) (synCvv)))
      (.classMem (synCin (synClnqrel R) (synCxp (synClnquo R C) (synClnquo R C)))
        (synCvv))
      p0025 p0026
  have p0028 :=
    @gSyl5eqel (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synClnqord R C)
      (synCin (synClnqrel R) (synCxp (synClnquo R C) (synClnquo R C))) (synCvv)
      p0000 p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end
