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

@[expose]
noncomputable def g_kqfinantinn (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp
          (syn_wa (syn_wbr A (syn_ckqrel (syn_clefin)) B)
            (syn_wbr B (syn_ckqrel (syn_clefin)) A)) (.classEq A B))) :=
  by
  have p0000 := @g_kqlefinbr A B (syn_cnnc) (syn_cnnc)
  have p0001 := @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0002 := @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) p0001 p0002
  have p0004 := @g_kqlefinbr B A (syn_cnnc) (syn_cnnc)
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)))
      (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin)))
      p0003 p0004
  have p0006 :=
    @g_anbi12d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wbr A (syn_ckqrel (syn_clefin)) B) (.classMem (syn_copk A B) (syn_clefin))
      (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin))
      p0000 p0005
  have p0007 :=
    @g_biimpd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (syn_wbr A (syn_ckqrel (syn_clefin)) B) (syn_wbr B (syn_ckqrel (syn_clefin)) A))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      p0006
  have p0008 := @g_lefinantinn A B
  have p0009 :=
    @g_syld (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (syn_wbr A (syn_ckqrel (syn_clefin)) B) (syn_wbr B (syn_ckqrel (syn_clefin)) A))
      (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
      (.classEq A B) p0007 p0008
  exact p0009

@[expose]
noncomputable def g_nntctfin (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classEq (syn_ctc N) (syn_ctfin N))) :=
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
  have dv_cache_0002 : a ∉ ((Wff.classEq (syn_ctc N) (syn_ctfin N))).fv :=
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
  have dv_cache_0003 : a ∉ ((Wff.classMem N (syn_cnnc))).fv :=
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
  have p0000 := @g_id (.classMem N (syn_cnnc))
  have p0001 := @g_nulnnn
  have p0002 := @g_eleq1 N (syn_c0) (syn_cnnc)
  have p0003 :=
    @g_mtbiri (.classEq N (syn_c0)) (.classMem N (syn_cnnc))
      (.classMem (syn_c0) (syn_cnnc)) p0001 p0002
  have p0004 := @g_necon2ai (.classMem N (syn_cnnc)) N (syn_c0) p0003
  have p0005 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) p0000
      p0004
  have p0006 := @g_tfinprop N a dv_cache_0001
  have p0007 :=
    @g_syl (.classMem N (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (syn_wa (.classMem (syn_ctfin N) (syn_cnnc))
        (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))))
      p0005 p0006
  have p0008 :=
    @g_simprd (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))
      (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) p0007
  have p0009 :=
    @g_simpl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))
  have p0010 := @g_simpl (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem N (syn_cnnc))
      p0009 p0010
  have p0012 := @g_nntccl N
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (.classMem N (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc)) p0011 p0012
  have p0017 := @g_tfincl N
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0011 p0017
  have p0019 :=
    @g_jca
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (.classMem (syn_ctc N) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0013 p0018
  have p0022 := @g_nnnc N
  have p0023 :=
    @g_syl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem N (syn_cnnc)) (.classMem N (syn_cncs)) p0010 p0022
  have p0024 := @g_simpr (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0025 :=
    @g_jca (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem N (syn_cncs)) (.classMem (.cv a) N) p0023 p0024
  have p0026 := @g_pw1eltc N (.cv a)
  have p0027 :=
    @g_syl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (syn_wa (.classMem N (syn_cncs)) (.classMem (.cv a) N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctc N)) p0025 p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctc N)) p0009 p0027
  have p0029 :=
    @g_simpr (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))
  have p0030 :=
    @g_jca
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctc N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)) p0028 p0029
  have p0031 :=
    @g_jca
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (syn_wa (.classMem (syn_ctc N) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctc N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      p0019 p0030
  have p0032 := @g_nnceleq (syn_cpw1 (.cv a)) (syn_ctc N) (syn_ctfin N)
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (syn_wa (syn_wa (.classMem (syn_ctc N) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctc N))
          (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))))
      (.classEq (syn_ctc N) (syn_ctfin N)) p0031 p0032
  have p0034 :=
    @g_ex (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)) (.classEq (syn_ctc N) (syn_ctfin N))
      p0033
  have p0035 :=
    @g_rexlimdva (.classMem N (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))
      (.classEq (syn_ctc N) (syn_ctfin N)) a N dv_cache_0002 dv_cache_0003 p0034
  have p0036 :=
    @g_mpd (.classMem N (syn_cnnc))
      (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))
      (.classEq (syn_ctc N) (syn_ctfin N)) p0008 p0035
  exact p0036

@[expose]
noncomputable def g_tc6lecan (M : Class) (N : Class)
    (hyp_tc6lecb_1 : Nominal.NPrf (.classMem M (syn_cncs)))
    (hyp_tc6lecb_2 : Nominal.NPrf (.classMem N (syn_cncs))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
        (syn_wbr M (syn_clec) N)) :=
  by
  have p0000 := @g_tlecg M N
  have p0001 :=
    @g_mp2an (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wb (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)))
      hyp_tc6lecb_1 hyp_tc6lecb_2 p0000
  have p0002 := @g_tccl M
  have p0003 := Nominal.mp hyp_tc6lecb_1 p0002
  have p0004 := @g_tccl N
  have p0005 := Nominal.mp hyp_tc6lecb_2 p0004
  have p0006 := @g_tlecg (syn_ctc M) (syn_ctc N)
  have p0007 :=
    @g_mp2an (.classMem (syn_ctc M) (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs))
      (syn_wb (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))
        (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))))
      p0003 p0005 p0006
  have p0008 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))
      (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))) p0001 p0007
  have p0011 := @g_tccl (syn_ctc M)
  have p0012 := Nominal.mp p0003 p0011
  have p0015 := @g_tccl (syn_ctc N)
  have p0016 := Nominal.mp p0005 p0015
  have p0017 := @g_tlecg (syn_ctc (syn_ctc M)) (syn_ctc (syn_ctc N))
  have p0018 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc M)) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      (syn_wb (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N)))
        (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      p0012 p0016 p0017
  have p0019 :=
    @g_bitri (syn_wbr M (syn_clec) N)
      (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N)))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
      p0008 p0018
  have p0024 := @g_tccl (syn_ctc (syn_ctc M))
  have p0025 := Nominal.mp p0012 p0024
  have p0030 := @g_tccl (syn_ctc (syn_ctc N))
  have p0031 := Nominal.mp p0016 p0030
  have p0032 := @g_tlecg (syn_ctc (syn_ctc (syn_ctc M))) (syn_ctc (syn_ctc (syn_ctc N)))
  have p0033 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc (syn_ctc M))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs))
      (syn_wb (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc N))))
        (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      p0025 p0031 p0032
  have p0034 :=
    @g_bitri (syn_wbr M (syn_clec) N)
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
      p0019 p0033
  have p0041 := @g_tccl (syn_ctc (syn_ctc (syn_ctc M)))
  have p0042 := Nominal.mp p0025 p0041
  have p0049 := @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0050 := Nominal.mp p0031 p0049
  have p0051 :=
    @g_tlecg (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0052 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs))
      (syn_wb (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
        (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0042 p0050 p0051
  have p0053 :=
    @g_bitri (syn_wbr M (syn_clec) N)
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      p0034 p0052
  have p0062 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))
  have p0063 := Nominal.mp p0042 p0062
  have p0072 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0073 := Nominal.mp p0050 p0072
  have p0074 :=
    @g_tlecg (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0075 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs))
      (syn_wb (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      p0063 p0073 p0074
  have p0076 :=
    @g_bitri (syn_wbr M (syn_clec) N)
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0053 p0075
  have p0077 :=
    @g_biimpri (syn_wbr M (syn_clec) N)
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0076
  exact p0077

@[expose]
noncomputable def g_tc2nc (A : Class)
    (hyp_tc2nc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))) :=
  by
  have p0000 := @g_tcnc A hyp_tc2nc_1
  have p0001 := @g_tceq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_pw1ex A hyp_tc2nc_1
  have p0004 := @g_tcnc (syn_cpw1 A) p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc A))) (syn_ctc (syn_cnc (syn_cpw1 A)))
      (syn_cnc (syn_cpw1 (syn_cpw1 A))) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_resiidima (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cima (syn_cres (syn_cid) A) B) (syn_cin A B)) :=
  by
  have p0000 := @g_cnvresid A
  have p0001 := @g_eqcomi (syn_ccnv (syn_cres (syn_cid) A)) (syn_cres (syn_cid) A) p0000
  have p0002 :=
    @g_imaeq1i (syn_cres (syn_cid) A) (syn_ccnv (syn_cres (syn_cid) A)) B p0001
  have p0003 := @g_cnvresima A B (syn_cid)
  have p0004 :=
    @g_eqtri (syn_cima (syn_cres (syn_cid) A) B)
      (syn_cima (syn_ccnv (syn_cres (syn_cid) A)) B)
      (syn_cin (syn_cima (syn_ccnv (syn_cid)) B) A) p0002 p0003
  have p0005 := @g_cnvi
  have p0006 := @g_imaeq1i (syn_ccnv (syn_cid)) (syn_cid) B p0005
  have p0007 := @g_imai B
  have p0008 :=
    @g_eqtri (syn_cima (syn_ccnv (syn_cid)) B) (syn_cima (syn_cid) B) B p0006 p0007
  have p0009 := @g_ineq1i (syn_cima (syn_ccnv (syn_cid)) B) B A p0008
  have p0010 :=
    @g_eqtri (syn_cima (syn_cres (syn_cid) A) B)
      (syn_cin (syn_cima (syn_ccnv (syn_cid)) B) A) (syn_cin B A) p0004 p0009
  have p0011 := @g_incom B A
  have p0012 :=
    @g_eqtri (syn_cima (syn_cres (syn_cid) A) B) (syn_cin B A) (syn_cin A B) p0010 p0011
  exact p0012

@[expose]
noncomputable def g_hnwsegfnex (D : Class) (R : Class)
    (hyp_hnwsegfnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwsegfn R D) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwsegfn R D))
  have p0001 := @g_idex
  have p0002 := @g_brex R D (syn_cwe)
  have p0003 := Nominal.mp hyp_hnwsegfnex_1 p0002
  have p0004 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0003
  have p0005 := @g_resex (syn_cid) D p0001 p0004
  have p0006 := @g_imageex (syn_cres (syn_cid) D) p0005
  have p0009 := @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0003
  have p0011 := @g_difex R (syn_cid) p0009 p0001
  have p0012 := @g_cnvex (syn_cdif R (syn_cid)) p0011
  have p0013 := @g_imageex (syn_ccnv (syn_cdif R (syn_cid))) p0012
  have p0014 :=
    @g_coex (syn_cimage (syn_cres (syn_cid) D))
      (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) p0006 p0013
  have p0015 :=
    @g_eqeltri (syn_chnwsegfn R D)
      (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
        (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))))
      (syn_cvv) p0000 p0014
  exact p0015

@[expose]
noncomputable def g_hnwcodefnex (D : Class) (R : Class)
    (hyp_hnwcodefnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcodefn R) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcodefn R))
  have p0001 := @g_idex
  have p0002 := @g_brex R D (syn_cwe)
  have p0003 := Nominal.mp hyp_hnwcodefnex_1 p0002
  have p0004 := @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0003
  have p0005 := @g_resex (syn_cid) R p0001 p0004
  have p0006 := @g_imageex (syn_cres (syn_cid) R) p0005
  have p0007 := @g_crossex
  have p0010 := @g_txpex (syn_cid) (syn_cid) p0001 p0001
  have p0011 := @g_coex (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0007 p0010
  have p0012 :=
    @g_coex (syn_cimage (syn_cres (syn_cid) R))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0006 p0011
  have p0014 :=
    @g_txpex
      (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
        (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))))
      (syn_cid) p0012 p0001
  have p0015 :=
    @g_eqeltri (syn_chnwcodefn R)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
      (syn_cvv) p0000 p0014
  exact p0015

@[expose]
noncomputable def g_hnwcutfnex (D : Class) (R : Class)
    (hyp_hnwcutfnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcutfn R D) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcutfn R D))
  have p0001 := @g_hnwcodefnex D R hyp_hnwcutfnex_1
  have p0002 := @g_hnwsegfnex D R hyp_hnwcutfnex_1
  have p0003 := @g_coex (syn_chnwcodefn R) (syn_chnwsegfn R D) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_chnwcutfn R D) (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D))
      (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_fvimagecl (B : Class) (F : Class)
    (hyp_fvimagecl_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_fvimagecl_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage F) B) (syn_cima F B)) :=
  by
  have p0000 := @g_eqid (syn_cima F B)
  have p0001 := @g_imaex F B hyp_fvimagecl_1 hyp_fvimagecl_2
  have p0002 := @g_brimage B (syn_cima F B) F hyp_fvimagecl_2 p0001
  have p0003 :=
    @g_mpbir (syn_wbr B (syn_cimage F) (syn_cima F B))
      (.classEq (syn_cima F B) (syn_cima F B)) p0000 p0002
  have p0004 := @g_wppimagefn F hyp_fvimagecl_1
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage F) (syn_cvv)) (.classMem B (syn_cvv)) p0004
      hyp_fvimagecl_2
  have p0006 := @g_fnbrfvb (syn_cvv) B (syn_cima F B) (syn_cimage F)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_mpbir (.classEq (syn_cfv (syn_cimage F) B) (syn_cima F B))
      (syn_wbr B (syn_cimage F) (syn_cima F B)) p0003 p0007
  exact p0008

@[expose]
noncomputable def g_fncovv (F : Class) (G : Class)
    (hyp_fncovv_1 : Nominal.NPrf (syn_wfn F (syn_cvv)))
    (hyp_fncovv_2 : Nominal.NPrf (syn_wfn G (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_ccom F G) (syn_cvv)) :=
  by
  have p0000 := @g_ssv (syn_crn G)
  have p0001 :=
    @g_n_3pm3_2i (syn_wfn F (syn_cvv)) (syn_wfn G (syn_cvv))
      (syn_wss (syn_crn G) (syn_cvv)) hyp_fncovv_1 hyp_fncovv_2 p0000
  have p0002 := @g_fnco (syn_cvv) (syn_cvv) F G
  have p0003 := Nominal.mp p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fvtxpvv (A : Class) (F : Class) (G : Class)
    (hyp_fvtxpvv_1 : Nominal.NPrf (syn_wfn F (syn_cvv)))
    (hyp_fvtxpvv_2 : Nominal.NPrf (syn_wfn G (syn_cvv)))
    (hyp_fvtxpvv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_ctxp F G) A) (syn_cop (syn_cfv F A) (syn_cfv G A))) :=
  by
  have p0000 := @g_eqid (syn_cfv F A)
  have p0001 :=
    @g_pm3_2i (syn_wfn F (syn_cvv)) (.classMem A (syn_cvv)) hyp_fvtxpvv_1 hyp_fvtxpvv_3
  have p0002 := @g_fnbrfvb (syn_cvv) A (syn_cfv F A) F
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_mpbi (.classEq (syn_cfv F A) (syn_cfv F A)) (syn_wbr A F (syn_cfv F A)) p0000 p0003
  have p0005 := @g_eqid (syn_cfv G A)
  have p0006 :=
    @g_pm3_2i (syn_wfn G (syn_cvv)) (.classMem A (syn_cvv)) hyp_fvtxpvv_2 hyp_fvtxpvv_3
  have p0007 := @g_fnbrfvb (syn_cvv) A (syn_cfv G A) G
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbi (.classEq (syn_cfv G A) (syn_cfv G A)) (syn_wbr A G (syn_cfv G A)) p0005 p0008
  have p0010 :=
    @g_pm3_2i (syn_wbr A F (syn_cfv F A)) (syn_wbr A G (syn_cfv G A)) p0004 p0009
  have p0011 := @g_trtxp A (syn_cfv F A) (syn_cfv G A) F G
  have p0012 :=
    @g_mpbir (syn_wbr A (syn_ctxp F G) (syn_cop (syn_cfv F A) (syn_cfv G A)))
      (syn_wa (syn_wbr A F (syn_cfv F A)) (syn_wbr A G (syn_cfv G A))) p0010 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn F (syn_cvv)) (syn_wfn G (syn_cvv)) hyp_fvtxpvv_1 hyp_fvtxpvv_2
  have p0014 := @g_fntxp (syn_cvv) (syn_cvv) F G
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_inidm (syn_cvv)
  have p0017 := @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp F G) p0016
  have p0018 :=
    @g_mpbi (syn_wfn (syn_ctxp F G) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp F G) (syn_cvv)) p0015 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_ctxp F G) (syn_cvv)) (.classMem A (syn_cvv)) p0018
      hyp_fvtxpvv_3
  have p0020 :=
    @g_fnbrfvb (syn_cvv) A (syn_cop (syn_cfv F A) (syn_cfv G A)) (syn_ctxp F G)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @g_mpbir (.classEq (syn_cfv (syn_ctxp F G) A) (syn_cop (syn_cfv F A) (syn_cfv G A)))
      (syn_wbr A (syn_ctxp F G) (syn_cop (syn_cfv F A) (syn_cfv G A))) p0012 p0021
  exact p0022

@[expose]
noncomputable def g_hnwsegfnfn (D : Class) (R : Class)
    (hyp_hnwsegfnfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwsegfn R D) (syn_cvv)) :=
  by
  have p0000 := @g_idex
  have p0001 := @g_brex R D (syn_cwe)
  have p0002 := Nominal.mp hyp_hnwsegfnfn_1 p0001
  have p0003 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 := @g_resex (syn_cid) D p0000 p0003
  have p0005 := @g_wppimagefn (syn_cres (syn_cid) D) p0004
  have p0008 := @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0010 := @g_difex R (syn_cid) p0008 p0000
  have p0011 := @g_cnvex (syn_cdif R (syn_cid)) p0010
  have p0012 := @g_wppimagefn (syn_ccnv (syn_cdif R (syn_cid))) p0011
  have p0013 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) D))
      (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) p0005 p0012
  have p0014 := (Nominal.classEqRefl (syn_chnwsegfn R D))
  have p0015 :=
    @g_fneq1i (syn_cvv) (syn_chnwsegfn R D)
      (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
        (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))))
      p0014
  have p0016 :=
    @g_mpbir (syn_wfn (syn_chnwsegfn R D) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
          (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) (syn_cvv))
      p0013 p0015
  exact p0016

@[expose]
noncomputable def g_hnwcodefnfn (D : Class) (R : Class)
    (hyp_hnwcodefnfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcodefn R) (syn_cvv)) :=
  by
  have p0000 := @g_idex
  have p0001 := @g_brex R D (syn_cwe)
  have p0002 := Nominal.mp hyp_hnwcodefnfn_1 p0001
  have p0003 := @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 := @g_resex (syn_cid) R p0000 p0003
  have p0005 := @g_wppimagefn (syn_cres (syn_cid) R) p0004
  have p0006 := @g_fncross
  have p0007 := @g_fnresi (syn_cvv)
  have p0008 := @g_resid (syn_cid)
  have p0009 := @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0008
  have p0010 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv))
      (syn_wfn (syn_cid) (syn_cvv)) p0007 p0009
  have p0015 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0010 p0010
  have p0016 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cid)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @g_inidm (syn_cvv)
  have p0019 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cid)) p0018
  have p0020 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) p0017 p0019
  have p0021 := @g_fncovv (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0006 p0020
  have p0022 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) R))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0005 p0021
  have p0027 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cvv))
      (syn_wfn (syn_cid) (syn_cvv)) p0022 p0010
  have p0028 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
        (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))))
      (syn_cid)
  have p0029 := Nominal.mp p0027 p0028
  have p0031 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
      p0018
  have p0032 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
            (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
            (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_cvv))
      p0029 p0031
  have p0033 := (Nominal.classEqRefl (syn_chnwcodefn R))
  have p0034 :=
    @g_fneq1i (syn_cvv) (syn_chnwcodefn R)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
      p0033
  have p0035 :=
    @g_mpbir (syn_wfn (syn_chnwcodefn R) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
            (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_cvv))
      p0032 p0034
  exact p0035

@[expose]
noncomputable def g_hnwcutfnfn (D : Class) (R : Class)
    (hyp_hnwcutfnfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcutfn R D) (syn_cvv)) :=
  by
  have p0000 := @g_hnwcodefnfn D R hyp_hnwcutfnfn_1
  have p0001 := @g_hnwsegfnfn D R hyp_hnwcutfnfn_1
  have p0002 := @g_fncovv (syn_chnwcodefn R) (syn_chnwsegfn R D) p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_chnwcutfn R D))
  have p0004 :=
    @g_fneq1i (syn_cvv) (syn_chnwcutfn R D)
      (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_chnwcutfn R D) (syn_cvv))
      (syn_wfn (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) (syn_cvv)) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_hnwsegfnval (B : Class) (D : Class) (R : Class)
    (hyp_hnwsegfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hnwsegfnval_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnwsegfnval_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chnwsegfn R D) B)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwsegfn R D))
  have p0001 :=
    @g_fveq1i B (syn_chnwsegfn R D)
      (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
        (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))))
      p0000
  have p0002 := @g_idex
  have p0003 := @g_difex R (syn_cid) hyp_hnwsegfnval_1 p0002
  have p0004 := @g_cnvex (syn_cdif R (syn_cid)) p0003
  have p0005 := @g_wppimagefn (syn_ccnv (syn_cdif R (syn_cid))) p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) (syn_cvv))
      (.classMem B (syn_cvv)) p0005 hyp_hnwsegfnval_3
  have p0007 :=
    @g_fvco2 (syn_cvv) B (syn_cimage (syn_cres (syn_cid) D))
      (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B)
      (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
          (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) B)
      (syn_cfv (syn_cimage (syn_cres (syn_cid) D))
        (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B))
      p0001 p0008
  have p0011 := @g_resex (syn_cid) D p0002 hyp_hnwsegfnval_2
  have p0012 := @g_fvex B (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))
  have p0013 :=
    @g_fvimagecl (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)
      (syn_cres (syn_cid) D) p0011 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B)
      (syn_cfv (syn_cimage (syn_cres (syn_cid) D))
        (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B))
      (syn_cima (syn_cres (syn_cid) D)
        (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B))
      p0009 p0013
  have p0015 := @g_resiidima D (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)
  have p0016 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B)
      (syn_cima (syn_cres (syn_cid) D)
        (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B))
      (syn_cin D (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)) p0014 p0015
  have p0020 := @g_fvimagecl B (syn_ccnv (syn_cdif R (syn_cid))) p0004 hyp_hnwsegfnval_3
  have p0021 :=
    @g_ineq2i (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B) D p0020
  have p0022 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B)
      (syn_cin D (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) p0016 p0021
  exact p0022

@[expose]
noncomputable def g_hnwcodefnval (B : Class) (R : Class)
    (hyp_hnwcodefnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hnwcodefnval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chnwcodefn R) B) (syn_cop (syn_cin R (syn_cxp B B)) B)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcodefn R))
  have p0001 :=
    @g_fveq1i B (syn_chnwcodefn R)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
      p0000
  have p0002 := @g_idex
  have p0003 := @g_resex (syn_cid) R p0002 hyp_hnwcodefnval_1
  have p0004 := @g_wppimagefn (syn_cres (syn_cid) R) p0003
  have p0005 := @g_fncross
  have p0006 := @g_fnresi (syn_cvv)
  have p0007 := @g_resid (syn_cid)
  have p0008 := @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv))
      (syn_wfn (syn_cid) (syn_cvv)) p0006 p0008
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0009 p0009
  have p0015 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cid)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_inidm (syn_cvv)
  have p0018 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cid)) p0017
  have p0019 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) p0016 p0018
  have p0020 := @g_fncovv (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0005 p0019
  have p0021 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) R))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0004 p0020
  have p0026 :=
    @g_fvtxpvv B
      (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
        (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))))
      (syn_cid) p0021 p0009 hyp_hnwcodefnval_2
  have p0043 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) (syn_cvv))
      (.classMem B (syn_cvv)) p0020 hyp_hnwcodefnval_2
  have p0044 :=
    @g_fvco2 (syn_cvv) B (syn_cimage (syn_cres (syn_cid) R))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))
  have p0045 := Nominal.mp p0043 p0044
  have p0060 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) (.classMem B (syn_cvv))
      p0019 hyp_hnwcodefnval_2
  have p0061 := @g_fvco2 (syn_cvv) B (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))
  have p0062 := Nominal.mp p0060 p0061
  have p0071 := @g_fvtxpvv B (syn_cid) (syn_cid) p0009 p0009 hyp_hnwcodefnval_2
  have p0072 := @g_fvi B (syn_cvv)
  have p0073 := Nominal.mp hyp_hnwcodefnval_2 p0072
  have p0076 := @g_opeq12i (syn_cfv (syn_cid) B) B (syn_cfv (syn_cid) B) B p0073 p0073
  have p0077 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_cid)) B)
      (syn_cop (syn_cfv (syn_cid) B) (syn_cfv (syn_cid) B)) (syn_cop B B) p0071 p0076
  have p0078 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cid) (syn_cid)) B) (syn_cop B B) (syn_ccross) p0077
  have p0079 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B)
      (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_cid) (syn_cid)) B))
      (syn_cfv (syn_ccross) (syn_cop B B)) p0062 p0078
  have p0080 := (Nominal.classEqRefl (syn_co B (syn_ccross) B))
  have p0081 :=
    @g_eqcomi (syn_co B (syn_ccross) B) (syn_cfv (syn_ccross) (syn_cop B B)) p0080
  have p0082 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B)
      (syn_cfv (syn_ccross) (syn_cop B B)) (syn_co B (syn_ccross) B) p0079 p0081
  have p0083 :=
    @g_pm3_2i (.classMem B (syn_cvv)) (.classMem B (syn_cvv)) hyp_hnwcodefnval_2
      hyp_hnwcodefnval_2
  have p0084 := @g_ovcross B B (syn_cvv) (syn_cvv)
  have p0085 := Nominal.mp p0083 p0084
  have p0086 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B)
      (syn_co B (syn_ccross) B) (syn_cxp B B) p0082 p0085
  have p0087 :=
    @g_fveq2i (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B)
      (syn_cxp B B) (syn_cimage (syn_cres (syn_cid) R)) p0086
  have p0088 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B)
      (syn_cfv (syn_cimage (syn_cres (syn_cid) R))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B))
      (syn_cfv (syn_cimage (syn_cres (syn_cid) R)) (syn_cxp B B)) p0045 p0087
  have p0091 := @g_xpex B B hyp_hnwcodefnval_2 hyp_hnwcodefnval_2
  have p0092 := @g_fvimagecl (syn_cxp B B) (syn_cres (syn_cid) R) p0003 p0091
  have p0093 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B)
      (syn_cfv (syn_cimage (syn_cres (syn_cid) R)) (syn_cxp B B))
      (syn_cima (syn_cres (syn_cid) R) (syn_cxp B B)) p0088 p0092
  have p0094 := @g_resiidima R (syn_cxp B B)
  have p0095 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B)
      (syn_cima (syn_cres (syn_cid) R) (syn_cxp B B)) (syn_cin R (syn_cxp B B)) p0093
      p0094
  have p0098 :=
    @g_opeq12i
      (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B)
      (syn_cin R (syn_cxp B B)) (syn_cfv (syn_cid) B) B p0095 p0073
  have p0099 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
            (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) B)
      (syn_cop (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
            (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B) (syn_cfv (syn_cid) B))
      (syn_cop (syn_cin R (syn_cxp B B)) B) p0026 p0098
  have p0100 :=
    @g_eqtri (syn_cfv (syn_chnwcodefn R) B)
      (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
            (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) B)
      (syn_cop (syn_cin R (syn_cxp B B)) B) p0001 p0099
  exact p0100

@[expose]
noncomputable def g_hnwcutfnvalg (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutfnvalg_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hnwcutfnvalg_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnwcutfnvalg_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chnwcutfn R D) B) (syn_cop (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcutfn R D))
  have p0001 :=
    @g_fveq1i B (syn_chnwcutfn R D) (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D))
      p0000
  have p0002 := @g_idex
  have p0003 := @g_resex (syn_cid) D p0002 hyp_hnwcutfnvalg_2
  have p0004 := @g_wppimagefn (syn_cres (syn_cid) D) p0003
  have p0006 := @g_difex R (syn_cid) hyp_hnwcutfnvalg_1 p0002
  have p0007 := @g_cnvex (syn_cdif R (syn_cid)) p0006
  have p0008 := @g_wppimagefn (syn_ccnv (syn_cdif R (syn_cid))) p0007
  have p0009 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) D))
      (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) p0004 p0008
  have p0010 := (Nominal.classEqRefl (syn_chnwsegfn R D))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_chnwsegfn R D)
      (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
        (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))))
      p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_chnwsegfn R D) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
          (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) (syn_cvv))
      p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_chnwsegfn R D) (syn_cvv)) (.classMem B (syn_cvv)) p0012
      hyp_hnwcutfnvalg_3
  have p0014 := @g_fvco2 (syn_cvv) B (syn_chnwcodefn R) (syn_chnwsegfn R D)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) B)
      (syn_cfv (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) B)
      (syn_cfv (syn_chnwcodefn R) (syn_cfv (syn_chnwsegfn R D) B)) p0001 p0015
  have p0017 :=
    @g_hnwsegfnval B D R hyp_hnwcutfnvalg_1 hyp_hnwcutfnvalg_2 hyp_hnwcutfnvalg_3
  have p0018 :=
    @g_fveq2i (syn_cfv (syn_chnwsegfn R D) B)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) (syn_chnwcodefn R) p0017
  have p0019 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) B)
      (syn_cfv (syn_chnwcodefn R) (syn_cfv (syn_chnwsegfn R D) B))
      (syn_cfv (syn_chnwcodefn R) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)))
      p0016 p0018
  have p0023 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) B p0007 hyp_hnwcutfnvalg_3
  have p0024 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B) hyp_hnwcutfnvalg_2 p0023
  have p0025 :=
    @g_hnwcodefnval (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) R
      hyp_hnwcutfnvalg_1 p0024
  have p0026 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) B)
      (syn_cfv (syn_chnwcodefn R) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)))
      (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)))
      p0019 p0025
  exact p0026

@[expose]
noncomputable def g_hnwcutfnvalcl (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutfnvalcl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (_hyp_hnwcutfnvalcl_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chnwcutfn R D) (syn_csn B)) (syn_chnwcutcode R D B)) :=
  by
  have p0000 := @g_brex R D (syn_cwe)
  have p0001 := Nominal.mp hyp_hnwcutfnvalcl_1 p0000
  have p0002 := @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0001
  have p0005 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0001
  have p0006 := @g_snex B
  have p0007 := @g_hnwcutfnvalg (syn_csn B) D R p0002 p0005 p0006
  have p0008 := (Nominal.classEqRefl (syn_chnwcutcode R D B))
  have p0009 :=
    @g_eqcomi (syn_chnwcutcode R D B)
      (syn_cop (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      p0008
  have p0010 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) (syn_csn B))
      (syn_cop (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      (syn_chnwcutcode R D B) p0007 p0009
  exact p0010

@[expose]
noncomputable def g_hnwcutrelex (D : Class) (R : Class)
    (hyp_hnwcutrelex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcutrel R D) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcutrel R D))
  have p0001 := @g_hnwcutfnex D R hyp_hnwcutrelex_1
  have p0002 := @g_brex R D (syn_cwe)
  have p0003 := Nominal.mp hyp_hnwcutrelex_1 p0002
  have p0004 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0003
  have p0005 := @g_pw1ex D p0004
  have p0006 := @g_resex (syn_chnwcutfn R D) (syn_cpw1 D) p0001 p0005
  have p0007 :=
    @g_eqeltri (syn_chnwcutrel R D) (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (syn_cvv)
      p0000 p0006
  exact p0007

@[expose]
noncomputable def g_hnwcutrelfn (D : Class) (R : Class)
    (hyp_hnwcutrelfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) :=
  by
  have p0000 := @g_hnwcutfnfn D R hyp_hnwcutrelfn_1
  have p0001 := @g_ssv (syn_cpw1 D)
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutfn R D) (syn_cvv)) (syn_wss (syn_cpw1 D) (syn_cvv))
      p0000 p0001
  have p0003 := @g_fnssres (syn_cvv) (syn_cpw1 D) (syn_chnwcutfn R D)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_chnwcutrel R D))
  have p0006 :=
    @g_fneq1i (syn_cpw1 D) (syn_chnwcutrel R D)
      (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
      (syn_wfn (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (syn_cpw1 D)) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_hnwpw1argcl (D : Class) (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv q)) D)
          (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))) :=
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
      ((syn_wa (.classMem (syn_cuni (.cv q)) D)
          (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))).fv :=
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
  have p0000 := @g_elpw1 x (.cv q) D dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv q) (syn_cpw1 D))
      (syn_wrex x D (.classEq (.cv q) (syn_csn (.cv x)))) p0000
  have p0002 := @g_simpr (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))
  have p0003 := @g_id (.classEq (.cv q) (syn_csn (.cv x)))
  have p0004 :=
    @g_unieqd (.classEq (.cv q) (syn_csn (.cv x))) (.cv q) (syn_csn (.cv x)) p0003
  have p0005 := @g_vex x
  have p0006 := @g_unisn (.cv x) p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x))
      (.classEq (.cv q) (syn_csn (.cv x))) p0006
  have p0008 :=
    @g_eqtrd (.classEq (.cv q) (syn_csn (.cv x))) (syn_cuni (.cv q))
      (syn_cuni (syn_csn (.cv x))) (.cv x) p0004 p0007
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x))))
      (.classEq (.cv q) (syn_csn (.cv x))) (.classEq (syn_cuni (.cv q)) (.cv x)) p0002
      p0008
  have p0010 := @g_simpl (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))
  have p0011 :=
    @g_eqeltrd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x))))
      (syn_cuni (.cv q)) (.cv x) D p0009 p0010
  have p0021 :=
    @g_sneqd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x))))
      (syn_cuni (.cv q)) (.cv x) p0009
  have p0022 :=
    @g_eqcomd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x))))
      (syn_csn (syn_cuni (.cv q))) (syn_csn (.cv x)) p0021
  have p0023 :=
    @g_eqtrd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (.cv q)
      (syn_csn (.cv x)) (syn_csn (syn_cuni (.cv q))) p0002 p0022
  have p0024 :=
    @g_jca (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x))))
      (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
      p0011 p0023
  have p0025 :=
    @g_rexlimiva (.classEq (.cv q) (syn_csn (.cv x)))
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      x D dv_cache_0003 p0024
  have p0026 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 D))
      (syn_wrex x D (.classEq (.cv q) (syn_csn (.cv x))))
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0001 p0025
  exact p0026

@[expose]
noncomputable def g_hnwcutrelval (D : Class) (R : Class) (q : Var)
    (hyp_hnwcutrelval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv q))
          (syn_chnwcutcode R D (syn_cuni (.cv q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcutrel R D))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_chnwcutrel R D) (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D))
      p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv q))
        (syn_cfv (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (.cv q)))
      (.classMem (.cv q) (syn_cpw1 D)) p0001
  have p0003 := @g_fvres (.cv q) (syn_cpw1 D) (syn_chnwcutfn R D)
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q))
      (syn_cfv (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (.cv q))
      (syn_cfv (syn_chnwcutfn R D) (.cv q)) p0002 p0003
  have p0005 := @g_hnwpw1argcl D q
  have p0006 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D)
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0007 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 D)) (.cv q) (syn_csn (syn_cuni (.cv q)))
      (syn_chnwcutfn R D) p0006
  have p0008 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q))
      (syn_cfv (syn_chnwcutfn R D) (.cv q))
      (syn_cfv (syn_chnwcutfn R D) (syn_csn (syn_cuni (.cv q)))) p0004 p0007
  have p0009 := @g_vex q
  have p0010 := @g_uniex (.cv q) p0009
  have p0011 := @g_hnwcutfnvalcl (syn_cuni (.cv q)) D R hyp_hnwcutrelval_1 p0010
  have p0012 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnwcutfn R D) (syn_csn (syn_cuni (.cv q))))
        (syn_chnwcutcode R D (syn_cuni (.cv q))))
      (.classMem (.cv q) (syn_cpw1 D)) p0011
  have p0013 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q))
      (syn_cfv (syn_chnwcutfn R D) (syn_csn (syn_cuni (.cv q))))
      (syn_chnwcutcode R D (syn_cuni (.cv q))) p0008 p0012
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

@[expose]
noncomputable def g_hnwcutrelf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutrelf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) :=
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
  have dv_cache_0002 : q ∉ ((syn_cpw1 D)).fv :=
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
  have dv_cache_0003 : q ∉ ((syn_chwcn D)).fv :=
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
  have dv_cache_0004 : q ∉ ((syn_chnwcutrel R D)).fv :=
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
  have p0000 := @g_hnwcutrelfn D R hyp_hnwcutrelf_1
  have p0001 := @g_hnwpw1argcl D q
  have p0002 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D)
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0001
  have p0003 := @g_hnwcutcodecncl (syn_cuni (.cv q)) D R dv_cache_0001 hyp_hnwcutrelf_1
  have p0004 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D)
      (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0002 p0003
  have p0005 := @g_hnwcutrelval D R q hyp_hnwcutrelf_1
  have p0006 :=
    @g_eleq1d (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q))
      (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D) p0005
  have p0007 :=
    @g_mpbird (.classMem (.cv q) (syn_cpw1 D))
      (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0004 p0006
  have p0008 :=
    @g_rgen (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)) q
      (syn_cpw1 D) p0007
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
      (syn_wral q (syn_cpw1 D) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)))
      p0000 p0008
  have p0010 :=
    @g_ffnfv q (syn_cpw1 D) (syn_chwcn D) (syn_chnwcutrel R D) dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0011 :=
    @g_mpbir (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (syn_wral q (syn_cpw1 D)
          (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D))))
      p0009 p0010
  exact p0011

@[expose]
noncomputable def g_sifmap (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))) :=
  by
  have p0000 := @g_ffn A B F
  have p0001 := @g_fnfun A F
  have p0002 := @g_syl (syn_wf F A B) (syn_wfn F A) (syn_wfun F) p0000 p0001
  have p0003 := @g_funsi F
  have p0004 := @g_syl (syn_wf F A B) (syn_wfun F) (syn_wfun (syn_csi F)) p0002 p0003
  have p0005 := @g_funfn (syn_csi F)
  have p0006 :=
    @g_biimpi (syn_wfun (syn_csi F)) (syn_wfn (syn_csi F) (syn_cdm (syn_csi F))) p0005
  have p0007 :=
    @g_syl (syn_wf F A B) (syn_wfun (syn_csi F))
      (syn_wfn (syn_csi F) (syn_cdm (syn_csi F))) p0004 p0006
  have p0008 := @g_dmsi F
  have p0009 :=
    @g_a1i (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F))) (syn_wf F A B) p0008
  have p0011 := @g_fndm A F
  have p0012 := @g_syl (syn_wf F A B) (syn_wfn F A) (.classEq (syn_cdm F) A) p0000 p0011
  have p0013 := @g_pw1eq (syn_cdm F) A
  have p0014 :=
    @g_syl (syn_wf F A B) (.classEq (syn_cdm F) A)
      (.classEq (syn_cpw1 (syn_cdm F)) (syn_cpw1 A)) p0012 p0013
  have p0015 :=
    @g_eqtrd (syn_wf F A B) (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F)) (syn_cpw1 A)
      p0009 p0014
  have p0016 :=
    @g_fneq2d (syn_wf F A B) (syn_cdm (syn_csi F)) (syn_cpw1 A) (syn_csi F) p0015
  have p0017 :=
    @g_mpbid (syn_wf F A B) (syn_wfn (syn_csi F) (syn_cdm (syn_csi F)))
      (syn_wfn (syn_csi F) (syn_cpw1 A)) p0007 p0016
  have p0018 := @g_frn A B F
  have p0019 := @g_pw1ss (syn_crn F) B
  have p0020 :=
    @g_syl (syn_wf F A B) (syn_wss (syn_crn F) B)
      (syn_wss (syn_cpw1 (syn_crn F)) (syn_cpw1 B)) p0018 p0019
  have p0021 := @g_rnsi F
  have p0022 :=
    @g_a1i (.classEq (syn_crn (syn_csi F)) (syn_cpw1 (syn_crn F))) (syn_wf F A B) p0021
  have p0023 :=
    @g_sseq1d (syn_wf F A B) (syn_crn (syn_csi F)) (syn_cpw1 (syn_crn F)) (syn_cpw1 B)
      p0022
  have p0024 :=
    @g_mpbird (syn_wf F A B) (syn_wss (syn_crn (syn_csi F)) (syn_cpw1 B))
      (syn_wss (syn_cpw1 (syn_crn F)) (syn_cpw1 B)) p0020 p0023
  have p0025 :=
    @g_jca (syn_wf F A B) (syn_wfn (syn_csi F) (syn_cpw1 A))
      (syn_wss (syn_crn (syn_csi F)) (syn_cpw1 B)) p0017 p0024
  have p0026 := (Nominal.biimpRefl (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)))
  have p0027 :=
    @g_sylibr (syn_wf F A B)
      (syn_wa (syn_wfn (syn_csi F) (syn_cpw1 A)) (syn_wss (syn_crn (syn_csi F)) (syn_cpw1 B)))
      (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) p0025 p0026
  exact p0027

@[expose]
noncomputable def g_sifvaldv (A : Class) (B : Class) (F : Class) (c : Var)
    (_dv_A_c : c ∉ A.fv) (_dv_B_c : c ∉ B.fv) (_dv_F_c : c ∉ F.fv)
    (hyp_sifvaldv_1 : Nominal.NPrf (syn_wf F A B)) :
    Nominal.NPrf
      (.imp (.classMem (.cv c) A) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c)))
          (syn_csn (syn_cfv F (.cv c))))) :=
  by
  have p0000 := @g_eqid (syn_cfv F (.cv c))
  have p0001 :=
    @g_a1i (.classEq (syn_cfv F (.cv c)) (syn_cfv F (.cv c))) (.classMem (.cv c) A) p0000
  have p0002 := @g_ffn A B F
  have p0003 := Nominal.mp hyp_sifvaldv_1 p0002
  have p0004 := @g_a1i (syn_wfn F A) (.classMem (.cv c) A) p0003
  have p0005 := @g_id (.classMem (.cv c) A)
  have p0006 :=
    @g_jca (.classMem (.cv c) A) (syn_wfn F A) (.classMem (.cv c) A) p0004 p0005
  have p0007 := @g_fnbrfvb A (.cv c) (syn_cfv F (.cv c)) F
  have p0008 :=
    @g_syl (.classMem (.cv c) A) (syn_wa (syn_wfn F A) (.classMem (.cv c) A))
      (syn_wb (.classEq (syn_cfv F (.cv c)) (syn_cfv F (.cv c)))
        (syn_wbr (.cv c) F (syn_cfv F (.cv c))))
      p0006 p0007
  have p0009 :=
    @g_mpbid (.classMem (.cv c) A) (.classEq (syn_cfv F (.cv c)) (syn_cfv F (.cv c)))
      (syn_wbr (.cv c) F (syn_cfv F (.cv c))) p0001 p0008
  have p0010 := @g_vex c
  have p0011 := @g_fvex (.cv c) F
  have p0012 := @g_brsnsi (.cv c) (syn_cfv F (.cv c)) F p0010 p0011
  have p0013 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c))))
        (syn_wbr (.cv c) F (syn_cfv F (.cv c))))
      (.classMem (.cv c) A) p0012
  have p0014 :=
    @g_mpbird (.classMem (.cv c) A)
      (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c))))
      (syn_wbr (.cv c) F (syn_cfv F (.cv c))) p0009 p0013
  have p0015 := @g_sifmap A B F
  have p0016 := Nominal.mp hyp_sifvaldv_1 p0015
  have p0017 := @g_ffn (syn_cpw1 A) (syn_cpw1 B) (syn_csi F)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_a1i (syn_wfn (syn_csi F) (syn_cpw1 A)) (.classMem (.cv c) A) p0018
  have p0020 := @g_snelpw1 (.cv c) A
  have p0021 :=
    @g_biimpri (.classMem (syn_csn (.cv c)) (syn_cpw1 A)) (.classMem (.cv c) A) p0020
  have p0022 :=
    @g_jca (.classMem (.cv c) A) (syn_wfn (syn_csi F) (syn_cpw1 A))
      (.classMem (syn_csn (.cv c)) (syn_cpw1 A)) p0019 p0021
  have p0023 :=
    @g_fnbrfvb (syn_cpw1 A) (syn_csn (.cv c)) (syn_csn (syn_cfv F (.cv c))) (syn_csi F)
  have p0024 :=
    @g_syl (.classMem (.cv c) A)
      (syn_wa (syn_wfn (syn_csi F) (syn_cpw1 A)) (.classMem (syn_csn (.cv c)) (syn_cpw1 A)))
      (syn_wb (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))
        (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c)))))
      p0022 p0023
  have p0025 :=
    @g_mpbird (.classMem (.cv c) A)
      (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))
      (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c)))) p0014 p0024
  exact p0025

@[expose]
noncomputable def g_sifvald (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_sifvald_1 : Nominal.NPrf (syn_wf F A B)) :
    Nominal.NPrf
      (.imp (.classMem C A)
        (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C)))) :=
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
          (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))))).fv :=
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
  have p0000 := @g_elex C A
  have p0001 := @g_eleq1 (.cv c) C A
  have p0002 := @g_sneq (.cv c) C
  have p0003 :=
    @g_fveq2d (.classEq (.cv c) C) (syn_csn (.cv c)) (syn_csn C) (syn_csi F) p0002
  have p0004 := @g_fveq2 (.cv c) C F
  have p0005 := @g_sneqd (.classEq (.cv c) C) (syn_cfv F (.cv c)) (syn_cfv F C) p0004
  have p0006 :=
    @g_eqeq12d (.classEq (.cv c) C) (syn_cfv (syn_csi F) (syn_csn (.cv c)))
      (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F (.cv c)))
      (syn_csn (syn_cfv F C)) p0003 p0005
  have p0007 :=
    @g_imbi12d (.classEq (.cv c) C) (.classMem (.cv c) A) (.classMem C A)
      (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))
      (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0001 p0006
  have p0008 :=
    @g_sifvaldv A B F c dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_sifvald_1
  have p0009 :=
    @g_vtoclg
      (.imp (.classMem (.cv c) A)
        (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))))
      (.imp (.classMem C A)
        (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))))
      c C (syn_cvv) dv_cache_0004 dv_cache_0005 p0007 p0008
  have p0010 :=
    @g_mpcom (.classMem C (syn_cvv)) (.classMem C A)
      (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_hnqmap1valcl (A : Class) (B : Class)
    (hyp_hnqmap1valcl_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_chwcn A))
        (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A)))) :=
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
      ((Wff.imp (.classMem B (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B))
            (syn_cec B (syn_chwniso A))))).fv :=
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
  have p0000 := @g_elex B (syn_chwcn A)
  have p0001 := @g_eleq1 (.cv u) B (syn_chwcn A)
  have p0002 := @g_sneq (.cv u) B
  have p0003 :=
    @g_fveq2d (.classEq (.cv u) B) (syn_csn (.cv u)) (syn_csn B) (syn_chnqmap1 A) p0002
  have p0004 := @g_eceq1 (.cv u) B (syn_chwniso A)
  have p0005 :=
    @g_eqeq12d (.classEq (.cv u) B) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))
      (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec B (syn_chwniso A)) p0003 p0004
  have p0006 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A))) p0001
      p0005
  have p0007 := @g_hnqmap1val u A dv_cache_0001 hyp_hnqmap1valcl_1
  have p0008 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))
          (syn_cec (.cv u) (syn_chwniso A))))
      (.imp (.classMem B (syn_chwcn A))
        (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A))))
      u B (syn_cvv) dv_cache_0002 dv_cache_0003 p0006 p0007
  have p0009 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A))) p0000
      p0008
  exact p0009

@[expose]
noncomputable def g_qmapcompvald (ph : Wff) (A : Class) (B : Class) (G : Class)
    (X : Class) (p : Var) (hyp_qmapcompvald_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_qmapcompvald_2 : Nominal.NPrf (syn_wf G X (syn_cpw1 (syn_chwcn A))))
    (hyp_qmapcompvald_3 : Nominal.NPrf (.imp ph (.classMem (.cv p) X)))
    (hyp_qmapcompvald_4 : Nominal.NPrf (.imp ph (.classEq (syn_cfv G (.cv p)) (syn_csn B))))
    (hyp_qmapcompvald_5 : Nominal.NPrf (.imp ph (.classMem B (syn_chwcn A)))) :
    Nominal.NPrf
      (.imp ph (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p))
          (syn_cec B (syn_chwniso A)))) :=
  by
  have p0000 := @g_ffn X (syn_cpw1 (syn_chwcn A)) G
  have p0001 := Nominal.mp hyp_qmapcompvald_2 p0000
  have p0002 := @g_a1i (syn_wfn G X) ph p0001
  have p0003 := @g_jca ph (syn_wfn G X) (.classMem (.cv p) X) p0002 hyp_qmapcompvald_3
  have p0004 := @g_fvco2 X (.cv p) (syn_chnqmap1 A) G
  have p0005 :=
    @g_syl ph (syn_wa (syn_wfn G X) (.classMem (.cv p) X))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p))
        (syn_cfv (syn_chnqmap1 A) (syn_cfv G (.cv p))))
      p0003 p0004
  have p0006 :=
    @g_fveq2d ph (syn_cfv G (.cv p)) (syn_csn B) (syn_chnqmap1 A) hyp_qmapcompvald_4
  have p0007 :=
    @g_eqtrd ph (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p))
      (syn_cfv (syn_chnqmap1 A) (syn_cfv G (.cv p)))
      (syn_cfv (syn_chnqmap1 A) (syn_csn B)) p0005 p0006
  have p0008 := @g_hnqmap1valcl A B hyp_qmapcompvald_1
  have p0009 :=
    @g_syl ph (.classMem B (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A)))
      hyp_qmapcompvald_5 p0008
  have p0010 :=
    @g_eqtrd ph (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p))
      (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A)) p0007 p0009
  exact p0010

@[expose]
noncomputable def g_hnwcutsirelf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutsirelf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (syn_wf (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D))
        (syn_cpw1 (syn_chwcn D))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_hnwcutrelf D R dv_cache_0001 hyp_hnwcutsirelf_1
  have p0001 := @g_sifmap (syn_cpw1 D) (syn_chwcn D) (syn_chnwcutrel R D)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hnwcutsirelex (D : Class) (R : Class)
    (hyp_hnwcutsirelex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_csi (syn_chnwcutrel R D)) (syn_cvv)) :=
  by
  have p0000 := @g_hnwcutrelex D R hyp_hnwcutsirelex_1
  have p0001 := @g_siex (syn_chnwcutrel R D) p0000
  exact p0001

@[expose]
noncomputable def g_hnwcutfactorf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutfactorf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (syn_wf (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))
        (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_brex R D (syn_cwe)
  have p0001 := Nominal.mp hyp_hnwcutfactorf_1 p0000
  have p0002 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0001
  have p0003 := @g_hnqmap1f D p0002
  have p0004 := @g_hnwcutsirelf D R dv_cache_0001 hyp_hnwcutfactorf_1
  have p0005 :=
    @g_pm3_2i (syn_wf (syn_chnqmap1 D) (syn_cpw1 (syn_chwcn D)) (syn_chnord D))
      (syn_wf (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn D)))
      p0003 p0004
  have p0006 :=
    @g_fco (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn D)) (syn_chnord D)
      (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))
  have p0007 := Nominal.mp p0005 p0006
  exact p0007

@[expose]
noncomputable def g_hnwcutrelvalcld (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutrelvalcld_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D)
        (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B))) :=
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
  have dv_cache_0001 : Disjoint ((syn_cuni (.cv x))).fv (R).fv := by
    exact
      (show Disjoint ((syn_cuni (.cv x))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((Class.cv x)).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ x } : Finset Var)) ((R).fv) from
                    (Finset.disjoint_singleton_left.mpr
                      (show x ∉ (R).fv from (by exact fresh_x_not_R))))))))
  have dv_cache_0002 : x ∉ ((syn_csn B)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cpw1 D)).fv :=
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
      ((Wff.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B))).fv :=
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
  have p0000 := @g_hnwcutrelval D R x hyp_hnwcutrelvalcld_1
  have p0001 :=
    @g_rgen
      (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv x)) (syn_chnwcutcode R D (syn_cuni (.cv x))))
      x (syn_cpw1 D) p0000
  have p0002 := @g_snelpw1 B D
  have p0003 := @g_biimpri (.classMem (syn_csn B) (syn_cpw1 D)) (.classMem B D) p0002
  have p0004 := @g_simpr (.classMem B D) (.classEq (.cv x) (syn_csn B))
  have p0005 :=
    @g_fveq2d (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (.cv x) (syn_csn B)
      (syn_chnwcutrel R D) p0004
  have p0007 :=
    @g_unieqd (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (.cv x) (syn_csn B)
      p0004
  have p0008 := @g_simpl (.classMem B D) (.classEq (.cv x) (syn_csn B))
  have p0009 := @g_unisng B D
  have p0010 :=
    @g_syl (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (.classMem B D)
      (.classEq (syn_cuni (syn_csn B)) B) p0008 p0009
  have p0011 :=
    @g_eqtrd (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (syn_cuni (.cv x))
      (syn_cuni (syn_csn B)) B p0007 p0010
  have p0012 := @g_hnwcutcodeeq3 (syn_cuni (.cv x)) B D R dv_cache_0001
  have p0013 :=
    @g_syl (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B)))
      (.classEq (syn_cuni (.cv x)) B)
      (.classEq (syn_chnwcutcode R D (syn_cuni (.cv x))) (syn_chnwcutcode R D B)) p0011
      p0012
  have p0014 :=
    @g_eqeq12d (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B)))
      (syn_cfv (syn_chnwcutrel R D) (.cv x)) (syn_cfv (syn_chnwcutrel R D) (syn_csn B))
      (syn_chnwcutcode R D (syn_cuni (.cv x))) (syn_chnwcutcode R D B) p0005 p0013
  have p0015 :=
    @g_rspcdv (.classMem B D)
      (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv x)) (syn_chnwcutcode R D (syn_cuni (.cv x))))
      (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B)) x
      (syn_csn B) (syn_cpw1 D) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0003 p0014
  have p0016 :=
    @g_mpi (.classMem B D)
      (syn_wral x (syn_cpw1 D) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv x))
          (syn_chnwcutcode R D (syn_cuni (.cv x)))))
      (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B)) p0001
      p0015
  exact p0016

@[expose]
noncomputable def g_hnwcutsirelval (D : Class) (R : Class) (q : Var)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutsirelval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classEq (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q))
          (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_pw12argcl (.cv q) D
  have p0001 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.cv q)
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csi (syn_chnwcutrel R D))
      p0001
  have p0004 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000
  have p0005 := @g_snelpw1 (syn_cuni (syn_cuni (.cv q))) D
  have p0006 :=
    @g_biimpri (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0005
  have p0007 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0004 p0006
  have p0008 := @g_hnwcutrelf D R dv_cache_0001 hyp_hnwcutsirelval_1
  have p0009 :=
    @g_sifvald (syn_cpw1 D) (syn_chwcn D) (syn_csn (syn_cuni (syn_cuni (.cv q))))
      (syn_chnwcutrel R D) p0008
  have p0010 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D))
      (.classEq (syn_cfv (syn_csi (syn_chnwcutrel R D))
          (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
        (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0007 p0009
  have p0011 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q))
      (syn_cfv (syn_csi (syn_chnwcutrel R D)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0002 p0010
  have p0014 := @g_hnwcutrelvalcld (syn_cuni (syn_cuni (.cv q))) D R hyp_hnwcutsirelval_1
  have p0015 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
        (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
      p0004 p0014
  have p0016 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) p0015
  have p0017 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q))
      (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0011 p0016
  exact p0017

@[expose]
noncomputable def g_hnwcutfactorval (D : Class) (R : Class) (q : Var)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutfactorval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_brex R D (syn_cwe)
  have p0001 := Nominal.mp hyp_hnwcutfactorval_1 p0000
  have p0002 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0001
  have p0003 := @g_hnwcutsirelf D R dv_cache_0001 hyp_hnwcutfactorval_1
  have p0004 := @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0005 := @g_hnwcutsirelval D R q dv_cache_0001 hyp_hnwcutfactorval_1
  have p0006 := @g_pw12argcl (.cv q) D
  have p0007 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_hnwcutcodecncl (syn_cuni (syn_cuni (.cv q))) D R dv_cache_0001
      hyp_hnwcutfactorval_1
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn D)) p0007
      p0008
  have p0010 :=
    @g_qmapcompvald (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) D
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_csi (syn_chnwcutrel R D))
      (syn_cpw1 (syn_cpw1 D)) q p0002 p0003 p0004 p0005 p0009
  exact p0010

@[expose]
noncomputable def g_hnwcutmapfactor (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapfactor_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.classEq (syn_chnwcutmap R D)
        (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))) :=
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
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
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
  have dv_cache_0003 : q ∉ ((syn_chnwcutmap R D)).fv :=
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
    q ∉ ((syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))).fv :=
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
  have p0000 := @g_hnwcutmapval D R q dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0001 := @g_hnwcutfactorval D R q dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0002 :=
    @g_eqcomd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) p0001
  have p0003 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_chnwcutmap R D) (.cv q))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))
      (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q)) p0000
      p0002
  have p0004 :=
    @g_rgen
      (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
        (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q)))
      q (syn_cpw1 (syn_cpw1 D)) p0003
  have p0005 := @g_hnwcutmapf D R dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0006 := @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (syn_chnwcutmap R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_hnwcutfactorf D R dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)
      (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)))
      (syn_wfn (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))
        (syn_cpw1 (syn_cpw1 D)))
      p0007 p0010
  have p0012 :=
    @g_eqfnfv q (syn_cpw1 (syn_cpw1 D)) (syn_chnwcutmap R D)
      (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) dv_cache_0002
      dv_cache_0003 dv_cache_0004
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_mpbir
      (.classEq (syn_chnwcutmap R D) (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))))
      (syn_wral q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q))))
      p0004 p0013
  exact p0014

@[expose]
noncomputable def g_hnwcutmapex (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcutmap R D) (syn_cvv)) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_hnwcutmapfactor D R dv_cache_0001 hyp_hnwcutmapex_1
  have p0001 := @g_brex R D (syn_cwe)
  have p0002 := Nominal.mp hyp_hnwcutmapex_1 p0001
  have p0003 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 := @g_hnqmap1exg D
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_hnwcutsirelex D R hyp_hnwcutmapex_1
  have p0007 := @g_coex (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)) p0005 p0006
  have p0008 :=
    @g_eqeltri (syn_chnwcutmap R D)
      (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_hnwcutmapcardle (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapcardle_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_chncard D)) :=
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
  have dv_cache_0002 : f ∉ ((syn_chnwcutmap R D)).fv :=
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
    f ∉ ((syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))).fv :=
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
  have dv_cache_0004 : f ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
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
  have dv_cache_0005 : f ∉ ((syn_chnord D)).fv :=
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
  have p0000 := @g_hnwcutmapf1 D R dv_cache_0001 hyp_hnwcutmapcardle_1
  have p0001 := @g_hnwcutmapex D R dv_cache_0001 hyp_hnwcutmapcardle_1
  have p0002 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (.cv f) (syn_chnwcutmap R D)
  have p0003 :=
    @g_spcegv (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))
      (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) f
      (syn_chnwcutmap R D) (syn_cvv) dv_cache_0002 dv_cache_0003 p0002
  have p0004 := Nominal.mp p0001 p0003
  have p0005 := Nominal.mp p0000 p0004
  have p0006 := @g_brex R D (syn_cwe)
  have p0007 := Nominal.mp hyp_hnwcutmapcardle_1 p0006
  have p0008 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0007
  have p0009 := @g_pw1ex D p0008
  have p0010 := @g_pw1ex (syn_cpw1 D) p0009
  have p0014 := @g_hnordex D p0008
  have p0015 :=
    @g_nclenc (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) f dv_cache_0004 dv_cache_0005 p0010
      p0014
  have p0016 :=
    @g_mpbir
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_cnc (syn_chnord D)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))) p0005 p0015
  have p0017 := (Nominal.classEqRefl (syn_chncard D))
  have p0018 := @g_eqcomi (syn_chncard D) (syn_cnc (syn_chnord D)) p0017
  have p0019 :=
    @g_breq2i (syn_cnc (syn_chnord D)) (syn_chncard D) (syn_cnc (syn_cpw1 (syn_cpw1 D)))
      (syn_clec) p0018
  have p0020 :=
    @g_mpbi
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_cnc (syn_chnord D)))
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_chncard D)) p0016 p0019
  exact p0020

@[expose]
noncomputable def g_hnwcutmaptc2le (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmaptc2le_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wbr (syn_ctc (syn_ctc (syn_cnc D))) (syn_clec) (syn_chncard D)) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_hnwcutmapcardle D R dv_cache_0001 hyp_hnwcutmaptc2le_1
  have p0001 := @g_brex R D (syn_cwe)
  have p0002 := Nominal.mp hyp_hnwcutmaptc2le_1 p0001
  have p0003 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 := @g_tc2nc D p0003
  have p0005 :=
    @g_breq1i (syn_ctc (syn_ctc (syn_cnc D))) (syn_cnc (syn_cpw1 (syn_cpw1 D)))
      (syn_chncard D) (syn_clec) p0004
  have p0006 :=
    @g_mpbir (syn_wbr (syn_ctc (syn_ctc (syn_cnc D))) (syn_clec) (syn_chncard D))
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_chncard D)) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_hwcnssbase (A : Class) (D : Class)
    (hyp_hwcnssbase_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf (syn_wss (syn_chwcn D) (syn_chwcn A)) :=
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
  have dv_cache_0001 : Disjoint (D).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (show Disjoint (D).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((D).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((D).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((D).fv) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show u ∉ (D).fv from (by exact fresh_u_not_D)))))),
                  (show Disjoint ((D).fv) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((D).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0002 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show u ∉ (A).fv from (by exact fresh_u_not_A)))))),
                  (show Disjoint ((A).fv) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0003 : u ∉ ((syn_chwcn D)).fv :=
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
  have dv_cache_0004 : u ∉ ((syn_chwcn A)).fv :=
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
  have p0000 := @g_hwcnraw u D
  have p0001 := @g_hwcnpair u D
  have p0002 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn D)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)
      p0001
  have p0003 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes D))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes D))
      p0000 p0002
  have p0004 := @g_fvex (.cv u) (syn_c1st)
  have p0005 := @g_fvex (.cv u) (syn_c2nd)
  have p0006 :=
    @g_elhwcodes D (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001
      p0004 p0005
  have p0007 :=
    @g_biimpi
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      p0006
  have p0008 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      p0003 p0007
  have p0009 :=
    @g_simpld (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0008
  have p0019 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0008
  have p0020 := @g_a1i (syn_wss D A) (.classMem (.cv u) (syn_chwcn D)) hyp_hwcnssbase_1
  have p0021 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_c2nd) (.cv u)) D A p0019
      p0020
  have p0022 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A) p0009 p0021
  have p0025 :=
    @g_elhwcodes A (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002
      p0004 p0005
  have p0026 :=
    @g_biimpri
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      p0025
  have p0027 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      p0022 p0026
  have p0029 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn D)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)
      p0001
  have p0030 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes A))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      p0027 p0029
  have p0031 := @g_hwcnsupp u D
  have p0032 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0030 p0031
  have p0033 := @g_elhwcn u A
  have p0034 :=
    @g_biimpri (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0033
  have p0035 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) p0032 p0034
  have p0036 := @g_ssriv u (syn_chwcn D) (syn_chwcn A) dv_cache_0003 dv_cache_0004 p0035
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

@[expose]
noncomputable def g_hwnisobaserestr (v : Var) (u : Var) (A : Class) (D : Class)
    (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (.imp (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))) :=
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
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0002 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)) p0000
  have p0003 := @g_hwcnraw u D
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes D)) p0002 p0003
  have p0006 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)) p0000
  have p0007 := @g_hwcnraw v D
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv v) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcodes D)) p0006 p0007
  have p0009 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D)) p0004
      p0008
  have p0010 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0011 := @g_hwnisohwisob v u A dv_cache_0001
  have p0012 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0011
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0010 p0012
  have p0014 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0013
  have p0015 := @g_brhwisoany v u A h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0016 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0014 p0016
  have p0018 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0017
  have p0019 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0009 p0018
  have p0020 := @g_brhwisoany v u D h dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0021 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwiso D) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) p0019 p0021
  have p0023 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) p0000 p0022
  have p0024 := @g_hwnisohwisob v u D dv_cache_0001
  have p0025 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwniso D) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwiso D) (.cv v)))
      p0024
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
        (syn_wbr (.cv u) (syn_chwiso D) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) p0023 p0025
  have p0027 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))
      p0026
  exact p0027

@[expose]
noncomputable def g_hwnisobaserestrcl (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C))) :=
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
          (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)))).fv :=
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
          (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y))))).fv :=
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
  have p0011 := @g_breq1 (.cv x) B (.cv y) (syn_chwniso A)
  have p0012 := @g_breq1 (.cv x) B (.cv y) (syn_chwniso D)
  have p0013 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
      (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr (.cv x) (syn_chwniso D) (.cv y))
      (syn_wbr B (syn_chwniso D) (.cv y)) p0011 p0012
  have p0014 :=
    @g_imbi12d (.classEq (.cv x) B)
      (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
      (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
      (.imp (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv x) (syn_chwniso D) (.cv y)))
      (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y))) p0010
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
  have p0019 := @g_breq2 (.cv y) C B (syn_chwniso A)
  have p0020 := @g_breq2 (.cv y) C B (syn_chwniso D)
  have p0021 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wbr B (syn_chwniso A) (.cv y))
      (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) (.cv y))
      (syn_wbr B (syn_chwniso D) C) p0019 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv y) C)
      (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
      (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y)))
      (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)) p0018 p0021
  have p0023 := @g_hwnisobaserestr y x A D dv_cache_0001
  have p0024 :=
    @g_vtocl2g
      (.imp (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
        (.imp (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
          (syn_wbr (.cv x) (syn_chwniso D) (.cv y))))
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y))))
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)))
      x y B C (syn_cvv) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0014 p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
        (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)))
      p0006 p0024
  have p0026 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D)))
      (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)) p0025
  exact p0026

@[expose]
noncomputable def g_brlnqrelg (x : Var) (y : Var) (C : Class) (D : Class) (R : Class)
    (V : Class) (W : Class) (dv_C_x : x ∉ C.fv) (_dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C V) (.classMem D W)) (syn_wb (syn_wbr C (syn_clnqrel R) D)
          (syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y)))))) :=
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
    a ∉ ((syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y))))).fv :=
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
    b ∉ ((syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y))))).fv :=
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
    @g_rexeq (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y))) x (.cv a) C dv_cache_0001
      dv_cache_0002
  have p0001 :=
    @g_rexeq (syn_wbr (.cv x) R (.cv y)) y (.cv b) D dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_rexbidv (.classEq (.cv b) D) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y)))
      (syn_wrex y D (syn_wbr (.cv x) R (.cv y))) x C dv_cache_0005 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lnqrel x y R a b
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0004 :=
    @g_brabg (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y))))
      (syn_wrex x C (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y))))
      (syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y)))) a b C D V W
      (syn_clnqrel R) dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0010 p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_ellnkerec (u : Var) (R : Class) (X : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv u) (syn_cec X (syn_clnker R)))
        (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X))) :=
  by
  have p0000 := @g_elec (.cv u) X (syn_clnker R)
  have p0001 := @g_brlnker R X (.cv u)
  have p0002 :=
    @g_bitri (.classMem (.cv u) (syn_cec X (syn_clnker R)))
      (syn_wbr X (syn_clnker R) (.cv u))
      (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ellnkerecg (B : Class) (C : Class) (R : Class) :
    Nominal.NPrf
      (syn_wb (.classMem B (syn_cec C (syn_clnker R)))
        (syn_wa (syn_wbr C R B) (syn_wbr B R C))) :=
  by
  have p0000 := @g_elec B C (syn_clnker R)
  have p0001 := @g_brlnker R C B
  have p0002 :=
    @g_bitri (.classMem B (syn_cec C (syn_clnker R))) (syn_wbr C (syn_clnker R) B)
      (syn_wa (syn_wbr C R B) (syn_wbr B R C)) p0000 p0001
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

@[expose]
noncomputable def g_lnqrelreps (v : Var) (u : Var) (C : Class) (R : Class) (X : Class)
    (Y : Class) (dv_C_u : u ∉ C.fv) (dv_C_v : v ∉ C.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_v : v ∉ R.fv) (dv_X_u : u ∉ X.fv) (dv_X_v : v ∉ X.fv) (dv_Y_u : u ∉ Y.fv)
    (dv_Y_v : v ∉ Y.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb
          (syn_wrex u (syn_cec X (syn_clnker R))
            (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v))))
          (syn_wbr X R Y))) :=
  by
  have dv_cache_0001 : v ∉ ((syn_cec X (syn_clnker R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          dv_X_v, dv_R_v, or_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_wbr X R Y)).fv :=
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
  have dv_cache_0003 : v ∉ ((syn_wbr X R Y)).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))).fv :=
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
  have dv_cache_0008 : v ∉ ((syn_cec Y (syn_clnker R))).fv :=
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
  have dv_cache_0011 : u ∉ ((syn_cec X (syn_clnker R))).fv :=
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
    u ∉ ((syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v)))).fv :=
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
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv u) R (.cv v))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
        (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0002 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem X C) (.classMem Y C))
  have p0003 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0002
  have p0004 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr R (syn_ctrans) C) p0001 p0004
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr R (syn_ctrans) C) p0000 p0005
  have p0009 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem X C) (.classMem Y C))
  have p0010 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem X C) (.classMem Y C) p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem X C) p0001 p0010
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem X C) p0000 p0011
  have p0014 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
        (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0015 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv u) (syn_cec X (syn_clnker R)))
      (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0014
  have p0016 := @g_ellnkerec v R Y
  have p0017 :=
    @g_biimpi (.classMem (.cv v) (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0016
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv v) (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0015 p0017
  have p0019 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y) p0018
  have p0022 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0002
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wss R (syn_cxp C C)) p0001 p0022
  have p0024 :=
    @g_ssbrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      R (syn_cxp C C) (.cv v) Y p0023
  have p0025 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv v) R Y) (syn_wbr (.cv v) (syn_cxp C C) Y) p0019 p0024
  have p0026 := @g_brxp (.cv v) Y C C
  have p0027 :=
    @g_biimpi (syn_wbr (.cv v) (syn_cxp C C) Y)
      (syn_wa (.classMem (.cv v) C) (.classMem Y C)) p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv v) (syn_cxp C C) Y) (syn_wa (.classMem (.cv v) C) (.classMem Y C))
      p0025 p0027
  have p0029 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv v) C) (.classMem Y C) p0028
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv v) C) p0000 p0029
  have p0034 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem X C) (.classMem Y C) p0009
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem Y C) p0001 p0034
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem Y C) p0000 p0035
  have p0052 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv u) (syn_cec X (syn_clnker R)))
      (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0014
  have p0053 := @g_ellnkerec u R X
  have p0054 :=
    @g_biimpi (.classMem (.cv u) (syn_cec X (syn_clnker R)))
      (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0053
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv u) (syn_cec X (syn_clnker R)))
      (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0052 p0054
  have p0056 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X) p0055
  have p0061 :=
    @g_ssbrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      R (syn_cxp C C) X (.cv u) p0023
  have p0062 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X R (.cv u)) (syn_wbr X (syn_cxp C C) (.cv u)) p0056 p0061
  have p0063 := @g_brxp X (.cv u) C C
  have p0064 :=
    @g_biimpi (syn_wbr X (syn_cxp C C) (.cv u))
      (syn_wa (.classMem X C) (.classMem (.cv u) C)) p0063
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X (syn_cxp C C) (.cv u)) (syn_wa (.classMem X C) (.classMem (.cv u) C))
      p0062 p0064
  have p0066 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem X C) (.classMem (.cv u) C) p0065
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv u) C) p0000 p0066
  have p0093 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X R (.cv u)) p0000 p0056
  have p0094 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv u) R (.cv v))
  have p0095 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      C R X (.cv u) (.cv v) p0006 p0012 p0067 p0030 p0093 p0094
  have p0103 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv v) R Y) p0000 p0019
  have p0104 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)))
      C R X (.cv v) Y p0006 p0012 p0030 p0036 p0095 p0103
  have p0105 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) p0104
  have p0106 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X R Y)
  have p0112 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr R (syn_ctrans) C) p0106 p0005
  have p0130 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv u) C) p0106 p0066
  have p0136 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem Y C) p0106 p0035
  have p0154 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem (.cv v) C) p0106 p0029
  have p0185 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (.classMem X C) p0106 p0011
  have p0198 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X) p0055
  have p0199 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv u) R X) p0106 p0198
  have p0200 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X R Y)
  have p0201 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      C R (.cv u) X Y p0112 p0130 p0185 p0136 p0199 p0200
  have p0208 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y) p0018
  have p0209 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr Y R (.cv v)) p0106 p0208
  have p0210 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
          (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
            (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y))
      C R (.cv u) Y (.cv v) p0112 p0130 p0136 p0154 p0201 p0209
  have p0211 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr X R Y) (syn_wbr (.cv u) R (.cv v)) p0210
  have p0212 :=
    @g_impbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) p0105 p0211
  have p0213 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R)))
          (.classMem (.cv v) (syn_cec Y (syn_clnker R)))))
      (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) p0212
  have p0214 :=
    @g_rexlimdvva
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) u v (syn_cec X (syn_clnker R))
      (syn_cec Y (syn_clnker R)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0213
  have p0215 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr X R Y)
  have p0218 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0003
  have p0221 :=
    @g_refd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      C R X p0218 p0010
  have p0228 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr X R X) (syn_wbr X R X) p0221 p0221
  have p0229 := @g_elec X X (syn_clnker R)
  have p0230 := @g_brlnker R X X
  have p0231 :=
    @g_bitri (.classMem X (syn_cec X (syn_clnker R))) (syn_wbr X (syn_clnker R) X)
      (syn_wa (syn_wbr X R X) (syn_wbr X R X)) p0229 p0230
  have p0232 :=
    @g_biimpri (.classMem X (syn_cec X (syn_clnker R)))
      (syn_wa (syn_wbr X R X) (syn_wbr X R X)) p0231
  have p0233 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr X R X) (syn_wbr X R X)) (.classMem X (syn_cec X (syn_clnker R)))
      p0228 p0232
  have p0234 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem X (syn_cec X (syn_clnker R))) p0215 p0233
  have p0241 :=
    @g_refd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      C R Y p0218 p0034
  have p0248 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr Y R Y) (syn_wbr Y R Y) p0241 p0241
  have p0249 := @g_elec Y Y (syn_clnker R)
  have p0250 := @g_brlnker R Y Y
  have p0251 :=
    @g_bitri (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wbr Y (syn_clnker R) Y)
      (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)) p0249 p0250
  have p0252 :=
    @g_biimpri (.classMem Y (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)) p0251
  have p0253 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)) (.classMem Y (syn_cec Y (syn_clnker R)))
      p0248 p0252
  have p0254 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wbr X R Y))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem Y (syn_cec Y (syn_clnker R))) p0215 p0253
  have p0255 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr X R Y)
  have p0256 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wbr X R Y))
      (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wbr X R Y) p0254 p0255
  have p0257 := @g_breq2 (.cv v) Y X R
  have p0258 :=
    @g_rspcev (syn_wbr X R (.cv v)) (syn_wbr X R Y) v Y (syn_cec Y (syn_clnker R))
      dv_cache_0007 dv_cache_0008 dv_cache_0003 p0257
  have p0259 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wbr X R Y))
      (syn_wa (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wbr X R Y))
      (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v))) p0256 p0258
  have p0260 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wbr X R Y))
      (.classMem X (syn_cec X (syn_clnker R)))
      (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v))) p0234 p0259
  have p0261 := @g_breq1 (.cv u) X (.cv v) R
  have p0262 :=
    @g_rexbidv (.classEq (.cv u) X) (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R (.cv v)) v
      (syn_cec Y (syn_clnker R)) dv_cache_0009 p0261
  have p0263 :=
    @g_rspcev (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))
      (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v))) u X
      (syn_cec X (syn_clnker R)) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0262
  have p0264 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wbr X R Y))
      (syn_wa (.classMem X (syn_cec X (syn_clnker R)))
        (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v))))
      (syn_wrex u (syn_cec X (syn_clnker R))
        (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v))))
      p0260 p0263
  have p0265 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr X R Y)
      (syn_wrex u (syn_cec X (syn_clnker R))
        (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v))))
      p0264
  have p0266 :=
    @g_impbid
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wrex u (syn_cec X (syn_clnker R))
        (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v))))
      (syn_wbr X R Y) p0214 p0265
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

@[expose]
noncomputable def g_lnkerexg (R : Class) :
    Nominal.NPrf (.imp (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnker R))
  have p0001 := @g_id (.classMem R (syn_cvv))
  have p0002 := @g_cnvexg R (syn_cvv)
  have p0003 :=
    @g_jca (.classMem R (syn_cvv)) (.classMem R (syn_cvv))
      (.classMem (syn_ccnv R) (syn_cvv)) p0001 p0002
  have p0004 := @g_inexg R (syn_ccnv R) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem R (syn_cvv))
      (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv)))
      (.classMem (syn_cin R (syn_ccnv R)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem R (syn_cvv)) (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cvv)
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_brlnqrelkern (C : Class) (R : Class) (X : Class) (Y : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem R (syn_cvv)) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wb
          (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
          (syn_wbr X R Y))) :=
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
  have dv_cache_0001 : u ∉ ((syn_cec X (syn_clnker R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          fresh_u_not_X, fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((syn_cec X (syn_clnker R))).fv :=
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
  have dv_cache_0003 : u ∉ ((syn_cec Y (syn_clnker R))).fv :=
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
  have dv_cache_0004 : v ∉ ((syn_cec Y (syn_clnker R))).fv :=
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
    @g_simpl (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0001 := (Nominal.classEqRefl (syn_clnker R))
  have p0002 := @g_id (.classMem R (syn_cvv))
  have p0003 := @g_cnvexg R (syn_cvv)
  have p0004 :=
    @g_jca (.classMem R (syn_cvv)) (.classMem R (syn_cvv))
      (.classMem (syn_ccnv R) (syn_cvv)) p0002 p0003
  have p0005 := @g_inexg R (syn_ccnv R) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem R (syn_cvv))
      (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv)))
      (.classMem (syn_cin R (syn_ccnv R)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl5eqel (.classMem R (syn_cvv)) (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cvv)
      p0001 p0006
  have p0008 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0000 p0007
  have p0009 := @g_ecexg X (syn_cvv) (syn_clnker R)
  have p0010 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem (syn_clnker R) (syn_cvv))
      (.classMem (syn_cec X (syn_clnker R)) (syn_cvv)) p0008 p0009
  have p0020 := @g_ecexg Y (syn_cvv) (syn_clnker R)
  have p0021 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem (syn_clnker R) (syn_cvv))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)) p0008 p0020
  have p0022 :=
    @g_jca
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem (syn_cec X (syn_clnker R)) (syn_cvv))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)) p0010 p0021
  have p0023 :=
    @g_brlnqrelg u v (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) R (syn_cvv)
      (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0024 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (.classMem (syn_cec X (syn_clnker R)) (syn_cvv))
        (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)))
      (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
        (syn_wrex u (syn_cec X (syn_clnker R))
          (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))))
      p0022 p0023
  have p0025 :=
    @g_simpr (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0026 :=
    @g_lnqrelreps v u C R X Y dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0007
  have p0027 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wb (syn_wrex u (syn_cec X (syn_clnker R))
          (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))) (syn_wbr X R Y))
      p0025 p0026
  have p0028 :=
    @g_bitrd
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
      (syn_wrex u (syn_cec X (syn_clnker R))
        (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v))))
      (syn_wbr X R Y) p0024 p0027
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

@[expose]
noncomputable def g_lnqrelexg (R : Class) :
    Nominal.NPrf (.imp (.classMem R (syn_cvv)) (.classMem (syn_clnqrel R) (syn_cvv))) :=
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
  have dv_cache_0003 : t ∉ ((syn_wbr (.cv x) R (.cv y))).fv :=
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
  have dv_cache_0004 : u ∉ ((syn_wbr (.cv x) R (.cv y))).fv :=
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
  have dv_cache_0005 : t ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0006 : u ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0007 : t ∉ ((syn_csn (.cv y))).fv :=
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
  have dv_cache_0008 : u ∉ ((syn_csn (.cv y))).fv :=
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
      ((syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
          (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)))).fv :=
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
      ((syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv :=
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
  have dv_cache_0019 : t ∉ ((syn_ccom (syn_csset) (syn_csi R))).fv :=
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
  have dv_cache_0020 : t ∉ ((syn_ccnv (syn_csset))).fv :=
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
  have dv_cache_0023 : u ∉ ((syn_csset)).fv :=
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
  have dv_cache_0024 : u ∉ ((syn_csi R)).fv :=
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
  have dv_cache_0029 : u ∉ ((syn_wbr (.cv t) (syn_csset) (.cv a))).fv :=
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
      ((syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv :=
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
      ((syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv :=
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
  have dv_cache_0032 : a ∉ ((syn_clnqrel R)).fv :=
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
  have dv_cache_0033 : b ∉ ((syn_clnqrel R)).fv :=
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
    a ∉ ((syn_ccom (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset)))).fv :=
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
    b ∉ ((syn_ccom (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset)))).fv :=
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
    @g_r2ex (syn_wbr (.cv x) R (.cv y)) x y (.cv a) (.cv b) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_19_41vv
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classEq (.cv u) (syn_csn (.cv y)))))
      (syn_wbr (.cv x) R (.cv y)) t u dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anass
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
      (syn_wbr (.cv x) R (.cv y))
  have p0003 :=
    @g_n_2exbii
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
            (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
          (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
          (syn_wbr (.cv x) R (.cv y))))
      t u p0002
  have p0004 :=
    @g_ancom
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
  have p0005 :=
    (Nominal.biimpRefl
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))))
  have p0006 :=
    @g_bitr4i
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classEq (.cv u) (syn_csn (.cv y)))))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))))
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))))
      p0004 p0005
  have p0007 :=
    @g_n_2exbii
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classEq (.cv u) (syn_csn (.cv y)))))
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))))
      t u p0006
  have p0008 := @g_snex (.cv x)
  have p0009 := @g_snex (.cv y)
  have p0010 := @g_breq1 (.cv t) (syn_csn (.cv x)) (.cv a) (syn_csset)
  have p0011 :=
    @g_anbi1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) (syn_csset) (.cv a))
      (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
      (syn_wbr (.cv u) (syn_csset) (.cv b)) p0010
  have p0012 := @g_breq1 (.cv u) (syn_csn (.cv y)) (.cv b) (syn_csset)
  have p0013 :=
    @g_anbi2d (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv u) (syn_csset) (.cv b))
      (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b))
      (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) p0012
  have p0014 :=
    @g_ceqsex2v
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
        (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
        (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)))
      t u (syn_csn (.cv x)) (syn_csn (.cv y)) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0008 p0009 p0011 p0013
  have p0015 := @g_vex x
  have p0016 := @g_vex a
  have p0017 := @g_brssetsn (.cv x) (.cv a) p0015 p0016
  have p0018 := @g_vex y
  have p0019 := @g_vex b
  have p0020 := @g_brssetsn (.cv y) (.cv b) p0018 p0019
  have p0021 :=
    @g_anbi12i (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (.classMem (.cv x) (.cv a))
      (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)) (.classMem (.cv y) (.cv b)) p0017
      p0020
  have p0022 :=
    @g_n_3bitri
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b)))
            (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))))))
      (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv t) (syn_csn (.cv x)))
            (.classEq (.cv u) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))))))
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a))
        (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)))
      (syn_wa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b))) p0007 p0014 p0021
  have p0023 :=
    @g_anbi1i
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b)))
            (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))))))
      (syn_wa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
      (syn_wbr (.cv x) R (.cv y)) p0022
  have p0024 :=
    @g_n_3bitr3i
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b)))
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wa (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b)))
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                (.classEq (.cv u) (syn_csn (.cv y))))))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
        (syn_wbr (.cv x) R (.cv y)))
      p0001 p0003 p0023
  have p0025 :=
    @g_n_2exbii
      (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
        (syn_wbr (.cv x) R (.cv y)))
      x y p0024
  have p0026 :=
    @g_bitr4i (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y))))
      (syn_wex x (syn_wex y
          (syn_wa (syn_wa (.classMem (.cv x) (.cv a)) (.classMem (.cv y) (.cv b)))
            (syn_wbr (.cv x) R (.cv y)))))
      (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      p0000 p0025
  have p0029 :=
    @g_brlnqrelg x y (.cv a) (.cv b) R (syn_cvv) (syn_cvv) dv_cache_0012 dv_cache_0001
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0002
  have p0030 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv)) (.classMem (.cv b) (syn_cvv))
      (syn_wb (syn_wbr (.cv a) (syn_clnqrel R) (.cv b))
        (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y)))))
      p0016 p0019 p0029
  have p0031 :=
    @g_brco t (.cv a) (.cv b) (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0032 := @g_brcnv (.cv a) (.cv t) (syn_csset)
  have p0033 :=
    @g_brco u (.cv t) (.cv b) (syn_csset) (syn_csi R) dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024
  have p0034 :=
    @g_brsi x y (.cv t) (.cv u) R dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
      dv_cache_0015 dv_cache_0016 dv_cache_0002
  have p0035 :=
    (Nominal.biimpRefl
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y))))
  have p0036 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wbr (.cv x) R (.cv y)))
      x y p0035
  have p0037 :=
    @g_bitri (syn_wbr (.cv t) (syn_csi R) (.cv u))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x)))
            (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      p0034 p0036
  have p0038 :=
    @g_anbi2ci (syn_wbr (.cv t) (syn_csi R) (.cv u))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wbr (.cv u) (syn_csset) (.cv b)) p0037
  have p0039 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv t) (syn_csi R) (.cv u)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))))
      u p0038
  have p0040 :=
    @g_bitri (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi R)) (.cv b))
      (syn_wex u (syn_wa (syn_wbr (.cv t) (syn_csi R) (.cv u))
          (syn_wbr (.cv u) (syn_csset) (.cv b))))
      (syn_wex u (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      p0033 p0039
  have p0041 :=
    @g_anbi12i (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
      (syn_wbr (.cv t) (syn_csset) (.cv a))
      (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi R)) (.cv b))
      (syn_wex u (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      p0032 p0040
  have p0042 :=
    @g_n_19_42v (syn_wbr (.cv t) (syn_csset) (.cv a))
      (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))))
      u dv_cache_0029
  have p0043 :=
    @g_n_19_42vv
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
        (syn_wbr (.cv x) R (.cv y)))
      x y dv_cache_0030 dv_cache_0031
  have p0044 :=
    @g_anass (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))
  have p0045 :=
    @g_bitr2i
      (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))))
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))))
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
        (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      p0043 p0044
  have p0046 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
        (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
              (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
              (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
              (syn_wbr (.cv x) R (.cv y))))))
      u p0045
  have p0047 :=
    @g_n_3bitr2i
      (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
        (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi R)) (.cv b)))
      (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wex u
          (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      (syn_wex u (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      (syn_wex u (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      p0041 p0042 p0046
  have p0048 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
        (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi R)) (.cv b)))
      (syn_wex u (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                  (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
      t p0047
  have p0049 :=
    @g_exrot4
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
          (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
          (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
          (syn_wbr (.cv x) R (.cv y))))
      t u x y
  have p0050 :=
    @g_n_3bitri
      (syn_wbr (.cv a)
        (syn_ccom (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset))) (.cv b))
      (syn_wex t (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t))
          (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi R)) (.cv b))))
      (syn_wex t (syn_wex u (syn_wex x (syn_wex y (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      p0031 p0048 p0049
  have p0051 :=
    @g_n_3bitr4i (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y))))
      (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa
                (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a))
                  (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa
                  (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
                    (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))
      (syn_wbr (.cv a) (syn_clnqrel R) (.cv b))
      (syn_wbr (.cv a)
        (syn_ccom (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset))) (.cv b))
      p0026 p0030 p0050
  have p0052 :=
    @g_eqbrriv a b (syn_clnqrel R)
      (syn_ccom (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset))) dv_cache_0032
      dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 p0051
  have p0053 := @g_ssetex
  have p0054 := @g_a1i (.classMem (syn_csset) (syn_cvv)) (.classMem R (syn_cvv)) p0053
  have p0055 := @g_siexg R (syn_cvv)
  have p0056 :=
    @g_jca (.classMem R (syn_cvv)) (.classMem (syn_csset) (syn_cvv))
      (.classMem (syn_csi R) (syn_cvv)) p0054 p0055
  have p0057 := @g_coexg (syn_csset) (syn_csi R) (syn_cvv) (syn_cvv)
  have p0058 :=
    @g_syl (.classMem R (syn_cvv))
      (syn_wa (.classMem (syn_csset) (syn_cvv)) (.classMem (syn_csi R) (syn_cvv)))
      (.classMem (syn_ccom (syn_csset) (syn_csi R)) (syn_cvv)) p0056 p0057
  have p0060 := @g_cnvexg (syn_csset) (syn_cvv)
  have p0061 := Nominal.mp p0053 p0060
  have p0062 :=
    @g_a1i (.classMem (syn_ccnv (syn_csset)) (syn_cvv)) (.classMem R (syn_cvv)) p0061
  have p0063 :=
    @g_jca (.classMem R (syn_cvv))
      (.classMem (syn_ccom (syn_csset) (syn_csi R)) (syn_cvv))
      (.classMem (syn_ccnv (syn_csset)) (syn_cvv)) p0058 p0062
  have p0064 :=
    @g_coexg (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset)) (syn_cvv) (syn_cvv)
  have p0065 :=
    @g_syl (.classMem R (syn_cvv))
      (syn_wa (.classMem (syn_ccom (syn_csset) (syn_csi R)) (syn_cvv))
        (.classMem (syn_ccnv (syn_csset)) (syn_cvv)))
      (.classMem (syn_ccom (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset))) (syn_cvv))
      p0063 p0064
  have p0066 :=
    @g_syl5eqel (.classMem R (syn_cvv)) (syn_clnqrel R)
      (syn_ccom (syn_ccom (syn_csset) (syn_csi R)) (syn_ccnv (syn_csset))) (syn_cvv) p0052
      p0065
  exact p0066

@[expose]
noncomputable def g_lnquoexg (C : Class) (R : Class) (_dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
        (.classMem (syn_clnquo R C) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnquo R C))
  have p0001 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 := @g_lnkerexg R
  have p0003 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0001 p0002
  have p0004 := @g_simpr (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0005 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnker R) (syn_cvv)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 := @g_qsexg C (syn_clnker R) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_cqs C (syn_clnker R)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_syl5eqel (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_clnquo R C)
      (syn_cqs C (syn_clnker R)) (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_lnqordexg (C : Class) (R : Class) (_dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
        (.classMem (syn_clnqord R C) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnqord R C))
  have p0001 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 := @g_lnqrelexg R
  have p0003 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem R (syn_cvv)) (.classMem (syn_clnqrel R) (syn_cvv)) p0001 p0002
  have p0004 := (Nominal.classEqRefl (syn_clnquo R C))
  have p0006 := @g_lnkerexg R
  have p0007 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0001 p0006
  have p0008 := @g_simpr (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0009 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnker R) (syn_cvv)) (.classMem C (syn_cvv)) p0007 p0008
  have p0010 := @g_qsexg C (syn_clnker R) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_cqs C (syn_clnker R)) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_syl5eqel (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_clnquo R C)
      (syn_cqs C (syn_clnker R)) (syn_cvv) p0004 p0011
  have p0022 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnquo R C) (syn_cvv)) (.classMem (syn_clnquo R C) (syn_cvv)) p0012
      p0012
  have p0023 := @g_xpexg (syn_clnquo R C) (syn_clnquo R C) (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (.classMem (syn_clnquo R C) (syn_cvv)) (.classMem (syn_clnquo R C) (syn_cvv)))
      (.classMem (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cvv)) p0022 p0023
  have p0025 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnqrel R) (syn_cvv))
      (.classMem (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cvv)) p0003 p0024
  have p0026 :=
    @g_inexg (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cvv)
      (syn_cvv)
  have p0027 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (.classMem (syn_clnqrel R) (syn_cvv))
        (.classMem (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cvv)))
      (.classMem (syn_cin (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)))
        (syn_cvv))
      p0025 p0026
  have p0028 :=
    @g_syl5eqel (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_clnqord R C)
      (syn_cin (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))) (syn_cvv)
      p0000 p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end
