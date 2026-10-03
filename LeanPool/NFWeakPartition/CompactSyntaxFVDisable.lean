/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.CompactSyntaxFV
public import LeanPool.NFWeakPartition.CompactSyntaxFVExplicit

/-! NF weak partition development: CompactSyntaxFVDisable. -/


public section

/-! Disable the legacy global simp registration; use explicit FV lemmas. -/

attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_wtru
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wb NFChoice.Compiler.CompactSyntaxFV.fv_syn_wo
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wa NFChoice.Compiler.CompactSyntaxFV.fv_syn_w3o
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_w3a
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wnan
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wex
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wnf
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wsb
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_weu
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wmo
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_wnfc
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wne
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wral
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wrex
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wreu
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wrmo
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_crab
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cvv
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wsbc
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csb
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cnin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ccompl
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_cin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cun
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cdif
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csymdif
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wss
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wpss
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_c0 NFChoice.Compiler.CompactSyntaxFV.fv_syn_cif
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cpw
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csn
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cpr
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ctp
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_cuni
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cint
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ciun
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_copk
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_c1c
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cpw1
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cuni1
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cxpk
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ccnvk
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cins2k
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cins3k
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cimak
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_ccomk
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cp6
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csik
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cssetk
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cimagek
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cidk
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cio
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_c0c
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cplc
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cnnc
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_clefin
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_cltfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cncfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ctfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cevenfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_coddfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wsfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cspfin
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cphi
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cop
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cproj1
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cproj2
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_copab
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_wbr
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_c1st
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cswap
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csset
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ccom
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cima
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csi
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cid
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cxp
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ccnv
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_crn
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cdm
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_cres
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wfun
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wfn NFChoice.Compiler.CompactSyntaxFV.fv_syn_wf
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wf1
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wfo
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_wf1o
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cfv
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_c2nd
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_co
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_coprab
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cmpt
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_cmpt2
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ctxp
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cfix
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ccup
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cdisj
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_caddcfn
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ccompose
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cins2
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cins3
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cimage
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cins4
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csi3
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_cfuns
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cfns
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cpw1fn
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cfullfun
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cclos1
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ctrans
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cref
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cantisym
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cpartial
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cconnex
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cstrict
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cfound
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_cwe
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_csym
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cer
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cec
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cqs
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cmap
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cen
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cncs
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_clec
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cltc
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cnc
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ctc
attribute [-simp] NFChoice.Compiler.CompactSyntaxFV.fv_syn_c2c
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_c3c
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cce
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_ctcfn
  NFChoice.Compiler.CompactSyntaxFV.fv_syn_cspac
