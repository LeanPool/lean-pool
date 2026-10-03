/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part049`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_sbthlem1 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (G : Class) (X : Class) (hyp_sbthlem1_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_sbthlem1_2 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_sbthlem1_3 : Nominal.NPrf (.classEq G (syn_cclos1 (syn_cdif X (syn_crn R)) R)))
    (hyp_sbthlem1_4 : Nominal.NPrf (.classEq A (syn_cin X G)))
    (hyp_sbthlem1_5 : Nominal.NPrf (.classEq B (syn_cdif X G)))
    (hyp_sbthlem1_6 : Nominal.NPrf (.classEq C (syn_cin (syn_crn R) G)))
    (hyp_sbthlem1_7 : Nominal.NPrf (.classEq D (syn_cdif (syn_crn R) G))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
          (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
        (syn_wbr (syn_crn R) (syn_cen) X)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf1 R (syn_cdm R) (syn_crn R)))
  have p0001 := @g_ssid (syn_crn R)
  have p0002 := (Nominal.biimpRefl (syn_wf R (syn_cdm R) (syn_crn R)))
  have p0003 :=
    @g_mpbiran2 (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfn R (syn_cdm R))
      (syn_wss (syn_crn R) (syn_crn R)) p0001 p0002
  have p0004 := @g_funfn R
  have p0005 :=
    @g_bitr4i (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfn R (syn_cdm R)) (syn_wfun R)
      p0003 p0004
  have p0006 :=
    @g_anbi1i (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfun R) (syn_wfun (syn_ccnv R))
      p0005
  have p0007 :=
    @g_bitri (syn_wf1 R (syn_cdm R) (syn_crn R))
      (syn_wa (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfun (syn_ccnv R)))
      (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) p0000 p0006
  have p0008 :=
    @g_biimpri (syn_wf1 R (syn_cdm R) (syn_crn R))
      (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) p0007
  have p0009 := @g_inss1 X G
  have p0010 := @g_sstr (syn_cin X G) X (syn_cdm R)
  have p0011 :=
    @g_mpan (syn_wss (syn_cin X G) X) (syn_wss X (syn_cdm R))
      (syn_wss (syn_cin X G) (syn_cdm R)) p0009 p0010
  have p0012 :=
    @g_syl5eqss (syn_wss X (syn_cdm R)) A (syn_cin X G) (syn_cdm R) hyp_sbthlem1_4 p0011
  have p0013 :=
    @g_adantr (syn_wss X (syn_cdm R)) (syn_wss A (syn_cdm R)) (syn_wss (syn_crn R) X)
      p0012
  have p0014 := @g_f1ores (syn_cdm R) (syn_crn R) A R
  have p0015 :=
    @g_syl2an (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
      (syn_wf1 R (syn_cdm R) (syn_crn R)) (syn_wss A (syn_cdm R))
      (syn_wf1o (syn_cres R A) A (syn_cima R A))
      (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)) p0008 p0013 p0014
  have p0016 := @g_rnex R hyp_sbthlem1_1
  have p0017 := @g_difex X (syn_crn R) hyp_sbthlem1_2 p0016
  have p0018 := @g_clos1ex R (syn_cdif X (syn_crn R)) p0017 hyp_sbthlem1_1
  have p0019 :=
    @g_eqeltri G (syn_cclos1 (syn_cdif X (syn_crn R)) R) (syn_cvv) hyp_sbthlem1_3 p0018
  have p0020 := @g_inex X G hyp_sbthlem1_2 p0019
  have p0021 := @g_eqeltri A (syn_cin X G) (syn_cvv) hyp_sbthlem1_4 p0020
  have p0022 := @g_resex R A hyp_sbthlem1_1 p0021
  have p0023 := @g_f1oen A (syn_cima R A) (syn_cres R A) p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wf1o (syn_cres R A) A (syn_cima R A)) (syn_wbr A (syn_cen) (syn_cima R A))
      p0015 p0023
  have p0025 :=
    @g_clos1baseima G R (syn_cdif X (syn_crn R)) p0017 hyp_sbthlem1_1 hyp_sbthlem1_3
  have p0026 :=
    @g_ineq2i G (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) (syn_crn R) p0025
  have p0027 := @g_indi (syn_crn R) (syn_cdif X (syn_crn R)) (syn_cima R G)
  have p0028 := @g_disjdif (syn_crn R) X
  have p0029 :=
    @g_uneq1i (syn_cin (syn_crn R) (syn_cdif X (syn_crn R))) (syn_c0)
      (syn_cin (syn_crn R) (syn_cima R G)) p0028
  have p0030 := @g_uncom (syn_c0) (syn_cin (syn_crn R) (syn_cima R G))
  have p0031 := @g_un0 (syn_cin (syn_crn R) (syn_cima R G))
  have p0032 :=
    @g_eqtri (syn_cun (syn_c0) (syn_cin (syn_crn R) (syn_cima R G)))
      (syn_cun (syn_cin (syn_crn R) (syn_cima R G)) (syn_c0))
      (syn_cin (syn_crn R) (syn_cima R G)) p0030 p0031
  have p0033 :=
    @g_n_3eqtri (syn_cin (syn_crn R) (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)))
      (syn_cun (syn_cin (syn_crn R) (syn_cdif X (syn_crn R)))
        (syn_cin (syn_crn R) (syn_cima R G)))
      (syn_cun (syn_c0) (syn_cin (syn_crn R) (syn_cima R G)))
      (syn_cin (syn_crn R) (syn_cima R G)) p0027 p0029 p0032
  have p0034 :=
    @g_n_3eqtri C (syn_cin (syn_crn R) G)
      (syn_cin (syn_crn R) (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)))
      (syn_cin (syn_crn R) (syn_cima R G)) hyp_sbthlem1_6 p0026 p0033
  have p0035 := @g_inss2 (syn_crn R) (syn_cima R G)
  have p0036 :=
    @g_a1i (syn_wss (syn_cin (syn_crn R) (syn_cima R G)) (syn_cima R G))
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      p0035
  have p0037 :=
    @g_syl5eqss
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      C (syn_cin (syn_crn R) (syn_cima R G)) (syn_cima R G) p0034 p0036
  have p0038 := @g_imassrn R G
  have p0039 :=
    @g_simprr (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wss X (syn_cdm R))
      (syn_wss (syn_crn R) X)
  have p0040 :=
    @g_syl5ss
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_cima R G) (syn_crn R) X p0038 p0039
  have p0041 := @g_difss X (syn_crn R)
  have p0042 :=
    @g_jctil
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wss (syn_cima R G) X) (syn_wss (syn_cdif X (syn_crn R)) X) p0040 p0041
  have p0043 := @g_unss (syn_cdif X (syn_crn R)) (syn_cima R G) X
  have p0044 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wa (syn_wss (syn_cdif X (syn_crn R)) X) (syn_wss (syn_cima R G) X))
      (syn_wss (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) X) p0042 p0043
  have p0045 :=
    @g_syl5eqss
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      G (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) X p0025 p0044
  have p0046 := @g_sseqin2 G X
  have p0047 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wss G X) (.classEq (syn_cin X G) G) p0045 p0046
  have p0048 :=
    @g_syl5eq
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      A (syn_cin X G) G hyp_sbthlem1_4 p0047
  have p0049 :=
    @g_imaeq2d
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      A G R p0048
  have p0050 :=
    @g_sseqtr4d
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      C (syn_cima R G) (syn_cima R A) p0037 p0049
  have p0051 := @g_ssun2 (syn_cima R G) (syn_cdif X (syn_crn R))
  have p0052 :=
    @g_sseqtr4i (syn_cima R G) (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) G p0051
      p0025
  have p0053 :=
    @g_sseq1d
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_cima R A) (syn_cima R G) G p0049
  have p0054 :=
    @g_mpbiri
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wss (syn_cima R A) G) (syn_wss (syn_cima R G) G) p0052 p0053
  have p0055 := @g_imassrn R A
  have p0056 :=
    @g_jctil
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wss (syn_cima R A) G) (syn_wss (syn_cima R A) (syn_crn R)) p0054 p0055
  have p0057 := @g_ssin (syn_cima R A) (syn_crn R) G
  have p0058 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wa (syn_wss (syn_cima R A) (syn_crn R)) (syn_wss (syn_cima R A) G))
      (syn_wss (syn_cima R A) (syn_cin (syn_crn R) G)) p0056 p0057
  have p0059 :=
    @g_syl6sseqr
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_cima R A) (syn_cin (syn_crn R) G) C p0058 hyp_sbthlem1_6
  have p0060 :=
    @g_eqssd
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      C (syn_cima R A) p0050 p0059
  have p0061 :=
    @g_breqtrrd
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      A (syn_cima R A) C (syn_cen) p0024 p0060
  have p0062 := @g_difex X G hyp_sbthlem1_2 p0019
  have p0063 := @g_eqeltri B (syn_cdif X G) (syn_cvv) hyp_sbthlem1_5 p0062
  have p0064 := @g_enrflx B p0063
  have p0065 := @g_difsscompl X G
  have p0066 :=
    @g_a1i (syn_wss (syn_cdif X G) (syn_ccompl G))
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      p0065
  have p0067 := (Nominal.classEqRefl (syn_cdif X G))
  have p0068 := @g_clos1base G R (syn_cdif X (syn_crn R)) hyp_sbthlem1_3
  have p0069 := @g_sscon34 (syn_cdif X (syn_crn R)) G
  have p0070 :=
    @g_mpbi (syn_wss (syn_cdif X (syn_crn R)) G)
      (syn_wss (syn_ccompl G) (syn_ccompl (syn_cdif X (syn_crn R)))) p0068 p0069
  have p0071 := (Nominal.classEqRefl (syn_cdif X (syn_crn R)))
  have p0072 :=
    @g_compleqi (syn_cdif X (syn_crn R)) (syn_cin X (syn_ccompl (syn_crn R))) p0071
  have p0073 := @g_iinun X (syn_ccompl (syn_crn R))
  have p0074 := @g_dblcompl (syn_crn R)
  have p0075 :=
    @g_uneq2i (syn_ccompl (syn_ccompl (syn_crn R))) (syn_crn R) (syn_ccompl X) p0074
  have p0076 :=
    @g_n_3eqtri (syn_ccompl (syn_cdif X (syn_crn R)))
      (syn_ccompl (syn_cin X (syn_ccompl (syn_crn R))))
      (syn_cun (syn_ccompl X) (syn_ccompl (syn_ccompl (syn_crn R))))
      (syn_cun (syn_ccompl X) (syn_crn R)) p0072 p0073 p0075
  have p0077 :=
    @g_sseqtri (syn_ccompl G) (syn_ccompl (syn_cdif X (syn_crn R)))
      (syn_cun (syn_ccompl X) (syn_crn R)) p0070 p0076
  have p0078 := @g_sslin (syn_ccompl G) (syn_cun (syn_ccompl X) (syn_crn R)) X
  have p0079 := Nominal.mp p0077 p0078
  have p0080 :=
    @g_eqsstri (syn_cdif X G) (syn_cin X (syn_ccompl G))
      (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R))) p0067 p0079
  have p0081 := @g_indi X (syn_ccompl X) (syn_crn R)
  have p0082 := @g_incompl X
  have p0083 :=
    @g_uneq1i (syn_cin X (syn_ccompl X)) (syn_c0) (syn_cin X (syn_crn R)) p0082
  have p0084 := @g_uncom (syn_c0) (syn_cin X (syn_crn R))
  have p0085 := @g_un0 (syn_cin X (syn_crn R))
  have p0086 :=
    @g_eqtri (syn_cun (syn_c0) (syn_cin X (syn_crn R)))
      (syn_cun (syn_cin X (syn_crn R)) (syn_c0)) (syn_cin X (syn_crn R)) p0084 p0085
  have p0087 :=
    @g_n_3eqtri (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R)))
      (syn_cun (syn_cin X (syn_ccompl X)) (syn_cin X (syn_crn R)))
      (syn_cun (syn_c0) (syn_cin X (syn_crn R))) (syn_cin X (syn_crn R)) p0081 p0083 p0086
  have p0088 := @g_inss2 X (syn_crn R)
  have p0089 :=
    @g_eqsstri (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R))) (syn_cin X (syn_crn R))
      (syn_crn R) p0087 p0088
  have p0090 :=
    @g_sstri (syn_cdif X G) (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R))) (syn_crn R)
      p0080 p0089
  have p0091 :=
    @g_jctil
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wss (syn_cdif X G) (syn_ccompl G)) (syn_wss (syn_cdif X G) (syn_crn R)) p0066
      p0090
  have p0092 := @g_ssin (syn_cdif X G) (syn_crn R) (syn_ccompl G)
  have p0093 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wa (syn_wss (syn_cdif X G) (syn_crn R)) (syn_wss (syn_cdif X G) (syn_ccompl G)))
      (syn_wss (syn_cdif X G) (syn_cin (syn_crn R) (syn_ccompl G))) p0091 p0092
  have p0094 := (Nominal.classEqRefl (syn_cdif (syn_crn R) G))
  have p0095 :=
    @g_eqtri D (syn_cdif (syn_crn R) G) (syn_cin (syn_crn R) (syn_ccompl G))
      hyp_sbthlem1_7 p0094
  have p0096 :=
    @g_n_3sstr4g
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_cdif X G) (syn_cin (syn_crn R) (syn_ccompl G)) B D p0093 hyp_sbthlem1_5 p0095
  have p0097 := @g_ssdif (syn_crn R) X G
  have p0098 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wss (syn_crn R) X) (syn_wss (syn_cdif (syn_crn R) G) (syn_cdif X G)) p0039
      p0097
  have p0099 :=
    @g_n_3sstr4g
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_cdif (syn_crn R) G) (syn_cdif X G) D B p0098 hyp_sbthlem1_7 hyp_sbthlem1_5
  have p0100 :=
    @g_eqssd
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      B D p0096 p0099
  have p0101 :=
    @g_syl5breq
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      B B D (syn_cen) p0064 p0100
  have p0102 := @g_ineq12i A (syn_cin X G) B (syn_cdif X G) hyp_sbthlem1_4 hyp_sbthlem1_5
  have p0103 := @g_inindif X G
  have p0104 :=
    @g_eqtri (syn_cin A B) (syn_cin (syn_cin X G) (syn_cdif X G)) (syn_c0) p0102 p0103
  have p0105 :=
    @g_ineq12i C (syn_cin (syn_crn R) G) D (syn_cdif (syn_crn R) G) hyp_sbthlem1_6
      hyp_sbthlem1_7
  have p0106 := @g_inindif (syn_crn R) G
  have p0107 :=
    @g_eqtri (syn_cin C D) (syn_cin (syn_cin (syn_crn R) G) (syn_cdif (syn_crn R) G))
      (syn_c0) p0105 p0106
  have p0108 := @g_unen A C B D
  have p0109 :=
    @g_mpanr12 (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D))
      (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin C D) (syn_c0))
      (syn_wbr (syn_cun A B) (syn_cen) (syn_cun C D)) p0104 p0107 p0108
  have p0110 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D)
      (syn_wbr (syn_cun A B) (syn_cen) (syn_cun C D)) p0061 p0101 p0109
  have p0111 := @g_ensym (syn_cun A B) (syn_cun C D)
  have p0112 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_wbr (syn_cun A B) (syn_cen) (syn_cun C D))
      (syn_wbr (syn_cun C D) (syn_cen) (syn_cun A B)) p0110 p0111
  have p0113 :=
    @g_uneq12i C (syn_cin (syn_crn R) G) D (syn_cdif (syn_crn R) G) hyp_sbthlem1_6
      hyp_sbthlem1_7
  have p0114 := @g_inundif (syn_crn R) G
  have p0115 :=
    @g_eqtri (syn_cun C D) (syn_cun (syn_cin (syn_crn R) G) (syn_cdif (syn_crn R) G))
      (syn_crn R) p0113 p0114
  have p0116 := @g_uneq12i A (syn_cin X G) B (syn_cdif X G) hyp_sbthlem1_4 hyp_sbthlem1_5
  have p0117 := @g_inundif X G
  have p0118 :=
    @g_eqtri (syn_cun A B) (syn_cun (syn_cin X G) (syn_cdif X G)) X p0116 p0117
  have p0119 :=
    @g_n_3brtr3g
      (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)))
      (syn_cun C D) (syn_cun A B) (syn_crn R) X (syn_cen) p0112 p0115 p0118
  exact p0119

@[expose]
noncomputable def g_sbthlem2 (B : Class) (R : Class) (V : Class)
    (hyp_sbthlem2_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
          (syn_w3a (.classMem B V) (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B)))
        (syn_wbr (syn_crn R) (syn_cen) B)) :=
  by
  let proofSupport : Finset Var := B.fv ∪ R.fv ∪ V.fv
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : b ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0002 :
    b ∉
      ((Wff.imp (syn_wa (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B))
          (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
            (syn_wbr (syn_crn R) (syn_cen) B)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_b_not_B, fresh_b_not_R, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_sseq1 (.cv b) B (syn_cdm R)
  have p0001 := @g_sseq2 (.cv b) B (syn_crn R)
  have p0002 :=
    @g_anbi12d (.classEq (.cv b) B) (syn_wss (.cv b) (syn_cdm R)) (syn_wss B (syn_cdm R))
      (syn_wss (syn_crn R) (.cv b)) (syn_wss (syn_crn R) B) p0000 p0001
  have p0003 := @g_breq2 (.cv b) B (syn_crn R) (syn_cen)
  have p0004 :=
    @g_imbi2d (.classEq (.cv b) B) (syn_wbr (syn_crn R) (syn_cen) (.cv b))
      (syn_wbr (syn_crn R) (syn_cen) B) (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
      p0003
  have p0005 :=
    @g_imbi12d (.classEq (.cv b) B)
      (syn_wa (syn_wss (.cv b) (syn_cdm R)) (syn_wss (syn_crn R) (.cv b)))
      (syn_wa (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B))
      (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
        (syn_wbr (syn_crn R) (syn_cen) (.cv b)))
      (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B))
      p0002 p0004
  have p0006 := @g_vex b
  have p0007 := @g_eqid (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R)
  have p0008 := @g_eqid (syn_cin (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0009 := @g_eqid (syn_cdif (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0010 :=
    @g_eqid (syn_cin (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0011 :=
    @g_eqid (syn_cdif (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0012 :=
    @g_sbthlem1 (syn_cin (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
      (syn_cdif (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
      (syn_cin (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
      (syn_cdif (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R)) R
      (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R) (.cv b) hyp_sbthlem2_1 p0006 p0007
      p0008 p0009 p0010 p0011
  have p0013 :=
    @g_expcom (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
      (syn_wa (syn_wss (.cv b) (syn_cdm R)) (syn_wss (syn_crn R) (.cv b)))
      (syn_wbr (syn_crn R) (syn_cen) (.cv b)) p0012
  have p0014 :=
    @g_vtoclg
      (.imp (syn_wa (syn_wss (.cv b) (syn_cdm R)) (syn_wss (syn_crn R) (.cv b)))
        (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R)))
          (syn_wbr (syn_crn R) (syn_cen) (.cv b))))
      (.imp (syn_wa (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B))
        (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B)))
      b B V dv_cache_0001 dv_cache_0002 p0005 p0013
  have p0015 :=
    @g_n_3impib (.classMem B V) (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B)
      (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B))
      p0014
  have p0016 :=
    @g_impcom (syn_w3a (.classMem B V) (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B))
      (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B)
      p0015
  exact p0016

@[expose]
noncomputable def g_sbthlem3 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr A (syn_cen) C) (syn_wss C B))
          (syn_wa (syn_wbr B (syn_cen) D) (syn_wss D A))) (syn_wbr A (syn_cen) B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let r : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_r_ne_s : r ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_C, not_false_eq_true])
  have dv_cache_0003 : s ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_B, not_false_eq_true])
  have dv_cache_0004 : s ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_D, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((syn_wf1o (.cv r) A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_not_A, fresh_s_not_C, fresh_s_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_wf1o (.cv s) B D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_not_B, fresh_r_not_D, fresh_r_ne_s, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    r ∉ ((Wff.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_r_not_C, fresh_r_not_B, fresh_r_not_D, fresh_r_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    s ∉ ((Wff.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_s_not_C, fresh_s_not_B, fresh_s_not_D, fresh_s_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_bren A C r dv_cache_0001 dv_cache_0002
  have p0001 := @g_bren B D s dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anbi12i (syn_wbr A (syn_cen) C) (syn_wex r (syn_wf1o (.cv r) A C))
      (syn_wbr B (syn_cen) D) (syn_wex s (syn_wf1o (.cv s) B D)) p0000 p0001
  have p0003 :=
    @g_eeanv (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D) r s dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D))
      (syn_wa (syn_wex r (syn_wf1o (.cv r) A C)) (syn_wex s (syn_wf1o (.cv s) B D)))
      (syn_wex r (syn_wex s (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)))) p0002
      p0003
  have p0005 :=
    @g_simprl (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wss C B)
      (syn_wss D A)
  have p0006 := @g_f1ofo A C (.cv r)
  have p0007 := @g_forn A C (.cv r)
  have p0008 :=
    @g_syl (syn_wf1o (.cv r) A C) (syn_wfo (.cv r) A C) (.classEq (syn_crn (.cv r)) C)
      p0006 p0007
  have p0009 :=
    @g_ad2antrr (syn_wf1o (.cv r) A C) (.classEq (syn_crn (.cv r)) C)
      (syn_wf1o (.cv s) B D) (syn_wa (syn_wss C B) (syn_wss D A)) p0008
  have p0010 := @g_f1odm B D (.cv s)
  have p0011 :=
    @g_ad2antlr (syn_wf1o (.cv s) B D) (.classEq (syn_cdm (.cv s)) B)
      (syn_wf1o (.cv r) A C) (syn_wa (syn_wss C B) (syn_wss D A)) p0010
  have p0012 :=
    @g_n_3sstr4d
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      C B (syn_crn (.cv r)) (syn_cdm (.cv s)) p0005 p0009 p0011
  have p0013 := @g_dmcosseq (.cv s) (.cv r)
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_wss (syn_crn (.cv r)) (syn_cdm (.cv s)))
      (.classEq (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_cdm (.cv r))) p0012 p0013
  have p0015 := @g_f1odm A C (.cv r)
  have p0016 :=
    @g_ad2antrr (syn_wf1o (.cv r) A C) (.classEq (syn_cdm (.cv r)) A)
      (syn_wf1o (.cv s) B D) (syn_wa (syn_wss C B) (syn_wss D A)) p0015
  have p0017 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_cdm (.cv r)) A p0014 p0016
  have p0018 := @g_f1ofun B D (.cv s)
  have p0019 := @g_f1ofun A C (.cv r)
  have p0020 := @g_funco (.cv s) (.cv r)
  have p0021 :=
    @g_syl2anr (syn_wf1o (.cv s) B D) (syn_wfun (.cv s)) (syn_wfun (.cv r))
      (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wf1o (.cv r) A C) p0018 p0019 p0020
  have p0022 := @g_dff1o2 A C (.cv r)
  have p0023 :=
    @g_simp2bi (syn_wf1o (.cv r) A C) (syn_wfn (.cv r) A) (syn_wfun (syn_ccnv (.cv r)))
      (.classEq (syn_crn (.cv r)) C) p0022
  have p0024 := @g_dff1o2 B D (.cv s)
  have p0025 :=
    @g_simp2bi (syn_wf1o (.cv s) B D) (syn_wfn (.cv s) B) (syn_wfun (syn_ccnv (.cv s)))
      (.classEq (syn_crn (.cv s)) D) p0024
  have p0026 := @g_funco (syn_ccnv (.cv r)) (syn_ccnv (.cv s))
  have p0027 :=
    @g_syl2an (syn_wf1o (.cv r) A C) (syn_wfun (syn_ccnv (.cv r)))
      (syn_wfun (syn_ccnv (.cv s)))
      (syn_wfun (syn_ccom (syn_ccnv (.cv r)) (syn_ccnv (.cv s)))) (syn_wf1o (.cv s) B D)
      p0023 p0025 p0026
  have p0028 := @g_cnvco (.cv s) (.cv r)
  have p0029 :=
    @g_funeqi (syn_ccnv (syn_ccom (.cv s) (.cv r)))
      (syn_ccom (syn_ccnv (.cv r)) (syn_ccnv (.cv s))) p0028
  have p0030 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
      (syn_wfun (syn_ccom (syn_ccnv (.cv r)) (syn_ccnv (.cv s))))
      (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) p0027 p0029
  have p0031 :=
    @g_jca (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
      (syn_wfun (syn_ccom (.cv s) (.cv r)))
      (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) p0021 p0030
  have p0032 :=
    @g_adantr (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
      (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r)))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))))
      (syn_wa (syn_wss C B) (syn_wss D A)) p0031
  have p0033 :=
    @g_dff1o2 (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))
      (syn_ccom (.cv s) (.cv r))
  have p0034 := @g_funfn (syn_ccom (.cv s) (.cv r))
  have p0035 :=
    @g_anbi1i (syn_wfun (syn_ccom (.cv s) (.cv r)))
      (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))))
      (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) p0034
  have p0036 := @g_eqid (syn_crn (syn_ccom (.cv s) (.cv r)))
  have p0037 :=
    (Nominal.biimpRefl
      (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))
        (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r))))))
  have p0038 :=
    @g_mpbiran2
      (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))
        (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))))
      (syn_wa (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))))
      (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r))))
      p0036 p0037
  have p0039 :=
    @g_bitr4i
      (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r)))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))))
      (syn_wa (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))))
      (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))
        (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))))
      p0035 p0038
  have p0040 :=
    @g_bitr4i
      (syn_wf1o (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))
        (syn_crn (syn_ccom (.cv s) (.cv r))))
      (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))
        (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))))
      (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r)))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))))
      p0033 p0039
  have p0041 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r)))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))))
      (syn_wf1o (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))
        (syn_crn (syn_ccom (.cv s) (.cv r))))
      p0032 p0040
  have p0042 := @g_vex s
  have p0043 := @g_vex r
  have p0044 := @g_coex (.cv s) (.cv r) p0042 p0043
  have p0045 :=
    @g_f1oen (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))
      (syn_ccom (.cv s) (.cv r)) p0044
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_wf1o (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))
        (syn_crn (syn_ccom (.cv s) (.cv r))))
      (syn_wbr (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_cen)
        (syn_crn (syn_ccom (.cv s) (.cv r))))
      p0041 p0045
  have p0047 :=
    @g_eqbrtrrd
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_cdm (syn_ccom (.cv s) (.cv r))) A (syn_crn (syn_ccom (.cv s) (.cv r)))
      (syn_cen) p0017 p0046
  have p0048 := @g_f1ofo B D (.cv s)
  have p0049 := @g_forn B D (.cv s)
  have p0050 :=
    @g_syl (syn_wf1o (.cv s) B D) (syn_wfo (.cv s) B D) (.classEq (syn_crn (.cv s)) D)
      p0048 p0049
  have p0051 := @g_rnex (.cv s) p0042
  have p0052 :=
    @g_syl6eqelr (syn_wf1o (.cv s) B D) D (syn_crn (.cv s)) (syn_cvv) p0050 p0051
  have p0053 :=
    @g_ad2antlr (syn_wf1o (.cv s) B D) (.classMem D (syn_cvv)) (syn_wf1o (.cv r) A C)
      (syn_wa (syn_wss C B) (syn_wss D A)) p0052
  have p0054 :=
    @g_simprr (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wss C B)
      (syn_wss D A)
  have p0055 :=
    @g_sseqtr4d
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      D A (syn_cdm (syn_ccom (.cv s) (.cv r))) p0054 p0017
  have p0056 := @g_rncoss (.cv s) (.cv r)
  have p0057 :=
    @g_ad2antlr (syn_wf1o (.cv s) B D) (.classEq (syn_crn (.cv s)) D)
      (syn_wf1o (.cv r) A C) (syn_wa (syn_wss C B) (syn_wss D A)) p0050
  have p0058 :=
    @g_syl5sseq
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_crn (.cv s)) (syn_crn (syn_ccom (.cv s) (.cv r))) D p0056 p0057
  have p0059 := @g_sbthlem2 D (syn_ccom (.cv s) (.cv r)) (syn_cvv) p0044
  have p0060 :=
    @g_syl13anc
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r)))
        (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))))
      (.classMem D (syn_cvv)) (syn_wss D (syn_cdm (syn_ccom (.cv s) (.cv r))))
      (syn_wss (syn_crn (syn_ccom (.cv s) (.cv r))) D)
      (syn_wbr (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_cen) D) p0032 p0053 p0055 p0058
      p0059
  have p0061 := @g_entr A (syn_crn (syn_ccom (.cv s) (.cv r))) D
  have p0062 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
        (syn_wa (syn_wss C B) (syn_wss D A)))
      (syn_wbr A (syn_cen) (syn_crn (syn_ccom (.cv s) (.cv r))))
      (syn_wbr (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_cen) D) (syn_wbr A (syn_cen) D)
      p0047 p0060 p0061
  have p0063 :=
    @g_ex (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
      (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D) p0062
  have p0064 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))
      (.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D)) r s
      dv_cache_0007 dv_cache_0008 p0063
  have p0065 :=
    @g_sylbi (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D))
      (syn_wex r (syn_wex s (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D))))
      (.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D)) p0004 p0064
  have p0066 :=
    @g_imp (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D))
      (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D) p0065
  have p0067 :=
    @g_an4s (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D) (syn_wss C B) (syn_wss D A)
      (syn_wbr A (syn_cen) D) p0066
  have p0068 := @g_ensymi B D
  have p0069 :=
    @g_ad2antrl (syn_wbr B (syn_cen) D) (syn_wbr D (syn_cen) B)
      (syn_wa (syn_wbr A (syn_cen) C) (syn_wss C B)) (syn_wss D A) p0068
  have p0070 := @g_entr A D B
  have p0071 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_wbr A (syn_cen) C) (syn_wss C B))
        (syn_wa (syn_wbr B (syn_cen) D) (syn_wss D A)))
      (syn_wbr A (syn_cen) D) (syn_wbr D (syn_cen) B) (syn_wbr A (syn_cen) B) p0067 p0069
      p0070
  exact p0071


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part050`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_sbth (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (.imp (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let g : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (h))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_g_ne_b : g ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_g : b ≠ g := Ne.symm fresh_g_ne_b
  have fresh_g_ne_d : g ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_g : d ≠ g := Ne.symm fresh_g_ne_d
  have fresh_g_ne_a : g ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_g : a ≠ g := Ne.symm fresh_g_ne_a
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_a : b ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have fresh_d_ne_a : d ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_d : a ≠ d := Ne.symm fresh_d_ne_a
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
  have dv_cache_0003 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0004 : g ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show g ≠ b from (by exact fresh_g_ne_b))
  have dv_cache_0005 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0006 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0007 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0008 : d ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0009 : a ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_B, not_false_eq_true])
  have dv_cache_0010 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_wss (.cv g) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_g, fresh_a_ne_b, or_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((syn_wss (.cv d) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_d, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0013 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0014 : d ∉ ((syn_wrex b B (syn_wss (.cv g) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_d_not_B, fresh_d_ne_g, fresh_d_ne_b, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0015 : g ∉ ((syn_wrex a A (syn_wss (.cv d) (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_g_not_A, fresh_g_ne_d, fresh_g_ne_a, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0016 : g ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show g ≠ d from (by exact fresh_g_ne_d))
  have dv_cache_0017 : a ∉ ((syn_cnc (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_d,
          not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Wff.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_g, fresh_b_ne_d, or_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((Wff.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_g, fresh_a_ne_d, or_false, not_false_eq_true])
  have dv_cache_0020 : b ∉ ((syn_cnc (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_d,
          not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_cnc (.cv g))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_g,
          not_false_eq_true])
  have dv_cache_0022 : b ∉ ((Wff.classEq A (syn_cnc (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_A, fresh_b_ne_g, or_false, not_false_eq_true])
  have dv_cache_0023 : g ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_g_not_A, fresh_g_not_B, or_false, not_false_eq_true])
  have dv_cache_0024 : d ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_d_not_A, fresh_d_not_B, or_false, not_false_eq_true])
  have dv_cache_0025 :
    g ∉ ((syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_g_not_A, fresh_g_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0026 :
    d ∉ ((syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_d_not_A, fresh_d_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_brlecg g b A B (syn_cncs) (syn_cncs) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 :=
    @g_brlecg d a B A (syn_cncs) (syn_cncs) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008
  have p0002 :=
    @g_ancoms (.classMem B (syn_cncs)) (.classMem A (syn_cncs))
      (syn_wb (syn_wbr B (syn_clec) A) (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a)))))
      p0001
  have p0003 :=
    @g_anbi12d (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wbr A (syn_clec) B) (syn_wrex g A (syn_wrex b B (syn_wss (.cv g) (.cv b))))
      (syn_wbr B (syn_clec) A) (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a))))
      p0000 p0002
  have p0004 :=
    @g_reeanv (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)) b a B A dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    @g_n_2rexbii
      (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
      (syn_wa (syn_wrex b B (syn_wss (.cv g) (.cv b))) (syn_wrex a A (syn_wss (.cv d) (.cv a))))
      g d A B p0004
  have p0006 :=
    @g_reeanv (syn_wrex b B (syn_wss (.cv g) (.cv b)))
      (syn_wrex a A (syn_wss (.cv d) (.cv a))) g d A B dv_cache_0006 dv_cache_0002
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0007 :=
    @g_bitri
      (syn_wrex g A (syn_wrex d B (syn_wrex b B
            (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))))
      (syn_wrex g A (syn_wrex d B (syn_wa (syn_wrex b B (syn_wss (.cv g) (.cv b)))
            (syn_wrex a A (syn_wss (.cv d) (.cv a))))))
      (syn_wa (syn_wrex g A (syn_wrex b B (syn_wss (.cv g) (.cv b))))
        (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a)))))
      p0005 p0006
  have p0008 :=
    @g_syl6bbr (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A))
      (syn_wa (syn_wrex g A (syn_wrex b B (syn_wss (.cv g) (.cv b))))
        (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a)))))
      (syn_wrex g A (syn_wrex d B (syn_wrex b B
            (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))))
      p0003 p0007
  have p0009 := @g_ncseqnc A (.cv g)
  have p0010 := @g_ncseqnc B (.cv d)
  have p0011 :=
    @g_bi2anan9 (.classMem A (syn_cncs)) (.classEq A (syn_cnc (.cv g)))
      (.classMem (.cv g) A) (.classMem B (syn_cncs)) (.classEq B (syn_cnc (.cv d)))
      (.classMem (.cv d) B) p0009 p0010
  have p0012 :=
    @g_biimpar (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d))))
      (syn_wa (.classMem (.cv g) A) (.classMem (.cv d) B)) p0011
  have p0013 :=
    @g_simplr (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))
      (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
  have p0014 := @g_ensym (.cv a) (.cv g)
  have p0015 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
        (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))
      (syn_wbr (.cv a) (syn_cen) (.cv g)) (syn_wbr (.cv g) (syn_cen) (.cv a)) p0013 p0014
  have p0016 :=
    @g_simprl
      (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
      (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))
  have p0017 :=
    @g_simpll (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))
      (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
  have p0018 :=
    @g_simprr
      (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
      (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))
  have p0019 := @g_sbthlem3 (.cv a) (.cv b) (.cv g) (.cv d)
  have p0020 :=
    @g_syl22anc
      (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
        (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))
      (syn_wbr (.cv a) (syn_cen) (.cv g)) (syn_wss (.cv g) (.cv b))
      (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wss (.cv d) (.cv a))
      (syn_wbr (.cv a) (syn_cen) (.cv b)) p0013 p0016 p0017 p0018 p0019
  have p0021 := @g_entr (.cv g) (.cv a) (.cv b)
  have p0022 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
        (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))
      (syn_wbr (.cv g) (syn_cen) (.cv a)) (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wbr (.cv g) (syn_cen) (.cv b)) p0015 p0020 p0021
  have p0023 := @g_entr (.cv g) (.cv b) (.cv d)
  have p0024 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
        (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))
      (syn_wbr (.cv g) (syn_cen) (.cv b)) (syn_wbr (.cv b) (syn_cen) (.cv d))
      (syn_wbr (.cv g) (syn_cen) (.cv d)) p0022 p0017 p0023
  have p0025 :=
    @g_ex (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
      (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
      (syn_wbr (.cv g) (syn_cen) (.cv d)) p0024
  have p0026 := @g_elnc (.cv b) (.cv d)
  have p0027 := @g_elnc (.cv a) (.cv g)
  have p0028 :=
    @g_anbi12i (.classMem (.cv b) (syn_cnc (.cv d))) (syn_wbr (.cv b) (syn_cen) (.cv d))
      (.classMem (.cv a) (syn_cnc (.cv g))) (syn_wbr (.cv a) (syn_cen) (.cv g)) p0026
      p0027
  have p0029 := @g_vex g
  have p0030 := @g_eqnc (.cv g) (.cv d) p0029
  have p0031 :=
    @g_imbi2i (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d)))
      (syn_wbr (.cv g) (syn_cen) (.cv d))
      (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) p0030
  have p0032 :=
    @g_n_3imtr4i
      (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)))
      (.imp (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
        (syn_wbr (.cv g) (syn_cen) (.cv d)))
      (syn_wa (.classMem (.cv b) (syn_cnc (.cv d))) (.classMem (.cv a) (syn_cnc (.cv g))))
      (.imp (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
        (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d))))
      p0025 p0028 p0031
  have p0033 :=
    @g_rexlimivv (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
      (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d))) b a (syn_cnc (.cv d))
      (syn_cnc (.cv g)) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0013 p0032
  have p0034 :=
    @g_rexeq (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) b
      B (syn_cnc (.cv d)) dv_cache_0003 dv_cache_0020
  have p0035 :=
    @g_rexeq (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) a A
      (syn_cnc (.cv g)) dv_cache_0007 dv_cache_0021
  have p0036 :=
    @g_rexbidv (.classEq A (syn_cnc (.cv g)))
      (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))
      (syn_wrex a (syn_cnc (.cv g))
        (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))
      b (syn_cnc (.cv d)) dv_cache_0022 p0035
  have p0037 :=
    @g_sylan9bbr (.classEq B (syn_cnc (.cv d)))
      (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
      (syn_wrex b (syn_cnc (.cv d))
        (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
      (.classEq A (syn_cnc (.cv g)))
      (syn_wrex b (syn_cnc (.cv d)) (syn_wrex a (syn_cnc (.cv g))
          (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
      p0034 p0036
  have p0038 := @g_eqeq12 A (syn_cnc (.cv g)) B (syn_cnc (.cv d))
  have p0039 :=
    @g_imbi12d (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d))))
      (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
      (syn_wrex b (syn_cnc (.cv d)) (syn_wrex a (syn_cnc (.cv g))
          (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
      (.classEq A B) (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d))) p0037 p0038
  have p0040 :=
    @g_mpbiri (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d))))
      (.imp (syn_wrex b B
          (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
        (.classEq A B))
      (.imp (syn_wrex b (syn_cnc (.cv d)) (syn_wrex a (syn_cnc (.cv g))
            (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
        (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d))))
      p0033 p0039
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (syn_wa (.classMem (.cv g) A) (.classMem (.cv d) B)))
      (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d))))
      (.imp (syn_wrex b B
          (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
        (.classEq A B))
      p0012 p0040
  have p0042 :=
    @g_rexlimdvva (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))
      (.classEq A B) g d A B dv_cache_0006 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0016 p0041
  have p0043 :=
    @g_sylbid (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A))
      (syn_wrex g A (syn_wrex d B (syn_wrex b B
            (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))))))
      (.classEq A B) p0008 p0042
  exact p0043

@[expose]
noncomputable def g_ltlenlec (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wb (syn_wbr M (syn_cltc) N)
          (syn_wa (syn_wbr M (syn_clec) N) (.neg (syn_wbr N (syn_clec) M))))) :=
  by
  have p0000 := @g_brltc M N
  have p0001 := @g_nclecid M
  have p0002 := @g_breq1 M N M (syn_clec)
  have p0003 :=
    @g_syl5ibcom (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) M) (.classEq M N)
      (syn_wbr N (syn_clec) M) p0001 p0002
  have p0004 :=
    @g_ad2antrr (.classMem M (syn_cncs)) (.imp (.classEq M N) (syn_wbr N (syn_clec) M))
      (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) N) p0003
  have p0005 := @g_sbth M N
  have p0006 :=
    @g_expdimp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr M (syn_clec) N) (syn_wbr N (syn_clec) M) (.classEq M N) p0005
  have p0007 :=
    @g_impbid
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wbr M (syn_clec) N))
      (.classEq M N) (syn_wbr N (syn_clec) M) p0004 p0006
  have p0008 :=
    @g_necon3abid
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wbr M (syn_clec) N))
      (syn_wbr N (syn_clec) M) M N p0007
  have p0009 :=
    @g_pm5_32da (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr M (syn_clec) N) (syn_wne M N) (.neg (syn_wbr N (syn_clec) M)) p0008
  have p0010 :=
    @g_syl5bb (syn_wbr M (syn_cltc) N) (syn_wa (syn_wbr M (syn_clec) N) (syn_wne M N))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wa (syn_wbr M (syn_clec) N) (.neg (syn_wbr N (syn_clec) M))) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_addlec (M : Class) (N : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M V) (.classMem N W) (syn_wne (syn_cplc M N) (syn_c0)))
        (syn_wbr M (syn_clec) (syn_cplc M N))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_M : z ∉ M.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_N : z ∉ N.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0003 : x ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0004 : y ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_M, not_false_eq_true])
  have dv_cache_0005 : x ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_N, not_false_eq_true])
  have dv_cache_0006 : y ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_N, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ ((syn_wss (.cv x) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cplc M N)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          Finset.mem_union, fresh_z_not_M, fresh_z_not_N, or_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_M, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cplc M N)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          Finset.mem_union, fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 :=
    @g_eladdc (.cv z) M N x y dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @g_ssun1 (.cv x) (.cv y)
  have p0002 := @g_sseq2 (.cv z) (syn_cun (.cv x) (.cv y)) (.cv x)
  have p0003 :=
    @g_mpbiri (.classEq (.cv z) (syn_cun (.cv x) (.cv y))) (syn_wss (.cv x) (.cv z))
      (syn_wss (.cv x) (syn_cun (.cv x) (.cv y))) p0001 p0002
  have p0004 :=
    @g_adantl (.classEq (.cv z) (syn_cun (.cv x) (.cv y))) (syn_wss (.cv x) (.cv z))
      (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) p0003
  have p0005 :=
    @g_rexlimivw
      (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
        (.classEq (.cv z) (syn_cun (.cv x) (.cv y))))
      (syn_wss (.cv x) (.cv z)) y N dv_cache_0008 p0004
  have p0006 :=
    @g_reximi
      (syn_wrex y N (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
          (.classEq (.cv z) (syn_cun (.cv x) (.cv y)))))
      (syn_wss (.cv x) (.cv z)) x M p0005
  have p0007 :=
    @g_sylbi (.classMem (.cv z) (syn_cplc M N))
      (syn_wrex x M (syn_wrex y N (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv x) (.cv y))))))
      (syn_wrex x M (syn_wss (.cv x) (.cv z))) p0000 p0006
  have p0008 :=
    @g_ancli (.classMem (.cv z) (syn_cplc M N)) (syn_wrex x M (syn_wss (.cv x) (.cv z)))
      p0007
  have p0009 :=
    @g_eximi (.classMem (.cv z) (syn_cplc M N))
      (syn_wa (.classMem (.cv z) (syn_cplc M N)) (syn_wrex x M (syn_wss (.cv x) (.cv z))))
      z p0008
  have p0010 := @g_n0 z (syn_cplc M N) dv_cache_0009
  have p0011 :=
    @g_rexcom (syn_wss (.cv x) (.cv z)) x z M (syn_cplc M N) dv_cache_0010 dv_cache_0011
      dv_cache_0012
  have p0012 :=
    (Nominal.biimpRefl (syn_wrex z (syn_cplc M N) (syn_wrex x M (syn_wss (.cv x) (.cv z)))))
  have p0013 :=
    @g_bitri (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z))))
      (syn_wrex z (syn_cplc M N) (syn_wrex x M (syn_wss (.cv x) (.cv z))))
      (syn_wex z (syn_wa (.classMem (.cv z) (syn_cplc M N))
          (syn_wrex x M (syn_wss (.cv x) (.cv z)))))
      p0011 p0012
  have p0014 :=
    @g_n_3imtr4i (syn_wex z (.classMem (.cv z) (syn_cplc M N)))
      (syn_wex z (syn_wa (.classMem (.cv z) (syn_cplc M N))
          (syn_wrex x M (syn_wss (.cv x) (.cv z)))))
      (syn_wne (syn_cplc M N) (syn_c0))
      (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))) p0009 p0010
      p0013
  have p0015 :=
    @g_n_3ad2ant3 (syn_wne (syn_cplc M N) (syn_c0)) (.classMem M V)
      (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))) (.classMem N W)
      p0014
  have p0016 := @g_addcexg M N V W
  have p0017 :=
    @g_brlecg x z M (syn_cplc M N) V (syn_cvv) dv_cache_0003 dv_cache_0011 dv_cache_0009
      dv_cache_0012
  have p0018 :=
    @g_syldan (.classMem M V) (.classMem N W) (.classMem (syn_cplc M N) (syn_cvv))
      (syn_wb (syn_wbr M (syn_clec) (syn_cplc M N))
        (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))))
      p0016 p0017
  have p0019 :=
    @g_n_3adant3 (.classMem M V) (.classMem N W)
      (syn_wb (syn_wbr M (syn_clec) (syn_cplc M N))
        (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))))
      (syn_wne (syn_cplc M N) (syn_c0)) p0018
  have p0020 :=
    @g_mpbird (syn_w3a (.classMem M V) (.classMem N W) (syn_wne (syn_cplc M N) (syn_c0)))
      (syn_wbr M (syn_clec) (syn_cplc M N))
      (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))) p0015 p0019
  exact p0020

@[expose]
noncomputable def g_addlecncs (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wbr M (syn_clec) (syn_cplc M N))) :=
  by
  have p0000 := @g_ncaddccl M N
  have p0001 := @g_nulnnc
  have p0002 := @g_eleq1 (syn_cplc M N) (syn_c0) (syn_cncs)
  have p0003 :=
    @g_mtbiri (.classEq (syn_cplc M N) (syn_c0)) (.classMem (syn_cplc M N) (syn_cncs))
      (.classMem (syn_c0) (syn_cncs)) p0001 p0002
  have p0004 :=
    @g_necon2ai (.classMem (syn_cplc M N) (syn_cncs)) (syn_cplc M N) (syn_c0) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classMem (syn_cplc M N) (syn_cncs)) (syn_wne (syn_cplc M N) (syn_c0)) p0000 p0004
  have p0006 := @g_addlec M N (syn_cncs) (syn_cncs)
  have p0007 :=
    @g_mpd3an3 (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wne (syn_cplc M N) (syn_c0)) (syn_wbr M (syn_clec) (syn_cplc M N)) p0005 p0006
  exact p0007

@[expose]
noncomputable def g_dflec2 (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wb (syn_wbr M (syn_clec) N)
          (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({ p } : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_p : a ≠ p := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_a : p ≠ a := Ne.symm fresh_a_ne_p
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_p : b ≠ p := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_b : p ≠ b := Ne.symm fresh_b_ne_p
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : a ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_M, not_false_eq_true])
  have dv_cache_0002 : a ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have dv_cache_0003 : b ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_N, not_false_eq_true])
  have dv_cache_0004 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0005 : p ∉ ((syn_cnc (syn_cdif (.cv b) (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_a, or_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 :
    p ∉
      ((Wff.classEq (syn_cnc (.cv b))
          (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_a, or_false, not_false_eq_true])
  have dv_cache_0008 :
    p ∉ ((syn_wa (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_N_p, fresh_p_ne_b, dv_M_p, fresh_p_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0009 : b ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_M, not_false_eq_true])
  have dv_cache_0010 :
    a ∉ ((syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_N, fresh_a_not_M, fresh_a_ne_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    b ∉ ((syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_not_N, fresh_b_not_M, fresh_b_ne_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    a ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_a_not_M, fresh_a_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    b ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_b_not_M, fresh_b_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 : p ∉ ((syn_wbr M (syn_clec) N)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, dv_M_p,
          dv_N_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    p ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, dv_M_p,
          dv_N_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_brlecg a b M N (syn_cncs) (syn_cncs) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @g_ncseqnc M (.cv a)
  have p0002 := @g_ncseqnc N (.cv b)
  have p0003 :=
    @g_bi2anan9 (.classMem M (syn_cncs)) (.classEq M (syn_cnc (.cv a)))
      (.classMem (.cv a) M) (.classMem N (syn_cncs)) (.classEq N (syn_cnc (.cv b)))
      (.classMem (.cv b) N) p0001 p0002
  have p0004 :=
    @g_biimpar (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wa (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))))
      (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) p0003
  have p0005 := @g_vex b
  have p0006 := @g_vex a
  have p0007 := @g_difex (.cv b) (.cv a) p0005 p0006
  have p0008 := @g_ncelncsi (syn_cdif (.cv b) (.cv a)) p0007
  have p0009 := @g_disjdif (.cv a) (.cv b)
  have p0010 := @g_ncdisjun (.cv a) (syn_cdif (.cv b) (.cv a)) p0006 p0007
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @g_undif2 (.cv a) (.cv b)
  have p0013 := @g_ssequn1 (.cv a) (.cv b)
  have p0014 :=
    @g_biimpi (syn_wss (.cv a) (.cv b)) (.classEq (syn_cun (.cv a) (.cv b)) (.cv b)) p0013
  have p0015 :=
    @g_syl5eq (syn_wss (.cv a) (.cv b)) (syn_cun (.cv a) (syn_cdif (.cv b) (.cv a)))
      (syn_cun (.cv a) (.cv b)) (.cv b) p0012 p0014
  have p0016 :=
    @g_nceqd (syn_wss (.cv a) (.cv b)) (syn_cun (.cv a) (syn_cdif (.cv b) (.cv a)))
      (.cv b) p0015
  have p0017 :=
    @g_syl5reqr (syn_wss (.cv a) (.cv b))
      (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a))))
      (syn_cnc (syn_cun (.cv a) (syn_cdif (.cv b) (.cv a)))) (syn_cnc (.cv b)) p0011 p0016
  have p0018 := @g_addceq2 (.cv p) (syn_cnc (syn_cdif (.cv b) (.cv a))) (syn_cnc (.cv a))
  have p0019 :=
    @g_eqeq2d (.classEq (.cv p) (syn_cnc (syn_cdif (.cv b) (.cv a))))
      (syn_cplc (syn_cnc (.cv a)) (.cv p))
      (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a)))) (syn_cnc (.cv b))
      p0018
  have p0020 :=
    @g_rspcev (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p)))
      (.classEq (syn_cnc (.cv b))
        (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a)))))
      p (syn_cnc (syn_cdif (.cv b) (.cv a))) (syn_cncs) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0019
  have p0021 :=
    @g_sylancr (syn_wss (.cv a) (.cv b))
      (.classMem (syn_cnc (syn_cdif (.cv b) (.cv a))) (syn_cncs))
      (.classEq (syn_cnc (.cv b))
        (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a)))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p))))
      p0008 p0017 p0020
  have p0022 := @g_id (.classEq N (syn_cnc (.cv b)))
  have p0023 := @g_addceq1 M (syn_cnc (.cv a)) (.cv p)
  have p0024 :=
    @g_eqeqan12d (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a))) N
      (syn_cnc (.cv b)) (syn_cplc M (.cv p)) (syn_cplc (syn_cnc (.cv a)) (.cv p)) p0022
      p0023
  have p0025 :=
    @g_rexbidv (syn_wa (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a))))
      (.classEq N (syn_cplc M (.cv p)))
      (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p))) p (syn_cncs)
      dv_cache_0008 p0024
  have p0026 :=
    @g_ancoms (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a)))
      (syn_wb (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) (syn_wrex p (syn_cncs)
          (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p)))))
      p0025
  have p0027 :=
    @g_syl5ibr (syn_wss (.cv a) (.cv b))
      (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))
      (syn_wa (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p))))
      p0021 p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)))
      (syn_wa (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))))
      (.imp (syn_wss (.cv a) (.cv b)) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))))
      p0004 p0027
  have p0029 :=
    @g_rexlimdvva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wss (.cv a) (.cv b)) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))
      a b M N dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0004 p0028
  have p0030 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wss (.cv a) (.cv b))))
      (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) p0000 p0029
  have p0031 := @g_addlecncs M (.cv p)
  have p0032 := @g_breq2 N (syn_cplc M (.cv p)) M (syn_clec)
  have p0033 :=
    @g_syl5ibrcom (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs)))
      (syn_wbr M (syn_clec) N) (.classEq N (syn_cplc M (.cv p)))
      (syn_wbr M (syn_clec) (syn_cplc M (.cv p))) p0031 p0032
  have p0034 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs))
      (.imp (.classEq N (syn_cplc M (.cv p))) (syn_wbr M (syn_clec) N))
      (.classMem N (syn_cncs)) p0033
  have p0035 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classEq N (syn_cplc M (.cv p))) (syn_wbr M (syn_clec) N) p (syn_cncs)
      dv_cache_0014 dv_cache_0015 p0034
  have p0036 :=
    @g_impbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr M (syn_clec) N) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))
      p0030 p0035
  exact p0036


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part051`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lectr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
        (.imp (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) C))
          (syn_wbr A (syn_clec) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
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
  have dv_cache_0005 : y ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classEq B (syn_cplc A (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, fresh_y_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq C (syn_cplc B (.cv y)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_C, fresh_x_not_B, fresh_x_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0010 : x ∉ ((syn_wbr A (syn_clec) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wbr A (syn_clec) C)).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_x_not_C, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    y ∉
      ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_y_not_C, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_dflec2 A B x dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_3adant3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (syn_wb (syn_wbr A (syn_clec) B)
        (syn_wrex x (syn_cncs) (.classEq B (syn_cplc A (.cv x)))))
      (.classMem C (syn_cncs)) p0000
  have p0002 := @g_dflec2 B C y dv_cache_0003 dv_cache_0004
  have p0003 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wb (syn_wbr B (syn_clec) C)
        (syn_wrex y (syn_cncs) (.classEq C (syn_cplc B (.cv y)))))
      (.classMem A (syn_cncs)) p0002
  have p0004 :=
    @g_anbi12d
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wbr A (syn_clec) B) (syn_wrex x (syn_cncs) (.classEq B (syn_cplc A (.cv x))))
      (syn_wbr B (syn_clec) C) (syn_wrex y (syn_cncs) (.classEq C (syn_cplc B (.cv y))))
      p0001 p0003
  have p0005 :=
    @g_reeanv (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y))) x y
      (syn_cncs) (syn_cncs) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009
  have p0006 :=
    @g_syl6bbr
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) C))
      (syn_wa (syn_wrex x (syn_cncs) (.classEq B (syn_cplc A (.cv x))))
        (syn_wrex y (syn_cncs) (.classEq C (syn_cplc B (.cv y)))))
      (syn_wrex x (syn_cncs) (syn_wrex y (syn_cncs)
          (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y))))))
      p0004 p0005
  have p0007 := @g_addceq1 B (syn_cplc A (.cv x)) (.cv y)
  have p0008 := @g_addcass A (.cv x) (.cv y)
  have p0009 :=
    @g_syl6eq (.classEq B (syn_cplc A (.cv x))) (syn_cplc B (.cv y))
      (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_cplc A (syn_cplc (.cv x) (.cv y)))
      p0007 p0008
  have p0010 :=
    @g_eqeq2d (.classEq B (syn_cplc A (.cv x))) (syn_cplc B (.cv y))
      (syn_cplc A (syn_cplc (.cv x) (.cv y))) C p0009
  have p0011 :=
    @g_biimpa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y)))
      (.classEq C (syn_cplc A (syn_cplc (.cv x) (.cv y)))) p0010
  have p0012 :=
    @g_simp1 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
  have p0013 := @g_ncaddccl (.cv x) (.cv y)
  have p0014 := @g_addlecncs A (syn_cplc (.cv x) (.cv y))
  have p0015 :=
    @g_syl2an
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (.classMem A (syn_cncs)) (.classMem (syn_cplc (.cv x) (.cv y)) (syn_cncs))
      (syn_wbr A (syn_clec) (syn_cplc A (syn_cplc (.cv x) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv y) (syn_cncs))) p0012 p0013
      p0014
  have p0016 := @g_breq2 C (syn_cplc A (syn_cplc (.cv x) (.cv y))) A (syn_clec)
  have p0017 :=
    @g_syl5ibrcom
      (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs)))
        (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv y) (syn_cncs))))
      (syn_wbr A (syn_clec) C) (.classEq C (syn_cplc A (syn_cplc (.cv x) (.cv y))))
      (syn_wbr A (syn_clec) (syn_cplc A (syn_cplc (.cv x) (.cv y)))) p0015 p0016
  have p0018 :=
    @g_syl5 (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y))))
      (.classEq C (syn_cplc A (syn_cplc (.cv x) (.cv y))))
      (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs)))
        (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv y) (syn_cncs))))
      (syn_wbr A (syn_clec) C) p0011 p0017
  have p0019 :=
    @g_rexlimdvva
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y))))
      (syn_wbr A (syn_clec) C) x y (syn_cncs) (syn_cncs) dv_cache_0005 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0009 p0018
  have p0020 :=
    @g_sylbid
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) C))
      (syn_wrex x (syn_cncs) (syn_wrex y (syn_cncs)
          (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y))))))
      (syn_wbr A (syn_clec) C) p0006 p0019
  exact p0020

@[expose]
noncomputable def g_nc0le1 (N : Class) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cncs))
        (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N))) :=
  by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_q : a ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_a : q ≠ a := Ne.symm fresh_a_ne_q
  have fresh_a_ne_p : a ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_a : p ≠ a := Ne.symm fresh_a_ne_p
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : a ∉ (N).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_a, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_a, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_csn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_x,
          not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_cnc (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_p_ne_a,
          not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_c1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_c1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_wss (.cv q) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, fresh_p_ne_a, or_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((syn_wss (syn_csn (.cv x)) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_a, or_false, not_false_eq_true])
  have dv_cache_0010 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0011 :
    x ∉
      ((syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_q,
          fresh_x_ne_p, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
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
  have dv_cache_0013 : q ∉ ((syn_cnc (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_a,
          not_false_eq_true])
  have dv_cache_0014 : q ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show q ≠ p from (by exact fresh_q_ne_p))
  have dv_cache_0015 :
    a ∉ ((syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_a_not_N, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_elncs a N dv_cache_0001
  have p0001 := @g_nceq (.cv a) (syn_c0)
  have p0002 := @g_df0c2
  have p0003 :=
    @g_syl6eqr (.classEq (.cv a) (syn_c0)) (syn_cnc (.cv a)) (syn_cnc (syn_c0)) (syn_c0c)
      p0001 p0002
  have p0004 :=
    @g_orcd (.classEq (.cv a) (syn_c0)) (.classEq (syn_cnc (.cv a)) (syn_c0c))
      (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) p0003
  have p0005 := @g_vex x
  have p0006 := @g_snss (.cv x) (.cv a) p0005
  have p0007 := @g_vex a
  have p0008 := @g_ncid (.cv a) p0007
  have p0009 := @g_snel1c (.cv x) p0005
  have p0010 := @g_sseq2 (.cv p) (.cv a) (.cv q)
  have p0011 := @g_sseq1 (.cv q) (syn_csn (.cv x)) (.cv a)
  have p0012 :=
    @g_rspc2ev (syn_wss (.cv q) (.cv p)) (syn_wss (syn_csn (.cv x)) (.cv a))
      (syn_wss (.cv q) (.cv a)) p q (.cv a) (syn_csn (.cv x)) (syn_cnc (.cv a)) (syn_c1c)
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0010 p0011
  have p0013 :=
    @g_mp3an12 (.classMem (.cv a) (syn_cnc (.cv a)))
      (.classMem (syn_csn (.cv x)) (syn_c1c)) (syn_wss (syn_csn (.cv x)) (.cv a))
      (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p))))
      p0008 p0009 p0012
  have p0014_e00_recanon :
    Nominal.NPrf (syn_wb (.objMem x a) (syn_wss (syn_csn (.cv x)) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0006
  have p0014 :=
    @g_sylbi (.objMem x a) (syn_wss (syn_csn (.cv x)) (.cv a))
      (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p))))
      p0014_e00_recanon p0013
  have p0015 :=
    @g_exlimiv (.objMem x a)
      (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p)))) x
      dv_cache_0011 p0014
  have p0016 := @g_n0 x (.cv a) dv_cache_0012
  have p0017 := @g_n_1cex
  have p0018 := @g_ncex (.cv a)
  have p0019 :=
    @g_brlec q p (syn_c1c) (syn_cnc (.cv a)) dv_cache_0007 dv_cache_0013 dv_cache_0005
      dv_cache_0014 p0017 p0018
  have p0020 :=
    @g_rexcom (syn_wss (.cv q) (.cv p)) q p (syn_c1c) (syn_cnc (.cv a)) dv_cache_0006
      dv_cache_0013 dv_cache_0014
  have p0021 :=
    @g_bitri (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a)))
      (syn_wrex q (syn_c1c) (syn_wrex p (syn_cnc (.cv a)) (syn_wss (.cv q) (.cv p))))
      (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p))))
      p0019 p0020
  have p0022_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wne (.cv a) (syn_c0)) (syn_wex x (.objMem x a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv syn_wex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0022 :=
    @g_n_3imtr4i (syn_wex x (.objMem x a))
      (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p))))
      (syn_wne (.cv a) (syn_c0)) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) p0015
      p0022_e01_recanon p0021
  have p0023 :=
    @g_olcd (syn_wne (.cv a) (syn_c0)) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a)))
      (.classEq (syn_cnc (.cv a)) (syn_c0c)) p0022
  have p0024 :=
    @g_pm2_61ine
      (syn_wo (.classEq (syn_cnc (.cv a)) (syn_c0c))
        (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))))
      (.cv a) (syn_c0) p0004 p0023
  have p0025 := @g_eqeq1 N (syn_cnc (.cv a)) (syn_c0c)
  have p0026 := @g_breq2 N (syn_cnc (.cv a)) (syn_c1c) (syn_clec)
  have p0027 :=
    @g_orbi12d (.classEq N (syn_cnc (.cv a))) (.classEq N (syn_c0c))
      (.classEq (syn_cnc (.cv a)) (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N)
      (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) p0025 p0026
  have p0028 :=
    @g_mpbiri (.classEq N (syn_cnc (.cv a)))
      (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N))
      (syn_wo (.classEq (syn_cnc (.cv a)) (syn_c0c))
        (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))))
      p0024 p0027
  have p0029 :=
    @g_exlimiv (.classEq N (syn_cnc (.cv a)))
      (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N)) a dv_cache_0015
      p0028
  have p0030 :=
    @g_sylbi (.classMem N (syn_cncs)) (syn_wex a (.classEq N (syn_cnc (.cv a))))
      (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N)) p0000 p0029
  exact p0030

@[expose]
noncomputable def g_nc0suc (m : Var) (N : Class) (dv_N_m : m ∉ N.fv) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cncs)) (syn_wo (.classEq N (syn_c0c))
          (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c)))))) :=
  by
  have dv_cache_0001 : m ∉ ((syn_c1c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : m ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_m, not_false_eq_true])
  have p0000 := @g_nc0le1 N
  have p0001 := @g_n_1cnc
  have p0002 := @g_dflec2 (syn_c1c) N m dv_cache_0001 dv_cache_0002
  have p0003 := @g_addccom (syn_c1c) (.cv m)
  have p0004 :=
    @g_eqeq2i (syn_cplc (syn_c1c) (.cv m)) (syn_cplc (.cv m) (syn_c1c)) N p0003
  have p0005 :=
    @g_rexbii (.classEq N (syn_cplc (syn_c1c) (.cv m)))
      (.classEq N (syn_cplc (.cv m) (syn_c1c))) m (syn_cncs) p0004
  have p0006 :=
    @g_syl6bb (syn_wa (.classMem (syn_c1c) (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr (syn_c1c) (syn_clec) N)
      (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (syn_c1c) (.cv m))))
      (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c)))) p0002 p0005
  have p0007 :=
    @g_mpan (.classMem (syn_c1c) (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wb (syn_wbr (syn_c1c) (syn_clec) N)
        (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c)))))
      p0001 p0006
  have p0008 :=
    @g_orbi2d (.classMem N (syn_cncs)) (syn_wbr (syn_c1c) (syn_clec) N)
      (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c))))
      (.classEq N (syn_c0c)) p0007
  have p0009 :=
    @g_mpbid (.classMem N (syn_cncs))
      (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N))
      (syn_wo (.classEq N (syn_c0c))
        (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c)))))
      p0000 p0008
  exact p0009

@[expose]
noncomputable def g_addceq0 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (syn_wb (.classEq (syn_cplc A B) (syn_c0c))
          (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Wff.neg (.classEq (syn_cplc A B) (syn_c0c)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have p0000 := @g_ianor (.classEq A (syn_c0c)) (.classEq B (syn_c0c))
  have p0001 := @g_nc0suc p A dv_cache_0001
  have p0002 :=
    @g_ord (.classMem A (syn_cncs)) (.classEq A (syn_c0c))
      (syn_wrex p (syn_cncs) (.classEq A (syn_cplc (.cv p) (syn_c1c)))) p0001
  have p0003 :=
    @g_adantr (.classMem A (syn_cncs))
      (.imp (.neg (.classEq A (syn_c0c)))
        (syn_wrex p (syn_cncs) (.classEq A (syn_cplc (.cv p) (syn_c1c)))))
      (.classMem B (syn_cncs)) p0002
  have p0004 := @g_addc32 (.cv p) (syn_c1c) B
  have p0005 := @g_n_0cnsuc (syn_cplc (.cv p) B)
  have p0006 :=
    @g_eqnetri (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B)
      (syn_cplc (syn_cplc (.cv p) B) (syn_c1c)) (syn_c0c) p0004 p0005
  have p0007 := @g_addceq1 A (syn_cplc (.cv p) (syn_c1c)) B
  have p0008 :=
    @g_eqeq1d (.classEq A (syn_cplc (.cv p) (syn_c1c))) (syn_cplc A B)
      (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B) (syn_c0c) p0007
  have p0009 :=
    @g_necon3bbid (.classEq A (syn_cplc (.cv p) (syn_c1c)))
      (.classEq (syn_cplc A B) (syn_c0c)) (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B)
      (syn_c0c) p0008
  have p0010 :=
    @g_mpbiri (.classEq A (syn_cplc (.cv p) (syn_c1c)))
      (.neg (.classEq (syn_cplc A B) (syn_c0c)))
      (syn_wne (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B) (syn_c0c)) p0006 p0009
  have p0011 :=
    @g_rexlimivw (.classEq A (syn_cplc (.cv p) (syn_c1c)))
      (.neg (.classEq (syn_cplc A B) (syn_c0c))) p (syn_cncs) dv_cache_0002 p0010
  have p0012 :=
    @g_syl6 (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (.neg (.classEq A (syn_c0c)))
      (syn_wrex p (syn_cncs) (.classEq A (syn_cplc (.cv p) (syn_c1c))))
      (.neg (.classEq (syn_cplc A B) (syn_c0c))) p0003 p0011
  have p0013 := @g_nc0suc p B dv_cache_0003
  have p0014 :=
    @g_ord (.classMem B (syn_cncs)) (.classEq B (syn_c0c))
      (syn_wrex p (syn_cncs) (.classEq B (syn_cplc (.cv p) (syn_c1c)))) p0013
  have p0015 :=
    @g_adantl (.classMem B (syn_cncs))
      (.imp (.neg (.classEq B (syn_c0c)))
        (syn_wrex p (syn_cncs) (.classEq B (syn_cplc (.cv p) (syn_c1c)))))
      (.classMem A (syn_cncs)) p0014
  have p0016 := @g_addcass A (.cv p) (syn_c1c)
  have p0017 := @g_n_0cnsuc (syn_cplc A (.cv p))
  have p0018 :=
    @g_eqnetrri (syn_cplc (syn_cplc A (.cv p)) (syn_c1c))
      (syn_cplc A (syn_cplc (.cv p) (syn_c1c))) (syn_c0c) p0016 p0017
  have p0019 := @g_addceq2 B (syn_cplc (.cv p) (syn_c1c)) A
  have p0020 :=
    @g_eqeq1d (.classEq B (syn_cplc (.cv p) (syn_c1c))) (syn_cplc A B)
      (syn_cplc A (syn_cplc (.cv p) (syn_c1c))) (syn_c0c) p0019
  have p0021 :=
    @g_necon3bbid (.classEq B (syn_cplc (.cv p) (syn_c1c)))
      (.classEq (syn_cplc A B) (syn_c0c)) (syn_cplc A (syn_cplc (.cv p) (syn_c1c)))
      (syn_c0c) p0020
  have p0022 :=
    @g_mpbiri (.classEq B (syn_cplc (.cv p) (syn_c1c)))
      (.neg (.classEq (syn_cplc A B) (syn_c0c)))
      (syn_wne (syn_cplc A (syn_cplc (.cv p) (syn_c1c))) (syn_c0c)) p0018 p0021
  have p0023 :=
    @g_rexlimivw (.classEq B (syn_cplc (.cv p) (syn_c1c)))
      (.neg (.classEq (syn_cplc A B) (syn_c0c))) p (syn_cncs) dv_cache_0002 p0022
  have p0024 :=
    @g_syl6 (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (.neg (.classEq B (syn_c0c)))
      (syn_wrex p (syn_cncs) (.classEq B (syn_cplc (.cv p) (syn_c1c))))
      (.neg (.classEq (syn_cplc A B) (syn_c0c))) p0015 p0023
  have p0025 :=
    @g_jaod (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (.neg (.classEq A (syn_c0c))) (.neg (.classEq (syn_cplc A B) (syn_c0c)))
      (.neg (.classEq B (syn_c0c))) p0012 p0024
  have p0026 :=
    @g_syl5bi (.neg (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))))
      (syn_wo (.neg (.classEq A (syn_c0c))) (.neg (.classEq B (syn_c0c))))
      (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (.neg (.classEq (syn_cplc A B) (syn_c0c))) p0000 p0025
  have p0027 :=
    @g_con4d (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c)))
      (.classEq (syn_cplc A B) (syn_c0c)) p0026
  have p0028 := @g_addceq12 A B (syn_c0c) (syn_c0c)
  have p0029 := @g_addcid2 (syn_c0c)
  have p0030 :=
    @g_syl6eq (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))) (syn_cplc A B)
      (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0028 p0029
  have p0031 :=
    @g_impbid1 (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (.classEq (syn_cplc A B) (syn_c0c))
      (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))) p0027 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part052`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dflec3 (f : Var) (M : Class) (N : Class) (a : Var) (b : Var)
    (dv_M_a : a ∉ M.fv) (dv_N_a : a ∉ N.fv) (dv_N_b : b ∉ N.fv) (dv_a_b : a ≠ b)
    (dv_a_f : a ≠ f) (dv_b_f : b ≠ f) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wb (syn_wbr M (syn_clec) N)
          (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ f } : Finset Var) ∪ M.fv ∪ N.fv ∪ ({ a } : Finset Var) ∪ ({ b } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_a : y ≠ a := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_ne_f : c ≠ f := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_f_ne_c : f ≠ c := Ne.symm fresh_c_ne_f
  have fresh_c_ne_a : c ≠ a := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_c : a ≠ c := Ne.symm fresh_c_ne_a
  have fresh_c_ne_b : c ≠ b := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have dv_cache_0001 : x ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0002 : y ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_N, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq M (syn_cnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq N (syn_cnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_N, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((syn_cnc (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_c_ne_x,
          not_false_eq_true])
  have dv_cache_0006 : c ∉ ((syn_cnc (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_c_ne_y,
          not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_cnc (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_y,
          not_false_eq_true])
  have dv_cache_0008 : c ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show c ≠ b from (by exact fresh_c_ne_b))
  have dv_cache_0009 : b ∉ ((syn_cnc (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_x,
          not_false_eq_true])
  have dv_cache_0010 : f ∉ ((syn_cres (syn_cid) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_c, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : f ∉ ((syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_c, (Ne.symm dv_b_f), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 : f ∉ ((Wff.objEq a c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, (Ne.symm dv_a_f), fresh_f_ne_c, or_false,
          not_false_eq_true])
  have dv_cache_0013 : a ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_c, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cnc (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_x,
          not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_c, dv_a_b, dv_a_f, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0016 :
    c ∉
      ((syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a,
          fresh_c_ne_b, fresh_c_ne_f, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : c ∉ ((syn_crn (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_c_ne_f,
          not_false_eq_true])
  have dv_cache_0018 : c ∉ ((syn_wss (syn_crn (.cv f)) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_f, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0019 :
    f ∉ ((syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_c,
          (Ne.symm dv_b_f), or_false, and_false, not_false_eq_true])
  have dv_cache_0020 : f ∉ ((Wff.classMem (.cv a) (syn_cnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_f), fresh_f_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0021 :
    a ∉ ((syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_c, dv_a_b,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((syn_cnc (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_y,
          not_false_eq_true])
  have dv_cache_0023 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show b ≠ a from (by exact Ne.symm dv_a_b))
  have dv_cache_0024 : b ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_b, not_false_eq_true])
  have dv_cache_0025 : a ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_M_a, not_false_eq_true])
  have dv_cache_0026 :
    a ∉ ((syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_M_a, fresh_a_ne_x, dv_N_a, fresh_a_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0027 :
    x ∉
      ((syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M
            (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_M, fresh_x_not_N, fresh_x_ne_a, fresh_x_ne_b,
          fresh_x_ne_f, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0028 :
    y ∉
      ((syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M
            (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_M, fresh_y_not_N, fresh_y_ne_a, fresh_y_ne_b,
          fresh_y_ne_f, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_elncs x M dv_cache_0001
  have p0001 := @g_elncs y N dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem M (syn_cncs)) (syn_wex x (.classEq M (syn_cnc (.cv x))))
      (.classMem N (syn_cncs)) (syn_wex y (.classEq N (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wa (syn_wex x (.classEq M (syn_cnc (.cv x))))
        (syn_wex y (.classEq N (syn_cnc (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))))
      p0002 p0003
  have p0005 := @g_ncex (.cv x)
  have p0006 := @g_ncex (.cv y)
  have p0007 :=
    @g_brlec c b (syn_cnc (.cv x)) (syn_cnc (.cv y)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0005 p0006
  have p0008 :=
    @g_rexcom (syn_wss (.cv c) (.cv b)) c b (syn_cnc (.cv x)) (syn_cnc (.cv y))
      dv_cache_0009 dv_cache_0006 dv_cache_0008
  have p0009 := @g_f1oi (.cv c)
  have p0010 := @g_f1of1 (.cv c) (.cv c) (syn_cres (syn_cid) (.cv c))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @g_f1ss (.cv c) (.cv c) (.cv b) (syn_cres (syn_cid) (.cv c))
  have p0013 :=
    @g_mpan (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv c))
      (syn_wss (.cv c) (.cv b)) (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b))
      p0011 p0012
  have p0014 := @g_idex
  have p0015 := @g_vex c
  have p0016 := @g_resex (syn_cid) (.cv c) p0014 p0015
  have p0017 := @g_f1eq1 (.cv c) (.cv b) (.cv f) (syn_cres (syn_cid) (.cv c))
  have p0018 :=
    @g_spcev (syn_wf1 (.cv f) (.cv c) (.cv b))
      (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b)) f
      (syn_cres (syn_cid) (.cv c)) dv_cache_0010 dv_cache_0011 p0016 p0017
  have p0019 :=
    @g_syl (syn_wss (.cv c) (.cv b))
      (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b))
      (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b))) p0013 p0018
  have p0020 := @g_f1eq2 (.cv a) (.cv c) (.cv b) (.cv f)
  have p0021_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a c)
        (syn_wb (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf1 (.cv f) (.cv c) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @g_exbidv (.objEq a c) (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wf1 (.cv f) (.cv c) (.cv b)) f dv_cache_0012 p0021_e00_recanon
  have p0022_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv c)) (syn_wb (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))
          (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl
          syn_cnin syn_wnan syn_ccom syn_copab syn_ccnv syn_cid
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0022 :=
    @g_rspcev (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))
      (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b))) a (.cv c) (syn_cnc (.cv x))
      dv_cache_0013 dv_cache_0014 dv_cache_0015 p0022_e00_recanon
  have p0023 :=
    @g_sylan2 (syn_wss (.cv c) (.cv b)) (.classMem (.cv c) (syn_cnc (.cv x)))
      (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b)))
      (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) p0019
      p0022
  have p0024 :=
    @g_rexlimiva (syn_wss (.cv c) (.cv b))
      (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) c
      (syn_cnc (.cv x)) dv_cache_0016 p0023
  have p0025 := @g_vex a
  have p0026 := @g_eqnc (.cv a) (.cv x) p0025
  have p0027 := @g_elnc (.cv a) (.cv x)
  have p0028 :=
    @g_bitr4i (.classEq (syn_cnc (.cv a)) (syn_cnc (.cv x)))
      (syn_wbr (.cv a) (syn_cen) (.cv x)) (.classMem (.cv a) (syn_cnc (.cv x))) p0026
      p0027
  have p0029 := @g_f1f1orn (.cv a) (.cv b) (.cv f)
  have p0030 := @g_vex f
  have p0031 := @g_f1oen (.cv a) (syn_crn (.cv f)) (.cv f) p0030
  have p0032 :=
    @g_syl (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf1o (.cv f) (.cv a) (syn_crn (.cv f)))
      (syn_wbr (.cv a) (syn_cen) (syn_crn (.cv f))) p0029 p0031
  have p0033 := @g_ensym (.cv a) (syn_crn (.cv f))
  have p0034 :=
    @g_sylib (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wbr (.cv a) (syn_cen) (syn_crn (.cv f)))
      (syn_wbr (syn_crn (.cv f)) (syn_cen) (.cv a)) p0032 p0033
  have p0035 := @g_elnc (syn_crn (.cv f)) (.cv a)
  have p0036 :=
    @g_sylibr (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wbr (syn_crn (.cv f)) (syn_cen) (.cv a))
      (.classMem (syn_crn (.cv f)) (syn_cnc (.cv a))) p0034 p0035
  have p0037 := @g_eleq2 (syn_cnc (.cv a)) (syn_cnc (.cv x)) (syn_crn (.cv f))
  have p0038 :=
    @g_syl5ib (syn_wf1 (.cv f) (.cv a) (.cv b))
      (.classMem (syn_crn (.cv f)) (syn_cnc (.cv a)))
      (.classEq (syn_cnc (.cv a)) (syn_cnc (.cv x)))
      (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x))) p0036 p0037
  have p0039 :=
    @g_sylbir (.classMem (.cv a) (syn_cnc (.cv x)))
      (.classEq (syn_cnc (.cv a)) (syn_cnc (.cv x)))
      (.imp (syn_wf1 (.cv f) (.cv a) (.cv b)) (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x))))
      p0028 p0038
  have p0040 :=
    @g_imp (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b))
      (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x))) p0039
  have p0041 := @g_f1f (.cv a) (.cv b) (.cv f)
  have p0042 := @g_frn (.cv a) (.cv b) (.cv f)
  have p0043 :=
    @g_syl (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf (.cv f) (.cv a) (.cv b))
      (syn_wss (syn_crn (.cv f)) (.cv b)) p0041 p0042
  have p0044 :=
    @g_adantl (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wss (syn_crn (.cv f)) (.cv b))
      (.classMem (.cv a) (syn_cnc (.cv x))) p0043
  have p0045 := @g_sseq1 (.cv c) (syn_crn (.cv f)) (.cv b)
  have p0046 :=
    @g_rspcev (syn_wss (.cv c) (.cv b)) (syn_wss (syn_crn (.cv f)) (.cv b)) c
      (syn_crn (.cv f)) (syn_cnc (.cv x)) dv_cache_0017 dv_cache_0005 dv_cache_0018 p0045
  have p0047 :=
    @g_syl2anc
      (syn_wa (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b)))
      (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x))) (syn_wss (syn_crn (.cv f)) (.cv b))
      (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) p0040 p0044 p0046
  have p0048 :=
    @g_ex (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) p0047
  have p0049 :=
    @g_exlimdv (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) f dv_cache_0019
      dv_cache_0020 p0048
  have p0050 :=
    @g_rexlimiv (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))
      (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) a (syn_cnc (.cv x))
      dv_cache_0021 p0049
  have p0051 :=
    @g_impbii (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b)))
      (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) p0024
      p0050
  have p0052 :=
    @g_rexbii (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b)))
      (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) b
      (syn_cnc (.cv y)) p0051
  have p0053 :=
    @g_bitri
      (syn_wrex c (syn_cnc (.cv x)) (syn_wrex b (syn_cnc (.cv y)) (syn_wss (.cv c) (.cv b))))
      (syn_wrex b (syn_cnc (.cv y)) (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))))
      (syn_wrex b (syn_cnc (.cv y))
        (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      p0008 p0052
  have p0054 :=
    @g_rexcom (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) b a (syn_cnc (.cv y))
      (syn_cnc (.cv x)) dv_cache_0022 dv_cache_0009 dv_cache_0023
  have p0055 :=
    @g_n_3bitri (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc (.cv y)))
      (syn_wrex c (syn_cnc (.cv x)) (syn_wrex b (syn_cnc (.cv y)) (syn_wss (.cv c) (.cv b))))
      (syn_wrex b (syn_cnc (.cv y))
        (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      (syn_wrex a (syn_cnc (.cv x))
        (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      p0007 p0053 p0054
  have p0056 := @g_breq12 M (syn_cnc (.cv x)) N (syn_cnc (.cv y)) (syn_clec)
  have p0057 := @g_simpl (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))
  have p0058 :=
    @g_rexeq (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) b N (syn_cnc (.cv y))
      dv_cache_0024 dv_cache_0007
  have p0059 :=
    @g_adantl (.classEq N (syn_cnc (.cv y)))
      (syn_wb (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))
        (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      (.classEq M (syn_cnc (.cv x))) p0058
  have p0060 :=
    @g_rexeqbidv (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))
      (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))
      (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) a M
      (syn_cnc (.cv x)) dv_cache_0025 dv_cache_0014 dv_cache_0026 p0057 p0059
  have p0061 :=
    @g_bibi12d (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))
      (syn_wbr M (syn_clec) N) (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc (.cv y)))
      (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      (syn_wrex a (syn_cnc (.cv x))
        (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      p0056 p0060
  have p0062 :=
    @g_mpbiri (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))
      (syn_wb (syn_wbr M (syn_clec) N)
        (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))
      (syn_wb (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc (.cv y)))
        (syn_wrex a (syn_cnc (.cv x))
          (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))
      p0055 p0061
  have p0063 :=
    @g_exlimivv (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))
      (syn_wb (syn_wbr M (syn_clec) N)
        (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))
      x y dv_cache_0027 dv_cache_0028 p0062
  have p0064 :=
    @g_sylbi (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))))
      (syn_wb (syn_wbr M (syn_clec) N)
        (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))
      p0004 p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part053`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nclenc (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv)
    (dv_B_f : f ∉ B.fv) (hyp_nclenc_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_nclenc_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({ f } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let g : Var := freshVar proofSupport 2
  let h : Var := freshVar proofSupport 3
  let i : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_f : p ≠ f := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_f : q ≠ f := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_ne_f : g ≠ f := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_g : f ≠ g := Ne.symm fresh_g_ne_f
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_h_not_B : h ∉ B.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_ne_f : h ≠ f := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_h : f ≠ h := Ne.symm fresh_h_ne_f
  have fresh_i : i ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_i_not_A : i ∉ A.fv := by
    intro h
    exact fresh_i (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_i_not_B : i ∉ B.fv := by
    intro h
    exact fresh_i (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_i_ne_f : i ≠ f := by
    intro h
    exact fresh_i (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_i : f ≠ i := Ne.symm fresh_i_ne_f
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_f : a ≠ f := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_f : b ≠ f := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_b : f ≠ b := Ne.symm fresh_b_ne_f
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_g : p ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_g_ne_p : g ≠ p := Ne.symm fresh_p_ne_g
  have fresh_p_ne_h : p ≠ h :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_h_ne_p : h ≠ p := Ne.symm fresh_p_ne_h
  have fresh_p_ne_i : p ≠ i :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_i_ne_p : i ≠ p := Ne.symm fresh_p_ne_i
  have fresh_q_ne_g : q ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_g_ne_q : g ≠ q := Ne.symm fresh_q_ne_g
  have fresh_q_ne_h : q ≠ h :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_h_ne_q : h ≠ q := Ne.symm fresh_q_ne_h
  have fresh_q_ne_i : q ≠ i :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_i_ne_q : i ≠ q := Ne.symm fresh_q_ne_i
  have fresh_g_ne_h : g ≠ h :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have fresh_g_ne_i : g ≠ i :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_i_ne_g : i ≠ g := Ne.symm fresh_g_ne_i
  have fresh_h_ne_i : h ≠ i :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_i_ne_h : i ≠ h := Ne.symm fresh_h_ne_i
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have dv_cache_0001 : p ∉ ((syn_cnc A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_p_not_A,
          not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_p_not_B,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_q_not_B,
          not_false_eq_true])
  have dv_cache_0004 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0005 : p ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ g from (by exact fresh_p_ne_g))
  have dv_cache_0006 : q ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show q ≠ g from (by exact fresh_q_ne_g))
  have dv_cache_0007 : h ∉ ((Class.cv p)).fv :=
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
          fresh_h_ne_p, not_false_eq_true])
  have dv_cache_0008 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0009 : i ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_i_ne_q, not_false_eq_true])
  have dv_cache_0010 : i ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_i_not_B, not_false_eq_true])
  have dv_cache_0011 : i ∉ ((syn_wf1o (.cv h) (.cv p) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_i_ne_p, fresh_i_not_A, fresh_i_ne_h, or_false,
          not_false_eq_true])
  have dv_cache_0012 : h ∉ ((syn_wf1o (.cv i) (.cv q) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_q, fresh_h_not_B, fresh_h_ne_i, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    f ∉ ((syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_i, fresh_f_ne_g, fresh_f_ne_h, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    f ∉ ((syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, dv_A_f, dv_B_f, fresh_f_ne_i, fresh_f_ne_g, fresh_f_ne_h,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    h ∉
      ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_h_ne_p, fresh_h_ne_q,
          fresh_h_ne_g, fresh_h_not_A, fresh_h_not_B, fresh_h_ne_f, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0016 :
    i ∉
      ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_i_ne_p, fresh_i_ne_q,
          fresh_i_ne_g, fresh_i_not_A, fresh_i_not_B, fresh_i_ne_f, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0017 : g ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0018 :
    g ∉ ((syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_p, fresh_g_not_A, fresh_g_ne_q, fresh_g_not_B,
          or_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((syn_cnc A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0020 : p ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0022 : f ∉ ((Wff.classEq (.cv a) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_a, dv_A_f, or_false, not_false_eq_true])
  have dv_cache_0023 : f ∉ ((Wff.classEq (.cv b) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_b, dv_B_f, or_false, not_false_eq_true])
  have dv_cache_0024 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0025 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0026 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_a_not_A,
          not_false_eq_true])
  have dv_cache_0028 : a ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_a_not_B,
          not_false_eq_true])
  have dv_cache_0029 : b ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_b_not_B,
          not_false_eq_true])
  have dv_cache_0030 : a ∉ ((syn_wex f (syn_wf1 (.cv f) A (.cv b)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, fresh_a_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0031 : b ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0032 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0033 : a ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show a ≠ f from (by exact fresh_a_ne_f))
  have dv_cache_0034 : b ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show b ≠ f from (by exact fresh_b_ne_f))
  have p0000 := @g_ncelncsi A hyp_nclenc_1
  have p0001 := @g_ncelncsi B hyp_nclenc_2
  have p0002 :=
    @g_dflec3 g (syn_cnc A) (syn_cnc B) p q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @g_mp2an (.classMem (syn_cnc A) (syn_cncs)) (.classMem (syn_cnc B) (syn_cncs))
      (syn_wb (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wrex p (syn_cnc A)
          (syn_wrex q (syn_cnc B) (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q))))))
      p0000 p0001 p0002
  have p0004 := @g_elnc (.cv p) A
  have p0005 := @g_bren (.cv p) A h dv_cache_0007 dv_cache_0008
  have p0006 :=
    @g_bitri (.classMem (.cv p) (syn_cnc A)) (syn_wbr (.cv p) (syn_cen) A)
      (syn_wex h (syn_wf1o (.cv h) (.cv p) A)) p0004 p0005
  have p0007 := @g_elnc (.cv q) B
  have p0008 := @g_bren (.cv q) B i dv_cache_0009 dv_cache_0010
  have p0009 :=
    @g_bitri (.classMem (.cv q) (syn_cnc B)) (syn_wbr (.cv q) (syn_cen) B)
      (syn_wex i (syn_wf1o (.cv i) (.cv q) B)) p0007 p0008
  have p0010 :=
    @g_anbi12i (.classMem (.cv p) (syn_cnc A)) (syn_wex h (syn_wf1o (.cv h) (.cv p) A))
      (.classMem (.cv q) (syn_cnc B)) (syn_wex i (syn_wf1o (.cv i) (.cv q) B)) p0006 p0009
  have p0011 :=
    @g_eeanv (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) h i dv_cache_0011
      dv_cache_0012
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))
      (syn_wa (syn_wex h (syn_wf1o (.cv h) (.cv p) A)) (syn_wex i (syn_wf1o (.cv i) (.cv q) B)))
      (syn_wex h (syn_wex i (syn_wa (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B))))
      p0010 p0011
  have p0013 := @g_f1of1 (.cv q) B (.cv i)
  have p0014 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv i) (.cv q) B) (syn_wf1o (.cv h) (.cv p) A)
      (syn_wf1 (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q)) p0013
  have p0015 :=
    @g_simp3 (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)
      (syn_wf1 (.cv g) (.cv p) (.cv q))
  have p0016 := @g_f1co (.cv p) (.cv q) B (.cv i) (.cv g)
  have p0017 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)
        (syn_wf1 (.cv g) (.cv p) (.cv q)))
      (syn_wf1 (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q))
      (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) B) p0014 p0015 p0016
  have p0018 := @g_f1ocnv (.cv p) A (.cv h)
  have p0019 := @g_f1of1 A (.cv p) (syn_ccnv (.cv h))
  have p0020 :=
    @g_syl (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (syn_ccnv (.cv h)) A (.cv p))
      (syn_wf1 (syn_ccnv (.cv h)) A (.cv p)) p0018 p0019
  have p0021 :=
    @g_n_3ad2ant1 (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)
      (syn_wf1 (syn_ccnv (.cv h)) A (.cv p)) (syn_wf1 (.cv g) (.cv p) (.cv q)) p0020
  have p0022 := @g_f1co A (.cv p) B (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))
  have p0023 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)
        (syn_wf1 (.cv g) (.cv p) (.cv q)))
      (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) B)
      (syn_wf1 (syn_ccnv (.cv h)) A (.cv p))
      (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B) p0017 p0021
      p0022
  have p0024 := @g_vex i
  have p0025 := @g_vex g
  have p0026 := @g_coex (.cv i) (.cv g) p0024 p0025
  have p0027 := @g_vex h
  have p0028 := @g_cnvex (.cv h) p0027
  have p0029 := @g_coex (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)) p0026 p0028
  have p0030 :=
    @g_f1eq1 A B (.cv f) (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))
  have p0031 :=
    @g_spcev (syn_wf1 (.cv f) A B)
      (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B) f
      (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) dv_cache_0013 dv_cache_0014
      p0029 p0030
  have p0032 :=
    @g_syl
      (syn_w3a (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)
        (syn_wf1 (.cv g) (.cv p) (.cv q)))
      (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B)
      (syn_wex f (syn_wf1 (.cv f) A B)) p0023 p0031
  have p0033 :=
    @g_n_3expia (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)
      (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)) p0032
  have p0034 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B))
      (.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B))) h i
      dv_cache_0015 dv_cache_0016 p0033
  have p0035 :=
    @g_sylbi (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))
      (syn_wex h (syn_wex i (syn_wa (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B))))
      (.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B))) p0012
      p0034
  have p0036 :=
    @g_exlimdv (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))
      (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)) g dv_cache_0017
      dv_cache_0018 p0035
  have p0037 :=
    @g_rexlimivv (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q)))
      (syn_wex f (syn_wf1 (.cv f) A B)) p q (syn_cnc A) (syn_cnc B) dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0004 p0036
  have p0038 :=
    @g_sylbi (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))
      (syn_wrex p (syn_cnc A)
        (syn_wrex q (syn_cnc B) (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q)))))
      (syn_wex f (syn_wf1 (.cv f) A B)) p0003 p0037
  have p0039 := @g_ncid A hyp_nclenc_1
  have p0040 := @g_ncid B hyp_nclenc_2
  have p0041 := @g_f1eq2 (.cv a) A (.cv b) (.cv f)
  have p0042 :=
    @g_exbidv (.classEq (.cv a) A) (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wf1 (.cv f) A (.cv b)) f dv_cache_0022 p0041
  have p0043 := @g_f1eq3 (.cv b) B A (.cv f)
  have p0044 :=
    @g_exbidv (.classEq (.cv b) B) (syn_wf1 (.cv f) A (.cv b)) (syn_wf1 (.cv f) A B) f
      dv_cache_0023 p0043
  have p0045 :=
    @g_rspc2ev (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))
      (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wex f (syn_wf1 (.cv f) A (.cv b))) a b A B
      (syn_cnc A) (syn_cnc B) dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 p0042 p0044
  have p0046 :=
    @g_mp3an12 (.classMem A (syn_cnc A)) (.classMem B (syn_cnc B))
      (syn_wex f (syn_wf1 (.cv f) A B))
      (syn_wrex a (syn_cnc A)
        (syn_wrex b (syn_cnc B) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      p0039 p0040 p0045
  have p0047 :=
    @g_dflec3 f (syn_cnc A) (syn_cnc B) a b dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0032 dv_cache_0033 dv_cache_0034
  have p0048 :=
    @g_mp2an (.classMem (syn_cnc A) (syn_cncs)) (.classMem (syn_cnc B) (syn_cncs))
      (syn_wb (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wrex a (syn_cnc A)
          (syn_wrex b (syn_cnc B) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))
      p0000 p0001 p0047
  have p0049 :=
    @g_sylibr (syn_wex f (syn_wf1 (.cv f) A B))
      (syn_wrex a (syn_cnc A)
        (syn_wrex b (syn_cnc B) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))
      (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) p0046 p0048
  have p0050 :=
    @g_impbii (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))
      (syn_wex f (syn_wf1 (.cv f) A B)) p0038 p0049
  exact p0050


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part054`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lenc (x : Var) (A : Class) (M : Class) (dv_A_x : x ∉ A.fv)
    (dv_M_x : x ∉ M.fv) (hyp_lenc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem M (syn_cncs))
        (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ M.fv
  let y : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let f : Var := freshVar proofSupport 3
  let g : Var := freshVar proofSupport 4
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
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_f_ne_x : f ≠ x := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_g_ne_x : g ≠ x := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_g : x ≠ g := Ne.symm fresh_g_ne_x
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_f : p ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_f_ne_p : f ≠ p := Ne.symm fresh_p_ne_f
  have fresh_p_ne_g : p ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_g_ne_p : g ≠ p := Ne.symm fresh_p_ne_g
  have fresh_q_ne_f : q ≠ f :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_f_ne_q : f ≠ q := Ne.symm fresh_q_ne_f
  have fresh_q_ne_g : q ≠ g :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_g_ne_q : g ≠ q := Ne.symm fresh_q_ne_g
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have dv_cache_0001 : y ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cnc (.cv y))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_p_ne_y,
          not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_p_not_A,
          not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0005 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0006 : f ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_p, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_y, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_q, not_false_eq_true])
  have dv_cache_0009 : g ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_A, not_false_eq_true])
  have dv_cache_0010 : g ∉ ((syn_wf1o (.cv f) (.cv p) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_p, fresh_g_ne_y, fresh_g_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0011 : f ∉ ((syn_wf1o (.cv g) (.cv q) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_q, fresh_f_not_A, fresh_f_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cima (.cv g) (.cv p))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_g, fresh_x_ne_p, or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_cnc (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_y,
          not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wss (syn_cima (.cv g) (.cv p)) A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_g, fresh_x_ne_p, dv_A_x, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    f ∉
      ((Wff.imp (syn_wss (.cv p) (.cv q))
          (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_p, fresh_f_ne_q,
          fresh_f_ne_y, fresh_f_ne_x, fresh_f_not_A, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0016 :
    g ∉
      ((Wff.imp (syn_wss (.cv p) (.cv q))
          (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_ne_p, fresh_g_ne_q,
          fresh_g_ne_y, fresh_g_ne_x, fresh_g_not_A, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0017 : q ∉ ((syn_cnc (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_y,
          not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x,
          fresh_p_not_A, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_y, fresh_q_ne_x,
          fresh_q_not_A, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 : x ∉ ((syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_A_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0021 : x ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_M_x, not_false_eq_true])
  have dv_cache_0022 :
    y ∉
      ((syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_M, fresh_y_not_A, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_elncs y M dv_cache_0001
  have p0001 := @g_ncex (.cv y)
  have p0002 := @g_ncex A
  have p0003 :=
    @g_brlec p q (syn_cnc (.cv y)) (syn_cnc A) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0001 p0002
  have p0004 := @g_elnc (.cv p) (.cv y)
  have p0005 := @g_bren (.cv p) (.cv y) f dv_cache_0006 dv_cache_0007
  have p0006 :=
    @g_bitri (.classMem (.cv p) (syn_cnc (.cv y))) (syn_wbr (.cv p) (syn_cen) (.cv y))
      (syn_wex f (syn_wf1o (.cv f) (.cv p) (.cv y))) p0004 p0005
  have p0007 := @g_elnc (.cv q) A
  have p0008 := @g_bren (.cv q) A g dv_cache_0008 dv_cache_0009
  have p0009 :=
    @g_bitri (.classMem (.cv q) (syn_cnc A)) (syn_wbr (.cv q) (syn_cen) A)
      (syn_wex g (syn_wf1o (.cv g) (.cv q) A)) p0007 p0008
  have p0010 :=
    @g_anbi12i (.classMem (.cv p) (syn_cnc (.cv y)))
      (syn_wex f (syn_wf1o (.cv f) (.cv p) (.cv y))) (.classMem (.cv q) (syn_cnc A))
      (syn_wex g (syn_wf1o (.cv g) (.cv q) A)) p0006 p0009
  have p0011 :=
    @g_eeanv (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) f g
      dv_cache_0010 dv_cache_0011
  have p0012 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv p) (syn_cnc (.cv y))) (.classMem (.cv q) (syn_cnc A)))
      (syn_wa (syn_wex f (syn_wf1o (.cv f) (.cv p) (.cv y)))
        (syn_wex g (syn_wf1o (.cv g) (.cv q) A)))
      (syn_wex f (syn_wex g
          (syn_wa (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A))))
      p0010 p0011
  have p0013 := @g_f1of1 (.cv q) A (.cv g)
  have p0014 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv g) (.cv q) A) (syn_wf1o (.cv f) (.cv p) (.cv y))
      (syn_wf1 (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q)) p0013
  have p0015 :=
    @g_simp3 (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
      (syn_wss (.cv p) (.cv q))
  have p0016 := @g_f1ores (.cv q) A (.cv p) (.cv g)
  have p0017 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
        (syn_wss (.cv p) (.cv q)))
      (syn_wf1 (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))
      (syn_wf1o (syn_cres (.cv g) (.cv p)) (.cv p) (syn_cima (.cv g) (.cv p))) p0014 p0015
      p0016
  have p0018 := @g_f1ocnv (.cv p) (.cv y) (.cv f)
  have p0019 :=
    @g_n_3ad2ant1 (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
      (syn_wf1o (syn_ccnv (.cv f)) (.cv y) (.cv p)) (syn_wss (.cv p) (.cv q)) p0018
  have p0020 :=
    @g_f1oco (.cv y) (.cv p) (syn_cima (.cv g) (.cv p)) (syn_cres (.cv g) (.cv p))
      (syn_ccnv (.cv f))
  have p0021 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
        (syn_wss (.cv p) (.cv q)))
      (syn_wf1o (syn_cres (.cv g) (.cv p)) (.cv p) (syn_cima (.cv g) (.cv p)))
      (syn_wf1o (syn_ccnv (.cv f)) (.cv y) (.cv p))
      (syn_wf1o (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))) (.cv y)
        (syn_cima (.cv g) (.cv p)))
      p0017 p0019 p0020
  have p0022 :=
    @g_f1ocnv (.cv y) (syn_cima (.cv g) (.cv p))
      (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f)))
  have p0023 := @g_vex g
  have p0024 := @g_vex p
  have p0025 := @g_resex (.cv g) (.cv p) p0023 p0024
  have p0026 := @g_vex f
  have p0027 := @g_cnvex (.cv f) p0026
  have p0028 := @g_coex (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f)) p0025 p0027
  have p0029 := @g_cnvex (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))) p0028
  have p0030 :=
    @g_f1oen (syn_cima (.cv g) (.cv p)) (.cv y)
      (syn_ccnv (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f)))) p0029
  have p0031 :=
    @g_n_3syl
      (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
        (syn_wss (.cv p) (.cv q)))
      (syn_wf1o (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))) (.cv y)
        (syn_cima (.cv g) (.cv p)))
      (syn_wf1o (syn_ccnv (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))))
        (syn_cima (.cv g) (.cv p)) (.cv y))
      (syn_wbr (syn_cima (.cv g) (.cv p)) (syn_cen) (.cv y)) p0021 p0022 p0030
  have p0032 := @g_elnc (syn_cima (.cv g) (.cv p)) (.cv y)
  have p0033 :=
    @g_sylibr
      (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
        (syn_wss (.cv p) (.cv q)))
      (syn_wbr (syn_cima (.cv g) (.cv p)) (syn_cen) (.cv y))
      (.classMem (syn_cima (.cv g) (.cv p)) (syn_cnc (.cv y))) p0031 p0032
  have p0034 := @g_imass2 (.cv p) (.cv q) (.cv g)
  have p0035 :=
    @g_n_3ad2ant3 (syn_wss (.cv p) (.cv q)) (syn_wf1o (.cv f) (.cv p) (.cv y))
      (syn_wss (syn_cima (.cv g) (.cv p)) (syn_cima (.cv g) (.cv q)))
      (syn_wf1o (.cv g) (.cv q) A) p0034
  have p0036 := @g_f1ofo (.cv q) A (.cv g)
  have p0037 := @g_foima (.cv q) A (.cv g)
  have p0038 :=
    @g_syl (syn_wf1o (.cv g) (.cv q) A) (syn_wfo (.cv g) (.cv q) A)
      (.classEq (syn_cima (.cv g) (.cv q)) A) p0036 p0037
  have p0039 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv g) (.cv q) A) (syn_wf1o (.cv f) (.cv p) (.cv y))
      (.classEq (syn_cima (.cv g) (.cv q)) A) (syn_wss (.cv p) (.cv q)) p0038
  have p0040 :=
    @g_sseqtrd
      (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
        (syn_wss (.cv p) (.cv q)))
      (syn_cima (.cv g) (.cv p)) (syn_cima (.cv g) (.cv q)) A p0035 p0039
  have p0041 := @g_sseq1 (.cv x) (syn_cima (.cv g) (.cv p)) A
  have p0042 :=
    @g_rspcev (syn_wss (.cv x) A) (syn_wss (syn_cima (.cv g) (.cv p)) A) x
      (syn_cima (.cv g) (.cv p)) (syn_cnc (.cv y)) dv_cache_0012 dv_cache_0013
      dv_cache_0014 p0041
  have p0043 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
        (syn_wss (.cv p) (.cv q)))
      (.classMem (syn_cima (.cv g) (.cv p)) (syn_cnc (.cv y)))
      (syn_wss (syn_cima (.cv g) (.cv p)) A)
      (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0033 p0040 p0042
  have p0044 :=
    @g_n_3expia (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)
      (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0043
  have p0045 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A))
      (.imp (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)))
      f g dv_cache_0015 dv_cache_0016 p0044
  have p0046 :=
    @g_sylbi
      (syn_wa (.classMem (.cv p) (syn_cnc (.cv y))) (.classMem (.cv q) (syn_cnc A)))
      (syn_wex f (syn_wex g
          (syn_wa (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A))))
      (.imp (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)))
      p0012 p0045
  have p0047 :=
    @g_rexlimivv (syn_wss (.cv p) (.cv q))
      (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p q (syn_cnc (.cv y)) (syn_cnc A)
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0005 p0046
  have p0048 :=
    @g_sylbi (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A))
      (syn_wrex p (syn_cnc (.cv y)) (syn_wrex q (syn_cnc A) (syn_wss (.cv p) (.cv q))))
      (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0003 p0047
  have p0049 := @g_vex x
  have p0050 := @g_nclec (.cv x) A p0049 hyp_lenc_1
  have p0051 := @g_eqnc (.cv x) (.cv y) p0049
  have p0052 := @g_elnc (.cv x) (.cv y)
  have p0053 :=
    @g_bitr4i (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y)))
      (syn_wbr (.cv x) (syn_cen) (.cv y)) (.classMem (.cv x) (syn_cnc (.cv y))) p0051
      p0052
  have p0054 := @g_breq1 (syn_cnc (.cv x)) (syn_cnc (.cv y)) (syn_cnc A) (syn_clec)
  have p0055 :=
    @g_sylbir (.classMem (.cv x) (syn_cnc (.cv y)))
      (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y)))
      (syn_wb (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc A))
        (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)))
      p0053 p0054
  have p0056 :=
    @g_syl5ib (syn_wss (.cv x) A) (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc A))
      (.classMem (.cv x) (syn_cnc (.cv y)))
      (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) p0050 p0055
  have p0057 :=
    @g_rexlimiv (syn_wss (.cv x) A) (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) x
      (syn_cnc (.cv y)) dv_cache_0020 p0056
  have p0058 :=
    @g_impbii (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A))
      (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0048 p0057
  have p0059 := @g_breq1 M (syn_cnc (.cv y)) (syn_cnc A) (syn_clec)
  have p0060 :=
    @g_rexeq (syn_wss (.cv x) A) x M (syn_cnc (.cv y)) dv_cache_0021 dv_cache_0013
  have p0061 :=
    @g_bibi12d (.classEq M (syn_cnc (.cv y))) (syn_wbr M (syn_clec) (syn_cnc A))
      (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A))
      (syn_wrex x M (syn_wss (.cv x) A))
      (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0059 p0060
  have p0062 :=
    @g_mpbiri (.classEq M (syn_cnc (.cv y)))
      (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A)))
      (syn_wb (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A))
        (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)))
      p0058 p0061
  have p0063 :=
    @g_exlimiv (.classEq M (syn_cnc (.cv y)))
      (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A))) y
      dv_cache_0022 p0062
  have p0064 :=
    @g_sylbi (.classMem M (syn_cncs)) (syn_wex y (.classEq M (syn_cnc (.cv y))))
      (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A))) p0000
      p0063
  exact p0064

@[expose]
noncomputable def g_tcncg (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (.classEq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A)))) :=
  by
  have p0000 := @g_ncelncs A V
  have p0001 := @g_tccl (syn_cnc A)
  have p0002 :=
    @g_syl (.classMem A V) (.classMem (syn_cnc A) (syn_cncs))
      (.classMem (syn_ctc (syn_cnc A)) (syn_cncs)) p0000 p0001
  have p0003 := @g_pw1exg A V
  have p0004 := @g_ncelncs (syn_cpw1 A) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv))
      (.classMem (syn_cnc (syn_cpw1 A)) (syn_cncs)) p0003 p0004
  have p0006 := @g_ncidg A V
  have p0007 := @g_pw1eltc (syn_cnc A) A
  have p0008 :=
    @g_syl2anc (.classMem A V) (.classMem (syn_cnc A) (syn_cncs))
      (.classMem A (syn_cnc A)) (.classMem (syn_cpw1 A) (syn_ctc (syn_cnc A))) p0000 p0006
      p0007
  have p0009 := @g_ncidg (syn_cpw1 A) (syn_cvv)
  have p0010 :=
    @g_syl (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv))
      (.classMem (syn_cpw1 A) (syn_cnc (syn_cpw1 A))) p0003 p0009
  have p0011 := @g_nceleq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A)) (syn_cpw1 A)
  have p0012 :=
    @g_syl22anc (.classMem A V) (.classMem (syn_ctc (syn_cnc A)) (syn_cncs))
      (.classMem (syn_cnc (syn_cpw1 A)) (syn_cncs))
      (.classMem (syn_cpw1 A) (syn_ctc (syn_cnc A)))
      (.classMem (syn_cpw1 A) (syn_cnc (syn_cpw1 A)))
      (.classEq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))) p0002 p0005 p0008 p0010
      p0011
  exact p0012

@[expose]
noncomputable def g_tcnc (A : Class) (hyp_tcnc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))) :=
  by
  have p0000 := @g_tcncg A (syn_cvv)
  have p0001 := Nominal.mp hyp_tcnc_1 p0000
  exact p0001

@[expose]
noncomputable def g_tcnc1c :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_cnc (syn_c1c))) (syn_cnc (syn_cpw1 (syn_c1c)))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_tcnc (syn_c1c) p0000
  exact p0001

@[expose]
noncomputable def g_tc11 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0002 : y ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_N, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq M (syn_cnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq N (syn_cnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_N, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉ ((syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_y_not_M, fresh_y_not_N, or_false, not_false_eq_true])
  have p0000 := @g_elncs x M dv_cache_0001
  have p0001 := @g_elncs y N dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem M (syn_cncs)) (syn_wex x (.classEq M (syn_cnc (.cv x))))
      (.classMem N (syn_cncs)) (syn_wex y (.classEq N (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wa (syn_wex x (.classEq M (syn_cnc (.cv x))))
        (syn_wex y (.classEq N (syn_cnc (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))))
      p0002 p0003
  have p0005 := @g_vex x
  have p0006 := @g_tcnc (.cv x) p0005
  have p0007 := @g_vex y
  have p0008 := @g_tcnc (.cv y) p0007
  have p0009 :=
    @g_eqeq12i (syn_ctc (syn_cnc (.cv x))) (syn_cnc (syn_cpw1 (.cv x)))
      (syn_ctc (syn_cnc (.cv y))) (syn_cnc (syn_cpw1 (.cv y))) p0006 p0008
  have p0010 := @g_enpw1 (.cv x) (.cv y)
  have p0011 := @g_eqnc (.cv x) (.cv y) p0005
  have p0012 := @g_pw1ex (.cv x) p0005
  have p0013 := @g_eqnc (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y)) p0012
  have p0014 :=
    @g_n_3bitr4ri (syn_wbr (.cv x) (syn_cen) (.cv y))
      (syn_wbr (syn_cpw1 (.cv x)) (syn_cen) (syn_cpw1 (.cv y)))
      (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y)))
      (.classEq (syn_cnc (syn_cpw1 (.cv x))) (syn_cnc (syn_cpw1 (.cv y)))) p0010 p0011
      p0013
  have p0015 :=
    @g_bitri (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_ctc (syn_cnc (.cv y))))
      (.classEq (syn_cnc (syn_cpw1 (.cv x))) (syn_cnc (syn_cpw1 (.cv y))))
      (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))) p0009 p0014
  have p0016 := @g_tceq M (syn_cnc (.cv x))
  have p0017 := @g_tceq N (syn_cnc (.cv y))
  have p0018 :=
    @g_eqeqan12d (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))) (syn_ctc M)
      (syn_ctc (syn_cnc (.cv x))) (syn_ctc N) (syn_ctc (syn_cnc (.cv y))) p0016 p0017
  have p0019 := @g_eqeq12 M (syn_cnc (.cv x)) N (syn_cnc (.cv y))
  have p0020 :=
    @g_bibi12d (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))
      (.classEq (syn_ctc M) (syn_ctc N))
      (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_ctc (syn_cnc (.cv y)))) (.classEq M N)
      (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))) p0018 p0019
  have p0021 :=
    @g_mpbiri (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))
      (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N))
      (syn_wb (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_ctc (syn_cnc (.cv y))))
        (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))))
      p0015 p0020
  have p0022 :=
    @g_exlimivv (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))
      (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N)) x y dv_cache_0005
      dv_cache_0006 p0021
  have p0023 :=
    @g_sylbi (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))))
      (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N)) p0004 p0022
  exact p0023


end NFChoice.DirectNominalPrf.WPPReplay

end
