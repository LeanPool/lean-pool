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

/-- Checked nominal proof certificate identified upstream as `g_sbthlem1`. -/
@[expose]
noncomputable def gSbthlem1 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (G : Class) (X : Class) (hyp_sbthlem1_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_sbthlem1_2 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_sbthlem1_3 : Nominal.NPrf (.classEq G (synCclos1 (synCdif X (synCrn R)) R)))
    (hyp_sbthlem1_4 : Nominal.NPrf (.classEq A (synCin X G)))
    (hyp_sbthlem1_5 : Nominal.NPrf (.classEq B (synCdif X G)))
    (hyp_sbthlem1_6 : Nominal.NPrf (.classEq C (synCin (synCrn R) G)))
    (hyp_sbthlem1_7 : Nominal.NPrf (.classEq D (synCdif (synCrn R) G))) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
          (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
        (synWbr (synCrn R) (synCen) X)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf1 R (synCdm R) (synCrn R)))
  have p0001 := @gSsid (synCrn R)
  have p0002 := (Nominal.biimpRefl (synWf R (synCdm R) (synCrn R)))
  have p0003 :=
    @gMpbiran2 (synWf R (synCdm R) (synCrn R)) (synWfn R (synCdm R))
      (synWss (synCrn R) (synCrn R)) p0001 p0002
  have p0004 := @gFunfn R
  have p0005 :=
    @gBitr4i (synWf R (synCdm R) (synCrn R)) (synWfn R (synCdm R)) (synWfun R)
      p0003 p0004
  have p0006 :=
    @gAnbi1i (synWf R (synCdm R) (synCrn R)) (synWfun R) (synWfun (synCcnv R))
      p0005
  have p0007 :=
    @gBitri (synWf1 R (synCdm R) (synCrn R))
      (synWa (synWf R (synCdm R) (synCrn R)) (synWfun (synCcnv R)))
      (synWa (synWfun R) (synWfun (synCcnv R))) p0000 p0006
  have p0008 :=
    @gBiimpri (synWf1 R (synCdm R) (synCrn R))
      (synWa (synWfun R) (synWfun (synCcnv R))) p0007
  have p0009 := @gInss1 X G
  have p0010 := @gSstr (synCin X G) X (synCdm R)
  have p0011 :=
    @gMpan (synWss (synCin X G) X) (synWss X (synCdm R))
      (synWss (synCin X G) (synCdm R)) p0009 p0010
  have p0012 :=
    @gSyl5eqss (synWss X (synCdm R)) A (synCin X G) (synCdm R) hyp_sbthlem1_4 p0011
  have p0013 :=
    @gAdantr (synWss X (synCdm R)) (synWss A (synCdm R)) (synWss (synCrn R) X)
      p0012
  have p0014 := @gF1ores (synCdm R) (synCrn R) A R
  have p0015 :=
    @gSyl2an (synWa (synWfun R) (synWfun (synCcnv R)))
      (synWf1 R (synCdm R) (synCrn R)) (synWss A (synCdm R))
      (synWf1o (synCres R A) A (synCima R A))
      (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)) p0008 p0013 p0014
  have p0016 := @gRnex R hyp_sbthlem1_1
  have p0017 := @gDifex X (synCrn R) hyp_sbthlem1_2 p0016
  have p0018 := @gClos1ex R (synCdif X (synCrn R)) p0017 hyp_sbthlem1_1
  have p0019 :=
    @gEqeltri G (synCclos1 (synCdif X (synCrn R)) R) (synCvv) hyp_sbthlem1_3 p0018
  have p0020 := @gInex X G hyp_sbthlem1_2 p0019
  have p0021 := @gEqeltri A (synCin X G) (synCvv) hyp_sbthlem1_4 p0020
  have p0022 := @gResex R A hyp_sbthlem1_1 p0021
  have p0023 := @gF1oen A (synCima R A) (synCres R A) p0022
  have p0024 :=
    @gSyl
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWf1o (synCres R A) A (synCima R A)) (synWbr A (synCen) (synCima R A))
      p0015 p0023
  have p0025 :=
    @gClos1baseima G R (synCdif X (synCrn R)) p0017 hyp_sbthlem1_1 hyp_sbthlem1_3
  have p0026 :=
    @gIneq2i G (synCun (synCdif X (synCrn R)) (synCima R G)) (synCrn R) p0025
  have p0027 := @gIndi (synCrn R) (synCdif X (synCrn R)) (synCima R G)
  have p0028 := @gDisjdif (synCrn R) X
  have p0029 :=
    @gUneq1i (synCin (synCrn R) (synCdif X (synCrn R))) (synC0)
      (synCin (synCrn R) (synCima R G)) p0028
  have p0030 := @gUncom (synC0) (synCin (synCrn R) (synCima R G))
  have p0031 := @gUn0 (synCin (synCrn R) (synCima R G))
  have p0032 :=
    @gEqtri (synCun (synC0) (synCin (synCrn R) (synCima R G)))
      (synCun (synCin (synCrn R) (synCima R G)) (synC0))
      (synCin (synCrn R) (synCima R G)) p0030 p0031
  have p0033 :=
    @gN3eqtri (synCin (synCrn R) (synCun (synCdif X (synCrn R)) (synCima R G)))
      (synCun (synCin (synCrn R) (synCdif X (synCrn R)))
        (synCin (synCrn R) (synCima R G)))
      (synCun (synC0) (synCin (synCrn R) (synCima R G)))
      (synCin (synCrn R) (synCima R G)) p0027 p0029 p0032
  have p0034 :=
    @gN3eqtri C (synCin (synCrn R) G)
      (synCin (synCrn R) (synCun (synCdif X (synCrn R)) (synCima R G)))
      (synCin (synCrn R) (synCima R G)) hyp_sbthlem1_6 p0026 p0033
  have p0035 := @gInss2 (synCrn R) (synCima R G)
  have p0036 :=
    @gA1i (synWss (synCin (synCrn R) (synCima R G)) (synCima R G))
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      p0035
  have p0037 :=
    @gSyl5eqss
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      C (synCin (synCrn R) (synCima R G)) (synCima R G) p0034 p0036
  have p0038 := @gImassrn R G
  have p0039 :=
    @gSimprr (synWa (synWfun R) (synWfun (synCcnv R))) (synWss X (synCdm R))
      (synWss (synCrn R) X)
  have p0040 :=
    @gSyl5ss
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synCima R G) (synCrn R) X p0038 p0039
  have p0041 := @gDifss X (synCrn R)
  have p0042 :=
    @gJctil
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWss (synCima R G) X) (synWss (synCdif X (synCrn R)) X) p0040 p0041
  have p0043 := @gUnss (synCdif X (synCrn R)) (synCima R G) X
  have p0044 :=
    @gSylib
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWa (synWss (synCdif X (synCrn R)) X) (synWss (synCima R G) X))
      (synWss (synCun (synCdif X (synCrn R)) (synCima R G)) X) p0042 p0043
  have p0045 :=
    @gSyl5eqss
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      G (synCun (synCdif X (synCrn R)) (synCima R G)) X p0025 p0044
  have p0046 := @gSseqin2 G X
  have p0047 :=
    @gSylib
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWss G X) (.classEq (synCin X G) G) p0045 p0046
  have p0048 :=
    @gSyl5eq
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      A (synCin X G) G hyp_sbthlem1_4 p0047
  have p0049 :=
    @gImaeq2d
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      A G R p0048
  have p0050 :=
    @gSseqtr4d
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      C (synCima R G) (synCima R A) p0037 p0049
  have p0051 := @gSsun2 (synCima R G) (synCdif X (synCrn R))
  have p0052 :=
    @gSseqtr4i (synCima R G) (synCun (synCdif X (synCrn R)) (synCima R G)) G p0051
      p0025
  have p0053 :=
    @gSseq1d
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synCima R A) (synCima R G) G p0049
  have p0054 :=
    @gMpbiri
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWss (synCima R A) G) (synWss (synCima R G) G) p0052 p0053
  have p0055 := @gImassrn R A
  have p0056 :=
    @gJctil
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWss (synCima R A) G) (synWss (synCima R A) (synCrn R)) p0054 p0055
  have p0057 := @gSsin (synCima R A) (synCrn R) G
  have p0058 :=
    @gSylib
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWa (synWss (synCima R A) (synCrn R)) (synWss (synCima R A) G))
      (synWss (synCima R A) (synCin (synCrn R) G)) p0056 p0057
  have p0059 :=
    @gSyl6sseqr
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synCima R A) (synCin (synCrn R) G) C p0058 hyp_sbthlem1_6
  have p0060 :=
    @gEqssd
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      C (synCima R A) p0050 p0059
  have p0061 :=
    @gBreqtrrd
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      A (synCima R A) C (synCen) p0024 p0060
  have p0062 := @gDifex X G hyp_sbthlem1_2 p0019
  have p0063 := @gEqeltri B (synCdif X G) (synCvv) hyp_sbthlem1_5 p0062
  have p0064 := @gEnrflx B p0063
  have p0065 := @gDifsscompl X G
  have p0066 :=
    @gA1i (synWss (synCdif X G) (synCcompl G))
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      p0065
  have p0067 := (Nominal.classEqRefl (synCdif X G))
  have p0068 := @gClos1base G R (synCdif X (synCrn R)) hyp_sbthlem1_3
  have p0069 := @gSscon34 (synCdif X (synCrn R)) G
  have p0070 :=
    @gMpbi (synWss (synCdif X (synCrn R)) G)
      (synWss (synCcompl G) (synCcompl (synCdif X (synCrn R)))) p0068 p0069
  have p0071 := (Nominal.classEqRefl (synCdif X (synCrn R)))
  have p0072 :=
    @gCompleqi (synCdif X (synCrn R)) (synCin X (synCcompl (synCrn R))) p0071
  have p0073 := @gIinun X (synCcompl (synCrn R))
  have p0074 := @gDblcompl (synCrn R)
  have p0075 :=
    @gUneq2i (synCcompl (synCcompl (synCrn R))) (synCrn R) (synCcompl X) p0074
  have p0076 :=
    @gN3eqtri (synCcompl (synCdif X (synCrn R)))
      (synCcompl (synCin X (synCcompl (synCrn R))))
      (synCun (synCcompl X) (synCcompl (synCcompl (synCrn R))))
      (synCun (synCcompl X) (synCrn R)) p0072 p0073 p0075
  have p0077 :=
    @gSseqtri (synCcompl G) (synCcompl (synCdif X (synCrn R)))
      (synCun (synCcompl X) (synCrn R)) p0070 p0076
  have p0078 := @gSslin (synCcompl G) (synCun (synCcompl X) (synCrn R)) X
  have p0079 := Nominal.mp p0077 p0078
  have p0080 :=
    @gEqsstri (synCdif X G) (synCin X (synCcompl G))
      (synCin X (synCun (synCcompl X) (synCrn R))) p0067 p0079
  have p0081 := @gIndi X (synCcompl X) (synCrn R)
  have p0082 := @gIncompl X
  have p0083 :=
    @gUneq1i (synCin X (synCcompl X)) (synC0) (synCin X (synCrn R)) p0082
  have p0084 := @gUncom (synC0) (synCin X (synCrn R))
  have p0085 := @gUn0 (synCin X (synCrn R))
  have p0086 :=
    @gEqtri (synCun (synC0) (synCin X (synCrn R)))
      (synCun (synCin X (synCrn R)) (synC0)) (synCin X (synCrn R)) p0084 p0085
  have p0087 :=
    @gN3eqtri (synCin X (synCun (synCcompl X) (synCrn R)))
      (synCun (synCin X (synCcompl X)) (synCin X (synCrn R)))
      (synCun (synC0) (synCin X (synCrn R))) (synCin X (synCrn R)) p0081 p0083 p0086
  have p0088 := @gInss2 X (synCrn R)
  have p0089 :=
    @gEqsstri (synCin X (synCun (synCcompl X) (synCrn R))) (synCin X (synCrn R))
      (synCrn R) p0087 p0088
  have p0090 :=
    @gSstri (synCdif X G) (synCin X (synCun (synCcompl X) (synCrn R))) (synCrn R)
      p0080 p0089
  have p0091 :=
    @gJctil
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWss (synCdif X G) (synCcompl G)) (synWss (synCdif X G) (synCrn R)) p0066
      p0090
  have p0092 := @gSsin (synCdif X G) (synCrn R) (synCcompl G)
  have p0093 :=
    @gSylib
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWa (synWss (synCdif X G) (synCrn R)) (synWss (synCdif X G) (synCcompl G)))
      (synWss (synCdif X G) (synCin (synCrn R) (synCcompl G))) p0091 p0092
  have p0094 := (Nominal.classEqRefl (synCdif (synCrn R) G))
  have p0095 :=
    @gEqtri D (synCdif (synCrn R) G) (synCin (synCrn R) (synCcompl G))
      hyp_sbthlem1_7 p0094
  have p0096 :=
    @gN3sstr4g
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synCdif X G) (synCin (synCrn R) (synCcompl G)) B D p0093 hyp_sbthlem1_5 p0095
  have p0097 := @gSsdif (synCrn R) X G
  have p0098 :=
    @gSyl
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWss (synCrn R) X) (synWss (synCdif (synCrn R) G) (synCdif X G)) p0039
      p0097
  have p0099 :=
    @gN3sstr4g
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synCdif (synCrn R) G) (synCdif X G) D B p0098 hyp_sbthlem1_7 hyp_sbthlem1_5
  have p0100 :=
    @gEqssd
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      B D p0096 p0099
  have p0101 :=
    @gSyl5breq
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      B B D (synCen) p0064 p0100
  have p0102 := @gIneq12i A (synCin X G) B (synCdif X G) hyp_sbthlem1_4 hyp_sbthlem1_5
  have p0103 := @gInindif X G
  have p0104 :=
    @gEqtri (synCin A B) (synCin (synCin X G) (synCdif X G)) (synC0) p0102 p0103
  have p0105 :=
    @gIneq12i C (synCin (synCrn R) G) D (synCdif (synCrn R) G) hyp_sbthlem1_6
      hyp_sbthlem1_7
  have p0106 := @gInindif (synCrn R) G
  have p0107 :=
    @gEqtri (synCin C D) (synCin (synCin (synCrn R) G) (synCdif (synCrn R) G))
      (synC0) p0105 p0106
  have p0108 := @gUnen A C B D
  have p0109 :=
    @gMpanr12 (synWa (synWbr A (synCen) C) (synWbr B (synCen) D))
      (.classEq (synCin A B) (synC0)) (.classEq (synCin C D) (synC0))
      (synWbr (synCun A B) (synCen) (synCun C D)) p0104 p0107 p0108
  have p0110 :=
    @gSyl2anc
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWbr A (synCen) C) (synWbr B (synCen) D)
      (synWbr (synCun A B) (synCen) (synCun C D)) p0061 p0101 p0109
  have p0111 := @gEnsym (synCun A B) (synCun C D)
  have p0112 :=
    @gSylib
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synWbr (synCun A B) (synCen) (synCun C D))
      (synWbr (synCun C D) (synCen) (synCun A B)) p0110 p0111
  have p0113 :=
    @gUneq12i C (synCin (synCrn R) G) D (synCdif (synCrn R) G) hyp_sbthlem1_6
      hyp_sbthlem1_7
  have p0114 := @gInundif (synCrn R) G
  have p0115 :=
    @gEqtri (synCun C D) (synCun (synCin (synCrn R) G) (synCdif (synCrn R) G))
      (synCrn R) p0113 p0114
  have p0116 := @gUneq12i A (synCin X G) B (synCdif X G) hyp_sbthlem1_4 hyp_sbthlem1_5
  have p0117 := @gInundif X G
  have p0118 :=
    @gEqtri (synCun A B) (synCun (synCin X G) (synCdif X G)) X p0116 p0117
  have p0119 :=
    @gN3brtr3g
      (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWa (synWss X (synCdm R)) (synWss (synCrn R) X)))
      (synCun C D) (synCun A B) (synCrn R) X (synCen) p0112 p0115 p0118
  exact p0119

/-- Checked nominal proof certificate identified upstream as `g_sbthlem2`. -/
@[expose]
noncomputable def gSbthlem2 (B : Class) (R : Class) (V : Class)
    (hyp_sbthlem2_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWfun R) (synWfun (synCcnv R)))
          (synW3a (.classMem B V) (synWss B (synCdm R)) (synWss (synCrn R) B)))
        (synWbr (synCrn R) (synCen) B)) :=
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
      ((Wff.imp (synWa (synWss B (synCdm R)) (synWss (synCrn R) B))
          (.imp (synWa (synWfun R) (synWfun (synCcnv R)))
            (synWbr (synCrn R) (synCen) B)))).fv :=
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
  have p0000 := @gSseq1 (.cv b) B (synCdm R)
  have p0001 := @gSseq2 (.cv b) B (synCrn R)
  have p0002 :=
    @gAnbi12d (.classEq (.cv b) B) (synWss (.cv b) (synCdm R)) (synWss B (synCdm R))
      (synWss (synCrn R) (.cv b)) (synWss (synCrn R) B) p0000 p0001
  have p0003 := @gBreq2 (.cv b) B (synCrn R) (synCen)
  have p0004 :=
    @gImbi2d (.classEq (.cv b) B) (synWbr (synCrn R) (synCen) (.cv b))
      (synWbr (synCrn R) (synCen) B) (synWa (synWfun R) (synWfun (synCcnv R)))
      p0003
  have p0005 :=
    @gImbi12d (.classEq (.cv b) B)
      (synWa (synWss (.cv b) (synCdm R)) (synWss (synCrn R) (.cv b)))
      (synWa (synWss B (synCdm R)) (synWss (synCrn R) B))
      (.imp (synWa (synWfun R) (synWfun (synCcnv R)))
        (synWbr (synCrn R) (synCen) (.cv b)))
      (.imp (synWa (synWfun R) (synWfun (synCcnv R))) (synWbr (synCrn R) (synCen) B))
      p0002 p0004
  have p0006 := @gVex b
  have p0007 := @gEqid (synCclos1 (synCdif (.cv b) (synCrn R)) R)
  have p0008 := @gEqid (synCin (.cv b) (synCclos1 (synCdif (.cv b) (synCrn R)) R))
  have p0009 := @gEqid (synCdif (.cv b) (synCclos1 (synCdif (.cv b) (synCrn R)) R))
  have p0010 :=
    @gEqid (synCin (synCrn R) (synCclos1 (synCdif (.cv b) (synCrn R)) R))
  have p0011 :=
    @gEqid (synCdif (synCrn R) (synCclos1 (synCdif (.cv b) (synCrn R)) R))
  have p0012 :=
    @gSbthlem1 (synCin (.cv b) (synCclos1 (synCdif (.cv b) (synCrn R)) R))
      (synCdif (.cv b) (synCclos1 (synCdif (.cv b) (synCrn R)) R))
      (synCin (synCrn R) (synCclos1 (synCdif (.cv b) (synCrn R)) R))
      (synCdif (synCrn R) (synCclos1 (synCdif (.cv b) (synCrn R)) R)) R
      (synCclos1 (synCdif (.cv b) (synCrn R)) R) (.cv b) hyp_sbthlem2_1 p0006 p0007
      p0008 p0009 p0010 p0011
  have p0013 :=
    @gExpcom (synWa (synWfun R) (synWfun (synCcnv R)))
      (synWa (synWss (.cv b) (synCdm R)) (synWss (synCrn R) (.cv b)))
      (synWbr (synCrn R) (synCen) (.cv b)) p0012
  have p0014 :=
    @gVtoclg
      (.imp (synWa (synWss (.cv b) (synCdm R)) (synWss (synCrn R) (.cv b)))
        (.imp (synWa (synWfun R) (synWfun (synCcnv R)))
          (synWbr (synCrn R) (synCen) (.cv b))))
      (.imp (synWa (synWss B (synCdm R)) (synWss (synCrn R) B))
        (.imp (synWa (synWfun R) (synWfun (synCcnv R))) (synWbr (synCrn R) (synCen) B)))
      b B V dv_cache_0001 dv_cache_0002 p0005 p0013
  have p0015 :=
    @gN3impib (.classMem B V) (synWss B (synCdm R)) (synWss (synCrn R) B)
      (.imp (synWa (synWfun R) (synWfun (synCcnv R))) (synWbr (synCrn R) (synCen) B))
      p0014
  have p0016 :=
    @gImpcom (synW3a (.classMem B V) (synWss B (synCdm R)) (synWss (synCrn R) B))
      (synWa (synWfun R) (synWfun (synCcnv R))) (synWbr (synCrn R) (synCen) B)
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_sbthlem3`. -/
@[expose]
noncomputable def gSbthlem3 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr A (synCen) C) (synWss C B))
          (synWa (synWbr B (synCen) D) (synWss D A))) (synWbr A (synCen) B)) :=
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
  have dv_cache_0005 : s ∉ ((synWf1o (.cv r) A C)).fv :=
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
  have dv_cache_0006 : r ∉ ((synWf1o (.cv s) B D)).fv :=
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
    r ∉ ((Wff.imp (synWa (synWss C B) (synWss D A)) (synWbr A (synCen) D))).fv :=
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
    s ∉ ((Wff.imp (synWa (synWss C B) (synWss D A)) (synWbr A (synCen) D))).fv :=
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
  have p0000 := @gBren A C r dv_cache_0001 dv_cache_0002
  have p0001 := @gBren B D s dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gAnbi12i (synWbr A (synCen) C) (synWex r (synWf1o (.cv r) A C))
      (synWbr B (synCen) D) (synWex s (synWf1o (.cv s) B D)) p0000 p0001
  have p0003 :=
    @gEeanv (synWf1o (.cv r) A C) (synWf1o (.cv s) B D) r s dv_cache_0005 dv_cache_0006
  have p0004 :=
    @gBitr4i (synWa (synWbr A (synCen) C) (synWbr B (synCen) D))
      (synWa (synWex r (synWf1o (.cv r) A C)) (synWex s (synWf1o (.cv s) B D)))
      (synWex r (synWex s (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D)))) p0002
      p0003
  have p0005 :=
    @gSimprl (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D)) (synWss C B)
      (synWss D A)
  have p0006 := @gF1ofo A C (.cv r)
  have p0007 := @gForn A C (.cv r)
  have p0008 :=
    @gSyl (synWf1o (.cv r) A C) (synWfo (.cv r) A C) (.classEq (synCrn (.cv r)) C)
      p0006 p0007
  have p0009 :=
    @gAd2antrr (synWf1o (.cv r) A C) (.classEq (synCrn (.cv r)) C)
      (synWf1o (.cv s) B D) (synWa (synWss C B) (synWss D A)) p0008
  have p0010 := @gF1odm B D (.cv s)
  have p0011 :=
    @gAd2antlr (synWf1o (.cv s) B D) (.classEq (synCdm (.cv s)) B)
      (synWf1o (.cv r) A C) (synWa (synWss C B) (synWss D A)) p0010
  have p0012 :=
    @gN3sstr4d
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      C B (synCrn (.cv r)) (synCdm (.cv s)) p0005 p0009 p0011
  have p0013 := @gDmcosseq (.cv s) (.cv r)
  have p0014 :=
    @gSyl
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synWss (synCrn (.cv r)) (synCdm (.cv s)))
      (.classEq (synCdm (synCcom (.cv s) (.cv r))) (synCdm (.cv r))) p0012 p0013
  have p0015 := @gF1odm A C (.cv r)
  have p0016 :=
    @gAd2antrr (synWf1o (.cv r) A C) (.classEq (synCdm (.cv r)) A)
      (synWf1o (.cv s) B D) (synWa (synWss C B) (synWss D A)) p0015
  have p0017 :=
    @gEqtrd
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synCdm (synCcom (.cv s) (.cv r))) (synCdm (.cv r)) A p0014 p0016
  have p0018 := @gF1ofun B D (.cv s)
  have p0019 := @gF1ofun A C (.cv r)
  have p0020 := @gFunco (.cv s) (.cv r)
  have p0021 :=
    @gSyl2anr (synWf1o (.cv s) B D) (synWfun (.cv s)) (synWfun (.cv r))
      (synWfun (synCcom (.cv s) (.cv r))) (synWf1o (.cv r) A C) p0018 p0019 p0020
  have p0022 := @gDff1o2 A C (.cv r)
  have p0023 :=
    @gSimp2bi (synWf1o (.cv r) A C) (synWfn (.cv r) A) (synWfun (synCcnv (.cv r)))
      (.classEq (synCrn (.cv r)) C) p0022
  have p0024 := @gDff1o2 B D (.cv s)
  have p0025 :=
    @gSimp2bi (synWf1o (.cv s) B D) (synWfn (.cv s) B) (synWfun (synCcnv (.cv s)))
      (.classEq (synCrn (.cv s)) D) p0024
  have p0026 := @gFunco (synCcnv (.cv r)) (synCcnv (.cv s))
  have p0027 :=
    @gSyl2an (synWf1o (.cv r) A C) (synWfun (synCcnv (.cv r)))
      (synWfun (synCcnv (.cv s)))
      (synWfun (synCcom (synCcnv (.cv r)) (synCcnv (.cv s)))) (synWf1o (.cv s) B D)
      p0023 p0025 p0026
  have p0028 := @gCnvco (.cv s) (.cv r)
  have p0029 :=
    @gFuneqi (synCcnv (synCcom (.cv s) (.cv r)))
      (synCcom (synCcnv (.cv r)) (synCcnv (.cv s))) p0028
  have p0030 :=
    @gSylibr (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
      (synWfun (synCcom (synCcnv (.cv r)) (synCcnv (.cv s))))
      (synWfun (synCcnv (synCcom (.cv s) (.cv r)))) p0027 p0029
  have p0031 :=
    @gJca (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
      (synWfun (synCcom (.cv s) (.cv r)))
      (synWfun (synCcnv (synCcom (.cv s) (.cv r)))) p0021 p0030
  have p0032 :=
    @gAdantr (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
      (synWa (synWfun (synCcom (.cv s) (.cv r)))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r)))))
      (synWa (synWss C B) (synWss D A)) p0031
  have p0033 :=
    @gDff1o2 (synCdm (synCcom (.cv s) (.cv r))) (synCrn (synCcom (.cv s) (.cv r)))
      (synCcom (.cv s) (.cv r))
  have p0034 := @gFunfn (synCcom (.cv s) (.cv r))
  have p0035 :=
    @gAnbi1i (synWfun (synCcom (.cv s) (.cv r)))
      (synWfn (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r))))
      (synWfun (synCcnv (synCcom (.cv s) (.cv r)))) p0034
  have p0036 := @gEqid (synCrn (synCcom (.cv s) (.cv r)))
  have p0037 :=
    (Nominal.biimpRefl
      (synW3a (synWfn (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r))))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r))))
        (.classEq (synCrn (synCcom (.cv s) (.cv r))) (synCrn (synCcom (.cv s) (.cv r))))))
  have p0038 :=
    @gMpbiran2
      (synW3a (synWfn (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r))))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r))))
        (.classEq (synCrn (synCcom (.cv s) (.cv r))) (synCrn (synCcom (.cv s) (.cv r)))))
      (synWa (synWfn (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r))))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r)))))
      (.classEq (synCrn (synCcom (.cv s) (.cv r))) (synCrn (synCcom (.cv s) (.cv r))))
      p0036 p0037
  have p0039 :=
    @gBitr4i
      (synWa (synWfun (synCcom (.cv s) (.cv r)))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r)))))
      (synWa (synWfn (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r))))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r)))))
      (synW3a (synWfn (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r))))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r))))
        (.classEq (synCrn (synCcom (.cv s) (.cv r))) (synCrn (synCcom (.cv s) (.cv r)))))
      p0035 p0038
  have p0040 :=
    @gBitr4i
      (synWf1o (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r)))
        (synCrn (synCcom (.cv s) (.cv r))))
      (synW3a (synWfn (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r))))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r))))
        (.classEq (synCrn (synCcom (.cv s) (.cv r))) (synCrn (synCcom (.cv s) (.cv r)))))
      (synWa (synWfun (synCcom (.cv s) (.cv r)))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r)))))
      p0033 p0039
  have p0041 :=
    @gSylibr
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synWa (synWfun (synCcom (.cv s) (.cv r)))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r)))))
      (synWf1o (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r)))
        (synCrn (synCcom (.cv s) (.cv r))))
      p0032 p0040
  have p0042 := @gVex s
  have p0043 := @gVex r
  have p0044 := @gCoex (.cv s) (.cv r) p0042 p0043
  have p0045 :=
    @gF1oen (synCdm (synCcom (.cv s) (.cv r))) (synCrn (synCcom (.cv s) (.cv r)))
      (synCcom (.cv s) (.cv r)) p0044
  have p0046 :=
    @gSyl
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synWf1o (synCcom (.cv s) (.cv r)) (synCdm (synCcom (.cv s) (.cv r)))
        (synCrn (synCcom (.cv s) (.cv r))))
      (synWbr (synCdm (synCcom (.cv s) (.cv r))) (synCen)
        (synCrn (synCcom (.cv s) (.cv r))))
      p0041 p0045
  have p0047 :=
    @gEqbrtrrd
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synCdm (synCcom (.cv s) (.cv r))) A (synCrn (synCcom (.cv s) (.cv r)))
      (synCen) p0017 p0046
  have p0048 := @gF1ofo B D (.cv s)
  have p0049 := @gForn B D (.cv s)
  have p0050 :=
    @gSyl (synWf1o (.cv s) B D) (synWfo (.cv s) B D) (.classEq (synCrn (.cv s)) D)
      p0048 p0049
  have p0051 := @gRnex (.cv s) p0042
  have p0052 :=
    @gSyl6eqelr (synWf1o (.cv s) B D) D (synCrn (.cv s)) (synCvv) p0050 p0051
  have p0053 :=
    @gAd2antlr (synWf1o (.cv s) B D) (.classMem D (synCvv)) (synWf1o (.cv r) A C)
      (synWa (synWss C B) (synWss D A)) p0052
  have p0054 :=
    @gSimprr (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D)) (synWss C B)
      (synWss D A)
  have p0055 :=
    @gSseqtr4d
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      D A (synCdm (synCcom (.cv s) (.cv r))) p0054 p0017
  have p0056 := @gRncoss (.cv s) (.cv r)
  have p0057 :=
    @gAd2antlr (synWf1o (.cv s) B D) (.classEq (synCrn (.cv s)) D)
      (synWf1o (.cv r) A C) (synWa (synWss C B) (synWss D A)) p0050
  have p0058 :=
    @gSyl5sseq
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synCrn (.cv s)) (synCrn (synCcom (.cv s) (.cv r))) D p0056 p0057
  have p0059 := @gSbthlem2 D (synCcom (.cv s) (.cv r)) (synCvv) p0044
  have p0060 :=
    @gSyl13anc
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synWa (synWfun (synCcom (.cv s) (.cv r)))
        (synWfun (synCcnv (synCcom (.cv s) (.cv r)))))
      (.classMem D (synCvv)) (synWss D (synCdm (synCcom (.cv s) (.cv r))))
      (synWss (synCrn (synCcom (.cv s) (.cv r))) D)
      (synWbr (synCrn (synCcom (.cv s) (.cv r))) (synCen) D) p0032 p0053 p0055 p0058
      p0059
  have p0061 := @gEntr A (synCrn (synCcom (.cv s) (.cv r))) D
  have p0062 :=
    @gSyl2anc
      (synWa (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
        (synWa (synWss C B) (synWss D A)))
      (synWbr A (synCen) (synCrn (synCcom (.cv s) (.cv r))))
      (synWbr (synCrn (synCcom (.cv s) (.cv r))) (synCen) D) (synWbr A (synCen) D)
      p0047 p0060 p0061
  have p0063 :=
    @gEx (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
      (synWa (synWss C B) (synWss D A)) (synWbr A (synCen) D) p0062
  have p0064 :=
    @gExlimivv (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))
      (.imp (synWa (synWss C B) (synWss D A)) (synWbr A (synCen) D)) r s
      dv_cache_0007 dv_cache_0008 p0063
  have p0065 :=
    @gSylbi (synWa (synWbr A (synCen) C) (synWbr B (synCen) D))
      (synWex r (synWex s (synWa (synWf1o (.cv r) A C) (synWf1o (.cv s) B D))))
      (.imp (synWa (synWss C B) (synWss D A)) (synWbr A (synCen) D)) p0004 p0064
  have p0066 :=
    @gImp (synWa (synWbr A (synCen) C) (synWbr B (synCen) D))
      (synWa (synWss C B) (synWss D A)) (synWbr A (synCen) D) p0065
  have p0067 :=
    @gAn4s (synWbr A (synCen) C) (synWbr B (synCen) D) (synWss C B) (synWss D A)
      (synWbr A (synCen) D) p0066
  have p0068 := @gEnsymi B D
  have p0069 :=
    @gAd2antrl (synWbr B (synCen) D) (synWbr D (synCen) B)
      (synWa (synWbr A (synCen) C) (synWss C B)) (synWss D A) p0068
  have p0070 := @gEntr A D B
  have p0071 :=
    @gSyl2anc
      (synWa (synWa (synWbr A (synCen) C) (synWss C B))
        (synWa (synWbr B (synCen) D) (synWss D A)))
      (synWbr A (synCen) D) (synWbr D (synCen) B) (synWbr A (synCen) B) p0067 p0069
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

/-- Checked nominal proof certificate identified upstream as `g_sbth`. -/
@[expose]
noncomputable def gSbth (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (.imp (synWa (synWbr A (synClec) B) (synWbr B (synClec) A)) (.classEq A B))) :=
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
  have dv_cache_0011 : a ∉ ((synWss (.cv g) (.cv b))).fv :=
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
  have dv_cache_0012 : b ∉ ((synWss (.cv d) (.cv a))).fv :=
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
  have dv_cache_0014 : d ∉ ((synWrex b B (synWss (.cv g) (.cv b)))).fv :=
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
  have dv_cache_0015 : g ∉ ((synWrex a A (synWss (.cv d) (.cv a)))).fv :=
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
  have dv_cache_0017 : a ∉ ((synCnc (.cv d))).fv :=
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
  have dv_cache_0018 : b ∉ ((Wff.classEq (synCnc (.cv g)) (synCnc (.cv d)))).fv :=
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
  have dv_cache_0019 : a ∉ ((Wff.classEq (synCnc (.cv g)) (synCnc (.cv d)))).fv :=
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
  have dv_cache_0020 : b ∉ ((synCnc (.cv d))).fv :=
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
  have dv_cache_0021 : a ∉ ((synCnc (.cv g))).fv :=
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
  have dv_cache_0022 : b ∉ ((Wff.classEq A (synCnc (.cv g)))).fv :=
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
    g ∉ ((synWa (.classMem A (synCncs)) (.classMem B (synCncs)))).fv :=
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
    d ∉ ((synWa (.classMem A (synCncs)) (.classMem B (synCncs)))).fv :=
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
    @gBrlecg g b A B (synCncs) (synCncs) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 :=
    @gBrlecg d a B A (synCncs) (synCncs) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008
  have p0002 :=
    @gAncoms (.classMem B (synCncs)) (.classMem A (synCncs))
      (synWb (synWbr B (synClec) A) (synWrex d B (synWrex a A (synWss (.cv d) (.cv a)))))
      p0001
  have p0003 :=
    @gAnbi12d (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWbr A (synClec) B) (synWrex g A (synWrex b B (synWss (.cv g) (.cv b))))
      (synWbr B (synClec) A) (synWrex d B (synWrex a A (synWss (.cv d) (.cv a))))
      p0000 p0002
  have p0004 :=
    @gReeanv (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)) b a B A dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    @gN2rexbii
      (synWrex b B (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
      (synWa (synWrex b B (synWss (.cv g) (.cv b))) (synWrex a A (synWss (.cv d) (.cv a))))
      g d A B p0004
  have p0006 :=
    @gReeanv (synWrex b B (synWss (.cv g) (.cv b)))
      (synWrex a A (synWss (.cv d) (.cv a))) g d A B dv_cache_0006 dv_cache_0002
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0007 :=
    @gBitri
      (synWrex g A (synWrex d B (synWrex b B
            (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))))
      (synWrex g A (synWrex d B (synWa (synWrex b B (synWss (.cv g) (.cv b)))
            (synWrex a A (synWss (.cv d) (.cv a))))))
      (synWa (synWrex g A (synWrex b B (synWss (.cv g) (.cv b))))
        (synWrex d B (synWrex a A (synWss (.cv d) (.cv a)))))
      p0005 p0006
  have p0008 :=
    @gSyl6bbr (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (synWbr A (synClec) B) (synWbr B (synClec) A))
      (synWa (synWrex g A (synWrex b B (synWss (.cv g) (.cv b))))
        (synWrex d B (synWrex a A (synWss (.cv d) (.cv a)))))
      (synWrex g A (synWrex d B (synWrex b B
            (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))))
      p0003 p0007
  have p0009 := @gNcseqnc A (.cv g)
  have p0010 := @gNcseqnc B (.cv d)
  have p0011 :=
    @gBi2anan9 (.classMem A (synCncs)) (.classEq A (synCnc (.cv g)))
      (.classMem (.cv g) A) (.classMem B (synCncs)) (.classEq B (synCnc (.cv d)))
      (.classMem (.cv d) B) p0009 p0010
  have p0012 :=
    @gBiimpar (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (.classEq A (synCnc (.cv g))) (.classEq B (synCnc (.cv d))))
      (synWa (.classMem (.cv g) A) (.classMem (.cv d) B)) p0011
  have p0013 :=
    @gSimplr (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g))
      (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))
  have p0014 := @gEnsym (.cv a) (.cv g)
  have p0015 :=
    @gSylib
      (synWa (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
        (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))))
      (synWbr (.cv a) (synCen) (.cv g)) (synWbr (.cv g) (synCen) (.cv a)) p0013 p0014
  have p0016 :=
    @gSimprl
      (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
      (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))
  have p0017 :=
    @gSimpll (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g))
      (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))
  have p0018 :=
    @gSimprr
      (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
      (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))
  have p0019 := @gSbthlem3 (.cv a) (.cv b) (.cv g) (.cv d)
  have p0020 :=
    @gSyl22anc
      (synWa (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
        (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))))
      (synWbr (.cv a) (synCen) (.cv g)) (synWss (.cv g) (.cv b))
      (synWbr (.cv b) (synCen) (.cv d)) (synWss (.cv d) (.cv a))
      (synWbr (.cv a) (synCen) (.cv b)) p0013 p0016 p0017 p0018 p0019
  have p0021 := @gEntr (.cv g) (.cv a) (.cv b)
  have p0022 :=
    @gSyl2anc
      (synWa (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
        (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))))
      (synWbr (.cv g) (synCen) (.cv a)) (synWbr (.cv a) (synCen) (.cv b))
      (synWbr (.cv g) (synCen) (.cv b)) p0015 p0020 p0021
  have p0023 := @gEntr (.cv g) (.cv b) (.cv d)
  have p0024 :=
    @gSyl2anc
      (synWa (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
        (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))))
      (synWbr (.cv g) (synCen) (.cv b)) (synWbr (.cv b) (synCen) (.cv d))
      (synWbr (.cv g) (synCen) (.cv d)) p0022 p0017 p0023
  have p0025 :=
    @gEx (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
      (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))
      (synWbr (.cv g) (synCen) (.cv d)) p0024
  have p0026 := @gElnc (.cv b) (.cv d)
  have p0027 := @gElnc (.cv a) (.cv g)
  have p0028 :=
    @gAnbi12i (.classMem (.cv b) (synCnc (.cv d))) (synWbr (.cv b) (synCen) (.cv d))
      (.classMem (.cv a) (synCnc (.cv g))) (synWbr (.cv a) (synCen) (.cv g)) p0026
      p0027
  have p0029 := @gVex g
  have p0030 := @gEqnc (.cv g) (.cv d) p0029
  have p0031 :=
    @gImbi2i (.classEq (synCnc (.cv g)) (synCnc (.cv d)))
      (synWbr (.cv g) (synCen) (.cv d))
      (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))) p0030
  have p0032 :=
    @gN3imtr4i
      (synWa (synWbr (.cv b) (synCen) (.cv d)) (synWbr (.cv a) (synCen) (.cv g)))
      (.imp (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))
        (synWbr (.cv g) (synCen) (.cv d)))
      (synWa (.classMem (.cv b) (synCnc (.cv d))) (.classMem (.cv a) (synCnc (.cv g))))
      (.imp (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))
        (.classEq (synCnc (.cv g)) (synCnc (.cv d))))
      p0025 p0028 p0031
  have p0033 :=
    @gRexlimivv (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))
      (.classEq (synCnc (.cv g)) (synCnc (.cv d))) b a (synCnc (.cv d))
      (synCnc (.cv g)) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0013 p0032
  have p0034 :=
    @gRexeq (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))) b
      B (synCnc (.cv d)) dv_cache_0003 dv_cache_0020
  have p0035 :=
    @gRexeq (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))) a A
      (synCnc (.cv g)) dv_cache_0007 dv_cache_0021
  have p0036 :=
    @gRexbidv (.classEq A (synCnc (.cv g)))
      (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))))
      (synWrex a (synCnc (.cv g))
        (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a))))
      b (synCnc (.cv d)) dv_cache_0022 p0035
  have p0037 :=
    @gSylan9bbr (.classEq B (synCnc (.cv d)))
      (synWrex b B (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
      (synWrex b (synCnc (.cv d))
        (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
      (.classEq A (synCnc (.cv g)))
      (synWrex b (synCnc (.cv d)) (synWrex a (synCnc (.cv g))
          (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
      p0034 p0036
  have p0038 := @gEqeq12 A (synCnc (.cv g)) B (synCnc (.cv d))
  have p0039 :=
    @gImbi12d (synWa (.classEq A (synCnc (.cv g))) (.classEq B (synCnc (.cv d))))
      (synWrex b B (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
      (synWrex b (synCnc (.cv d)) (synWrex a (synCnc (.cv g))
          (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
      (.classEq A B) (.classEq (synCnc (.cv g)) (synCnc (.cv d))) p0037 p0038
  have p0040 :=
    @gMpbiri (synWa (.classEq A (synCnc (.cv g))) (.classEq B (synCnc (.cv d))))
      (.imp (synWrex b B
          (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
        (.classEq A B))
      (.imp (synWrex b (synCnc (.cv d)) (synWrex a (synCnc (.cv g))
            (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
        (.classEq (synCnc (.cv g)) (synCnc (.cv d))))
      p0033 p0039
  have p0041 :=
    @gSyl
      (synWa (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (synWa (.classMem (.cv g) A) (.classMem (.cv d) B)))
      (synWa (.classEq A (synCnc (.cv g))) (.classEq B (synCnc (.cv d))))
      (.imp (synWrex b B
          (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
        (.classEq A B))
      p0012 p0040
  have p0042 :=
    @gRexlimdvva (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWrex b B (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))
      (.classEq A B) g d A B dv_cache_0006 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0016 p0041
  have p0043 :=
    @gSylbid (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (synWbr A (synClec) B) (synWbr B (synClec) A))
      (synWrex g A (synWrex d B (synWrex b B
            (synWrex a A (synWa (synWss (.cv g) (.cv b)) (synWss (.cv d) (.cv a)))))))
      (.classEq A B) p0008 p0042
  exact p0043

/-- Checked nominal proof certificate identified upstream as `g_ltlenlec`. -/
@[expose]
noncomputable def gLtlenlec (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWb (synWbr M (synCltc) N)
          (synWa (synWbr M (synClec) N) (.neg (synWbr N (synClec) M))))) :=
  by
  have p0000 := @gBrltc M N
  have p0001 := @gNclecid M
  have p0002 := @gBreq1 M N M (synClec)
  have p0003 :=
    @gSyl5ibcom (.classMem M (synCncs)) (synWbr M (synClec) M) (.classEq M N)
      (synWbr N (synClec) M) p0001 p0002
  have p0004 :=
    @gAd2antrr (.classMem M (synCncs)) (.imp (.classEq M N) (synWbr N (synClec) M))
      (.classMem N (synCncs)) (synWbr M (synClec) N) p0003
  have p0005 := @gSbth M N
  have p0006 :=
    @gExpdimp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr M (synClec) N) (synWbr N (synClec) M) (.classEq M N) p0005
  have p0007 :=
    @gImpbid
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWbr M (synClec) N))
      (.classEq M N) (synWbr N (synClec) M) p0004 p0006
  have p0008 :=
    @gNecon3abid
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWbr M (synClec) N))
      (synWbr N (synClec) M) M N p0007
  have p0009 :=
    @gPm532da (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr M (synClec) N) (synWne M N) (.neg (synWbr N (synClec) M)) p0008
  have p0010 :=
    @gSyl5bb (synWbr M (synCltc) N) (synWa (synWbr M (synClec) N) (synWne M N))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWa (synWbr M (synClec) N) (.neg (synWbr N (synClec) M))) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_addlec`. -/
@[expose]
noncomputable def gAddlec (M : Class) (N : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M V) (.classMem N W) (synWne (synCplc M N) (synC0)))
        (synWbr M (synClec) (synCplc M N))) :=
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
  have dv_cache_0008 : y ∉ ((synWss (.cv x) (.cv z))).fv :=
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
  have dv_cache_0009 : z ∉ ((synCplc M N)).fv :=
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
  have dv_cache_0011 : x ∉ ((synCplc M N)).fv :=
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
    @gEladdc (.cv z) M N x y dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @gSsun1 (.cv x) (.cv y)
  have p0002 := @gSseq2 (.cv z) (synCun (.cv x) (.cv y)) (.cv x)
  have p0003 :=
    @gMpbiri (.classEq (.cv z) (synCun (.cv x) (.cv y))) (synWss (.cv x) (.cv z))
      (synWss (.cv x) (synCun (.cv x) (.cv y))) p0001 p0002
  have p0004 :=
    @gAdantl (.classEq (.cv z) (synCun (.cv x) (.cv y))) (synWss (.cv x) (.cv z))
      (.classEq (synCin (.cv x) (.cv y)) (synC0)) p0003
  have p0005 :=
    @gRexlimivw
      (synWa (.classEq (synCin (.cv x) (.cv y)) (synC0))
        (.classEq (.cv z) (synCun (.cv x) (.cv y))))
      (synWss (.cv x) (.cv z)) y N dv_cache_0008 p0004
  have p0006 :=
    @gReximi
      (synWrex y N (synWa (.classEq (synCin (.cv x) (.cv y)) (synC0))
          (.classEq (.cv z) (synCun (.cv x) (.cv y)))))
      (synWss (.cv x) (.cv z)) x M p0005
  have p0007 :=
    @gSylbi (.classMem (.cv z) (synCplc M N))
      (synWrex x M (synWrex y N (synWa (.classEq (synCin (.cv x) (.cv y)) (synC0))
            (.classEq (.cv z) (synCun (.cv x) (.cv y))))))
      (synWrex x M (synWss (.cv x) (.cv z))) p0000 p0006
  have p0008 :=
    @gAncli (.classMem (.cv z) (synCplc M N)) (synWrex x M (synWss (.cv x) (.cv z)))
      p0007
  have p0009 :=
    @gEximi (.classMem (.cv z) (synCplc M N))
      (synWa (.classMem (.cv z) (synCplc M N)) (synWrex x M (synWss (.cv x) (.cv z))))
      z p0008
  have p0010 := @gN0 z (synCplc M N) dv_cache_0009
  have p0011 :=
    @gRexcom (synWss (.cv x) (.cv z)) x z M (synCplc M N) dv_cache_0010 dv_cache_0011
      dv_cache_0012
  have p0012 :=
    (Nominal.biimpRefl (synWrex z (synCplc M N) (synWrex x M (synWss (.cv x) (.cv z)))))
  have p0013 :=
    @gBitri (synWrex x M (synWrex z (synCplc M N) (synWss (.cv x) (.cv z))))
      (synWrex z (synCplc M N) (synWrex x M (synWss (.cv x) (.cv z))))
      (synWex z (synWa (.classMem (.cv z) (synCplc M N))
          (synWrex x M (synWss (.cv x) (.cv z)))))
      p0011 p0012
  have p0014 :=
    @gN3imtr4i (synWex z (.classMem (.cv z) (synCplc M N)))
      (synWex z (synWa (.classMem (.cv z) (synCplc M N))
          (synWrex x M (synWss (.cv x) (.cv z)))))
      (synWne (synCplc M N) (synC0))
      (synWrex x M (synWrex z (synCplc M N) (synWss (.cv x) (.cv z)))) p0009 p0010
      p0013
  have p0015 :=
    @gN3ad2ant3 (synWne (synCplc M N) (synC0)) (.classMem M V)
      (synWrex x M (synWrex z (synCplc M N) (synWss (.cv x) (.cv z)))) (.classMem N W)
      p0014
  have p0016 := @gAddcexg M N V W
  have p0017 :=
    @gBrlecg x z M (synCplc M N) V (synCvv) dv_cache_0003 dv_cache_0011 dv_cache_0009
      dv_cache_0012
  have p0018 :=
    @gSyldan (.classMem M V) (.classMem N W) (.classMem (synCplc M N) (synCvv))
      (synWb (synWbr M (synClec) (synCplc M N))
        (synWrex x M (synWrex z (synCplc M N) (synWss (.cv x) (.cv z)))))
      p0016 p0017
  have p0019 :=
    @gN3adant3 (.classMem M V) (.classMem N W)
      (synWb (synWbr M (synClec) (synCplc M N))
        (synWrex x M (synWrex z (synCplc M N) (synWss (.cv x) (.cv z)))))
      (synWne (synCplc M N) (synC0)) p0018
  have p0020 :=
    @gMpbird (synW3a (.classMem M V) (.classMem N W) (synWne (synCplc M N) (synC0)))
      (synWbr M (synClec) (synCplc M N))
      (synWrex x M (synWrex z (synCplc M N) (synWss (.cv x) (.cv z)))) p0015 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_addlecncs`. -/
@[expose]
noncomputable def gAddlecncs (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWbr M (synClec) (synCplc M N))) :=
  by
  have p0000 := @gNcaddccl M N
  have p0001 := @gNulnnc
  have p0002 := @gEleq1 (synCplc M N) (synC0) (synCncs)
  have p0003 :=
    @gMtbiri (.classEq (synCplc M N) (synC0)) (.classMem (synCplc M N) (synCncs))
      (.classMem (synC0) (synCncs)) p0001 p0002
  have p0004 :=
    @gNecon2ai (.classMem (synCplc M N) (synCncs)) (synCplc M N) (synC0) p0003
  have p0005 :=
    @gSyl (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classMem (synCplc M N) (synCncs)) (synWne (synCplc M N) (synC0)) p0000 p0004
  have p0006 := @gAddlec M N (synCncs) (synCncs)
  have p0007 :=
    @gMpd3an3 (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWne (synCplc M N) (synC0)) (synWbr M (synClec) (synCplc M N)) p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dflec2`. -/
@[expose]
noncomputable def gDflec2 (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWb (synWbr M (synClec) N)
          (synWrex p (synCncs) (.classEq N (synCplc M (.cv p)))))) :=
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
  have dv_cache_0005 : p ∉ ((synCnc (synCdif (.cv b) (.cv a)))).fv :=
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
  have dv_cache_0006 : p ∉ ((synCncs)).fv :=
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
      ((Wff.classEq (synCnc (.cv b))
          (synCplc (synCnc (.cv a)) (synCnc (synCdif (.cv b) (.cv a)))))).fv :=
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
    p ∉ ((synWa (.classEq N (synCnc (.cv b))) (.classEq M (synCnc (.cv a))))).fv :=
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
    a ∉ ((synWrex p (synCncs) (.classEq N (synCplc M (.cv p))))).fv :=
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
    b ∉ ((synWrex p (synCncs) (.classEq N (synCplc M (.cv p))))).fv :=
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
    a ∉ ((synWa (.classMem M (synCncs)) (.classMem N (synCncs)))).fv :=
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
    b ∉ ((synWa (.classMem M (synCncs)) (.classMem N (synCncs)))).fv :=
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
  have dv_cache_0014 : p ∉ ((synWbr M (synClec) N)).fv :=
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
    p ∉ ((synWa (.classMem M (synCncs)) (.classMem N (synCncs)))).fv :=
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
    @gBrlecg a b M N (synCncs) (synCncs) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @gNcseqnc M (.cv a)
  have p0002 := @gNcseqnc N (.cv b)
  have p0003 :=
    @gBi2anan9 (.classMem M (synCncs)) (.classEq M (synCnc (.cv a)))
      (.classMem (.cv a) M) (.classMem N (synCncs)) (.classEq N (synCnc (.cv b)))
      (.classMem (.cv b) N) p0001 p0002
  have p0004 :=
    @gBiimpar (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWa (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b))))
      (synWa (.classMem (.cv a) M) (.classMem (.cv b) N)) p0003
  have p0005 := @gVex b
  have p0006 := @gVex a
  have p0007 := @gDifex (.cv b) (.cv a) p0005 p0006
  have p0008 := @gNcelncsi (synCdif (.cv b) (.cv a)) p0007
  have p0009 := @gDisjdif (.cv a) (.cv b)
  have p0010 := @gNcdisjun (.cv a) (synCdif (.cv b) (.cv a)) p0006 p0007
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @gUndif2 (.cv a) (.cv b)
  have p0013 := @gSsequn1 (.cv a) (.cv b)
  have p0014 :=
    @gBiimpi (synWss (.cv a) (.cv b)) (.classEq (synCun (.cv a) (.cv b)) (.cv b)) p0013
  have p0015 :=
    @gSyl5eq (synWss (.cv a) (.cv b)) (synCun (.cv a) (synCdif (.cv b) (.cv a)))
      (synCun (.cv a) (.cv b)) (.cv b) p0012 p0014
  have p0016 :=
    @gNceqd (synWss (.cv a) (.cv b)) (synCun (.cv a) (synCdif (.cv b) (.cv a)))
      (.cv b) p0015
  have p0017 :=
    @gSyl5reqr (synWss (.cv a) (.cv b))
      (synCplc (synCnc (.cv a)) (synCnc (synCdif (.cv b) (.cv a))))
      (synCnc (synCun (.cv a) (synCdif (.cv b) (.cv a)))) (synCnc (.cv b)) p0011 p0016
  have p0018 := @gAddceq2 (.cv p) (synCnc (synCdif (.cv b) (.cv a))) (synCnc (.cv a))
  have p0019 :=
    @gEqeq2d (.classEq (.cv p) (synCnc (synCdif (.cv b) (.cv a))))
      (synCplc (synCnc (.cv a)) (.cv p))
      (synCplc (synCnc (.cv a)) (synCnc (synCdif (.cv b) (.cv a)))) (synCnc (.cv b))
      p0018
  have p0020 :=
    @gRspcev (.classEq (synCnc (.cv b)) (synCplc (synCnc (.cv a)) (.cv p)))
      (.classEq (synCnc (.cv b))
        (synCplc (synCnc (.cv a)) (synCnc (synCdif (.cv b) (.cv a)))))
      p (synCnc (synCdif (.cv b) (.cv a))) (synCncs) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0019
  have p0021 :=
    @gSylancr (synWss (.cv a) (.cv b))
      (.classMem (synCnc (synCdif (.cv b) (.cv a))) (synCncs))
      (.classEq (synCnc (.cv b))
        (synCplc (synCnc (.cv a)) (synCnc (synCdif (.cv b) (.cv a)))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv b)) (synCplc (synCnc (.cv a)) (.cv p))))
      p0008 p0017 p0020
  have p0022 := @gId (.classEq N (synCnc (.cv b)))
  have p0023 := @gAddceq1 M (synCnc (.cv a)) (.cv p)
  have p0024 :=
    @gEqeqan12d (.classEq N (synCnc (.cv b))) (.classEq M (synCnc (.cv a))) N
      (synCnc (.cv b)) (synCplc M (.cv p)) (synCplc (synCnc (.cv a)) (.cv p)) p0022
      p0023
  have p0025 :=
    @gRexbidv (synWa (.classEq N (synCnc (.cv b))) (.classEq M (synCnc (.cv a))))
      (.classEq N (synCplc M (.cv p)))
      (.classEq (synCnc (.cv b)) (synCplc (synCnc (.cv a)) (.cv p))) p (synCncs)
      dv_cache_0008 p0024
  have p0026 :=
    @gAncoms (.classEq N (synCnc (.cv b))) (.classEq M (synCnc (.cv a)))
      (synWb (synWrex p (synCncs) (.classEq N (synCplc M (.cv p)))) (synWrex p (synCncs)
          (.classEq (synCnc (.cv b)) (synCplc (synCnc (.cv a)) (.cv p)))))
      p0025
  have p0027 :=
    @gSyl5ibr (synWss (.cv a) (.cv b))
      (synWrex p (synCncs) (.classEq N (synCplc M (.cv p))))
      (synWa (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv b)) (synCplc (synCnc (.cv a)) (.cv p))))
      p0021 p0026
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWa (.classMem (.cv a) M) (.classMem (.cv b) N)))
      (synWa (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b))))
      (.imp (synWss (.cv a) (.cv b)) (synWrex p (synCncs) (.classEq N (synCplc M (.cv p)))))
      p0004 p0027
  have p0029 :=
    @gRexlimdvva (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWss (.cv a) (.cv b)) (synWrex p (synCncs) (.classEq N (synCplc M (.cv p))))
      a b M N dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0004 p0028
  have p0030 :=
    @gSylbid (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr M (synClec) N) (synWrex a M (synWrex b N (synWss (.cv a) (.cv b))))
      (synWrex p (synCncs) (.classEq N (synCplc M (.cv p)))) p0000 p0029
  have p0031 := @gAddlecncs M (.cv p)
  have p0032 := @gBreq2 N (synCplc M (.cv p)) M (synClec)
  have p0033 :=
    @gSyl5ibrcom (synWa (.classMem M (synCncs)) (.classMem (.cv p) (synCncs)))
      (synWbr M (synClec) N) (.classEq N (synCplc M (.cv p)))
      (synWbr M (synClec) (synCplc M (.cv p))) p0031 p0032
  have p0034 :=
    @gAdantlr (.classMem M (synCncs)) (.classMem (.cv p) (synCncs))
      (.imp (.classEq N (synCplc M (.cv p))) (synWbr M (synClec) N))
      (.classMem N (synCncs)) p0033
  have p0035 :=
    @gRexlimdva (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classEq N (synCplc M (.cv p))) (synWbr M (synClec) N) p (synCncs)
      dv_cache_0014 dv_cache_0015 p0034
  have p0036 :=
    @gImpbid (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr M (synClec) N) (synWrex p (synCncs) (.classEq N (synCplc M (.cv p))))
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

/-- Checked nominal proof certificate identified upstream as `g_lectr`. -/
@[expose]
noncomputable def gLectr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
        (.imp (synWa (synWbr A (synClec) B) (synWbr B (synClec) C))
          (synWbr A (synClec) C))) :=
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
  have dv_cache_0005 : y ∉ ((synCncs)).fv :=
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
  have dv_cache_0006 : x ∉ ((synCncs)).fv :=
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
  have dv_cache_0007 : y ∉ ((Wff.classEq B (synCplc A (.cv x)))).fv :=
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
  have dv_cache_0008 : x ∉ ((Wff.classEq C (synCplc B (.cv y)))).fv :=
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
  have dv_cache_0010 : x ∉ ((synWbr A (synClec) C)).fv :=
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
  have dv_cache_0011 : y ∉ ((synWbr A (synClec) C)).fv :=
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
      ((synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs)))).fv :=
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
      ((synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs)))).fv :=
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
  have p0000 := @gDflec2 A B x dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gN3adant3 (.classMem A (synCncs)) (.classMem B (synCncs))
      (synWb (synWbr A (synClec) B)
        (synWrex x (synCncs) (.classEq B (synCplc A (.cv x)))))
      (.classMem C (synCncs)) p0000
  have p0002 := @gDflec2 B C y dv_cache_0003 dv_cache_0004
  have p0003 :=
    @gN3adant1 (.classMem B (synCncs)) (.classMem C (synCncs))
      (synWb (synWbr B (synClec) C)
        (synWrex y (synCncs) (.classEq C (synCplc B (.cv y)))))
      (.classMem A (synCncs)) p0002
  have p0004 :=
    @gAnbi12d
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWbr A (synClec) B) (synWrex x (synCncs) (.classEq B (synCplc A (.cv x))))
      (synWbr B (synClec) C) (synWrex y (synCncs) (.classEq C (synCplc B (.cv y))))
      p0001 p0003
  have p0005 :=
    @gReeanv (.classEq B (synCplc A (.cv x))) (.classEq C (synCplc B (.cv y))) x y
      (synCncs) (synCncs) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009
  have p0006 :=
    @gSyl6bbr
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWa (synWbr A (synClec) B) (synWbr B (synClec) C))
      (synWa (synWrex x (synCncs) (.classEq B (synCplc A (.cv x))))
        (synWrex y (synCncs) (.classEq C (synCplc B (.cv y)))))
      (synWrex x (synCncs) (synWrex y (synCncs)
          (synWa (.classEq B (synCplc A (.cv x))) (.classEq C (synCplc B (.cv y))))))
      p0004 p0005
  have p0007 := @gAddceq1 B (synCplc A (.cv x)) (.cv y)
  have p0008 := @gAddcass A (.cv x) (.cv y)
  have p0009 :=
    @gSyl6eq (.classEq B (synCplc A (.cv x))) (synCplc B (.cv y))
      (synCplc (synCplc A (.cv x)) (.cv y)) (synCplc A (synCplc (.cv x) (.cv y)))
      p0007 p0008
  have p0010 :=
    @gEqeq2d (.classEq B (synCplc A (.cv x))) (synCplc B (.cv y))
      (synCplc A (synCplc (.cv x) (.cv y))) C p0009
  have p0011 :=
    @gBiimpa (.classEq B (synCplc A (.cv x))) (.classEq C (synCplc B (.cv y)))
      (.classEq C (synCplc A (synCplc (.cv x) (.cv y)))) p0010
  have p0012 :=
    @gSimp1 (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs))
  have p0013 := @gNcaddccl (.cv x) (.cv y)
  have p0014 := @gAddlecncs A (synCplc (.cv x) (.cv y))
  have p0015 :=
    @gSyl2an
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (.classMem A (synCncs)) (.classMem (synCplc (.cv x) (.cv y)) (synCncs))
      (synWbr A (synClec) (synCplc A (synCplc (.cv x) (.cv y))))
      (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv y) (synCncs))) p0012 p0013
      p0014
  have p0016 := @gBreq2 C (synCplc A (synCplc (.cv x) (.cv y))) A (synClec)
  have p0017 :=
    @gSyl5ibrcom
      (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs)))
        (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv y) (synCncs))))
      (synWbr A (synClec) C) (.classEq C (synCplc A (synCplc (.cv x) (.cv y))))
      (synWbr A (synClec) (synCplc A (synCplc (.cv x) (.cv y)))) p0015 p0016
  have p0018 :=
    @gSyl5 (synWa (.classEq B (synCplc A (.cv x))) (.classEq C (synCplc B (.cv y))))
      (.classEq C (synCplc A (synCplc (.cv x) (.cv y))))
      (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs)))
        (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv y) (synCncs))))
      (synWbr A (synClec) C) p0011 p0017
  have p0019 :=
    @gRexlimdvva
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWa (.classEq B (synCplc A (.cv x))) (.classEq C (synCplc B (.cv y))))
      (synWbr A (synClec) C) x y (synCncs) (synCncs) dv_cache_0005 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0009 p0018
  have p0020 :=
    @gSylbid
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWa (synWbr A (synClec) B) (synWbr B (synClec) C))
      (synWrex x (synCncs) (synWrex y (synCncs)
          (synWa (.classEq B (synCplc A (.cv x))) (.classEq C (synCplc B (.cv y))))))
      (synWbr A (synClec) C) p0006 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_nc0le1`. -/
@[expose]
noncomputable def gNc0le1 (N : Class) :
    Nominal.NPrf
      (.imp (.classMem N (synCncs))
        (synWo (.classEq N (synC0c)) (synWbr (synC1c) (synClec) N))) :=
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
  have dv_cache_0004 : q ∉ ((synCsn (.cv x))).fv :=
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
  have dv_cache_0005 : p ∉ ((synCnc (.cv a))).fv :=
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
  have dv_cache_0006 : p ∉ ((synC1c)).fv :=
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
  have dv_cache_0007 : q ∉ ((synC1c)).fv :=
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
  have dv_cache_0008 : p ∉ ((synWss (.cv q) (.cv a))).fv :=
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
  have dv_cache_0009 : q ∉ ((synWss (synCsn (.cv x)) (.cv a))).fv :=
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
      ((synWrex p (synCnc (.cv a)) (synWrex q (synC1c) (synWss (.cv q) (.cv p))))).fv :=
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
  have dv_cache_0013 : q ∉ ((synCnc (.cv a))).fv :=
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
    a ∉ ((synWo (.classEq N (synC0c)) (synWbr (synC1c) (synClec) N))).fv :=
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
  have p0000 := @gElncs a N dv_cache_0001
  have p0001 := @gNceq (.cv a) (synC0)
  have p0002 := @gDf0c2
  have p0003 :=
    @gSyl6eqr (.classEq (.cv a) (synC0)) (synCnc (.cv a)) (synCnc (synC0)) (synC0c)
      p0001 p0002
  have p0004 :=
    @gOrcd (.classEq (.cv a) (synC0)) (.classEq (synCnc (.cv a)) (synC0c))
      (synWbr (synC1c) (synClec) (synCnc (.cv a))) p0003
  have p0005 := @gVex x
  have p0006 := @gSnss (.cv x) (.cv a) p0005
  have p0007 := @gVex a
  have p0008 := @gNcid (.cv a) p0007
  have p0009 := @gSnel1c (.cv x) p0005
  have p0010 := @gSseq2 (.cv p) (.cv a) (.cv q)
  have p0011 := @gSseq1 (.cv q) (synCsn (.cv x)) (.cv a)
  have p0012 :=
    @gRspc2ev (synWss (.cv q) (.cv p)) (synWss (synCsn (.cv x)) (.cv a))
      (synWss (.cv q) (.cv a)) p q (.cv a) (synCsn (.cv x)) (synCnc (.cv a)) (synC1c)
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0010 p0011
  have p0013 :=
    @gMp3an12 (.classMem (.cv a) (synCnc (.cv a)))
      (.classMem (synCsn (.cv x)) (synC1c)) (synWss (synCsn (.cv x)) (.cv a))
      (synWrex p (synCnc (.cv a)) (synWrex q (synC1c) (synWss (.cv q) (.cv p))))
      p0008 p0009 p0012
  have p0014_e00_recanon :
    Nominal.NPrf (synWb (.objMem x a) (synWss (synCsn (.cv x)) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa synCsn
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
    @gSylbi (.objMem x a) (synWss (synCsn (.cv x)) (.cv a))
      (synWrex p (synCnc (.cv a)) (synWrex q (synC1c) (synWss (.cv q) (.cv p))))
      p0014_e00_recanon p0013
  have p0015 :=
    @gExlimiv (.objMem x a)
      (synWrex p (synCnc (.cv a)) (synWrex q (synC1c) (synWss (.cv q) (.cv p)))) x
      dv_cache_0011 p0014
  have p0016 := @gN0 x (.cv a) dv_cache_0012
  have p0017 := @gN1cex
  have p0018 := @gNcex (.cv a)
  have p0019 :=
    @gBrlec q p (synC1c) (synCnc (.cv a)) dv_cache_0007 dv_cache_0013 dv_cache_0005
      dv_cache_0014 p0017 p0018
  have p0020 :=
    @gRexcom (synWss (.cv q) (.cv p)) q p (synC1c) (synCnc (.cv a)) dv_cache_0006
      dv_cache_0013 dv_cache_0014
  have p0021 :=
    @gBitri (synWbr (synC1c) (synClec) (synCnc (.cv a)))
      (synWrex q (synC1c) (synWrex p (synCnc (.cv a)) (synWss (.cv q) (.cv p))))
      (synWrex p (synCnc (.cv a)) (synWrex q (synC1c) (synWss (.cv q) (.cv p))))
      p0019 p0020
  have p0022_e01_recanon :
    Nominal.NPrf (synWb (synWne (.cv a) (synC0)) (synWex x (.objMem x a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv synWex
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
    @gN3imtr4i (synWex x (.objMem x a))
      (synWrex p (synCnc (.cv a)) (synWrex q (synC1c) (synWss (.cv q) (.cv p))))
      (synWne (.cv a) (synC0)) (synWbr (synC1c) (synClec) (synCnc (.cv a))) p0015
      p0022_e01_recanon p0021
  have p0023 :=
    @gOlcd (synWne (.cv a) (synC0)) (synWbr (synC1c) (synClec) (synCnc (.cv a)))
      (.classEq (synCnc (.cv a)) (synC0c)) p0022
  have p0024 :=
    @gPm261ine
      (synWo (.classEq (synCnc (.cv a)) (synC0c))
        (synWbr (synC1c) (synClec) (synCnc (.cv a))))
      (.cv a) (synC0) p0004 p0023
  have p0025 := @gEqeq1 N (synCnc (.cv a)) (synC0c)
  have p0026 := @gBreq2 N (synCnc (.cv a)) (synC1c) (synClec)
  have p0027 :=
    @gOrbi12d (.classEq N (synCnc (.cv a))) (.classEq N (synC0c))
      (.classEq (synCnc (.cv a)) (synC0c)) (synWbr (synC1c) (synClec) N)
      (synWbr (synC1c) (synClec) (synCnc (.cv a))) p0025 p0026
  have p0028 :=
    @gMpbiri (.classEq N (synCnc (.cv a)))
      (synWo (.classEq N (synC0c)) (synWbr (synC1c) (synClec) N))
      (synWo (.classEq (synCnc (.cv a)) (synC0c))
        (synWbr (synC1c) (synClec) (synCnc (.cv a))))
      p0024 p0027
  have p0029 :=
    @gExlimiv (.classEq N (synCnc (.cv a)))
      (synWo (.classEq N (synC0c)) (synWbr (synC1c) (synClec) N)) a dv_cache_0015
      p0028
  have p0030 :=
    @gSylbi (.classMem N (synCncs)) (synWex a (.classEq N (synCnc (.cv a))))
      (synWo (.classEq N (synC0c)) (synWbr (synC1c) (synClec) N)) p0000 p0029
  exact p0030

/-- Checked nominal proof certificate identified upstream as `g_nc0suc`. -/
@[expose]
noncomputable def gNc0suc (m : Var) (N : Class) (dv_N_m : m ∉ N.fv) :
    Nominal.NPrf
      (.imp (.classMem N (synCncs)) (synWo (.classEq N (synC0c))
          (synWrex m (synCncs) (.classEq N (synCplc (.cv m) (synC1c)))))) :=
  by
  have dv_cache_0001 : m ∉ ((synC1c)).fv := by
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
  have p0000 := @gNc0le1 N
  have p0001 := @gN1cnc
  have p0002 := @gDflec2 (synC1c) N m dv_cache_0001 dv_cache_0002
  have p0003 := @gAddccom (synC1c) (.cv m)
  have p0004 :=
    @gEqeq2i (synCplc (synC1c) (.cv m)) (synCplc (.cv m) (synC1c)) N p0003
  have p0005 :=
    @gRexbii (.classEq N (synCplc (synC1c) (.cv m)))
      (.classEq N (synCplc (.cv m) (synC1c))) m (synCncs) p0004
  have p0006 :=
    @gSyl6bb (synWa (.classMem (synC1c) (synCncs)) (.classMem N (synCncs)))
      (synWbr (synC1c) (synClec) N)
      (synWrex m (synCncs) (.classEq N (synCplc (synC1c) (.cv m))))
      (synWrex m (synCncs) (.classEq N (synCplc (.cv m) (synC1c)))) p0002 p0005
  have p0007 :=
    @gMpan (.classMem (synC1c) (synCncs)) (.classMem N (synCncs))
      (synWb (synWbr (synC1c) (synClec) N)
        (synWrex m (synCncs) (.classEq N (synCplc (.cv m) (synC1c)))))
      p0001 p0006
  have p0008 :=
    @gOrbi2d (.classMem N (synCncs)) (synWbr (synC1c) (synClec) N)
      (synWrex m (synCncs) (.classEq N (synCplc (.cv m) (synC1c))))
      (.classEq N (synC0c)) p0007
  have p0009 :=
    @gMpbid (.classMem N (synCncs))
      (synWo (.classEq N (synC0c)) (synWbr (synC1c) (synClec) N))
      (synWo (.classEq N (synC0c))
        (synWrex m (synCncs) (.classEq N (synCplc (.cv m) (synC1c)))))
      p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_addceq0`. -/
@[expose]
noncomputable def gAddceq0 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (synWb (.classEq (synCplc A B) (synC0c))
          (synWa (.classEq A (synC0c)) (.classEq B (synC0c))))) :=
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
  have dv_cache_0002 : p ∉ ((Wff.neg (.classEq (synCplc A B) (synC0c)))).fv :=
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
  have p0000 := @gIanor (.classEq A (synC0c)) (.classEq B (synC0c))
  have p0001 := @gNc0suc p A dv_cache_0001
  have p0002 :=
    @gOrd (.classMem A (synCncs)) (.classEq A (synC0c))
      (synWrex p (synCncs) (.classEq A (synCplc (.cv p) (synC1c)))) p0001
  have p0003 :=
    @gAdantr (.classMem A (synCncs))
      (.imp (.neg (.classEq A (synC0c)))
        (synWrex p (synCncs) (.classEq A (synCplc (.cv p) (synC1c)))))
      (.classMem B (synCncs)) p0002
  have p0004 := @gAddc32 (.cv p) (synC1c) B
  have p0005 := @gN0cnsuc (synCplc (.cv p) B)
  have p0006 :=
    @gEqnetri (synCplc (synCplc (.cv p) (synC1c)) B)
      (synCplc (synCplc (.cv p) B) (synC1c)) (synC0c) p0004 p0005
  have p0007 := @gAddceq1 A (synCplc (.cv p) (synC1c)) B
  have p0008 :=
    @gEqeq1d (.classEq A (synCplc (.cv p) (synC1c))) (synCplc A B)
      (synCplc (synCplc (.cv p) (synC1c)) B) (synC0c) p0007
  have p0009 :=
    @gNecon3bbid (.classEq A (synCplc (.cv p) (synC1c)))
      (.classEq (synCplc A B) (synC0c)) (synCplc (synCplc (.cv p) (synC1c)) B)
      (synC0c) p0008
  have p0010 :=
    @gMpbiri (.classEq A (synCplc (.cv p) (synC1c)))
      (.neg (.classEq (synCplc A B) (synC0c)))
      (synWne (synCplc (synCplc (.cv p) (synC1c)) B) (synC0c)) p0006 p0009
  have p0011 :=
    @gRexlimivw (.classEq A (synCplc (.cv p) (synC1c)))
      (.neg (.classEq (synCplc A B) (synC0c))) p (synCncs) dv_cache_0002 p0010
  have p0012 :=
    @gSyl6 (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (.neg (.classEq A (synC0c)))
      (synWrex p (synCncs) (.classEq A (synCplc (.cv p) (synC1c))))
      (.neg (.classEq (synCplc A B) (synC0c))) p0003 p0011
  have p0013 := @gNc0suc p B dv_cache_0003
  have p0014 :=
    @gOrd (.classMem B (synCncs)) (.classEq B (synC0c))
      (synWrex p (synCncs) (.classEq B (synCplc (.cv p) (synC1c)))) p0013
  have p0015 :=
    @gAdantl (.classMem B (synCncs))
      (.imp (.neg (.classEq B (synC0c)))
        (synWrex p (synCncs) (.classEq B (synCplc (.cv p) (synC1c)))))
      (.classMem A (synCncs)) p0014
  have p0016 := @gAddcass A (.cv p) (synC1c)
  have p0017 := @gN0cnsuc (synCplc A (.cv p))
  have p0018 :=
    @gEqnetrri (synCplc (synCplc A (.cv p)) (synC1c))
      (synCplc A (synCplc (.cv p) (synC1c))) (synC0c) p0016 p0017
  have p0019 := @gAddceq2 B (synCplc (.cv p) (synC1c)) A
  have p0020 :=
    @gEqeq1d (.classEq B (synCplc (.cv p) (synC1c))) (synCplc A B)
      (synCplc A (synCplc (.cv p) (synC1c))) (synC0c) p0019
  have p0021 :=
    @gNecon3bbid (.classEq B (synCplc (.cv p) (synC1c)))
      (.classEq (synCplc A B) (synC0c)) (synCplc A (synCplc (.cv p) (synC1c)))
      (synC0c) p0020
  have p0022 :=
    @gMpbiri (.classEq B (synCplc (.cv p) (synC1c)))
      (.neg (.classEq (synCplc A B) (synC0c)))
      (synWne (synCplc A (synCplc (.cv p) (synC1c))) (synC0c)) p0018 p0021
  have p0023 :=
    @gRexlimivw (.classEq B (synCplc (.cv p) (synC1c)))
      (.neg (.classEq (synCplc A B) (synC0c))) p (synCncs) dv_cache_0002 p0022
  have p0024 :=
    @gSyl6 (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (.neg (.classEq B (synC0c)))
      (synWrex p (synCncs) (.classEq B (synCplc (.cv p) (synC1c))))
      (.neg (.classEq (synCplc A B) (synC0c))) p0015 p0023
  have p0025 :=
    @gJaod (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (.neg (.classEq A (synC0c))) (.neg (.classEq (synCplc A B) (synC0c)))
      (.neg (.classEq B (synC0c))) p0012 p0024
  have p0026 :=
    @gSyl5bi (.neg (synWa (.classEq A (synC0c)) (.classEq B (synC0c))))
      (synWo (.neg (.classEq A (synC0c))) (.neg (.classEq B (synC0c))))
      (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (.neg (.classEq (synCplc A B) (synC0c))) p0000 p0025
  have p0027 :=
    @gCon4d (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (.classEq A (synC0c)) (.classEq B (synC0c)))
      (.classEq (synCplc A B) (synC0c)) p0026
  have p0028 := @gAddceq12 A B (synC0c) (synC0c)
  have p0029 := @gAddcid2 (synC0c)
  have p0030 :=
    @gSyl6eq (synWa (.classEq A (synC0c)) (.classEq B (synC0c))) (synCplc A B)
      (synCplc (synC0c) (synC0c)) (synC0c) p0028 p0029
  have p0031 :=
    @gImpbid1 (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (.classEq (synCplc A B) (synC0c))
      (synWa (.classEq A (synC0c)) (.classEq B (synC0c))) p0027 p0030
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

/-- Checked nominal proof certificate identified upstream as `g_dflec3`. -/
@[expose]
noncomputable def gDflec3 (f : Var) (M : Class) (N : Class) (a : Var) (b : Var)
    (dv_M_a : a ∉ M.fv) (dv_N_a : a ∉ N.fv) (dv_N_b : b ∉ N.fv) (dv_a_b : a ≠ b)
    (dv_a_f : a ≠ f) (dv_b_f : b ≠ f) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWb (synWbr M (synClec) N)
          (synWrex a M (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))) :=
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
  have dv_cache_0003 : y ∉ ((Wff.classEq M (synCnc (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq N (synCnc (.cv y)))).fv :=
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
  have dv_cache_0005 : c ∉ ((synCnc (.cv x))).fv :=
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
  have dv_cache_0006 : c ∉ ((synCnc (.cv y))).fv :=
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
  have dv_cache_0007 : b ∉ ((synCnc (.cv y))).fv :=
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
  have dv_cache_0009 : b ∉ ((synCnc (.cv x))).fv :=
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
  have dv_cache_0010 : f ∉ ((synCres (synCid) (.cv c))).fv :=
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
  have dv_cache_0011 : f ∉ ((synWf1 (synCres (synCid) (.cv c)) (.cv c) (.cv b))).fv :=
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
  have dv_cache_0014 : a ∉ ((synCnc (.cv x))).fv :=
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
  have dv_cache_0015 : a ∉ ((synWex f (synWf1 (.cv f) (.cv c) (.cv b)))).fv :=
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
      ((synWrex a (synCnc (.cv x)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))).fv :=
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
  have dv_cache_0017 : c ∉ ((synCrn (.cv f))).fv :=
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
  have dv_cache_0018 : c ∉ ((synWss (synCrn (.cv f)) (.cv b))).fv :=
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
    f ∉ ((synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b)))).fv :=
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
  have dv_cache_0020 : f ∉ ((Wff.classMem (.cv a) (synCnc (.cv x)))).fv :=
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
    a ∉ ((synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b)))).fv :=
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
  have dv_cache_0022 : a ∉ ((synCnc (.cv y))).fv :=
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
    a ∉ ((synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))).fv :=
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
      ((synWb (synWbr M (synClec) N) (synWrex a M
            (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))).fv :=
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
      ((synWb (synWbr M (synClec) N) (synWrex a M
            (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))).fv :=
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
  have p0000 := @gElncs x M dv_cache_0001
  have p0001 := @gElncs y N dv_cache_0002
  have p0002 :=
    @gAnbi12i (.classMem M (synCncs)) (synWex x (.classEq M (synCnc (.cv x))))
      (.classMem N (synCncs)) (synWex y (.classEq N (synCnc (.cv y)))) p0000 p0001
  have p0003 :=
    @gEeanv (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gBitr4i (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWa (synWex x (.classEq M (synCnc (.cv x))))
        (synWex y (.classEq N (synCnc (.cv y)))))
      (synWex x (synWex y
          (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))))
      p0002 p0003
  have p0005 := @gNcex (.cv x)
  have p0006 := @gNcex (.cv y)
  have p0007 :=
    @gBrlec c b (synCnc (.cv x)) (synCnc (.cv y)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0005 p0006
  have p0008 :=
    @gRexcom (synWss (.cv c) (.cv b)) c b (synCnc (.cv x)) (synCnc (.cv y))
      dv_cache_0009 dv_cache_0006 dv_cache_0008
  have p0009 := @gF1oi (.cv c)
  have p0010 := @gF1of1 (.cv c) (.cv c) (synCres (synCid) (.cv c))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @gF1ss (.cv c) (.cv c) (.cv b) (synCres (synCid) (.cv c))
  have p0013 :=
    @gMpan (synWf1 (synCres (synCid) (.cv c)) (.cv c) (.cv c))
      (synWss (.cv c) (.cv b)) (synWf1 (synCres (synCid) (.cv c)) (.cv c) (.cv b))
      p0011 p0012
  have p0014 := @gIdex
  have p0015 := @gVex c
  have p0016 := @gResex (synCid) (.cv c) p0014 p0015
  have p0017 := @gF1eq1 (.cv c) (.cv b) (.cv f) (synCres (synCid) (.cv c))
  have p0018 :=
    @gSpcev (synWf1 (.cv f) (.cv c) (.cv b))
      (synWf1 (synCres (synCid) (.cv c)) (.cv c) (.cv b)) f
      (synCres (synCid) (.cv c)) dv_cache_0010 dv_cache_0011 p0016 p0017
  have p0019 :=
    @gSyl (synWss (.cv c) (.cv b))
      (synWf1 (synCres (synCid) (.cv c)) (.cv c) (.cv b))
      (synWex f (synWf1 (.cv f) (.cv c) (.cv b))) p0013 p0018
  have p0020 := @gF1eq2 (.cv a) (.cv c) (.cv b) (.cv f)
  have p0021_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a c)
        (synWb (synWf1 (.cv f) (.cv a) (.cv b)) (synWf1 (.cv f) (.cv c) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @gExbidv (.objEq a c) (synWf1 (.cv f) (.cv a) (.cv b))
      (synWf1 (.cv f) (.cv c) (.cv b)) f dv_cache_0012 p0021_e00_recanon
  have p0022_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv c)) (synWb (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))
          (synWex f (synWf1 (.cv f) (.cv c) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWf1 synWa synWf synWfun synWss synCin synCcompl
          synCnin synWnan synCcom synCopab synCcnv synCid
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
    @gRspcev (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))
      (synWex f (synWf1 (.cv f) (.cv c) (.cv b))) a (.cv c) (synCnc (.cv x))
      dv_cache_0013 dv_cache_0014 dv_cache_0015 p0022_e00_recanon
  have p0023 :=
    @gSylan2 (synWss (.cv c) (.cv b)) (.classMem (.cv c) (synCnc (.cv x)))
      (synWex f (synWf1 (.cv f) (.cv c) (.cv b)))
      (synWrex a (synCnc (.cv x)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))) p0019
      p0022
  have p0024 :=
    @gRexlimiva (synWss (.cv c) (.cv b))
      (synWrex a (synCnc (.cv x)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))) c
      (synCnc (.cv x)) dv_cache_0016 p0023
  have p0025 := @gVex a
  have p0026 := @gEqnc (.cv a) (.cv x) p0025
  have p0027 := @gElnc (.cv a) (.cv x)
  have p0028 :=
    @gBitr4i (.classEq (synCnc (.cv a)) (synCnc (.cv x)))
      (synWbr (.cv a) (synCen) (.cv x)) (.classMem (.cv a) (synCnc (.cv x))) p0026
      p0027
  have p0029 := @gF1f1orn (.cv a) (.cv b) (.cv f)
  have p0030 := @gVex f
  have p0031 := @gF1oen (.cv a) (synCrn (.cv f)) (.cv f) p0030
  have p0032 :=
    @gSyl (synWf1 (.cv f) (.cv a) (.cv b)) (synWf1o (.cv f) (.cv a) (synCrn (.cv f)))
      (synWbr (.cv a) (synCen) (synCrn (.cv f))) p0029 p0031
  have p0033 := @gEnsym (.cv a) (synCrn (.cv f))
  have p0034 :=
    @gSylib (synWf1 (.cv f) (.cv a) (.cv b))
      (synWbr (.cv a) (synCen) (synCrn (.cv f)))
      (synWbr (synCrn (.cv f)) (synCen) (.cv a)) p0032 p0033
  have p0035 := @gElnc (synCrn (.cv f)) (.cv a)
  have p0036 :=
    @gSylibr (synWf1 (.cv f) (.cv a) (.cv b))
      (synWbr (synCrn (.cv f)) (synCen) (.cv a))
      (.classMem (synCrn (.cv f)) (synCnc (.cv a))) p0034 p0035
  have p0037 := @gEleq2 (synCnc (.cv a)) (synCnc (.cv x)) (synCrn (.cv f))
  have p0038 :=
    @gSyl5ib (synWf1 (.cv f) (.cv a) (.cv b))
      (.classMem (synCrn (.cv f)) (synCnc (.cv a)))
      (.classEq (synCnc (.cv a)) (synCnc (.cv x)))
      (.classMem (synCrn (.cv f)) (synCnc (.cv x))) p0036 p0037
  have p0039 :=
    @gSylbir (.classMem (.cv a) (synCnc (.cv x)))
      (.classEq (synCnc (.cv a)) (synCnc (.cv x)))
      (.imp (synWf1 (.cv f) (.cv a) (.cv b)) (.classMem (synCrn (.cv f)) (synCnc (.cv x))))
      p0028 p0038
  have p0040 :=
    @gImp (.classMem (.cv a) (synCnc (.cv x))) (synWf1 (.cv f) (.cv a) (.cv b))
      (.classMem (synCrn (.cv f)) (synCnc (.cv x))) p0039
  have p0041 := @gF1f (.cv a) (.cv b) (.cv f)
  have p0042 := @gFrn (.cv a) (.cv b) (.cv f)
  have p0043 :=
    @gSyl (synWf1 (.cv f) (.cv a) (.cv b)) (synWf (.cv f) (.cv a) (.cv b))
      (synWss (synCrn (.cv f)) (.cv b)) p0041 p0042
  have p0044 :=
    @gAdantl (synWf1 (.cv f) (.cv a) (.cv b)) (synWss (synCrn (.cv f)) (.cv b))
      (.classMem (.cv a) (synCnc (.cv x))) p0043
  have p0045 := @gSseq1 (.cv c) (synCrn (.cv f)) (.cv b)
  have p0046 :=
    @gRspcev (synWss (.cv c) (.cv b)) (synWss (synCrn (.cv f)) (.cv b)) c
      (synCrn (.cv f)) (synCnc (.cv x)) dv_cache_0017 dv_cache_0005 dv_cache_0018 p0045
  have p0047 :=
    @gSyl2anc
      (synWa (.classMem (.cv a) (synCnc (.cv x))) (synWf1 (.cv f) (.cv a) (.cv b)))
      (.classMem (synCrn (.cv f)) (synCnc (.cv x))) (synWss (synCrn (.cv f)) (.cv b))
      (synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b))) p0040 p0044 p0046
  have p0048 :=
    @gEx (.classMem (.cv a) (synCnc (.cv x))) (synWf1 (.cv f) (.cv a) (.cv b))
      (synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b))) p0047
  have p0049 :=
    @gExlimdv (.classMem (.cv a) (synCnc (.cv x))) (synWf1 (.cv f) (.cv a) (.cv b))
      (synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b))) f dv_cache_0019
      dv_cache_0020 p0048
  have p0050 :=
    @gRexlimiv (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))
      (synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b))) a (synCnc (.cv x))
      dv_cache_0021 p0049
  have p0051 :=
    @gImpbii (synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b)))
      (synWrex a (synCnc (.cv x)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))) p0024
      p0050
  have p0052 :=
    @gRexbii (synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b)))
      (synWrex a (synCnc (.cv x)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))) b
      (synCnc (.cv y)) p0051
  have p0053 :=
    @gBitri
      (synWrex c (synCnc (.cv x)) (synWrex b (synCnc (.cv y)) (synWss (.cv c) (.cv b))))
      (synWrex b (synCnc (.cv y)) (synWrex c (synCnc (.cv x)) (synWss (.cv c) (.cv b))))
      (synWrex b (synCnc (.cv y))
        (synWrex a (synCnc (.cv x)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      p0008 p0052
  have p0054 :=
    @gRexcom (synWex f (synWf1 (.cv f) (.cv a) (.cv b))) b a (synCnc (.cv y))
      (synCnc (.cv x)) dv_cache_0022 dv_cache_0009 dv_cache_0023
  have p0055 :=
    @gN3bitri (synWbr (synCnc (.cv x)) (synClec) (synCnc (.cv y)))
      (synWrex c (synCnc (.cv x)) (synWrex b (synCnc (.cv y)) (synWss (.cv c) (.cv b))))
      (synWrex b (synCnc (.cv y))
        (synWrex a (synCnc (.cv x)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      (synWrex a (synCnc (.cv x))
        (synWrex b (synCnc (.cv y)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      p0007 p0053 p0054
  have p0056 := @gBreq12 M (synCnc (.cv x)) N (synCnc (.cv y)) (synClec)
  have p0057 := @gSimpl (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y)))
  have p0058 :=
    @gRexeq (synWex f (synWf1 (.cv f) (.cv a) (.cv b))) b N (synCnc (.cv y))
      dv_cache_0024 dv_cache_0007
  have p0059 :=
    @gAdantl (.classEq N (synCnc (.cv y)))
      (synWb (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))
        (synWrex b (synCnc (.cv y)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      (.classEq M (synCnc (.cv x))) p0058
  have p0060 :=
    @gRexeqbidv (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))
      (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))
      (synWrex b (synCnc (.cv y)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))) a M
      (synCnc (.cv x)) dv_cache_0025 dv_cache_0014 dv_cache_0026 p0057 p0059
  have p0061 :=
    @gBibi12d (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))
      (synWbr M (synClec) N) (synWbr (synCnc (.cv x)) (synClec) (synCnc (.cv y)))
      (synWrex a M (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      (synWrex a (synCnc (.cv x))
        (synWrex b (synCnc (.cv y)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      p0056 p0060
  have p0062 :=
    @gMpbiri (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))
      (synWb (synWbr M (synClec) N)
        (synWrex a M (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))
      (synWb (synWbr (synCnc (.cv x)) (synClec) (synCnc (.cv y)))
        (synWrex a (synCnc (.cv x))
          (synWrex b (synCnc (.cv y)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))
      p0055 p0061
  have p0063 :=
    @gExlimivv (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))
      (synWb (synWbr M (synClec) N)
        (synWrex a M (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))
      x y dv_cache_0027 dv_cache_0028 p0062
  have p0064 :=
    @gSylbi (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWex x (synWex y
          (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))))
      (synWb (synWbr M (synClec) N)
        (synWrex a M (synWrex b N (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))
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

/-- Checked nominal proof certificate identified upstream as `g_nclenc`. -/
@[expose]
noncomputable def gNclenc (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv)
    (dv_B_f : f ∉ B.fv) (hyp_nclenc_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_nclenc_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCnc A) (synClec) (synCnc B)) (synWex f (synWf1 (.cv f) A B))) :=
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
  have dv_cache_0001 : p ∉ ((synCnc A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_p_not_A,
          not_false_eq_true])
  have dv_cache_0002 : p ∉ ((synCnc B)).fv :=
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
  have dv_cache_0003 : q ∉ ((synCnc B)).fv :=
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
  have dv_cache_0011 : i ∉ ((synWf1o (.cv h) (.cv p) A)).fv :=
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
  have dv_cache_0012 : h ∉ ((synWf1o (.cv i) (.cv q) B)).fv :=
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
    f ∉ ((synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)))).fv :=
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
    f ∉ ((synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h))) A B)).fv :=
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
      ((Wff.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f (synWf1 (.cv f) A B)))).fv :=
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
      ((Wff.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f (synWf1 (.cv f) A B)))).fv :=
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
  have dv_cache_0017 : g ∉ ((synWex f (synWf1 (.cv f) A B))).fv :=
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
    g ∉ ((synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B)))).fv :=
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
  have dv_cache_0019 : q ∉ ((synCnc A)).fv :=
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
  have dv_cache_0020 : p ∉ ((synWex f (synWf1 (.cv f) A B))).fv :=
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
  have dv_cache_0021 : q ∉ ((synWex f (synWf1 (.cv f) A B))).fv :=
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
  have dv_cache_0027 : a ∉ ((synCnc A)).fv :=
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
  have dv_cache_0028 : a ∉ ((synCnc B)).fv :=
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
  have dv_cache_0029 : b ∉ ((synCnc B)).fv :=
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
  have dv_cache_0030 : a ∉ ((synWex f (synWf1 (.cv f) A (.cv b)))).fv :=
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
  have dv_cache_0031 : b ∉ ((synWex f (synWf1 (.cv f) A B))).fv :=
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
  have p0000 := @gNcelncsi A hyp_nclenc_1
  have p0001 := @gNcelncsi B hyp_nclenc_2
  have p0002 :=
    @gDflec3 g (synCnc A) (synCnc B) p q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @gMp2an (.classMem (synCnc A) (synCncs)) (.classMem (synCnc B) (synCncs))
      (synWb (synWbr (synCnc A) (synClec) (synCnc B)) (synWrex p (synCnc A)
          (synWrex q (synCnc B) (synWex g (synWf1 (.cv g) (.cv p) (.cv q))))))
      p0000 p0001 p0002
  have p0004 := @gElnc (.cv p) A
  have p0005 := @gBren (.cv p) A h dv_cache_0007 dv_cache_0008
  have p0006 :=
    @gBitri (.classMem (.cv p) (synCnc A)) (synWbr (.cv p) (synCen) A)
      (synWex h (synWf1o (.cv h) (.cv p) A)) p0004 p0005
  have p0007 := @gElnc (.cv q) B
  have p0008 := @gBren (.cv q) B i dv_cache_0009 dv_cache_0010
  have p0009 :=
    @gBitri (.classMem (.cv q) (synCnc B)) (synWbr (.cv q) (synCen) B)
      (synWex i (synWf1o (.cv i) (.cv q) B)) p0007 p0008
  have p0010 :=
    @gAnbi12i (.classMem (.cv p) (synCnc A)) (synWex h (synWf1o (.cv h) (.cv p) A))
      (.classMem (.cv q) (synCnc B)) (synWex i (synWf1o (.cv i) (.cv q) B)) p0006 p0009
  have p0011 :=
    @gEeanv (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B) h i dv_cache_0011
      dv_cache_0012
  have p0012 :=
    @gBitr4i (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B)))
      (synWa (synWex h (synWf1o (.cv h) (.cv p) A)) (synWex i (synWf1o (.cv i) (.cv q) B)))
      (synWex h (synWex i (synWa (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B))))
      p0010 p0011
  have p0013 := @gF1of1 (.cv q) B (.cv i)
  have p0014 :=
    @gN3ad2ant2 (synWf1o (.cv i) (.cv q) B) (synWf1o (.cv h) (.cv p) A)
      (synWf1 (.cv i) (.cv q) B) (synWf1 (.cv g) (.cv p) (.cv q)) p0013
  have p0015 :=
    @gSimp3 (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B)
      (synWf1 (.cv g) (.cv p) (.cv q))
  have p0016 := @gF1co (.cv p) (.cv q) B (.cv i) (.cv g)
  have p0017 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B)
        (synWf1 (.cv g) (.cv p) (.cv q)))
      (synWf1 (.cv i) (.cv q) B) (synWf1 (.cv g) (.cv p) (.cv q))
      (synWf1 (synCcom (.cv i) (.cv g)) (.cv p) B) p0014 p0015 p0016
  have p0018 := @gF1ocnv (.cv p) A (.cv h)
  have p0019 := @gF1of1 A (.cv p) (synCcnv (.cv h))
  have p0020 :=
    @gSyl (synWf1o (.cv h) (.cv p) A) (synWf1o (synCcnv (.cv h)) A (.cv p))
      (synWf1 (synCcnv (.cv h)) A (.cv p)) p0018 p0019
  have p0021 :=
    @gN3ad2ant1 (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B)
      (synWf1 (synCcnv (.cv h)) A (.cv p)) (synWf1 (.cv g) (.cv p) (.cv q)) p0020
  have p0022 := @gF1co A (.cv p) B (synCcom (.cv i) (.cv g)) (synCcnv (.cv h))
  have p0023 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B)
        (synWf1 (.cv g) (.cv p) (.cv q)))
      (synWf1 (synCcom (.cv i) (.cv g)) (.cv p) B)
      (synWf1 (synCcnv (.cv h)) A (.cv p))
      (synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h))) A B) p0017 p0021
      p0022
  have p0024 := @gVex i
  have p0025 := @gVex g
  have p0026 := @gCoex (.cv i) (.cv g) p0024 p0025
  have p0027 := @gVex h
  have p0028 := @gCnvex (.cv h) p0027
  have p0029 := @gCoex (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)) p0026 p0028
  have p0030 :=
    @gF1eq1 A B (.cv f) (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)))
  have p0031 :=
    @gSpcev (synWf1 (.cv f) A B)
      (synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h))) A B) f
      (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h))) dv_cache_0013 dv_cache_0014
      p0029 p0030
  have p0032 :=
    @gSyl
      (synW3a (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B)
        (synWf1 (.cv g) (.cv p) (.cv q)))
      (synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h))) A B)
      (synWex f (synWf1 (.cv f) A B)) p0023 p0031
  have p0033 :=
    @gN3expia (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B)
      (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f (synWf1 (.cv f) A B)) p0032
  have p0034 :=
    @gExlimivv (synWa (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B))
      (.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f (synWf1 (.cv f) A B))) h i
      dv_cache_0015 dv_cache_0016 p0033
  have p0035 :=
    @gSylbi (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B)))
      (synWex h (synWex i (synWa (synWf1o (.cv h) (.cv p) A) (synWf1o (.cv i) (.cv q) B))))
      (.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f (synWf1 (.cv f) A B))) p0012
      p0034
  have p0036 :=
    @gExlimdv (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B)))
      (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f (synWf1 (.cv f) A B)) g dv_cache_0017
      dv_cache_0018 p0035
  have p0037 :=
    @gRexlimivv (synWex g (synWf1 (.cv g) (.cv p) (.cv q)))
      (synWex f (synWf1 (.cv f) A B)) p q (synCnc A) (synCnc B) dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0004 p0036
  have p0038 :=
    @gSylbi (synWbr (synCnc A) (synClec) (synCnc B))
      (synWrex p (synCnc A)
        (synWrex q (synCnc B) (synWex g (synWf1 (.cv g) (.cv p) (.cv q)))))
      (synWex f (synWf1 (.cv f) A B)) p0003 p0037
  have p0039 := @gNcid A hyp_nclenc_1
  have p0040 := @gNcid B hyp_nclenc_2
  have p0041 := @gF1eq2 (.cv a) A (.cv b) (.cv f)
  have p0042 :=
    @gExbidv (.classEq (.cv a) A) (synWf1 (.cv f) (.cv a) (.cv b))
      (synWf1 (.cv f) A (.cv b)) f dv_cache_0022 p0041
  have p0043 := @gF1eq3 (.cv b) B A (.cv f)
  have p0044 :=
    @gExbidv (.classEq (.cv b) B) (synWf1 (.cv f) A (.cv b)) (synWf1 (.cv f) A B) f
      dv_cache_0023 p0043
  have p0045 :=
    @gRspc2ev (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))
      (synWex f (synWf1 (.cv f) A B)) (synWex f (synWf1 (.cv f) A (.cv b))) a b A B
      (synCnc A) (synCnc B) dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 p0042 p0044
  have p0046 :=
    @gMp3an12 (.classMem A (synCnc A)) (.classMem B (synCnc B))
      (synWex f (synWf1 (.cv f) A B))
      (synWrex a (synCnc A)
        (synWrex b (synCnc B) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      p0039 p0040 p0045
  have p0047 :=
    @gDflec3 f (synCnc A) (synCnc B) a b dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0032 dv_cache_0033 dv_cache_0034
  have p0048 :=
    @gMp2an (.classMem (synCnc A) (synCncs)) (.classMem (synCnc B) (synCncs))
      (synWb (synWbr (synCnc A) (synClec) (synCnc B)) (synWrex a (synCnc A)
          (synWrex b (synCnc B) (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))))
      p0000 p0001 p0047
  have p0049 :=
    @gSylibr (synWex f (synWf1 (.cv f) A B))
      (synWrex a (synCnc A)
        (synWrex b (synCnc B) (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))))
      (synWbr (synCnc A) (synClec) (synCnc B)) p0046 p0048
  have p0050 :=
    @gImpbii (synWbr (synCnc A) (synClec) (synCnc B))
      (synWex f (synWf1 (.cv f) A B)) p0038 p0049
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

/-- Checked nominal proof certificate identified upstream as `g_lenc`. -/
@[expose]
noncomputable def gLenc (x : Var) (A : Class) (M : Class) (dv_A_x : x ∉ A.fv)
    (dv_M_x : x ∉ M.fv) (hyp_lenc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem M (synCncs))
        (synWb (synWbr M (synClec) (synCnc A)) (synWrex x M (synWss (.cv x) A)))) :=
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
  have dv_cache_0002 : p ∉ ((synCnc (.cv y))).fv :=
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
  have dv_cache_0003 : p ∉ ((synCnc A)).fv :=
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
  have dv_cache_0004 : q ∉ ((synCnc A)).fv :=
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
  have dv_cache_0010 : g ∉ ((synWf1o (.cv f) (.cv p) (.cv y))).fv :=
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
  have dv_cache_0011 : f ∉ ((synWf1o (.cv g) (.cv q) A)).fv :=
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
  have dv_cache_0012 : x ∉ ((synCima (.cv g) (.cv p))).fv :=
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
  have dv_cache_0013 : x ∉ ((synCnc (.cv y))).fv :=
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
  have dv_cache_0014 : x ∉ ((synWss (synCima (.cv g) (.cv p)) A)).fv :=
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
      ((Wff.imp (synWss (.cv p) (.cv q))
          (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)))).fv :=
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
      ((Wff.imp (synWss (.cv p) (.cv q))
          (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)))).fv :=
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
  have dv_cache_0017 : q ∉ ((synCnc (.cv y))).fv :=
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
  have dv_cache_0018 : p ∉ ((synWrex x (synCnc (.cv y)) (synWss (.cv x) A))).fv :=
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
  have dv_cache_0019 : q ∉ ((synWrex x (synCnc (.cv y)) (synWss (.cv x) A))).fv :=
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
  have dv_cache_0020 : x ∉ ((synWbr (synCnc (.cv y)) (synClec) (synCnc A))).fv :=
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
      ((synWb (synWbr M (synClec) (synCnc A)) (synWrex x M (synWss (.cv x) A)))).fv :=
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
  have p0000 := @gElncs y M dv_cache_0001
  have p0001 := @gNcex (.cv y)
  have p0002 := @gNcex A
  have p0003 :=
    @gBrlec p q (synCnc (.cv y)) (synCnc A) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0001 p0002
  have p0004 := @gElnc (.cv p) (.cv y)
  have p0005 := @gBren (.cv p) (.cv y) f dv_cache_0006 dv_cache_0007
  have p0006 :=
    @gBitri (.classMem (.cv p) (synCnc (.cv y))) (synWbr (.cv p) (synCen) (.cv y))
      (synWex f (synWf1o (.cv f) (.cv p) (.cv y))) p0004 p0005
  have p0007 := @gElnc (.cv q) A
  have p0008 := @gBren (.cv q) A g dv_cache_0008 dv_cache_0009
  have p0009 :=
    @gBitri (.classMem (.cv q) (synCnc A)) (synWbr (.cv q) (synCen) A)
      (synWex g (synWf1o (.cv g) (.cv q) A)) p0007 p0008
  have p0010 :=
    @gAnbi12i (.classMem (.cv p) (synCnc (.cv y)))
      (synWex f (synWf1o (.cv f) (.cv p) (.cv y))) (.classMem (.cv q) (synCnc A))
      (synWex g (synWf1o (.cv g) (.cv q) A)) p0006 p0009
  have p0011 :=
    @gEeanv (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A) f g
      dv_cache_0010 dv_cache_0011
  have p0012 :=
    @gBitr4i
      (synWa (.classMem (.cv p) (synCnc (.cv y))) (.classMem (.cv q) (synCnc A)))
      (synWa (synWex f (synWf1o (.cv f) (.cv p) (.cv y)))
        (synWex g (synWf1o (.cv g) (.cv q) A)))
      (synWex f (synWex g
          (synWa (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A))))
      p0010 p0011
  have p0013 := @gF1of1 (.cv q) A (.cv g)
  have p0014 :=
    @gN3ad2ant2 (synWf1o (.cv g) (.cv q) A) (synWf1o (.cv f) (.cv p) (.cv y))
      (synWf1 (.cv g) (.cv q) A) (synWss (.cv p) (.cv q)) p0013
  have p0015 :=
    @gSimp3 (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
      (synWss (.cv p) (.cv q))
  have p0016 := @gF1ores (.cv q) A (.cv p) (.cv g)
  have p0017 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
        (synWss (.cv p) (.cv q)))
      (synWf1 (.cv g) (.cv q) A) (synWss (.cv p) (.cv q))
      (synWf1o (synCres (.cv g) (.cv p)) (.cv p) (synCima (.cv g) (.cv p))) p0014 p0015
      p0016
  have p0018 := @gF1ocnv (.cv p) (.cv y) (.cv f)
  have p0019 :=
    @gN3ad2ant1 (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
      (synWf1o (synCcnv (.cv f)) (.cv y) (.cv p)) (synWss (.cv p) (.cv q)) p0018
  have p0020 :=
    @gF1oco (.cv y) (.cv p) (synCima (.cv g) (.cv p)) (synCres (.cv g) (.cv p))
      (synCcnv (.cv f))
  have p0021 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
        (synWss (.cv p) (.cv q)))
      (synWf1o (synCres (.cv g) (.cv p)) (.cv p) (synCima (.cv g) (.cv p)))
      (synWf1o (synCcnv (.cv f)) (.cv y) (.cv p))
      (synWf1o (synCcom (synCres (.cv g) (.cv p)) (synCcnv (.cv f))) (.cv y)
        (synCima (.cv g) (.cv p)))
      p0017 p0019 p0020
  have p0022 :=
    @gF1ocnv (.cv y) (synCima (.cv g) (.cv p))
      (synCcom (synCres (.cv g) (.cv p)) (synCcnv (.cv f)))
  have p0023 := @gVex g
  have p0024 := @gVex p
  have p0025 := @gResex (.cv g) (.cv p) p0023 p0024
  have p0026 := @gVex f
  have p0027 := @gCnvex (.cv f) p0026
  have p0028 := @gCoex (synCres (.cv g) (.cv p)) (synCcnv (.cv f)) p0025 p0027
  have p0029 := @gCnvex (synCcom (synCres (.cv g) (.cv p)) (synCcnv (.cv f))) p0028
  have p0030 :=
    @gF1oen (synCima (.cv g) (.cv p)) (.cv y)
      (synCcnv (synCcom (synCres (.cv g) (.cv p)) (synCcnv (.cv f)))) p0029
  have p0031 :=
    @gN3syl
      (synW3a (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
        (synWss (.cv p) (.cv q)))
      (synWf1o (synCcom (synCres (.cv g) (.cv p)) (synCcnv (.cv f))) (.cv y)
        (synCima (.cv g) (.cv p)))
      (synWf1o (synCcnv (synCcom (synCres (.cv g) (.cv p)) (synCcnv (.cv f))))
        (synCima (.cv g) (.cv p)) (.cv y))
      (synWbr (synCima (.cv g) (.cv p)) (synCen) (.cv y)) p0021 p0022 p0030
  have p0032 := @gElnc (synCima (.cv g) (.cv p)) (.cv y)
  have p0033 :=
    @gSylibr
      (synW3a (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
        (synWss (.cv p) (.cv q)))
      (synWbr (synCima (.cv g) (.cv p)) (synCen) (.cv y))
      (.classMem (synCima (.cv g) (.cv p)) (synCnc (.cv y))) p0031 p0032
  have p0034 := @gImass2 (.cv p) (.cv q) (.cv g)
  have p0035 :=
    @gN3ad2ant3 (synWss (.cv p) (.cv q)) (synWf1o (.cv f) (.cv p) (.cv y))
      (synWss (synCima (.cv g) (.cv p)) (synCima (.cv g) (.cv q)))
      (synWf1o (.cv g) (.cv q) A) p0034
  have p0036 := @gF1ofo (.cv q) A (.cv g)
  have p0037 := @gFoima (.cv q) A (.cv g)
  have p0038 :=
    @gSyl (synWf1o (.cv g) (.cv q) A) (synWfo (.cv g) (.cv q) A)
      (.classEq (synCima (.cv g) (.cv q)) A) p0036 p0037
  have p0039 :=
    @gN3ad2ant2 (synWf1o (.cv g) (.cv q) A) (synWf1o (.cv f) (.cv p) (.cv y))
      (.classEq (synCima (.cv g) (.cv q)) A) (synWss (.cv p) (.cv q)) p0038
  have p0040 :=
    @gSseqtrd
      (synW3a (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
        (synWss (.cv p) (.cv q)))
      (synCima (.cv g) (.cv p)) (synCima (.cv g) (.cv q)) A p0035 p0039
  have p0041 := @gSseq1 (.cv x) (synCima (.cv g) (.cv p)) A
  have p0042 :=
    @gRspcev (synWss (.cv x) A) (synWss (synCima (.cv g) (.cv p)) A) x
      (synCima (.cv g) (.cv p)) (synCnc (.cv y)) dv_cache_0012 dv_cache_0013
      dv_cache_0014 p0041
  have p0043 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
        (synWss (.cv p) (.cv q)))
      (.classMem (synCima (.cv g) (.cv p)) (synCnc (.cv y)))
      (synWss (synCima (.cv g) (.cv p)) A)
      (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)) p0033 p0040 p0042
  have p0044 :=
    @gN3expia (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A)
      (synWss (.cv p) (.cv q)) (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)) p0043
  have p0045 :=
    @gExlimivv (synWa (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A))
      (.imp (synWss (.cv p) (.cv q)) (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)))
      f g dv_cache_0015 dv_cache_0016 p0044
  have p0046 :=
    @gSylbi
      (synWa (.classMem (.cv p) (synCnc (.cv y))) (.classMem (.cv q) (synCnc A)))
      (synWex f (synWex g
          (synWa (synWf1o (.cv f) (.cv p) (.cv y)) (synWf1o (.cv g) (.cv q) A))))
      (.imp (synWss (.cv p) (.cv q)) (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)))
      p0012 p0045
  have p0047 :=
    @gRexlimivv (synWss (.cv p) (.cv q))
      (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)) p q (synCnc (.cv y)) (synCnc A)
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0005 p0046
  have p0048 :=
    @gSylbi (synWbr (synCnc (.cv y)) (synClec) (synCnc A))
      (synWrex p (synCnc (.cv y)) (synWrex q (synCnc A) (synWss (.cv p) (.cv q))))
      (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)) p0003 p0047
  have p0049 := @gVex x
  have p0050 := @gNclec (.cv x) A p0049 hyp_lenc_1
  have p0051 := @gEqnc (.cv x) (.cv y) p0049
  have p0052 := @gElnc (.cv x) (.cv y)
  have p0053 :=
    @gBitr4i (.classEq (synCnc (.cv x)) (synCnc (.cv y)))
      (synWbr (.cv x) (synCen) (.cv y)) (.classMem (.cv x) (synCnc (.cv y))) p0051
      p0052
  have p0054 := @gBreq1 (synCnc (.cv x)) (synCnc (.cv y)) (synCnc A) (synClec)
  have p0055 :=
    @gSylbir (.classMem (.cv x) (synCnc (.cv y)))
      (.classEq (synCnc (.cv x)) (synCnc (.cv y)))
      (synWb (synWbr (synCnc (.cv x)) (synClec) (synCnc A))
        (synWbr (synCnc (.cv y)) (synClec) (synCnc A)))
      p0053 p0054
  have p0056 :=
    @gSyl5ib (synWss (.cv x) A) (synWbr (synCnc (.cv x)) (synClec) (synCnc A))
      (.classMem (.cv x) (synCnc (.cv y)))
      (synWbr (synCnc (.cv y)) (synClec) (synCnc A)) p0050 p0055
  have p0057 :=
    @gRexlimiv (synWss (.cv x) A) (synWbr (synCnc (.cv y)) (synClec) (synCnc A)) x
      (synCnc (.cv y)) dv_cache_0020 p0056
  have p0058 :=
    @gImpbii (synWbr (synCnc (.cv y)) (synClec) (synCnc A))
      (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)) p0048 p0057
  have p0059 := @gBreq1 M (synCnc (.cv y)) (synCnc A) (synClec)
  have p0060 :=
    @gRexeq (synWss (.cv x) A) x M (synCnc (.cv y)) dv_cache_0021 dv_cache_0013
  have p0061 :=
    @gBibi12d (.classEq M (synCnc (.cv y))) (synWbr M (synClec) (synCnc A))
      (synWbr (synCnc (.cv y)) (synClec) (synCnc A))
      (synWrex x M (synWss (.cv x) A))
      (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)) p0059 p0060
  have p0062 :=
    @gMpbiri (.classEq M (synCnc (.cv y)))
      (synWb (synWbr M (synClec) (synCnc A)) (synWrex x M (synWss (.cv x) A)))
      (synWb (synWbr (synCnc (.cv y)) (synClec) (synCnc A))
        (synWrex x (synCnc (.cv y)) (synWss (.cv x) A)))
      p0058 p0061
  have p0063 :=
    @gExlimiv (.classEq M (synCnc (.cv y)))
      (synWb (synWbr M (synClec) (synCnc A)) (synWrex x M (synWss (.cv x) A))) y
      dv_cache_0022 p0062
  have p0064 :=
    @gSylbi (.classMem M (synCncs)) (synWex y (.classEq M (synCnc (.cv y))))
      (synWb (synWbr M (synClec) (synCnc A)) (synWrex x M (synWss (.cv x) A))) p0000
      p0063
  exact p0064

/-- Checked nominal proof certificate identified upstream as `g_tcncg`. -/
@[expose]
noncomputable def gTcncg (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (.classEq (synCtc (synCnc A)) (synCnc (synCpw1 A)))) :=
  by
  have p0000 := @gNcelncs A V
  have p0001 := @gTccl (synCnc A)
  have p0002 :=
    @gSyl (.classMem A V) (.classMem (synCnc A) (synCncs))
      (.classMem (synCtc (synCnc A)) (synCncs)) p0000 p0001
  have p0003 := @gPw1exg A V
  have p0004 := @gNcelncs (synCpw1 A) (synCvv)
  have p0005 :=
    @gSyl (.classMem A V) (.classMem (synCpw1 A) (synCvv))
      (.classMem (synCnc (synCpw1 A)) (synCncs)) p0003 p0004
  have p0006 := @gNcidg A V
  have p0007 := @gPw1eltc (synCnc A) A
  have p0008 :=
    @gSyl2anc (.classMem A V) (.classMem (synCnc A) (synCncs))
      (.classMem A (synCnc A)) (.classMem (synCpw1 A) (synCtc (synCnc A))) p0000 p0006
      p0007
  have p0009 := @gNcidg (synCpw1 A) (synCvv)
  have p0010 :=
    @gSyl (.classMem A V) (.classMem (synCpw1 A) (synCvv))
      (.classMem (synCpw1 A) (synCnc (synCpw1 A))) p0003 p0009
  have p0011 := @gNceleq (synCtc (synCnc A)) (synCnc (synCpw1 A)) (synCpw1 A)
  have p0012 :=
    @gSyl22anc (.classMem A V) (.classMem (synCtc (synCnc A)) (synCncs))
      (.classMem (synCnc (synCpw1 A)) (synCncs))
      (.classMem (synCpw1 A) (synCtc (synCnc A)))
      (.classMem (synCpw1 A) (synCnc (synCpw1 A)))
      (.classEq (synCtc (synCnc A)) (synCnc (synCpw1 A))) p0002 p0005 p0008 p0010
      p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_tcnc`. -/
@[expose]
noncomputable def gTcnc (A : Class) (hyp_tcnc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCtc (synCnc A)) (synCnc (synCpw1 A))) :=
  by
  have p0000 := @gTcncg A (synCvv)
  have p0001 := Nominal.mp hyp_tcnc_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_tcnc1c`. -/
@[expose]
noncomputable def gTcnc1c :
    Nominal.NPrf
      (.classEq (synCtc (synCnc (synC1c))) (synCnc (synCpw1 (synC1c)))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gTcnc (synC1c) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_tc11`. -/
@[expose]
noncomputable def gTc11 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWb (.classEq (synCtc M) (synCtc N)) (.classEq M N))) :=
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
  have dv_cache_0003 : y ∉ ((Wff.classEq M (synCnc (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq N (synCnc (.cv y)))).fv :=
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
    x ∉ ((synWb (.classEq (synCtc M) (synCtc N)) (.classEq M N))).fv :=
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
    y ∉ ((synWb (.classEq (synCtc M) (synCtc N)) (.classEq M N))).fv :=
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
  have p0000 := @gElncs x M dv_cache_0001
  have p0001 := @gElncs y N dv_cache_0002
  have p0002 :=
    @gAnbi12i (.classMem M (synCncs)) (synWex x (.classEq M (synCnc (.cv x))))
      (.classMem N (synCncs)) (synWex y (.classEq N (synCnc (.cv y)))) p0000 p0001
  have p0003 :=
    @gEeanv (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gBitr4i (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWa (synWex x (.classEq M (synCnc (.cv x))))
        (synWex y (.classEq N (synCnc (.cv y)))))
      (synWex x (synWex y
          (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))))
      p0002 p0003
  have p0005 := @gVex x
  have p0006 := @gTcnc (.cv x) p0005
  have p0007 := @gVex y
  have p0008 := @gTcnc (.cv y) p0007
  have p0009 :=
    @gEqeq12i (synCtc (synCnc (.cv x))) (synCnc (synCpw1 (.cv x)))
      (synCtc (synCnc (.cv y))) (synCnc (synCpw1 (.cv y))) p0006 p0008
  have p0010 := @gEnpw1 (.cv x) (.cv y)
  have p0011 := @gEqnc (.cv x) (.cv y) p0005
  have p0012 := @gPw1ex (.cv x) p0005
  have p0013 := @gEqnc (synCpw1 (.cv x)) (synCpw1 (.cv y)) p0012
  have p0014 :=
    @gN3bitr4ri (synWbr (.cv x) (synCen) (.cv y))
      (synWbr (synCpw1 (.cv x)) (synCen) (synCpw1 (.cv y)))
      (.classEq (synCnc (.cv x)) (synCnc (.cv y)))
      (.classEq (synCnc (synCpw1 (.cv x))) (synCnc (synCpw1 (.cv y)))) p0010 p0011
      p0013
  have p0015 :=
    @gBitri (.classEq (synCtc (synCnc (.cv x))) (synCtc (synCnc (.cv y))))
      (.classEq (synCnc (synCpw1 (.cv x))) (synCnc (synCpw1 (.cv y))))
      (.classEq (synCnc (.cv x)) (synCnc (.cv y))) p0009 p0014
  have p0016 := @gTceq M (synCnc (.cv x))
  have p0017 := @gTceq N (synCnc (.cv y))
  have p0018 :=
    @gEqeqan12d (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))) (synCtc M)
      (synCtc (synCnc (.cv x))) (synCtc N) (synCtc (synCnc (.cv y))) p0016 p0017
  have p0019 := @gEqeq12 M (synCnc (.cv x)) N (synCnc (.cv y))
  have p0020 :=
    @gBibi12d (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))
      (.classEq (synCtc M) (synCtc N))
      (.classEq (synCtc (synCnc (.cv x))) (synCtc (synCnc (.cv y)))) (.classEq M N)
      (.classEq (synCnc (.cv x)) (synCnc (.cv y))) p0018 p0019
  have p0021 :=
    @gMpbiri (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))
      (synWb (.classEq (synCtc M) (synCtc N)) (.classEq M N))
      (synWb (.classEq (synCtc (synCnc (.cv x))) (synCtc (synCnc (.cv y))))
        (.classEq (synCnc (.cv x)) (synCnc (.cv y))))
      p0015 p0020
  have p0022 :=
    @gExlimivv (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))
      (synWb (.classEq (synCtc M) (synCtc N)) (.classEq M N)) x y dv_cache_0005
      dv_cache_0006 p0021
  have p0023 :=
    @gSylbi (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWex x (synWex y
          (synWa (.classEq M (synCnc (.cv x))) (.classEq N (synCnc (.cv y))))))
      (synWb (.classEq (synCtc M) (synCtc N)) (.classEq M N)) p0004 p0022
  exact p0023


end NFChoice.DirectNominalPrf.WPPReplay

end
