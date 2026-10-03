/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part061`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppcardt6fnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt6fn)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcardt6fn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))
      (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppcardt6fn)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
        (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))))
      (.classMem D (syn_cncs)) p0001
  have p0003 := @g_wppcardt4fnmapndv
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_a1i
      (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem D (syn_cncs)) p0007
  have p0009 := @g_id (.classMem D (syn_cncs))
  have p0010 := @g_snelpw1 D (syn_cncs)
  have p0011 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs))
      p0010
  have p0012 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cncs))
      (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0009 p0011
  have p0013 := @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0014 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0013
  have p0015 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0012 p0014
  have p0016 := @g_snelpw1 (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0017 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0016
  have p0018 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0015 p0017
  have p0019 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0020 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0019
  have p0021 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0018 p0020
  have p0022 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn D))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
  have p0023 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0022
  have p0024 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      p0021 p0023
  have p0025 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
  have p0026 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      p0025
  have p0027 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      p0024 p0026
  have p0028 :=
    @g_jca (.classMem D (syn_cncs))
      (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      p0008 p0027
  have p0029 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cncs)))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0030 :=
    @g_syl (.classMem D (syn_cncs))
      (syn_wa (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn)))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
          (syn_cpw1 (syn_cpw1 (syn_cncs))))
        (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))))
      (.classEq (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
        (syn_cfv (syn_cwppcardt2fn) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn)))
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))))
      p0028 p0029
  have p0050 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_csi (syn_cwppcardt4fn)) p0005
  have p0051 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classEq (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn)))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_csn
          (syn_cfv (syn_csi (syn_cwppcardt4fn))
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))))
      p0024 p0050
  have p0066 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cwppcardt4fn) p0003
  have p0067 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classEq (syn_cfv (syn_csi (syn_cwppcardt4fn))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))
        (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      p0021 p0066
  have p0068 :=
    @g_sneqd (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_cwppcardt4fn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))
      (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))))
      p0067
  have p0069 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_csn (syn_cfv (syn_csi (syn_cwppcardt4fn))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_csn (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      p0051 p0068
  have p0070 := @g_wppcardt4fnvalsingndv D
  have p0071 :=
    @g_sneqd (.classMem D (syn_cncs))
      (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) p0070
  have p0072 :=
    @g_sneqd (.classMem D (syn_cncs))
      (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))))
      (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))) p0071
  have p0073 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_csn (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) p0069 p0072
  have p0074 :=
    @g_fveq2d (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cwppcardt2fn)
      p0073
  have p0075 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_cfv (syn_cwppcardt2fn) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn)))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))))
      (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      p0030 p0074
  have p0076 := @g_tccl D
  have p0077 := @g_tccl (syn_ctc D)
  have p0078 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc D) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc D)) (syn_cncs)) p0076 p0077
  have p0079 := @g_tccl (syn_ctc (syn_ctc D))
  have p0080 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc (syn_ctc D)) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc D))) (syn_cncs)) p0078 p0079
  have p0081 := @g_tccl (syn_ctc (syn_ctc (syn_ctc D)))
  have p0082 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc D))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) (syn_cncs)) p0080 p0081
  have p0083 := @g_wppcardt2fnvalsingndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))
  have p0084 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) (syn_cncs))
      (.classEq (syn_cfv (syn_cwppcardt2fn)
          (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      p0082 p0083
  have p0085 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) p0075 p0084
  have p0086 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) p0002 p0085
  exact p0086

@[expose]
noncomputable def g_wppconcrete6fnfnndv :
    Nominal.NPrf (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn))) :=
  by
  have p0000 := @g_enex
  have p0001 := @g_wppimagefn (syn_cen) p0000
  have p0002 := @g_wpplitphnordpointfnexndv
  have p0003 := @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 := @g_wppfamilyrep2fnfnndv
  have p0005 := @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn))
      (syn_cwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_wppdirecth1famfnfnndv
  have p0011 := @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010
      p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv))
      (syn_csi (syn_cwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi
      (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0018 p0019
  have p0021 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_cvv))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (syn_cwppdirecth2famfn))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cwppdirecth2famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
      p0024
  have p0026 :=
    @g_mpbir
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0023 p0025
  have p0027 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn)
  have p0028 :=
    @g_mpbi
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wf (syn_cwppdirecth2famfn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0026 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv))
      (syn_wf (syn_cwppdirecth2famfn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0001 p0028
  have p0030 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := (Nominal.classEqRefl (syn_cwppconcrete6codefn))
  have p0033 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
      p0032
  have p0034 :=
    @g_mpbir
      (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0031 p0033
  have p0035 := @g_wppcardt2fnf1ndv
  have p0036 := @g_wppcardt4fnf1ndv
  have p0037 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn) p0036
  have p0038 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0037
  have p0039 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0035 p0038
  have p0040 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 := (Nominal.classEqRefl (syn_cwppcardt6fn))
  have p0043 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbir
      (syn_wf1 (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      p0041 p0044
  have p0046 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @g_f1ofn (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @g_f1of (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0064 := Nominal.mp p0047 p0063
  have p0065 :=
    @g_frn (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0066 := Nominal.mp p0064 p0065
  have p0067 := @g_ssv (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0068 := @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cvv)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 := @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cvv))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0073 := Nominal.mp p0071 p0072
  have p0074 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @g_pm3_2i
      (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0066 p0075
  have p0077 :=
    @g_sstr (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0078 := Nominal.mp p0076 p0077
  have p0079 :=
    @g_n_3pm3_2i
      (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccnv (syn_cwppcardt6fn)) (syn_crn (syn_cwppcardt6fn)))
      (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0034 p0049 p0078
  have p0080 :=
    @g_fnco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))
  have p0081 := Nominal.mp p0079 p0080
  have p0082 := (Nominal.classEqRefl (syn_cwppconcrete6fn))
  have p0083 :=
    @g_fneq1i (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn)
      (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn)))
      (syn_wfn (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)))
        (syn_crn (syn_cwppcardt6fn)))
      p0081 p0083
  exact p0084

@[expose]
noncomputable def g_wppconcrete6fndmndv :
    Nominal.NPrf
      (.classEq (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn))) :=
  by
  have p0000 := @g_enex
  have p0001 := @g_wppimagefn (syn_cen) p0000
  have p0002 := @g_wpplitphnordpointfnexndv
  have p0003 := @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 := @g_wppfamilyrep2fnfnndv
  have p0005 := @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn))
      (syn_cwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_wppdirecth1famfnfnndv
  have p0011 := @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010
      p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv))
      (syn_csi (syn_cwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi
      (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0018 p0019
  have p0021 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_cvv))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (syn_cwppdirecth2famfn))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cwppdirecth2famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
      p0024
  have p0026 :=
    @g_mpbir
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0023 p0025
  have p0027 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn)
  have p0028 :=
    @g_mpbi
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wf (syn_cwppdirecth2famfn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0026 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv))
      (syn_wf (syn_cwppdirecth2famfn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0001 p0028
  have p0030 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := (Nominal.classEqRefl (syn_cwppconcrete6codefn))
  have p0033 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
      p0032
  have p0034 :=
    @g_mpbir
      (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0031 p0033
  have p0035 := @g_wppcardt2fnf1ndv
  have p0036 := @g_wppcardt4fnf1ndv
  have p0037 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn) p0036
  have p0038 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0037
  have p0039 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0035 p0038
  have p0040 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 := (Nominal.classEqRefl (syn_cwppcardt6fn))
  have p0043 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbir
      (syn_wf1 (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      p0041 p0044
  have p0046 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @g_f1ofn (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @g_f1of (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0064 := Nominal.mp p0047 p0063
  have p0065 :=
    @g_frn (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0066 := Nominal.mp p0064 p0065
  have p0067 := @g_ssv (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0068 := @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cvv)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 := @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cvv))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0073 := Nominal.mp p0071 p0072
  have p0074 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @g_pm3_2i
      (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0066 p0075
  have p0077 :=
    @g_sstr (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0078 := Nominal.mp p0076 p0077
  have p0079 :=
    @g_n_3pm3_2i
      (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccnv (syn_cwppcardt6fn)) (syn_crn (syn_cwppcardt6fn)))
      (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0034 p0049 p0078
  have p0080 :=
    @g_fnco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))
  have p0081 := Nominal.mp p0079 p0080
  have p0082 := (Nominal.classEqRefl (syn_cwppconcrete6fn))
  have p0083 :=
    @g_fneq1i (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn)
      (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn)))
      (syn_wfn (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)))
        (syn_crn (syn_cwppcardt6fn)))
      p0081 p0083
  have p0085 := @g_fndm (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn)
  have p0086 := Nominal.mp p0084 p0085
  exact p0086

@[expose]
noncomputable def g_wppconcrete6fnfunsndv :
    Nominal.NPrf (.classMem (syn_cwppconcrete6fn) (syn_cfuns)) :=
  by
  have p0000 := @g_enex
  have p0001 := @g_wppimagefn (syn_cen) p0000
  have p0002 := @g_wpplitphnordpointfnexndv
  have p0003 := @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 := @g_wppfamilyrep2fnfnndv
  have p0005 := @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn))
      (syn_cwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_wppdirecth1famfnfnndv
  have p0011 := @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010
      p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv))
      (syn_csi (syn_cwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi
      (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0018 p0019
  have p0021 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_cvv))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (syn_cwppdirecth2famfn))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cwppdirecth2famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
      p0024
  have p0026 :=
    @g_mpbir
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0023 p0025
  have p0027 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn)
  have p0028 :=
    @g_mpbi
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wf (syn_cwppdirecth2famfn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0026 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv))
      (syn_wf (syn_cwppdirecth2famfn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0001 p0028
  have p0030 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := (Nominal.classEqRefl (syn_cwppconcrete6codefn))
  have p0033 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
      p0032
  have p0034 :=
    @g_mpbir
      (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0031 p0033
  have p0035 := @g_wppcardt2fnf1ndv
  have p0036 := @g_wppcardt4fnf1ndv
  have p0037 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn) p0036
  have p0038 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0037
  have p0039 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0035 p0038
  have p0040 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 := (Nominal.classEqRefl (syn_cwppcardt6fn))
  have p0043 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbir
      (syn_wf1 (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      p0041 p0044
  have p0046 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @g_f1ofn (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @g_f1of (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0064 := Nominal.mp p0047 p0063
  have p0065 :=
    @g_frn (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0066 := Nominal.mp p0064 p0065
  have p0067 := @g_ssv (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0068 := @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cvv)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 := @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cvv))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0073 := Nominal.mp p0071 p0072
  have p0074 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @g_pm3_2i
      (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0066 p0075
  have p0077 :=
    @g_sstr (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0078 := Nominal.mp p0076 p0077
  have p0079 :=
    @g_n_3pm3_2i
      (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccnv (syn_cwppcardt6fn)) (syn_crn (syn_cwppcardt6fn)))
      (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0034 p0049 p0078
  have p0080 :=
    @g_fnco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))
  have p0081 := Nominal.mp p0079 p0080
  have p0082 := (Nominal.classEqRefl (syn_cwppconcrete6fn))
  have p0083 :=
    @g_fneq1i (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn)
      (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn)))
      (syn_wfn (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)))
        (syn_crn (syn_cwppcardt6fn)))
      p0081 p0083
  have p0085 := @g_fnfun (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn)
  have p0086 := Nominal.mp p0084 p0085
  have p0090 := @g_imageex (syn_cen) p0000
  have p0093 := @g_imageex (syn_cwpplitphnordpointfn) p0002
  have p0094 := @g_wppfamilyrep2fnexndv
  have p0095 :=
    @g_coex (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn) p0093 p0094
  have p0096 := @g_wppdirecth1famfnexndv
  have p0097 := @g_siex (syn_cwppdirecth1famfn) p0096
  have p0098 := @g_siex (syn_csi (syn_cwppdirecth1famfn)) p0097
  have p0099 :=
    @g_coex (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn))) p0095 p0098
  have p0100 :=
    @g_eqeltri (syn_cwppdirecth2famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
      (syn_cvv) p0024 p0099
  have p0101 := @g_coex (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn) p0090 p0100
  have p0102 :=
    @g_eqeltri (syn_cwppconcrete6codefn)
      (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_cvv) p0032 p0101
  have p0104 := @g_wppcardt2fnexndv
  have p0105 := @g_wppcardt4fnexndv
  have p0106 := @g_siex (syn_cwppcardt4fn) p0105
  have p0107 := @g_siex (syn_csi (syn_cwppcardt4fn)) p0106
  have p0108 :=
    @g_coex (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))) p0104 p0107
  have p0109 :=
    @g_eqeltri (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cvv) p0042
      p0108
  have p0110 := @g_cnvex (syn_cwppcardt6fn) p0109
  have p0111 :=
    @g_coex (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)) p0102 p0110
  have p0112 :=
    @g_eqeltri (syn_cwppconcrete6fn)
      (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) (syn_cvv) p0082
      p0111
  have p0113 := @g_elfuns (syn_cwppconcrete6fn) p0112
  have p0114 :=
    @g_mpbir (.classMem (syn_cwppconcrete6fn) (syn_cfuns))
      (syn_wfun (syn_cwppconcrete6fn)) p0086 p0113
  exact p0114


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part062`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppconcrete6fnvalndv (X : Class)
    (hyp_wppconcrete6fnvalndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw X))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppconcrete6fn))
  have p0001 :=
    @g_fveq1i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
      (syn_cwppconcrete6fn)
      (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) p0000
  have p0002 := @g_wppcardt2fnf1ndv
  have p0003 := @g_wppcardt4fnf1ndv
  have p0004 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn) p0003
  have p0005 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0004
  have p0006 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0002 p0005
  have p0007 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (syn_cwppcardt6fn))
  have p0010 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_mpbir
      (syn_wf1 (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      p0008 p0011
  have p0013 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_f1ofn (syn_crn (syn_cwppcardt6fn))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_ccnv (syn_cwppcardt6fn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_ncelncsi X hyp_wppconcrete6fnvalndv_1
  have p0018 := @g_wppcardt6fnvalsingndv (syn_cnc X)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @g_wppcardt2fnmapndv
  have p0021 := @g_wppcardt4fnmapndv
  have p0022 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @g_pm3_2i (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0020 p0025
  have p0027 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0028 := Nominal.mp p0026 p0027
  have p0030 :=
    @g_feq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) p0009
  have p0031 :=
    @g_mpbir
      (syn_wf (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      (syn_wf (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      p0028 p0030
  have p0032 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0033 := Nominal.mp p0031 p0032
  have p0035 := @g_snelpw1 (syn_cnc X) (syn_cncs)
  have p0036 :=
    @g_mpbir (.classMem (syn_csn (syn_cnc X)) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cnc X) (syn_cncs)) p0017 p0035
  have p0037 := @g_snelpw1 (syn_csn (syn_cnc X)) (syn_cpw1 (syn_cncs))
  have p0038 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_cnc X))) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn (syn_cnc X)) (syn_cpw1 (syn_cncs))) p0036 p0037
  have p0039 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_cnc X))) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0040 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classMem (syn_csn (syn_csn (syn_cnc X))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0038
      p0039
  have p0041 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_cnc X))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0042 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0040 p0041
  have p0043 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
  have p0044 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0042 p0043
  have p0045 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
  have p0046 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      p0044 p0045
  have p0047 :=
    @g_pm3_2i
      (syn_wfn (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      p0033 p0046
  have p0048 :=
    @g_fnfvelrn
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_cwppcardt6fn)
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @g_eqeltrri
      (syn_cfv (syn_cwppcardt6fn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
      (syn_crn (syn_cwppcardt6fn)) p0019 p0049
  have p0051 :=
    @g_pm3_2i (syn_wfn (syn_ccnv (syn_cwppcardt6fn)) (syn_crn (syn_cwppcardt6fn)))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
        (syn_crn (syn_cwppcardt6fn)))
      p0016 p0050
  have p0052 :=
    @g_fvco2 (syn_crn (syn_cwppcardt6fn))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
      (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))
  have p0053 := Nominal.mp p0051 p0052
  have p0068 :=
    @g_f1f1orn
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0069 := Nominal.mp p0012 p0068
  have p0083 :=
    @g_pm3_2i
      (syn_wf1o (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_crn (syn_cwppcardt6fn)))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      p0069 p0046
  have p0084 :=
    @g_f1ocnvfv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_crn (syn_cwppcardt6fn))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
      (syn_cwppcardt6fn)
  have p0085 := Nominal.mp p0083 p0084
  have p0086 := Nominal.mp p0019 p0085
  have p0087 :=
    @g_fveq2i
      (syn_cfv (syn_ccnv (syn_cwppcardt6fn))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_cwppconcrete6codefn) p0086
  have p0088 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_cfv (syn_cwppconcrete6codefn) (syn_cfv (syn_ccnv (syn_cwppcardt6fn))
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))
      (syn_cfv (syn_cwppconcrete6codefn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      p0053 p0087
  have p0089 := @g_wppconcrete6codefnvalndv X hyp_wppconcrete6fnvalndv_1
  have p0090 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_cfv (syn_cwppconcrete6codefn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) p0088 p0089
  have p0091 :=
    @g_eqtri
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_cfv (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) p0001 p0090
  exact p0091

@[expose]
noncomputable def g_letc2w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (.cv p)))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0003 :
    p ∉
      ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
          (.classEq M (syn_ctc (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 :
    q ∉ ((syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0005 :
    q ∉
      ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))
  have p0001 := @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs))
      p0000 p0001
  have p0004 := @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs))
      p0000 p0004
  have p0006 := @g_tccl N
  have p0007 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))
  have p0009 :=
    @g_simpr (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))
  have p0010 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))) p0008 p0009
  have p0011 :=
    @g_n_3jca
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (.classMem M (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))) p0002 p0007 p0010
  have p0012 := @g_letc M (syn_ctc N) q dv_cache_0001
  have p0013 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0011 p0012
  have p0014 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0015 :=
    @g_simpr
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (.classMem (.cv q) (syn_cncs))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) p0014 p0015
  have p0018 :=
    @g_simpl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (.classMem (.cv q) (syn_cncs))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      p0014 p0018
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (.classMem N (syn_cncs)) p0019 p0005
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))) p0019 p0010
  have p0031 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0032 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc N)) (syn_clec) p0031
  have p0033 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc N))) p0030 p0032
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (.classMem (syn_ctc N) (syn_cncs)) p0019 p0007
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0016 p0045
  have p0047 := @g_tlecg (.cv q) (syn_ctc N)
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)))
      (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc N))
        (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc N))))
      p0046 p0047
  have p0049 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc N))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc N))) p0033 p0048
  have p0050 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc N)) p0016 p0023 p0049
  have p0051 := @g_letc (.cv q) N p dv_cache_0002
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr (.cv q) (syn_clec) (syn_ctc N)))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (.cv p)))) p0050 p0051
  have p0053 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
          (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (.cv p)))
  have p0054 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv p) (syn_cncs))
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
            (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (.cv p))))
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
          (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      p0053 p0054
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
            (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (.cv p))))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (.classEq M (syn_ctc (.cv q))) p0055 p0031
  have p0058 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
          (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (.cv p)))
  have p0059 := @g_tceq (.cv q) (syn_ctc (.cv p))
  have p0060 :=
    @g_a1i
      (.imp (.classEq (.cv q) (syn_ctc (.cv p)))
        (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (.cv p)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
            (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (.cv p))))
      p0059
  have p0061 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
            (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (.cv p))))
      (.classEq (.cv q) (syn_ctc (.cv p)))
      (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (.cv p)))) p0058 p0060
  have p0062 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
            (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (.cv p))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (.cv p))) p0057 p0061
  have p0063 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
          (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (.cv p))) (.classEq M (syn_ctc (syn_ctc (.cv p)))) p0062
  have p0064 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (.classEq (.cv q) (syn_ctc (.cv p))) (.classEq M (syn_ctc (syn_ctc (.cv p)))) p
      (syn_cncs) dv_cache_0003 p0063
  have p0065 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
        (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (.cv p))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (.cv p))))) p0052 p0064
  have p0066 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N)))) (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (.cv p))))) p0065
  have p0067 :=
    @g_rexlimdva
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (.cv p))))) q (syn_cncs)
      dv_cache_0004 dv_cache_0005 p0066
  have p0068 :=
    @g_mpd
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (.cv p))))) p0013 p0067
  exact p0068

@[expose]
noncomputable def g_letc3w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0003 : p ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_p, not_false_eq_true])
  have dv_cache_0004 :
    p ∉
      ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 :
    q ∉ ((syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
  have p0001 := @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs))
      p0000 p0001
  have p0004 := @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs))
      p0000 p0004
  have p0006 := @g_tccl N
  have p0007 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 := @g_tccl (syn_ctc N)
  have p0009 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      p0007 p0008
  have p0010 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
  have p0011 :=
    @g_simpr (.classMem M (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
  have p0012 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0010 p0011
  have p0013 :=
    @g_n_3jca
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0002 p0009 p0012
  have p0014 := @g_letc M (syn_ctc (syn_ctc N)) q dv_cache_0001
  have p0015 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0013 p0014
  have p0016 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0017 :=
    @g_simpr
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classMem (.cv q) (syn_cncs))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) p0016 p0017
  have p0020 :=
    @g_simpl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classMem (.cv q) (syn_cncs))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
        (.classMem (.cv q) (syn_cncs)))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      p0016 p0020
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classMem N (syn_cncs)) p0021 p0005
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0021 p0012
  have p0033 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0034 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc N))) (syn_clec) p0033
  have p0035 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0032 p0034
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0021 p0009
  have p0050 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0018
      p0049
  have p0051 := @g_tlecg (.cv q) (syn_ctc (syn_ctc N))
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)))
      (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc N)))
        (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      p0050 p0051
  have p0053 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc N)))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0035 p0052
  have p0054 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc N))) p0018 p0025 p0053
  have p0055 := @g_letc2w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc N))))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p))))) p0054 p0055
  have p0057 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p))))
  have p0058 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv p) (syn_cncs))
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p)))))
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      p0057 p0058
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p)))))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq M (syn_ctc (.cv q))) p0059 p0033
  have p0062 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p))))
  have p0063 := @g_tceq (.cv q) (syn_ctc (syn_ctc (.cv p)))
  have p0064 :=
    @g_a1i
      (.imp (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p))))
        (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p)))))
      p0063
  have p0065 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p)))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p))))
      (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (.cv p))))) p0062 p0064
  have p0066 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p)))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (.cv p)))) p0061 p0065
  have p0067 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p))))) p0066
  have p0068 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p))))) p (syn_cncs) dv_cache_0004 p0067
  have p0069 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (.cv p)))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0056
      p0068
  have p0070 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0069
  have p0071 :=
    @g_rexlimdva
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) q
      (syn_cncs) dv_cache_0005 dv_cache_0006 p0070
  have p0072 :=
    @g_mpd
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0015
      p0071
  exact p0072


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part063`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_letc4w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0003 : p ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_p, not_false_eq_true])
  have dv_cache_0004 :
    p ∉
      ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 :
    q ∉
      ((syn_wrex p (syn_cncs)
          (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0001 := @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs))
      p0000 p0001
  have p0004 := @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs))
      p0000 p0004
  have p0006 := @g_tccl N
  have p0007 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 := @g_tccl (syn_ctc N)
  have p0009 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      p0007 p0008
  have p0010 := @g_tccl (syn_ctc (syn_ctc N))
  have p0011 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0009 p0010
  have p0012 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0013 :=
    @g_simpr (.classMem M (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0014 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wa (.classMem M (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0012 p0013
  have p0015 :=
    @g_n_3jca
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0002 p0011 p0014
  have p0016 := @g_letc M (syn_ctc (syn_ctc (syn_ctc N))) q dv_cache_0001
  have p0017 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0015 p0016
  have p0018 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0019 :=
    @g_simpr
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem (.cv q) (syn_cncs))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) p0018 p0019
  have p0022 :=
    @g_simpl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem (.cv q) (syn_cncs))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (.classMem (.cv q) (syn_cncs)))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      p0018 p0022
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem N (syn_cncs)) p0023 p0005
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0023 p0014
  have p0035 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0036 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_clec) p0035
  have p0037 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
      p0034 p0036
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0023 p0011
  have p0054 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0020 p0053
  have p0055 := @g_tlecg (.cv q) (syn_ctc (syn_ctc (syn_ctc N)))
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (.classMem (.cv q) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
        (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      p0054 p0055
  have p0057 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
      p0037 p0056
  have p0058 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0020 p0027 p0057
  have p0059 := @g_letc3w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      p0058 p0059
  have p0061 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
  have p0062 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv p) (syn_cncs))
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      p0061 p0062
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq M (syn_ctc (.cv q))) p0063 p0035
  have p0066 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
  have p0067 := @g_tceq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))
  have p0068 :=
    @g_a1i
      (.imp (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
        (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      p0067
  have p0069 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
      (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0066
      p0068
  have p0070 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))) p0065 p0069
  have p0071 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0070
  have p0072 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p (syn_cncs)
      dv_cache_0004 p0071
  have p0073 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      p0060 p0072
  have p0074 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      p0073
  have p0075 :=
    @g_rexlimdva
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      q (syn_cncs) dv_cache_0005 dv_cache_0006 p0074
  have p0076 :=
    @g_mpd
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      p0017 p0075
  exact p0076

@[expose]
noncomputable def g_letc5w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
        (syn_wrex p (syn_cncs)
          (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0003 : p ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_p, not_false_eq_true])
  have dv_cache_0004 :
    p ∉
      ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 :
    q ∉
      ((syn_wrex p (syn_cncs)
          (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0001 := @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs))
      p0000 p0001
  have p0004 := @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs))
      p0000 p0004
  have p0006 := @g_tccl N
  have p0007 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 := @g_tccl (syn_ctc N)
  have p0009 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      p0007 p0008
  have p0010 := @g_tccl (syn_ctc (syn_ctc N))
  have p0011 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0009 p0010
  have p0012 := @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0013 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0011 p0012
  have p0014 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0015 :=
    @g_simpr (.classMem M (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0016 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wa (.classMem M (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0014
      p0015
  have p0017 :=
    @g_n_3jca
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem M (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0002
      p0013 p0016
  have p0018 := @g_letc M (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) q dv_cache_0001
  have p0019 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_w3a (.classMem M (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0017 p0018
  have p0020 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0021 :=
    @g_simpr
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem (.cv q) (syn_cncs))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) p0020 p0021
  have p0024 :=
    @g_simpl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem (.cv q) (syn_cncs))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
        (.classMem (.cv q) (syn_cncs)))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0020 p0024
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem N (syn_cncs)) p0025 p0005
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0025
      p0016
  have p0037 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0038 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_clec)
      p0037
  have p0039 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      p0036 p0038
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0025 p0013
  have p0058 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0022 p0057
  have p0059 := @g_tlecg (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (.classMem (.cv q) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
        (syn_wbr (syn_ctc (.cv q)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0058 p0059
  have p0061 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      p0039 p0060
  have p0062 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0022 p0029
      p0061
  have p0063 := @g_letc4w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      p0062 p0063
  have p0065 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
  have p0066 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv p) (syn_cncs))
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      p0065 p0066
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq M (syn_ctc (.cv q))) p0067 p0037
  have p0070 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
  have p0071 := @g_tceq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
  have p0072 :=
    @g_a1i
      (.imp (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
        (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      p0071
  have p0073 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      p0070 p0072
  have p0074 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0069
      p0073
  have p0075 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0074
  have p0076 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p (syn_cncs)
      dv_cache_0004 p0075
  have p0077 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0064 p0076
  have p0078 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0077
  have p0079 :=
    @g_rexlimdva
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      q (syn_cncs) dv_cache_0005 dv_cache_0006 p0078
  have p0080 :=
    @g_mpd
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0019 p0079
  exact p0080


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part064`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_letc6w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (syn_wrex p (syn_cncs) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0003 : p ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_p, not_false_eq_true])
  have dv_cache_0004 :
    p ∉
      ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 :
    q ∉
      ((syn_wrex p (syn_cncs) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0001 := @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs))
      p0000 p0001
  have p0004 := @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs))
      p0000 p0004
  have p0006 := @g_tccl N
  have p0007 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 := @g_tccl (syn_ctc N)
  have p0009 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      p0007 p0008
  have p0010 := @g_tccl (syn_ctc (syn_ctc N))
  have p0011 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (syn_ctc (syn_ctc N)) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0009 p0010
  have p0012 := @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0013 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0011 p0012
  have p0014 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0015 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) p0013
      p0014
  have p0016 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0017 :=
    @g_simpr (.classMem M (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0018 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0016 p0017
  have p0019 :=
    @g_n_3jca
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem M (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0002 p0015 p0018
  have p0020 :=
    @g_letc M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) q dv_cache_0001
  have p0021 :=
    @g_syl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_w3a (.classMem M (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs))
        (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0019 p0020
  have p0022 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0023 :=
    @g_simpr
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (.cv q) (syn_cncs))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) p0022 p0023
  have p0026 :=
    @g_simpl
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (.cv q) (syn_cncs))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv q) (syn_cncs)))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      p0022 p0026
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem N (syn_cncs)) p0027 p0005
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0027 p0018
  have p0039 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
  have p0040 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_clec) p0039
  have p0041 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0038 p0040
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) p0027
      p0015
  have p0062 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) p0024
      p0061
  have p0063 := @g_tlecg (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wa (.classMem (.cv q) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
        (syn_wbr (syn_ctc (.cv q)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      p0062 p0063
  have p0065 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      p0041 p0064
  have p0066 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
      p0024 p0031 p0065
  have p0067 := @g_letc5w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs))
        (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
      (syn_wrex p (syn_cncs)
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0066 p0067
  have p0069 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
  have p0070 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classMem (.cv p) (syn_cncs))
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec)
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      p0069 p0070
  have p0073 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec)
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq M (syn_ctc (.cv q))) p0071 p0039
  have p0074 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
  have p0075 := @g_tceq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
  have p0076 :=
    @g_a1i
      (.imp (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
        (.classEq (syn_ctc (.cv q))
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec)
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0075
  have p0077 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec)
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (.classEq (syn_ctc (.cv q))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0074 p0076
  have p0078 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
                (syn_wbr M (syn_clec)
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
              (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      M (syn_ctc (.cv q))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0073 p0077
  have p0079 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0078
  have p0080 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p
      (syn_cncs) dv_cache_0004 p0079
  have p0081 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs)
        (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      p0068 p0080
  have p0082 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      p0081
  have p0083 :=
    @g_rexlimdva
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classEq M (syn_ctc (.cv q)))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      q (syn_cncs) dv_cache_0005 dv_cache_0006 p0082
  have p0084 :=
    @g_mpd
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q))))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      p0021 p0083
  exact p0084

@[expose]
noncomputable def g_wppconcrete6dmcovndv (D : Class) (p : Var) (_dv_D_p : p ∉ D.fv)
    (hyp_wppconcrete6dmcovndv_1 : Nominal.NPrf (.classMem D (syn_cncs))) :
    Nominal.NPrf
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : q ∉ ((Class.cv p)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_p, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.classMem (.cv p) (syn_crn (syn_cwppcardt6fn)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn,
          Finset.mem_union, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 :
    q ∉
      ((syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, fresh_q_not_D, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0001 := @g_hwcardssnc (syn_cvv)
  have p0002 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv p) p0001
  have p0003 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cncs)) p0000
      p0002
  have p0004 :=
    @g_a1i (.classMem D (syn_cncs))
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      hyp_wppconcrete6dmcovndv_1
  have p0005 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0006 :=
    @g_n_3jca
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_cncs)) (.classMem D (syn_cncs))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      p0003 p0004 p0005
  have p0007 := @g_letc6w6ndv (.cv p) D q dv_cache_0001 dv_cache_0002
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_w3a (.classMem (.cv p) (syn_cncs)) (.classMem D (syn_cncs))
        (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wrex q (syn_cncs) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      p0006 p0007
  have p0009 := @g_wppcardt6fnmapndv
  have p0010 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_a1i
      (syn_wfn (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      p0011
  have p0013 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
  have p0014 :=
    @g_simpr
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv q) (syn_cncs))
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) p0013 p0014
  have p0016 := @g_snelpw1 (.cv q) (syn_cncs)
  have p0017 :=
    @g_biimpri (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) p0016
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (.cv q) (syn_cncs)) (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs)))
      p0015 p0017
  have p0019 := @g_snelpw1 (syn_csn (.cv q)) (syn_cpw1 (syn_cncs))
  have p0020 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs))) p0019
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0018 p0020
  have p0022 := @g_snelpw1 (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0023 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn (syn_csn (syn_csn (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0021 p0023
  have p0025 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (.cv q))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0026 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classMem (syn_csn (syn_csn (syn_csn (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0025
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (.cv q))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0024 p0026
  have p0028 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
  have p0029 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0028
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      p0027 p0029
  have p0031 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
  have p0032 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      p0030 p0032
  have p0034 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (syn_wfn (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
      p0012 p0033
  have p0035 :=
    @g_fnfvelrn
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))
      (syn_cwppcardt6fn)
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (syn_wa (syn_wfn (syn_cwppcardt6fn)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
        (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))))
      (.classMem (syn_cfv (syn_cwppcardt6fn)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))))
        (syn_crn (syn_cwppcardt6fn)))
      p0034 p0035
  have p0037 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
  have p0041 := @g_wppcardt6fnvalsingndv (.cv q)
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (.cv q) (syn_cncs))
      (.classEq (syn_cfv (syn_cwppcardt6fn)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
      p0015 p0041
  have p0043 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (syn_cfv (syn_cwppcardt6fn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))) p0042
  have p0044 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))
      (syn_cfv (syn_cwppcardt6fn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))))
      p0037 p0043
  have p0045 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.cv p)
      (syn_cfv (syn_cwppcardt6fn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))))
      (syn_crn (syn_cwppcardt6fn)) p0044
  have p0046 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv p) (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn)))
      (.classMem (syn_cfv (syn_cwppcardt6fn)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))))
        (syn_crn (syn_cwppcardt6fn)))
      p0036 p0045
  have p0047 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
      (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) p0046
  have p0048 :=
    @g_rexlimdva
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
      (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) q (syn_cncs) dv_cache_0003
      dv_cache_0004 p0047
  have p0049 :=
    @g_mpd
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wrex q (syn_cncs) (.classEq (.cv p)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))))
      (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) p0008 p0048
  have p0050 :=
    @g_ex (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) p0049
  have p0051 := @g_wppconcrete6fndmndv
  have p0052 :=
    @g_eleq2i (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn)) (.cv p) p0051
  have p0053 :=
    @g_a1i
      (syn_wb (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
        (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0052
  have p0054 :=
    @g_sylibrd (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn)))
      (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) p0050 p0053
  have p0055 :=
    @g_rgen
      (.imp (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))
      p (syn_chwcards (syn_cvv)) p0054
  exact p0055


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part065`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppconcrete6dmpaircovndv (D : Class) (p : Var) (_dv_D_p : p ∉ D.fv)
    (hyp_wppconcrete6dmpaircovndv_1 : Nominal.NPrf (.classMem D (syn_cncs)))
    (hyp_wppconcrete6dmpaircovndv_2 : Nominal.NPrf
        (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) :
    Nominal.NPrf
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
            (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : q ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_p, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 :
    q ∉
      ((Wff.imp (syn_wbr (.cv p) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          Finset.mem_union, Finset.mem_singleton, fresh_q_ne_p, fresh_q_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_ctc (.cv p))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_p,
          not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((Wff.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          Finset.mem_union, Finset.mem_singleton, fresh_q_ne_p, fresh_q_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0001 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0002 := @g_wppconcrete6dmcovndv D q dv_cache_0001 hyp_wppconcrete6dmpaircovndv_1
  have p0003 := @g_id (.classEq (.cv q) (.cv p))
  have p0004 :=
    @g_breq1d (.classEq (.cv q) (.cv p)) (.cv q) (.cv p)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_clec) p0003
  have p0006 :=
    @g_eleq1d (.classEq (.cv q) (.cv p)) (.cv q) (.cv p) (syn_cdm (syn_cwppconcrete6fn))
      p0003
  have p0007 :=
    @g_imbi12d (.classEq (.cv q) (.cv p))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) p0004 p0006
  have p0008 :=
    @g_rspcv
      (.imp (syn_wbr (.cv q) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn))))
      (.imp (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))
      q (.cv p) (syn_chwcards (syn_cvv)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0007
  have p0009 :=
    @g_com12 (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wral q (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv q) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn)))))
      (.imp (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))
      p0008
  have p0010 := Nominal.mp p0002 p0009
  have p0011 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))
      p0001 p0010
  have p0012 :=
    @g_mpd
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) p0000 p0011
  have p0015 := @g_hwcardssnc (syn_cvv)
  have p0016 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv p) p0015
  have p0017 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cncs)) p0001
      p0016
  have p0018 := @g_tccl D
  have p0019 := Nominal.mp hyp_wppconcrete6dmpaircovndv_1 p0018
  have p0020 := @g_tccl (syn_ctc D)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @g_tccl (syn_ctc (syn_ctc D))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @g_tccl (syn_ctc (syn_ctc (syn_ctc D)))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @g_a1i
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs))
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      p0029
  have p0031 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs))
      p0017 p0030
  have p0032 :=
    @g_tlecg (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))
  have p0033 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wa (.classMem (.cv p) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (syn_wbr (syn_ctc (.cv p)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))))
      p0031 p0032
  have p0034 :=
    @g_mpbid
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (syn_wbr (syn_ctc (.cv p)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      p0000 p0033
  have p0035 :=
    @g_a1i
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      hyp_wppconcrete6dmpaircovndv_2
  have p0036 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wbr (syn_ctc (.cv p)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      p0034 p0035
  have p0041 := @g_tccl (.cv p)
  have p0042 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_cncs)) (.classMem (syn_ctc (.cv p)) (syn_cncs)) p0017 p0041
  have p0055 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))
  have p0056 := Nominal.mp p0029 p0055
  have p0057 :=
    @g_a1i
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (syn_cncs))
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      p0056
  have p0071 :=
    @g_n_3jca
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (syn_ctc (.cv p)) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs))
      p0042 p0057 p0030
  have p0072 :=
    @g_lectr (syn_ctc (.cv p))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))
  have p0073 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_w3a (.classMem (syn_ctc (.cv p)) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))
          (syn_cncs)))
      (.imp (syn_wa (syn_wbr (syn_ctc (.cv p)) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
            (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
        (syn_wbr (syn_ctc (.cv p)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      p0071 p0072
  have p0074 :=
    @g_mpd
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wa (syn_wbr (syn_ctc (.cv p)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
        (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wbr (syn_ctc (.cv p)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      p0036 p0073
  have p0076 := @g_hwcardstcclndv (.cv p)
  have p0077 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv))) p0001 p0076
  have p0079 := @g_id (.classEq (.cv q) (syn_ctc (.cv p)))
  have p0080 :=
    @g_breq1d (.classEq (.cv q) (syn_ctc (.cv p))) (.cv q) (syn_ctc (.cv p))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_clec) p0079
  have p0082 :=
    @g_eleq1d (.classEq (.cv q) (syn_ctc (.cv p))) (.cv q) (syn_ctc (.cv p))
      (syn_cdm (syn_cwppconcrete6fn)) p0079
  have p0083 :=
    @g_imbi12d (.classEq (.cv q) (syn_ctc (.cv p)))
      (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (syn_wbr (syn_ctc (.cv p)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) p0080 p0082
  have p0084 :=
    @g_rspcv
      (.imp (syn_wbr (.cv q) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn))))
      (.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))
      q (syn_ctc (.cv p)) (syn_chwcards (syn_cvv)) dv_cache_0005 dv_cache_0003
      dv_cache_0006 p0083
  have p0085 :=
    @g_com12 (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv)))
      (syn_wral q (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv q) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
          (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn)))))
      (.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))
      p0084
  have p0086 := Nominal.mp p0002 p0085
  have p0087 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))
      p0077 p0086
  have p0088 :=
    @g_mpd
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (syn_wbr (syn_ctc (.cv p)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) p0074 p0087
  have p0089 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))
      (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) p0012 p0088
  have p0090 :=
    @g_ex (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
      (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
        (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))
      p0089
  have p0091 :=
    @g_rgen
      (.imp (syn_wbr (.cv p) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
        (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
          (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))
      p (syn_chwcards (syn_cvv)) p0090
  exact p0091

@[expose]
noncomputable def g_hncardnc1ndv :
    Nominal.NPrf (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_hncardnc (syn_c1c)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wppconcrete6hncard1dmcovndv (p : Var) :
    Nominal.NPrf
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))) :=
  by
  have dv_cache_0001 : p ∉ ((syn_chncard (syn_c1c))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 := @g_n_1cex
  have p0001 := @g_hncardnc (syn_c1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_wppconcrete6dmcovndv (syn_chncard (syn_c1c)) p dv_cache_0001 p0002
  exact p0003

@[expose]
noncomputable def g_wppconcrete6hncard1dmpaircovndv (p : Var)
    (hyp_wppconcrete6hncard1dmpaircovndv_1 : Nominal.NPrf (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) :
    Nominal.NPrf
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
            (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) :=
  by
  have dv_cache_0001 : p ∉ ((syn_chncard (syn_c1c))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 := @g_n_1cex
  have p0001 := @g_hncardnc (syn_c1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_wppconcrete6dmpaircovndv (syn_chncard (syn_c1c)) p dv_cache_0001 p0002
      hyp_wppconcrete6hncard1dmpaircovndv_1
  exact p0003

@[expose]
noncomputable def g_hncardtcshiftcondndv (A : Class)
    (hyp_hncardtcshiftcondndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_hncardtcshiftcondndv_2 : Nominal.NPrf
        (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A)))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_chncard A)) (syn_chncard (syn_cpw1 A))) :=
  by
  have p0000 := @g_hncardtc A hyp_hncardtcshiftcondndv_1
  have p0001 := @g_hnordex A hyp_hncardtcshiftcondndv_1
  have p0002 := @g_pw1ex (syn_chnord A) p0001
  have p0003 := @g_eqnc (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) p0002
  have p0004 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_chnord A))) (syn_cnc (syn_chnord (syn_cpw1 A))))
      (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A)))
      hyp_hncardtcshiftcondndv_2 p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_chncard A)) (syn_cnc (syn_cpw1 (syn_chnord A)))
      (syn_cnc (syn_chnord (syn_cpw1 A))) p0000 p0004
  have p0006 := (Nominal.classEqRefl (syn_chncard (syn_cpw1 A)))
  have p0007 :=
    @g_eqtr4i (syn_ctc (syn_chncard A)) (syn_cnc (syn_chnord (syn_cpw1 A)))
      (syn_chncard (syn_cpw1 A)) p0005 p0006
  exact p0007

@[expose]
noncomputable def g_hnsicodeliftfnexndv :
    Nominal.NPrf (.classMem (syn_chnsicodeliftfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnsicodeliftfn))
  have p0001 := @g_lnpwsirelfnex
  have p0002 := @g_lnpwpw1secondfnex
  have p0003 := @g_txpex (syn_clnpwsirelfn) (syn_clnpwpw1secondfn) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_chnsicodeliftfn) (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn))
      (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_hnsicodeliftfnfnndv :
    Nominal.NPrf (syn_wfn (syn_chnsicodeliftfn) (syn_cvv)) :=
  by
  have p0000 := @g_lnpwsirelfnfn
  have p0001 := @g_lnpwpw1secondfnfn
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_clnpwsirelfn) (syn_cvv))
      (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) p0000 p0001
  have p0003 := @g_fntxp (syn_cvv) (syn_cvv) (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_inidm (syn_cvv)
  have p0006 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) p0005
  have p0007 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_cvv)) p0004 p0006
  have p0008 := (Nominal.classEqRefl (syn_chnsicodeliftfn))
  have p0009 :=
    @g_fneq1i (syn_cvv) (syn_chnsicodeliftfn)
      (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) p0008
  have p0010 :=
    @g_mpbir (syn_wfn (syn_chnsicodeliftfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_cvv)) p0007 p0009
  exact p0010

@[expose]
noncomputable def g_sisuppdndv (ph : Wff) (D : Class) (R : Class)
    (hyp_sisuppdndv_1 : Nominal.NPrf (.imp ph (syn_wss R (syn_cxp D D)))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_csi R) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0006 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0007 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0008 :
    z ∉
      ((Wff.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    w ∉
      ((Wff.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0010 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0011 : w ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_csi R)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_cxp (syn_cpw1 D) (syn_cpw1 D))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cxp (syn_cpw1 D) (syn_cpw1 D))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_y_not_D, or_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (ph).fv :=
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
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0017 : y ∉ (ph).fv :=
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
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0018 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csi R) (.cv y)))
  have p0001 :=
    @g_biimpri (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) p0000
  have p0002 :=
    @g_brsi z w (.cv x) (.cv y) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wex z (syn_wex w
            (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
              (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))))))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) p0002
  have p0004 :=
    @g_mpbid (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R))
      (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
            (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w)))))
      p0001 p0003
  have p0005 :=
    @g_a1i
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) (syn_wex z (syn_wex w
            (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
              (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))))))
      ph p0004
  have p0006 :=
    @g_simp3 (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
      (syn_wbr (.cv z) R (.cv w))
  have p0007 := (Nominal.biimpRefl (syn_wbr (.cv z) R (.cv w)))
  have p0008 :=
    @g_a1i (syn_wb (syn_wbr (.cv z) R (.cv w)) (.classMem (syn_cop (.cv z) (.cv w)) R))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      p0007
  have p0009 :=
    @g_mpbid
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (syn_wbr (.cv z) R (.cv w)) (.classMem (syn_cop (.cv z) (.cv w)) R) p0006 p0008
  have p0010 :=
    @g_a1i
      (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
          (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv z) (.cv w)) R))
      ph p0009
  have p0011 := @g_sseld ph R (syn_cxp D D) (syn_cop (.cv z) (.cv w)) hyp_sisuppdndv_1
  have p0012 :=
    @g_syld ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (syn_cop (.cv z) (.cv w)) R)
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D)) p0010 p0011
  have p0013 := @g_opelxp (.cv z) (.cv w) D D
  have p0014 :=
    @g_biimpi (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D))
      (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0013
  have p0015 :=
    @g_syl6 ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D))
      (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0012 p0014
  have p0016 := @g_simpl (.classMem (.cv z) D) (.classMem (.cv w) D)
  have p0017 :=
    @g_syl6 ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) (.classMem (.cv z) D) p0015
      p0016
  have p0018 := @g_snelpw1 (.cv z) D
  have p0019 :=
    @g_biimpri (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) (.classMem (.cv z) D) p0018
  have p0020 :=
    @g_simp1 (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
      (syn_wbr (.cv z) R (.cv w))
  have p0021 :=
    @g_eleq1d
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.cv x) (syn_csn (.cv z)) (syn_cpw1 D) p0020
  have p0022 :=
    @g_biimprd
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (.cv x) (syn_cpw1 D)) (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) p0021
  have p0023 :=
    @g_syl5 (.classMem (.cv z) D) (.classMem (syn_csn (.cv z)) (syn_cpw1 D))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (.cv x) (syn_cpw1 D)) p0019 p0022
  have p0024 :=
    @g_a1i
      (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
          (syn_wbr (.cv z) R (.cv w)))
        (.imp (.classMem (.cv z) D) (.classMem (.cv x) (syn_cpw1 D))))
      ph p0023
  have p0025 :=
    @g_mpdd ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (.cv z) D) (.classMem (.cv x) (syn_cpw1 D)) p0017 p0024
  have p0036 := @g_simpr (.classMem (.cv z) D) (.classMem (.cv w) D)
  have p0037 :=
    @g_syl6 ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) (.classMem (.cv w) D) p0015
      p0036
  have p0038 := @g_snelpw1 (.cv w) D
  have p0039 :=
    @g_biimpri (.classMem (syn_csn (.cv w)) (syn_cpw1 D)) (.classMem (.cv w) D) p0038
  have p0040 :=
    @g_simp2 (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
      (syn_wbr (.cv z) R (.cv w))
  have p0041 :=
    @g_eleq1d
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.cv y) (syn_csn (.cv w)) (syn_cpw1 D) p0040
  have p0042 :=
    @g_biimprd
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (.cv y) (syn_cpw1 D)) (.classMem (syn_csn (.cv w)) (syn_cpw1 D)) p0041
  have p0043 :=
    @g_syl5 (.classMem (.cv w) D) (.classMem (syn_csn (.cv w)) (syn_cpw1 D))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (.cv y) (syn_cpw1 D)) p0039 p0042
  have p0044 :=
    @g_a1i
      (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
          (syn_wbr (.cv z) R (.cv w)))
        (.imp (.classMem (.cv w) D) (.classMem (.cv y) (syn_cpw1 D))))
      ph p0043
  have p0045 :=
    @g_mpdd ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (.cv w) D) (.classMem (.cv y) (syn_cpw1 D)) p0037 p0044
  have p0046 :=
    @g_jcad ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) p0025 p0045
  have p0047 := @g_opelxp (.cv x) (.cv y) (syn_cpw1 D) (syn_cpw1 D)
  have p0048 :=
    @g_biimpri (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))
      (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) p0047
  have p0049 :=
    @g_syl6 ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0046
      p0048
  have p0050 :=
    @g_exlimdvv ph
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
        (syn_wbr (.cv z) R (.cv w)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) z w
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0049
  have p0051 :=
    @g_syld ph (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R))
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
            (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w)))))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0005
      p0050
  have p0052 :=
    @g_relssdv ph x y (syn_csi R) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)) dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      p0051
  exact p0052

@[expose]
noncomputable def g_hnsicodeliftcodeclndv (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem
          (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn (syn_cpw1 A)))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 :
    Disjoint ((syn_cpw1 A)).fv ((syn_csi (syn_cfv (syn_c1st) (.cv u)))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((syn_cpw1 A)).fv ((syn_csi (syn_cfv (syn_c1st) (.cv u)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi];
          exact
            (show Disjoint ((A).fv) (((syn_cfv (syn_c1st) (.cv u))).fv) from
              (by
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
                                  (show u ∉ (A).fv from (by exact dv_A_u)))))),
                        (show Disjoint ((A).fv) (((syn_c1st)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                            exact
                              (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                (by simp))))⟩))))))
  have p0000 := @g_hwcnwendv u A dv_cache_0001
  have p0001 := @g_siwendv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe)
        (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      p0000 p0001
  have p0003 := @g_hwcnbase u A dv_cache_0001
  have p0004 := @g_pw1ss (syn_cfv (syn_c2nd) (.cv u)) A
  have p0005 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)
      (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A)) p0003 p0004
  have p0006 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe)
        (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A)) p0002 p0005
  have p0007 := @g_fvex (.cv u) (syn_c1st)
  have p0008 := @g_siex (syn_cfv (syn_c1st) (.cv u)) p0007
  have p0009 := @g_fvex (.cv u) (syn_c2nd)
  have p0010 := @g_pw1ex (syn_cfv (syn_c2nd) (.cv u)) p0009
  have p0011 :=
    @g_elhwcodes (syn_cpw1 A) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))
      (syn_csi (syn_cfv (syn_c1st) (.cv u))) dv_cache_0002 p0008 p0010
  have p0012 :=
    @g_biimpri
      (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A)))
      (syn_wa (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe)
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A)))
      p0011
  have p0013 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe)
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A)))
      (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A)))
      p0006 p0012
  have p0014 := @g_hwcnsupp u A
  have p0015 :=
    @g_sisuppdndv (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) p0014
  have p0020 :=
    @g_opfv1st (syn_csi (syn_cfv (syn_c1st) (.cv u)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0008 p0010
  have p0025 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (.cv u)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0008 p0010
  have p0031 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0025 p0025
  have p0032 :=
    @g_sseq12i
      (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_csi (syn_cfv (syn_c1st) (.cv u)))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd)
          (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cxp (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      p0020 p0031
  have p0033 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A))
      (syn_wss (syn_csi (syn_cfv (syn_c1st) (.cv u)))
        (syn_cxp (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
              (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd)
            (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
              (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      p0015 p0032
  have p0034 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A)))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
              (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd)
            (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
              (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      p0013 p0033
  have p0039 :=
    @g_opex (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))
      p0008 p0010
  have p0040 :=
    @g_elhwcncl (syn_cpw1 A)
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
            (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A))) (syn_wss
          (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
              (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd)
              (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
                (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd)
              (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
                (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))))
      (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn (syn_cpw1 A)))
      p0034 p0041
  exact p0042

@[expose]
noncomputable def g_hnsicodeliftfnvalgndv (D : Class) (R : Class)
    (hyp_hnsicodeliftfnvalgndv_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hnsicodeliftfnvalgndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
        (.classEq (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D)))
          (syn_cop (syn_csi R) (syn_cpw1 D)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnsicodeliftfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_chnsicodeliftfn)
      (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) p0000
  have p0002 := @g_lnpwsirelfnfn
  have p0003 := @g_lnpwpw1secondfnfn
  have p0004 := @g_snex (syn_cop R D)
  have p0005 :=
    @g_fvtxpvv (syn_csn (syn_cop R D)) (syn_clnpwsirelfn) (syn_clnpwpw1secondfn) p0002
      p0003 p0004
  have p0006 :=
    @g_eqtri (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D)))
      (syn_cop (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D)))
        (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))))
      p0001 p0005
  have p0007 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D)))
        (syn_cop (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D)))
          (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))))
      (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0006
  have p0008 :=
    @g_lnpwsirelfnvalg D R hyp_hnsicodeliftfnvalgndv_1 hyp_hnsicodeliftfnvalgndv_2
  have p0009 :=
    @g_lnpwpw1secondfnval D R hyp_hnsicodeliftfnvalgndv_1 hyp_hnsicodeliftfnvalgndv_2
  have p0010 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D))
      (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0009
  have p0011 :=
    @g_opeq12d (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_csi R)
      (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D) p0008 p0010
  have p0012 :=
    @g_eqtrd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D)))
      (syn_cop (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D)))
        (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))))
      (syn_cop (syn_csi R) (syn_cpw1 D)) p0007 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end
