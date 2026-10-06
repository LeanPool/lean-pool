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

/-- Checked nominal proof certificate identified upstream as `g_wppcardt6fnvalsingndv`. -/
@[expose]
noncomputable def gWppcardt6fnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (synCncs)) (.classEq (synCfv (synCwppcardt6fn)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcardt6fn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))
      (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn)))) p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synCwppcardt6fn)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
        (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))))
      (.classMem D (synCncs)) p0001
  have p0003 := @gWppcardt4fnmapndv
  have p0004 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsi (synCwppcardt4fn))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gA1i
      (synWf (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      (.classMem D (synCncs)) p0007
  have p0009 := @gId (.classMem D (synCncs))
  have p0010 := @gSnelpw1 D (synCncs)
  have p0011 :=
    @gBiimpri (.classMem (synCsn D) (synCpw1 (synCncs))) (.classMem D (synCncs))
      p0010
  have p0012 :=
    @gSyl (.classMem D (synCncs)) (.classMem D (synCncs))
      (.classMem (synCsn D) (synCpw1 (synCncs))) p0009 p0011
  have p0013 := @gSnelpw1 (synCsn D) (synCpw1 (synCncs))
  have p0014 :=
    @gBiimpri (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn D) (synCpw1 (synCncs))) p0013
  have p0015 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCsn D) (synCpw1 (synCncs)))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))) p0012 p0014
  have p0016 := @gSnelpw1 (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))
  have p0017 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))) p0016
  have p0018 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0015 p0017
  have p0019 :=
    @gSnelpw1 (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs))))
  have p0020 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0019
  have p0021 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0018 p0020
  have p0022 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn D))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
  have p0023 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn D)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0022
  have p0024 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn D)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      p0021 p0023
  have p0025 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn (synCsn D)))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
  have p0026 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn D)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      p0025
  have p0027 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn D)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      p0024 p0026
  have p0028 :=
    @gJca (.classMem D (synCncs))
      (synWf (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      p0008 p0027
  have p0029 :=
    @gFvco3 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCncs)))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt4fn)))
  have p0030 :=
    @gSyl (.classMem D (synCncs))
      (synWa (synWf (synCsi (synCsi (synCwppcardt4fn)))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
          (synCpw1 (synCpw1 (synCncs))))
        (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))))
      (.classEq (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
        (synCfv (synCwppcardt2fn) (synCfv (synCsi (synCsi (synCwppcardt4fn)))
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))))
      p0028 p0029
  have p0050 :=
    @gSifvald (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsn (synCsn (synCsn (synCsn (synCsn D)))))
      (synCsi (synCwppcardt4fn)) p0005
  have p0051 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn D)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classEq (synCfv (synCsi (synCsi (synCwppcardt4fn)))
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))) (synCsn
          (synCfv (synCsi (synCwppcardt4fn))
            (synCsn (synCsn (synCsn (synCsn (synCsn D))))))))
      p0024 p0050
  have p0066 :=
    @gSifvald (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCsn (synCsn (synCsn (synCsn D)))) (synCwppcardt4fn) p0003
  have p0067 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classEq (synCfv (synCsi (synCwppcardt4fn))
          (synCsn (synCsn (synCsn (synCsn (synCsn D))))))
        (synCsn (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D)))))))
      p0021 p0066
  have p0068 :=
    @gSneqd (.classMem D (synCncs))
      (synCfv (synCsi (synCwppcardt4fn)) (synCsn (synCsn (synCsn (synCsn (synCsn D))))))
      (synCsn (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D))))))
      p0067
  have p0069 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCsi (synCsi (synCwppcardt4fn)))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCsn (synCfv (synCsi (synCwppcardt4fn))
          (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCsn (synCsn (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D)))))))
      p0051 p0068
  have p0070 := @gWppcardt4fnvalsingndv D
  have p0071 :=
    @gSneqd (.classMem D (synCncs))
      (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D)))))
      (synCtc (synCtc (synCtc (synCtc D)))) p0070
  have p0072 :=
    @gSneqd (.classMem D (synCncs))
      (synCsn (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D))))))
      (synCsn (synCtc (synCtc (synCtc (synCtc D))))) p0071
  have p0073 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCsi (synCsi (synCwppcardt4fn)))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCsn (synCsn (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCsn (synCsn (synCtc (synCtc (synCtc (synCtc D)))))) p0069 p0072
  have p0074 :=
    @gFveq2d (.classMem D (synCncs))
      (synCfv (synCsi (synCsi (synCwppcardt4fn)))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCsn (synCsn (synCtc (synCtc (synCtc (synCtc D)))))) (synCwppcardt2fn)
      p0073
  have p0075 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCfv (synCwppcardt2fn) (synCfv (synCsi (synCsi (synCwppcardt4fn)))
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D))))))))
      (synCfv (synCwppcardt2fn) (synCsn (synCsn (synCtc (synCtc (synCtc (synCtc D)))))))
      p0030 p0074
  have p0076 := @gTccl D
  have p0077 := @gTccl (synCtc D)
  have p0078 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCtc D) (synCncs))
      (.classMem (synCtc (synCtc D)) (synCncs)) p0076 p0077
  have p0079 := @gTccl (synCtc (synCtc D))
  have p0080 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCtc (synCtc D)) (synCncs))
      (.classMem (synCtc (synCtc (synCtc D))) (synCncs)) p0078 p0079
  have p0081 := @gTccl (synCtc (synCtc (synCtc D)))
  have p0082 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCtc (synCtc (synCtc D))) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc D)))) (synCncs)) p0080 p0081
  have p0083 := @gWppcardt2fnvalsingndv (synCtc (synCtc (synCtc (synCtc D))))
  have p0084 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc D)))) (synCncs))
      (.classEq (synCfv (synCwppcardt2fn)
          (synCsn (synCsn (synCtc (synCtc (synCtc (synCtc D)))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      p0082 p0083
  have p0085 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCfv (synCwppcardt2fn) (synCsn (synCsn (synCtc (synCtc (synCtc (synCtc D)))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) p0075 p0084
  have p0086 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCwppcardt6fn) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn D)))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) p0002 p0085
  exact p0086

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6fnfnndv`. -/
@[expose]
noncomputable def gWppconcrete6fnfnndv :
    Nominal.NPrf (synWfn (synCwppconcrete6fn) (synCrn (synCwppcardt6fn))) :=
  by
  have p0000 := @gEnex
  have p0001 := @gWppimagefn (synCen) p0000
  have p0002 := @gWpplitphnordpointfnexndv
  have p0003 := @gWppimagefn (synCwpplitphnordpointfn) p0002
  have p0004 := @gWppfamilyrep2fnfnndv
  have p0005 := @gDffn2 (synCvv) (synCwppfamilyrep2fn)
  have p0006 :=
    @gMpbi (synWfn (synCwppfamilyrep2fn) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0004 p0005
  have p0007 :=
    @gPm32i (synWfn (synCimage (synCwpplitphnordpointfn)) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0003 p0006
  have p0008 :=
    @gFnfco (synCvv) (synCvv) (synCimage (synCwpplitphnordpointfn))
      (synCwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gWppdirecth1famfnfnndv
  have p0011 := @gDffn2 (synCpw1 (synCpw1 (synCvv))) (synCwppdirecth1famfn)
  have p0012 :=
    @gMpbi (synWfn (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))))
      (synWf (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))) (synCvv)) p0010
      p0011
  have p0013 :=
    @gSifmap (synCpw1 (synCpw1 (synCvv))) (synCvv) (synCwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCvv)))) (synCpw1 (synCvv))
      (synCsi (synCwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCpw1 (synCpw1 (synCvv))) (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gDffn2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0020 :=
    @gMpbi
      (synWfn (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0018 p0019
  have p0021 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCvv))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0009 p0020
  have p0022 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (synCwppdirecth2famfn))
  have p0025 :=
    @gFneq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCwppdirecth2famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecth1famfn))))
      p0024
  have p0026 :=
    @gMpbir
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecth1famfn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0023 p0025
  have p0027 :=
    @gDffn2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCwppdirecth2famfn)
  have p0028 :=
    @gMpbi
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWf (synCwppdirecth2famfn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0026 p0027
  have p0029 :=
    @gPm32i (synWfn (synCimage (synCen)) (synCvv))
      (synWf (synCwppdirecth2famfn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0001 p0028
  have p0030 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCimage (synCen)) (synCwppdirecth2famfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := (Nominal.classEqRefl (synCwppconcrete6codefn))
  have p0033 :=
    @gFneq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCwppconcrete6codefn) (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
      p0032
  have p0034 :=
    @gMpbir
      (synWfn (synCwppconcrete6codefn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0031 p0033
  have p0035 := @gWppcardt2fnf1ndv
  have p0036 := @gWppcardt4fnf1ndv
  have p0037 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn) p0036
  have p0038 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsi (synCwppcardt4fn)) p0037
  have p0039 :=
    @gPm32i (synWf1 (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf1 (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      p0035 p0038
  have p0040 :=
    @gF1co (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt4fn)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 := (Nominal.classEqRefl (synCwppcardt6fn))
  have p0043 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @gMpbir
      (synWf1 (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      (synWf1 (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      p0041 p0044
  have p0046 :=
    @gF1cnv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @gF1ofn (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @gF1of (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0064 := Nominal.mp p0047 p0063
  have p0065 :=
    @gFrn (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0066 := Nominal.mp p0064 p0065
  have p0067 := @gSsv (synCpw1 (synCpw1 (synCncs)))
  have p0068 := @gPw1ss (synCpw1 (synCpw1 (synCncs))) (synCvv)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 := @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCncs)))) (synCpw1 (synCvv))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synCpw1 (synCpw1 (synCvv)))
  have p0073 := Nominal.mp p0071 p0072
  have p0074 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCpw1 (synCpw1 (synCvv))))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @gPm32i
      (synWss (synCrn (synCcnv (synCwppcardt6fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0066 p0075
  have p0077 :=
    @gSstr (synCrn (synCcnv (synCwppcardt6fn)))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
  have p0078 := Nominal.mp p0076 p0077
  have p0079 :=
    @gN3pm32i
      (synWfn (synCwppconcrete6codefn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcnv (synCwppcardt6fn)) (synCrn (synCwppcardt6fn)))
      (synWss (synCrn (synCcnv (synCwppcardt6fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0034 p0049 p0078
  have p0080 :=
    @gFnco (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCrn (synCwppcardt6fn)) (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))
  have p0081 := Nominal.mp p0079 p0080
  have p0082 := (Nominal.classEqRefl (synCwppconcrete6fn))
  have p0083 :=
    @gFneq1i (synCrn (synCwppcardt6fn)) (synCwppconcrete6fn)
      (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))) p0082
  have p0084 :=
    @gMpbir (synWfn (synCwppconcrete6fn) (synCrn (synCwppcardt6fn)))
      (synWfn (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)))
        (synCrn (synCwppcardt6fn)))
      p0081 p0083
  exact p0084

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6fndmndv`. -/
@[expose]
noncomputable def gWppconcrete6fndmndv :
    Nominal.NPrf
      (.classEq (synCdm (synCwppconcrete6fn)) (synCrn (synCwppcardt6fn))) :=
  by
  have p0000 := @gEnex
  have p0001 := @gWppimagefn (synCen) p0000
  have p0002 := @gWpplitphnordpointfnexndv
  have p0003 := @gWppimagefn (synCwpplitphnordpointfn) p0002
  have p0004 := @gWppfamilyrep2fnfnndv
  have p0005 := @gDffn2 (synCvv) (synCwppfamilyrep2fn)
  have p0006 :=
    @gMpbi (synWfn (synCwppfamilyrep2fn) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0004 p0005
  have p0007 :=
    @gPm32i (synWfn (synCimage (synCwpplitphnordpointfn)) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0003 p0006
  have p0008 :=
    @gFnfco (synCvv) (synCvv) (synCimage (synCwpplitphnordpointfn))
      (synCwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gWppdirecth1famfnfnndv
  have p0011 := @gDffn2 (synCpw1 (synCpw1 (synCvv))) (synCwppdirecth1famfn)
  have p0012 :=
    @gMpbi (synWfn (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))))
      (synWf (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))) (synCvv)) p0010
      p0011
  have p0013 :=
    @gSifmap (synCpw1 (synCpw1 (synCvv))) (synCvv) (synCwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCvv)))) (synCpw1 (synCvv))
      (synCsi (synCwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCpw1 (synCpw1 (synCvv))) (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gDffn2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0020 :=
    @gMpbi
      (synWfn (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0018 p0019
  have p0021 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCvv))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0009 p0020
  have p0022 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (synCwppdirecth2famfn))
  have p0025 :=
    @gFneq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCwppdirecth2famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecth1famfn))))
      p0024
  have p0026 :=
    @gMpbir
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecth1famfn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0023 p0025
  have p0027 :=
    @gDffn2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCwppdirecth2famfn)
  have p0028 :=
    @gMpbi
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWf (synCwppdirecth2famfn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0026 p0027
  have p0029 :=
    @gPm32i (synWfn (synCimage (synCen)) (synCvv))
      (synWf (synCwppdirecth2famfn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0001 p0028
  have p0030 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCimage (synCen)) (synCwppdirecth2famfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := (Nominal.classEqRefl (synCwppconcrete6codefn))
  have p0033 :=
    @gFneq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCwppconcrete6codefn) (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
      p0032
  have p0034 :=
    @gMpbir
      (synWfn (synCwppconcrete6codefn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0031 p0033
  have p0035 := @gWppcardt2fnf1ndv
  have p0036 := @gWppcardt4fnf1ndv
  have p0037 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn) p0036
  have p0038 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsi (synCwppcardt4fn)) p0037
  have p0039 :=
    @gPm32i (synWf1 (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf1 (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      p0035 p0038
  have p0040 :=
    @gF1co (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt4fn)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 := (Nominal.classEqRefl (synCwppcardt6fn))
  have p0043 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @gMpbir
      (synWf1 (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      (synWf1 (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      p0041 p0044
  have p0046 :=
    @gF1cnv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @gF1ofn (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @gF1of (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0064 := Nominal.mp p0047 p0063
  have p0065 :=
    @gFrn (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0066 := Nominal.mp p0064 p0065
  have p0067 := @gSsv (synCpw1 (synCpw1 (synCncs)))
  have p0068 := @gPw1ss (synCpw1 (synCpw1 (synCncs))) (synCvv)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 := @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCncs)))) (synCpw1 (synCvv))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synCpw1 (synCpw1 (synCvv)))
  have p0073 := Nominal.mp p0071 p0072
  have p0074 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCpw1 (synCpw1 (synCvv))))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @gPm32i
      (synWss (synCrn (synCcnv (synCwppcardt6fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0066 p0075
  have p0077 :=
    @gSstr (synCrn (synCcnv (synCwppcardt6fn)))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
  have p0078 := Nominal.mp p0076 p0077
  have p0079 :=
    @gN3pm32i
      (synWfn (synCwppconcrete6codefn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcnv (synCwppcardt6fn)) (synCrn (synCwppcardt6fn)))
      (synWss (synCrn (synCcnv (synCwppcardt6fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0034 p0049 p0078
  have p0080 :=
    @gFnco (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCrn (synCwppcardt6fn)) (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))
  have p0081 := Nominal.mp p0079 p0080
  have p0082 := (Nominal.classEqRefl (synCwppconcrete6fn))
  have p0083 :=
    @gFneq1i (synCrn (synCwppcardt6fn)) (synCwppconcrete6fn)
      (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))) p0082
  have p0084 :=
    @gMpbir (synWfn (synCwppconcrete6fn) (synCrn (synCwppcardt6fn)))
      (synWfn (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)))
        (synCrn (synCwppcardt6fn)))
      p0081 p0083
  have p0085 := @gFndm (synCrn (synCwppcardt6fn)) (synCwppconcrete6fn)
  have p0086 := Nominal.mp p0084 p0085
  exact p0086

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6fnfunsndv`. -/
@[expose]
noncomputable def gWppconcrete6fnfunsndv :
    Nominal.NPrf (.classMem (synCwppconcrete6fn) (synCfuns)) :=
  by
  have p0000 := @gEnex
  have p0001 := @gWppimagefn (synCen) p0000
  have p0002 := @gWpplitphnordpointfnexndv
  have p0003 := @gWppimagefn (synCwpplitphnordpointfn) p0002
  have p0004 := @gWppfamilyrep2fnfnndv
  have p0005 := @gDffn2 (synCvv) (synCwppfamilyrep2fn)
  have p0006 :=
    @gMpbi (synWfn (synCwppfamilyrep2fn) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0004 p0005
  have p0007 :=
    @gPm32i (synWfn (synCimage (synCwpplitphnordpointfn)) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0003 p0006
  have p0008 :=
    @gFnfco (synCvv) (synCvv) (synCimage (synCwpplitphnordpointfn))
      (synCwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gWppdirecth1famfnfnndv
  have p0011 := @gDffn2 (synCpw1 (synCpw1 (synCvv))) (synCwppdirecth1famfn)
  have p0012 :=
    @gMpbi (synWfn (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))))
      (synWf (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))) (synCvv)) p0010
      p0011
  have p0013 :=
    @gSifmap (synCpw1 (synCpw1 (synCvv))) (synCvv) (synCwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCvv)))) (synCpw1 (synCvv))
      (synCsi (synCwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCpw1 (synCpw1 (synCvv))) (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gDffn2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0020 :=
    @gMpbi
      (synWfn (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0018 p0019
  have p0021 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCvv))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0009 p0020
  have p0022 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (synCwppdirecth2famfn))
  have p0025 :=
    @gFneq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCwppdirecth2famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecth1famfn))))
      p0024
  have p0026 :=
    @gMpbir
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecth1famfn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0023 p0025
  have p0027 :=
    @gDffn2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCwppdirecth2famfn)
  have p0028 :=
    @gMpbi
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWf (synCwppdirecth2famfn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0026 p0027
  have p0029 :=
    @gPm32i (synWfn (synCimage (synCen)) (synCvv))
      (synWf (synCwppdirecth2famfn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0001 p0028
  have p0030 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCimage (synCen)) (synCwppdirecth2famfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := (Nominal.classEqRefl (synCwppconcrete6codefn))
  have p0033 :=
    @gFneq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCwppconcrete6codefn) (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
      p0032
  have p0034 :=
    @gMpbir
      (synWfn (synCwppconcrete6codefn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0031 p0033
  have p0035 := @gWppcardt2fnf1ndv
  have p0036 := @gWppcardt4fnf1ndv
  have p0037 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn) p0036
  have p0038 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsi (synCwppcardt4fn)) p0037
  have p0039 :=
    @gPm32i (synWf1 (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf1 (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      p0035 p0038
  have p0040 :=
    @gF1co (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt4fn)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 := (Nominal.classEqRefl (synCwppcardt6fn))
  have p0043 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @gMpbir
      (synWf1 (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      (synWf1 (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      p0041 p0044
  have p0046 :=
    @gF1cnv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @gF1ofn (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @gF1of (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0064 := Nominal.mp p0047 p0063
  have p0065 :=
    @gFrn (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0066 := Nominal.mp p0064 p0065
  have p0067 := @gSsv (synCpw1 (synCpw1 (synCncs)))
  have p0068 := @gPw1ss (synCpw1 (synCpw1 (synCncs))) (synCvv)
  have p0069 := Nominal.mp p0067 p0068
  have p0070 := @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCncs)))) (synCpw1 (synCvv))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synCpw1 (synCpw1 (synCvv)))
  have p0073 := Nominal.mp p0071 p0072
  have p0074 :=
    @gPw1ss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCpw1 (synCpw1 (synCvv))))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @gPm32i
      (synWss (synCrn (synCcnv (synCwppcardt6fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWss (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0066 p0075
  have p0077 :=
    @gSstr (synCrn (synCcnv (synCwppcardt6fn)))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
  have p0078 := Nominal.mp p0076 p0077
  have p0079 :=
    @gN3pm32i
      (synWfn (synCwppconcrete6codefn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcnv (synCwppcardt6fn)) (synCrn (synCwppcardt6fn)))
      (synWss (synCrn (synCcnv (synCwppcardt6fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0034 p0049 p0078
  have p0080 :=
    @gFnco (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCrn (synCwppcardt6fn)) (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))
  have p0081 := Nominal.mp p0079 p0080
  have p0082 := (Nominal.classEqRefl (synCwppconcrete6fn))
  have p0083 :=
    @gFneq1i (synCrn (synCwppcardt6fn)) (synCwppconcrete6fn)
      (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))) p0082
  have p0084 :=
    @gMpbir (synWfn (synCwppconcrete6fn) (synCrn (synCwppcardt6fn)))
      (synWfn (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)))
        (synCrn (synCwppcardt6fn)))
      p0081 p0083
  have p0085 := @gFnfun (synCrn (synCwppcardt6fn)) (synCwppconcrete6fn)
  have p0086 := Nominal.mp p0084 p0085
  have p0090 := @gImageex (synCen) p0000
  have p0093 := @gImageex (synCwpplitphnordpointfn) p0002
  have p0094 := @gWppfamilyrep2fnexndv
  have p0095 :=
    @gCoex (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn) p0093 p0094
  have p0096 := @gWppdirecth1famfnexndv
  have p0097 := @gSiex (synCwppdirecth1famfn) p0096
  have p0098 := @gSiex (synCsi (synCwppdirecth1famfn)) p0097
  have p0099 :=
    @gCoex (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecth1famfn))) p0095 p0098
  have p0100 :=
    @gEqeltri (synCwppdirecth2famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecth1famfn))))
      (synCvv) p0024 p0099
  have p0101 := @gCoex (synCimage (synCen)) (synCwppdirecth2famfn) p0090 p0100
  have p0102 :=
    @gEqeltri (synCwppconcrete6codefn)
      (synCcom (synCimage (synCen)) (synCwppdirecth2famfn)) (synCvv) p0032 p0101
  have p0104 := @gWppcardt2fnexndv
  have p0105 := @gWppcardt4fnexndv
  have p0106 := @gSiex (synCwppcardt4fn) p0105
  have p0107 := @gSiex (synCsi (synCwppcardt4fn)) p0106
  have p0108 :=
    @gCoex (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))) p0104 p0107
  have p0109 :=
    @gEqeltri (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn)))) (synCvv) p0042
      p0108
  have p0110 := @gCnvex (synCwppcardt6fn) p0109
  have p0111 :=
    @gCoex (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)) p0102 p0110
  have p0112 :=
    @gEqeltri (synCwppconcrete6fn)
      (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))) (synCvv) p0082
      p0111
  have p0113 := @gElfuns (synCwppconcrete6fn) p0112
  have p0114 :=
    @gMpbir (.classMem (synCwppconcrete6fn) (synCfuns))
      (synWfun (synCwppconcrete6fn)) p0086 p0113
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

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6fnvalndv`. -/
@[expose]
noncomputable def gWppconcrete6fnvalndv (X : Class)
    (hyp_wppconcrete6fnvalndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
        (synChncard (synChnord (synCpw (synCpw X))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppconcrete6fn))
  have p0001 :=
    @gFveq1i (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
      (synCwppconcrete6fn)
      (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))) p0000
  have p0002 := @gWppcardt2fnf1ndv
  have p0003 := @gWppcardt4fnf1ndv
  have p0004 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn) p0003
  have p0005 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsi (synCwppcardt4fn)) p0004
  have p0006 :=
    @gPm32i (synWf1 (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf1 (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      p0002 p0005
  have p0007 :=
    @gF1co (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt4fn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (synCwppcardt6fn))
  have p0010 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gMpbir
      (synWf1 (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      (synWf1 (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      p0008 p0011
  have p0013 :=
    @gF1cnv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gF1ofn (synCrn (synCwppcardt6fn))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCcnv (synCwppcardt6fn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gNcelncsi X hyp_wppconcrete6fnvalndv_1
  have p0018 := @gWppcardt6fnvalsingndv (synCnc X)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @gWppcardt2fnmapndv
  have p0021 := @gWppcardt4fnmapndv
  have p0022 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsi (synCwppcardt4fn))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @gPm32i (synWf (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      p0020 p0025
  have p0027 :=
    @gFco (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt4fn)))
  have p0028 := Nominal.mp p0026 p0027
  have p0030 :=
    @gFeq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn)))) p0009
  have p0031 :=
    @gMpbir
      (synWf (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      (synWf (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      p0028 p0030
  have p0032 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0033 := Nominal.mp p0031 p0032
  have p0035 := @gSnelpw1 (synCnc X) (synCncs)
  have p0036 :=
    @gMpbir (.classMem (synCsn (synCnc X)) (synCpw1 (synCncs)))
      (.classMem (synCnc X) (synCncs)) p0017 p0035
  have p0037 := @gSnelpw1 (synCsn (synCnc X)) (synCpw1 (synCncs))
  have p0038 :=
    @gMpbir (.classMem (synCsn (synCsn (synCnc X))) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn (synCnc X)) (synCpw1 (synCncs))) p0036 p0037
  have p0039 :=
    @gSnelpw1 (synCsn (synCsn (synCnc X))) (synCpw1 (synCpw1 (synCncs)))
  have p0040 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCnc X))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classMem (synCsn (synCsn (synCnc X))) (synCpw1 (synCpw1 (synCncs)))) p0038
      p0039
  have p0041 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCnc X))))
      (synCpw1 (synCpw1 (synCpw1 (synCncs))))
  have p0042 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCnc X)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classMem (synCsn (synCsn (synCsn (synCnc X))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0040 p0041
  have p0043 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn (synCnc X)))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
  have p0044 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCnc X)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0042 p0043
  have p0045 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
  have p0046 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      p0044 p0045
  have p0047 :=
    @gPm32i
      (synWfn (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      p0033 p0046
  have p0048 :=
    @gFnfvelrn
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
      (synCwppcardt6fn)
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @gEqeltrri
      (synCfv (synCwppcardt6fn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
      (synCrn (synCwppcardt6fn)) p0019 p0049
  have p0051 :=
    @gPm32i (synWfn (synCcnv (synCwppcardt6fn)) (synCrn (synCwppcardt6fn)))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
        (synCrn (synCwppcardt6fn)))
      p0016 p0050
  have p0052 :=
    @gFvco2 (synCrn (synCwppcardt6fn))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
      (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn))
  have p0053 := Nominal.mp p0051 p0052
  have p0068 :=
    @gF1f1orn
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0069 := Nominal.mp p0012 p0068
  have p0083 :=
    @gPm32i
      (synWf1o (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCrn (synCwppcardt6fn)))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      p0069 p0046
  have p0084 :=
    @gF1ocnvfv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCrn (synCwppcardt6fn))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
      (synCwppcardt6fn)
  have p0085 := Nominal.mp p0083 p0084
  have p0086 := Nominal.mp p0019 p0085
  have p0087 :=
    @gFveq2i
      (synCfv (synCcnv (synCwppcardt6fn))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
      (synCwppconcrete6codefn) p0086
  have p0088 :=
    @gEqtri
      (synCfv (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synCfv (synCwppconcrete6codefn) (synCfv (synCcnv (synCwppcardt6fn))
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))))
      (synCfv (synCwppconcrete6codefn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      p0053 p0087
  have p0089 := @gWppconcrete6codefnvalndv X hyp_wppconcrete6fnvalndv_1
  have p0090 :=
    @gEqtri
      (synCfv (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synCfv (synCwppconcrete6codefn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      (synChncard (synChnord (synCpw (synCpw X)))) p0088 p0089
  have p0091 :=
    @gEqtri
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synCfv (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synChncard (synChnord (synCpw (synCpw X)))) p0001 p0090
  exact p0091

/-- Checked nominal proof certificate identified upstream as `g_letc2w6ndv`. -/
@[expose]
noncomputable def gLetc2w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc N))))
        (synWrex p (synCncs) (.classEq M (synCtc (synCtc (.cv p)))))) :=
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
      ((synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
          (.classEq M (synCtc (.cv q))))).fv :=
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
    q ∉ ((synWrex p (synCncs) (.classEq M (synCtc (synCtc (.cv p)))))).fv :=
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
      ((synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc N))))).fv :=
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
    @gN3simpa (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc N)))
  have p0001 := @gSimpl (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0002 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem M (synCncs))
      p0000 p0001
  have p0004 := @gSimpr (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0005 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem N (synCncs))
      p0000 p0004
  have p0006 := @gTccl N
  have p0007 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (.classMem N (synCncs)) (.classMem (synCtc N) (synCncs)) p0005 p0006
  have p0008 :=
    @gN3simpb (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc N)))
  have p0009 :=
    @gSimpr (.classMem M (synCncs)) (synWbr M (synClec) (synCtc (synCtc N)))
  have p0010 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (synWa (.classMem M (synCncs)) (synWbr M (synClec) (synCtc (synCtc N))))
      (synWbr M (synClec) (synCtc (synCtc N))) p0008 p0009
  have p0011 :=
    @gN3jca
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (.classMem M (synCncs)) (.classMem (synCtc N) (synCncs))
      (synWbr M (synClec) (synCtc (synCtc N))) p0002 p0007 p0010
  have p0012 := @gLetc M (synCtc N) q dv_cache_0001
  have p0013 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (synW3a (.classMem M (synCncs)) (.classMem (synCtc N) (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q)))) p0011 p0012
  have p0014 :=
    @gSimpl
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0015 :=
    @gSimpr
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (.classMem (.cv q) (synCncs))
  have p0016 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
      (.classMem (.cv q) (synCncs)) p0014 p0015
  have p0018 :=
    @gSimpl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (.classMem (.cv q) (synCncs))
  have p0019 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      p0014 p0018
  have p0023 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (.classMem N (synCncs)) p0019 p0005
  have p0030 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (synWbr M (synClec) (synCtc (synCtc N))) p0019 p0010
  have p0031 :=
    @gSimpr
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0032 :=
    @gBreq1d
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      M (synCtc (.cv q)) (synCtc (synCtc N)) (synClec) p0031
  have p0033 :=
    @gMpbid
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synWbr M (synClec) (synCtc (synCtc N)))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc N))) p0030 p0032
  have p0045 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (.classMem (synCtc N) (synCncs)) p0019 p0007
  have p0046 :=
    @gJca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) (.classMem (synCtc N) (synCncs)) p0016 p0045
  have p0047 := @gTlecg (.cv q) (synCtc N)
  have p0048 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synWa (.classMem (.cv q) (synCncs)) (.classMem (synCtc N) (synCncs)))
      (synWb (synWbr (.cv q) (synClec) (synCtc N))
        (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc N))))
      p0046 p0047
  have p0049 :=
    @gMpbird
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synWbr (.cv q) (synClec) (synCtc N))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc N))) p0033 p0048
  have p0050 :=
    @gN3jca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
      (synWbr (.cv q) (synClec) (synCtc N)) p0016 p0023 p0049
  have p0051 := @gLetc (.cv q) N p dv_cache_0002
  have p0052 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
        (synWbr (.cv q) (synClec) (synCtc N)))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (.cv p)))) p0050 p0051
  have p0053 :=
    @gSimpl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
          (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (.cv p)))
  have p0054 :=
    @gSimpl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (.classMem (.cv p) (synCncs))
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
            (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (.cv p))))
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
          (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      p0053 p0054
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
            (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (.cv p))))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (.classEq M (synCtc (.cv q))) p0055 p0031
  have p0058 :=
    @gSimpr
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
          (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (.cv p)))
  have p0059 := @gTceq (.cv q) (synCtc (.cv p))
  have p0060 :=
    @gA1i
      (.imp (.classEq (.cv q) (synCtc (.cv p)))
        (.classEq (synCtc (.cv q)) (synCtc (synCtc (.cv p)))))
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
            (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (.cv p))))
      p0059
  have p0061 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
            (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (.cv p))))
      (.classEq (.cv q) (synCtc (.cv p)))
      (.classEq (synCtc (.cv q)) (synCtc (synCtc (.cv p)))) p0058 p0060
  have p0062 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
            (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (.cv p))))
      M (synCtc (.cv q)) (synCtc (synCtc (.cv p))) p0057 p0061
  have p0063 :=
    @gEx
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
          (.classEq M (synCtc (.cv q)))) (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (.cv p))) (.classEq M (synCtc (synCtc (.cv p)))) p0062
  have p0064 :=
    @gReximdva
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (.classEq (.cv q) (synCtc (.cv p))) (.classEq M (synCtc (synCtc (.cv p)))) p
      (synCncs) dv_cache_0003 p0063
  have p0065 :=
    @gMpd
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
        (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (.cv p))))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (.cv p))))) p0052 p0064
  have p0066 :=
    @gEx
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc N)))) (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (.cv p))))) p0065
  have p0067 :=
    @gRexlimdva
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (.cv p))))) q (synCncs)
      dv_cache_0004 dv_cache_0005 p0066
  have p0068 :=
    @gMpd
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc N))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (.cv p))))) p0013 p0067
  exact p0068

/-- Checked nominal proof certificate identified upstream as `g_letc3w6ndv`. -/
@[expose]
noncomputable def gLetc3w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
        (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (.cv p))))))) :=
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
      ((synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))).fv :=
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
    q ∉ ((synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (.cv p))))))).fv :=
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
      ((synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))).fv :=
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
    @gN3simpa (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc N))))
  have p0001 := @gSimpl (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0002 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem M (synCncs))
      p0000 p0001
  have p0004 := @gSimpr (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0005 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem N (synCncs))
      p0000 p0004
  have p0006 := @gTccl N
  have p0007 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classMem N (synCncs)) (.classMem (synCtc N) (synCncs)) p0005 p0006
  have p0008 := @gTccl (synCtc N)
  have p0009 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classMem (synCtc N) (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs))
      p0007 p0008
  have p0010 :=
    @gN3simpb (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc N))))
  have p0011 :=
    @gSimpr (.classMem M (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc N))))
  have p0012 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synWa (.classMem M (synCncs)) (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc N)))) p0010 p0011
  have p0013 :=
    @gN3jca
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classMem M (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc N)))) p0002 p0009 p0012
  have p0014 := @gLetc M (synCtc (synCtc N)) q dv_cache_0001
  have p0015 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synW3a (.classMem M (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q)))) p0013 p0014
  have p0016 :=
    @gSimpl
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0017 :=
    @gSimpr
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classMem (.cv q) (synCncs))
  have p0018 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
        (.classMem (.cv q) (synCncs)))
      (.classMem (.cv q) (synCncs)) p0016 p0017
  have p0020 :=
    @gSimpl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classMem (.cv q) (synCncs))
  have p0021 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
        (.classMem (.cv q) (synCncs)))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      p0016 p0020
  have p0025 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classMem N (synCncs)) p0021 p0005
  have p0032 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc N)))) p0021 p0012
  have p0033 :=
    @gSimpr
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0034 :=
    @gBreq1d
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      M (synCtc (.cv q)) (synCtc (synCtc (synCtc N))) (synClec) p0033
  have p0035 :=
    @gMpbid
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc N))))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc N)))) p0032 p0034
  have p0049 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classMem (synCtc (synCtc N)) (synCncs)) p0021 p0009
  have p0050 :=
    @gJca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs)) p0018
      p0049
  have p0051 := @gTlecg (.cv q) (synCtc (synCtc N))
  have p0052 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (.classMem (.cv q) (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs)))
      (synWb (synWbr (.cv q) (synClec) (synCtc (synCtc N)))
        (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc N)))))
      p0050 p0051
  have p0053 :=
    @gMpbird
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr (.cv q) (synClec) (synCtc (synCtc N)))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc N)))) p0035 p0052
  have p0054 :=
    @gN3jca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
      (synWbr (.cv q) (synClec) (synCtc (synCtc N))) p0018 p0025 p0053
  have p0055 := @gLetc2w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0056 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
        (synWbr (.cv q) (synClec) (synCtc (synCtc N))))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (synCtc (.cv p))))) p0054 p0055
  have p0057 :=
    @gSimpl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (.cv p))))
  have p0058 :=
    @gSimpl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv p) (synCncs))
  have p0059 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs))) (.classEq (.cv q) (synCtc (synCtc (.cv p)))))
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      p0057 p0058
  have p0061 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs))) (.classEq (.cv q) (synCtc (synCtc (.cv p)))))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq M (synCtc (.cv q))) p0059 p0033
  have p0062 :=
    @gSimpr
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (.cv p))))
  have p0063 := @gTceq (.cv q) (synCtc (synCtc (.cv p)))
  have p0064 :=
    @gA1i
      (.imp (.classEq (.cv q) (synCtc (synCtc (.cv p))))
        (.classEq (synCtc (.cv q)) (synCtc (synCtc (synCtc (.cv p))))))
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs))) (.classEq (.cv q) (synCtc (synCtc (.cv p)))))
      p0063
  have p0065 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs))) (.classEq (.cv q) (synCtc (synCtc (.cv p)))))
      (.classEq (.cv q) (synCtc (synCtc (.cv p))))
      (.classEq (synCtc (.cv q)) (synCtc (synCtc (synCtc (.cv p))))) p0062 p0064
  have p0066 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs))) (.classEq (.cv q) (synCtc (synCtc (.cv p)))))
      M (synCtc (.cv q)) (synCtc (synCtc (synCtc (.cv p)))) p0061 p0065
  have p0067 :=
    @gEx
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (.cv p))))
      (.classEq M (synCtc (synCtc (synCtc (.cv p))))) p0066
  have p0068 :=
    @gReximdva
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq (.cv q) (synCtc (synCtc (.cv p))))
      (.classEq M (synCtc (synCtc (synCtc (.cv p))))) p (synCncs) dv_cache_0004 p0067
  have p0069 :=
    @gMpd
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (synCtc (.cv p)))))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (.cv p)))))) p0056
      p0068
  have p0070 :=
    @gEx
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (.cv p)))))) p0069
  have p0071 :=
    @gRexlimdva
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (.cv p)))))) q
      (synCncs) dv_cache_0005 dv_cache_0006 p0070
  have p0072 :=
    @gMpd
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc N)))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (.cv p)))))) p0015
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

/-- Checked nominal proof certificate identified upstream as `g_letc4w6ndv`. -/
@[expose]
noncomputable def gLetc4w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
        (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))))) :=
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
      ((synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))).fv :=
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
      ((synWrex p (synCncs)
          (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))))).fv :=
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
      ((synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))).fv :=
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
    @gN3simpa (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
  have p0001 := @gSimpl (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0002 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem M (synCncs))
      p0000 p0001
  have p0004 := @gSimpr (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0005 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem N (synCncs))
      p0000 p0004
  have p0006 := @gTccl N
  have p0007 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem N (synCncs)) (.classMem (synCtc N) (synCncs)) p0005 p0006
  have p0008 := @gTccl (synCtc N)
  have p0009 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem (synCtc N) (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs))
      p0007 p0008
  have p0010 := @gTccl (synCtc (synCtc N))
  have p0011 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem (synCtc (synCtc N)) (synCncs))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs)) p0009 p0010
  have p0012 :=
    @gN3simpb (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
  have p0013 :=
    @gSimpr (.classMem M (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
  have p0014 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWa (.classMem M (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))) p0012 p0013
  have p0015 :=
    @gN3jca
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem M (synCncs)) (.classMem (synCtc (synCtc (synCtc N))) (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))) p0002 p0011 p0014
  have p0016 := @gLetc M (synCtc (synCtc (synCtc N))) q dv_cache_0001
  have p0017 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synW3a (.classMem M (synCncs)) (.classMem (synCtc (synCtc (synCtc N))) (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q)))) p0015 p0016
  have p0018 :=
    @gSimpl
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0019 :=
    @gSimpr
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem (.cv q) (synCncs))
  have p0020 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
        (.classMem (.cv q) (synCncs)))
      (.classMem (.cv q) (synCncs)) p0018 p0019
  have p0022 :=
    @gSimpl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem (.cv q) (synCncs))
  have p0023 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
        (.classMem (.cv q) (synCncs)))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      p0018 p0022
  have p0027 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem N (synCncs)) p0023 p0005
  have p0034 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))) p0023 p0014
  have p0035 :=
    @gSimpr
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0036 :=
    @gBreq1d
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      M (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc N)))) (synClec) p0035
  have p0037 :=
    @gMpbid
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
      p0034 p0036
  have p0053 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs)) p0023 p0011
  have p0054 :=
    @gJca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs)) p0020 p0053
  have p0055 := @gTlecg (.cv q) (synCtc (synCtc (synCtc N)))
  have p0056 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (.classMem (.cv q) (synCncs))
        (.classMem (synCtc (synCtc (synCtc N))) (synCncs)))
      (synWb (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc N))))
        (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      p0054 p0055
  have p0057 :=
    @gMpbird
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc N))))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
      p0037 p0056
  have p0058 :=
    @gN3jca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc N)))) p0020 p0027 p0057
  have p0059 := @gLetc3w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0060 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
        (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc N)))))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p))))))
      p0058 p0059
  have p0061 :=
    @gSimpl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p)))))
  have p0062 :=
    @gSimpl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv p) (synCncs))
  have p0063 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p))))))
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      p0061 p0062
  have p0065 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p))))))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq M (synCtc (.cv q))) p0063 p0035
  have p0066 :=
    @gSimpr
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p)))))
  have p0067 := @gTceq (.cv q) (synCtc (synCtc (synCtc (.cv p))))
  have p0068 :=
    @gA1i
      (.imp (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p)))))
        (.classEq (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p))))))
      p0067
  have p0069 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p))))))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p)))))
      (.classEq (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (.cv p)))))) p0066
      p0068
  have p0070 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p))))))
      M (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (.cv p))))) p0065 p0069
  have p0071 :=
    @gEx
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p)))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))) p0070
  have p0072 :=
    @gReximdva
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p)))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))) p (synCncs)
      dv_cache_0004 p0071
  have p0073 :=
    @gMpd
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (synCtc (synCtc (.cv p))))))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      p0060 p0072
  have p0074 :=
    @gEx
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      p0073
  have p0075 :=
    @gRexlimdva
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      q (synCncs) dv_cache_0005 dv_cache_0006 p0074
  have p0076 :=
    @gMpd
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs) (.classEq M (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      p0017 p0075
  exact p0076

/-- Checked nominal proof certificate identified upstream as `g_letc5w6ndv`. -/
@[expose]
noncomputable def gLetc5w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
        (synWrex p (synCncs)
          (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))) :=
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
      ((synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))).fv :=
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
      ((synWrex p (synCncs)
          (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))).fv :=
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
      ((synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))).fv :=
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
    @gN3simpa (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
  have p0001 := @gSimpl (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0002 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem M (synCncs))
      p0000 p0001
  have p0004 := @gSimpr (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0005 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem N (synCncs))
      p0000 p0004
  have p0006 := @gTccl N
  have p0007 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem N (synCncs)) (.classMem (synCtc N) (synCncs)) p0005 p0006
  have p0008 := @gTccl (synCtc N)
  have p0009 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem (synCtc N) (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs))
      p0007 p0008
  have p0010 := @gTccl (synCtc (synCtc N))
  have p0011 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem (synCtc (synCtc N)) (synCncs))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs)) p0009 p0010
  have p0012 := @gTccl (synCtc (synCtc (synCtc N)))
  have p0013 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs)) p0011 p0012
  have p0014 :=
    @gN3simpb (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
  have p0015 :=
    @gSimpr (.classMem M (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
  have p0016 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWa (.classMem M (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))) p0014
      p0015
  have p0017 :=
    @gN3jca
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem M (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))) p0002
      p0013 p0016
  have p0018 := @gLetc M (synCtc (synCtc (synCtc (synCtc N)))) q dv_cache_0001
  have p0019 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synW3a (.classMem M (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q)))) p0017 p0018
  have p0020 :=
    @gSimpl
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0021 :=
    @gSimpr
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem (.cv q) (synCncs))
  have p0022 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
        (.classMem (.cv q) (synCncs)))
      (.classMem (.cv q) (synCncs)) p0020 p0021
  have p0024 :=
    @gSimpl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem (.cv q) (synCncs))
  have p0025 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
        (.classMem (.cv q) (synCncs)))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0020 p0024
  have p0029 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem N (synCncs)) p0025 p0005
  have p0036 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))) p0025
      p0016
  have p0037 :=
    @gSimpr
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0038 :=
    @gBreq1d
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      M (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synClec)
      p0037
  have p0039 :=
    @gMpbid
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      p0036 p0038
  have p0057 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs)) p0025 p0013
  have p0058 :=
    @gJca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs)) p0022 p0057
  have p0059 := @gTlecg (.cv q) (synCtc (synCtc (synCtc (synCtc N))))
  have p0060 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (.classMem (.cv q) (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs)))
      (synWb (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
        (synWbr (synCtc (.cv q)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0058 p0059
  have p0061 :=
    @gMpbird
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc N)))))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      p0039 p0060
  have p0062 :=
    @gN3jca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc N))))) p0022 p0029
      p0061
  have p0063 := @gLetc4w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0064 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
        (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc N))))))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      p0062 p0063
  have p0065 :=
    @gSimpl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p))))))
  have p0066 :=
    @gSimpl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv p) (synCncs))
  have p0067 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      p0065 p0066
  have p0069 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq M (synCtc (.cv q))) p0067 p0037
  have p0070 :=
    @gSimpr
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p))))))
  have p0071 := @gTceq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))
  have p0072 :=
    @gA1i
      (.imp (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p))))))
        (.classEq (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      p0071
  have p0073 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p))))))
      (.classEq (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      p0070 p0072
  have p0074 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      M (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))) p0069
      p0073
  have p0075 :=
    @gEx
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p))))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))) p0074
  have p0076 :=
    @gReximdva
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p))))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))) p (synCncs)
      dv_cache_0004 p0075
  have p0077 :=
    @gMpd
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs) (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      p0064 p0076
  have p0078 :=
    @gEx
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      p0077
  have p0079 :=
    @gRexlimdva
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      q (synCncs) dv_cache_0005 dv_cache_0006 p0078
  have p0080 :=
    @gMpd
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
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

/-- Checked nominal proof certificate identified upstream as `g_letc6w6ndv`. -/
@[expose]
noncomputable def gLetc6w6ndv (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv)
    (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (synWrex p (synCncs) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))) :=
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
      ((synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))).fv :=
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
      ((synWrex p (synCncs) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))).fv :=
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
      ((synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))).fv :=
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
    @gN3simpa (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
  have p0001 := @gSimpl (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0002 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem M (synCncs))
      p0000 p0001
  have p0004 := @gSimpr (.classMem M (synCncs)) (.classMem N (synCncs))
  have p0005 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWa (.classMem M (synCncs)) (.classMem N (synCncs))) (.classMem N (synCncs))
      p0000 p0004
  have p0006 := @gTccl N
  have p0007 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem N (synCncs)) (.classMem (synCtc N) (synCncs)) p0005 p0006
  have p0008 := @gTccl (synCtc N)
  have p0009 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (synCtc N) (synCncs)) (.classMem (synCtc (synCtc N)) (synCncs))
      p0007 p0008
  have p0010 := @gTccl (synCtc (synCtc N))
  have p0011 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (synCtc (synCtc N)) (synCncs))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs)) p0009 p0010
  have p0012 := @gTccl (synCtc (synCtc (synCtc N)))
  have p0013 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (synCtc (synCtc (synCtc N))) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs)) p0011 p0012
  have p0014 := @gTccl (synCtc (synCtc (synCtc (synCtc N))))
  have p0015 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (synCtc (synCtc (synCtc (synCtc N)))) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synCncs)) p0013
      p0014
  have p0016 :=
    @gN3simpb (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
  have p0017 :=
    @gSimpr (.classMem M (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
  have p0018 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWa (.classMem M (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0016 p0017
  have p0019 :=
    @gN3jca
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem M (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synCncs))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0002 p0015 p0018
  have p0020 :=
    @gLetc M (synCtc (synCtc (synCtc (synCtc (synCtc N))))) q dv_cache_0001
  have p0021 :=
    @gSyl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synW3a (.classMem M (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synCncs))
        (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q)))) p0019 p0020
  have p0022 :=
    @gSimpl
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0023 :=
    @gSimpr
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (.cv q) (synCncs))
  have p0024 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv q) (synCncs)))
      (.classMem (.cv q) (synCncs)) p0022 p0023
  have p0026 :=
    @gSimpl
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (.cv q) (synCncs))
  have p0027 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv q) (synCncs)))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      p0022 p0026
  have p0031 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem N (synCncs)) p0027 p0005
  have p0038 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0027 p0018
  have p0039 :=
    @gSimpr
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
  have p0040 :=
    @gBreq1d
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      M (synCtc (.cv q)) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      (synClec) p0039
  have p0041 :=
    @gMpbid
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr M (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWbr (synCtc (.cv q)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0038 p0040
  have p0061 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synCncs)) p0027
      p0015
  have p0062 :=
    @gJca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synCncs)) p0024
      p0061
  have p0063 := @gTlecg (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))
  have p0064 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWa (.classMem (.cv q) (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc N))))) (synCncs)))
      (synWb (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
        (synWbr (synCtc (.cv q)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      p0062 p0063
  have p0065 :=
    @gMpbird
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      (synWbr (synCtc (.cv q)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      p0041 p0064
  have p0066 :=
    @gN3jca
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N))))))
      p0024 p0031 p0065
  have p0067 := @gLetc5w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0068 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synW3a (.classMem (.cv q) (synCncs)) (.classMem N (synCncs))
        (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))
      (synWrex p (synCncs)
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      p0066 p0067
  have p0069 :=
    @gSimpl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
  have p0070 :=
    @gSimpl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classMem (.cv p) (synCncs))
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec)
                  (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      p0069 p0070
  have p0073 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec)
                  (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq M (synCtc (.cv q))) p0071 p0039
  have p0074 :=
    @gSimpr
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
  have p0075 := @gTceq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))
  have p0076 :=
    @gA1i
      (.imp (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
        (.classEq (synCtc (.cv q))
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec)
                  (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      p0075
  have p0077 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec)
                  (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (.classEq (synCtc (.cv q))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      p0074 p0076
  have p0078 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
                (synWbr M (synClec)
                  (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
              (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
          (.classMem (.cv p) (synCncs)))
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      M (synCtc (.cv q))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))) p0073 p0077
  have p0079 :=
    @gEx
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
        (.classMem (.cv p) (synCncs)))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      p0078
  have p0080 :=
    @gReximdva
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))) p
      (synCncs) dv_cache_0004 p0079
  have p0081 :=
    @gMpd
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv q) (synCncs))) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs)
        (.classEq (.cv q) (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      p0068 p0080
  have p0082 :=
    @gEx
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      p0081
  have p0083 :=
    @gRexlimdva
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classEq M (synCtc (.cv q)))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      q (synCncs) dv_cache_0005 dv_cache_0006 p0082
  have p0084 :=
    @gMpd
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWrex q (synCncs) (.classEq M (synCtc (.cv q))))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      p0021 p0083
  exact p0084

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6dmcovndv`. -/
@[expose]
noncomputable def gWppconcrete6dmcovndv (D : Class) (p : Var) (_dv_D_p : p ∉ D.fv)
    (hyp_wppconcrete6dmcovndv_1 : Nominal.NPrf (.classMem D (synCncs))) :
    Nominal.NPrf
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))) :=
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
  have dv_cache_0003 : q ∉ ((Wff.classMem (.cv p) (synCrn (synCwppcardt6fn)))).fv :=
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
      ((synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))).fv :=
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
    @gSimpl (.classMem (.cv p) (synChwcards (synCvv)))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
  have p0001 := @gHwcardssnc (synCvv)
  have p0002 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv p) p0001
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv p) (synCncs)) p0000
      p0002
  have p0004 :=
    @gA1i (.classMem D (synCncs))
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      hyp_wppconcrete6dmcovndv_1
  have p0005 :=
    @gSimpr (.classMem (.cv p) (synChwcards (synCvv)))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
  have p0006 :=
    @gN3jca
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synCncs)) (.classMem D (synCncs))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      p0003 p0004 p0005
  have p0007 := @gLetc6w6ndv (.cv p) D q dv_cache_0001 dv_cache_0002
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synW3a (.classMem (.cv p) (synCncs)) (.classMem D (synCncs))
        (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWrex q (synCncs) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      p0006 p0007
  have p0009 := @gWppcardt6fnmapndv
  have p0010 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gA1i
      (synWfn (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      p0011
  have p0013 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq (.cv p) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q))))))))
  have p0014 :=
    @gSimpr
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv q) (synCncs))
  have p0015 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
        (.classMem (.cv q) (synCncs)))
      (.classMem (.cv q) (synCncs)) p0013 p0014
  have p0016 := @gSnelpw1 (.cv q) (synCncs)
  have p0017 :=
    @gBiimpri (.classMem (synCsn (.cv q)) (synCpw1 (synCncs)))
      (.classMem (.cv q) (synCncs)) p0016
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (.cv q) (synCncs)) (.classMem (synCsn (.cv q)) (synCpw1 (synCncs)))
      p0015 p0017
  have p0019 := @gSnelpw1 (synCsn (.cv q)) (synCpw1 (synCncs))
  have p0020 :=
    @gBiimpri (.classMem (synCsn (synCsn (.cv q))) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn (.cv q)) (synCpw1 (synCncs))) p0019
  have p0021 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (synCsn (.cv q)) (synCpw1 (synCncs)))
      (.classMem (synCsn (synCsn (.cv q))) (synCpw1 (synCpw1 (synCncs)))) p0018 p0020
  have p0022 := @gSnelpw1 (synCsn (synCsn (.cv q))) (synCpw1 (synCpw1 (synCncs)))
  have p0023 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classMem (synCsn (synCsn (.cv q))) (synCpw1 (synCpw1 (synCncs)))) p0022
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (synCsn (synCsn (.cv q))) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn (synCsn (synCsn (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0021 p0023
  have p0025 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (.cv q))))
      (synCpw1 (synCpw1 (synCpw1 (synCncs))))
  have p0026 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv q)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classMem (synCsn (synCsn (synCsn (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0025
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (synCsn (synCsn (synCsn (.cv q))))
        (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv q)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0024 p0026
  have p0028 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn (.cv q)))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
  have p0029 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv q)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0028
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv q)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      p0027 p0029
  have p0031 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
  have p0032 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      p0031
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      p0030 p0032
  have p0034 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (synWfn (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
      p0012 p0033
  have p0035 :=
    @gFnfvelrn
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q)))))))
      (synCwppcardt6fn)
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (synWa (synWfn (synCwppcardt6fn)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))))
        (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))))
      (.classMem (synCfv (synCwppcardt6fn)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))))
        (synCrn (synCwppcardt6fn)))
      p0034 p0035
  have p0037 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq (.cv p) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q))))))))
  have p0041 := @gWppcardt6fnvalsingndv (.cv q)
  have p0042 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (.cv q) (synCncs))
      (.classEq (synCfv (synCwppcardt6fn)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q))))))))
      p0015 p0041
  have p0043 :=
    @gEqcomd
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (synCfv (synCwppcardt6fn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q))))))) p0042
  have p0044 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.cv p) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))
      (synCfv (synCwppcardt6fn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))))
      p0037 p0043
  have p0045 :=
    @gEleq1d
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.cv p)
      (synCfv (synCwppcardt6fn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))))
      (synCrn (synCwppcardt6fn)) p0044
  have p0046 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv)))
            (synWbr (.cv p) (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (.classMem (.cv q) (synCncs))) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (.cv p) (synCrn (synCwppcardt6fn)))
      (.classMem (synCfv (synCwppcardt6fn)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv q))))))))
        (synCrn (synCwppcardt6fn)))
      p0036 p0045
  have p0047 :=
    @gEx
      (synWa (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
        (.classMem (.cv q) (synCncs)))
      (.classEq (.cv p) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q))))))))
      (.classMem (.cv p) (synCrn (synCwppcardt6fn))) p0046
  have p0048 :=
    @gRexlimdva
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classEq (.cv p) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q))))))))
      (.classMem (.cv p) (synCrn (synCwppcardt6fn))) q (synCncs) dv_cache_0003
      dv_cache_0004 p0047
  have p0049 :=
    @gMpd
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWrex q (synCncs) (.classEq (.cv p)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv q)))))))))
      (.classMem (.cv p) (synCrn (synCwppcardt6fn))) p0008 p0048
  have p0050 :=
    @gEx (.classMem (.cv p) (synChwcards (synCvv)))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (.classMem (.cv p) (synCrn (synCwppcardt6fn))) p0049
  have p0051 := @gWppconcrete6fndmndv
  have p0052 :=
    @gEleq2i (synCdm (synCwppconcrete6fn)) (synCrn (synCwppcardt6fn)) (.cv p) p0051
  have p0053 :=
    @gA1i
      (synWb (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
        (.classMem (.cv p) (synCrn (synCwppcardt6fn))))
      (.classMem (.cv p) (synChwcards (synCvv))) p0052
  have p0054 :=
    @gSylibrd (.classMem (.cv p) (synChwcards (synCvv)))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (.classMem (.cv p) (synCrn (synCwppcardt6fn)))
      (.classMem (.cv p) (synCdm (synCwppconcrete6fn))) p0050 p0053
  have p0055 :=
    @gRgen
      (.imp (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))
      p (synChwcards (synCvv)) p0054
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

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6dmpaircovndv`. -/
@[expose]
noncomputable def gWppconcrete6dmpaircovndv (D : Class) (p : Var) (_dv_D_p : p ∉ D.fv)
    (hyp_wppconcrete6dmpaircovndv_1 : Nominal.NPrf (.classMem D (synCncs)))
    (hyp_wppconcrete6dmpaircovndv_2 : Nominal.NPrf
        (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))) :
    Nominal.NPrf
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
            (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn)))))) :=
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
  have dv_cache_0003 : q ∉ ((synChwcards (synCvv))).fv :=
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
      ((Wff.imp (synWbr (.cv p) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))).fv :=
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
  have dv_cache_0005 : q ∉ ((synCtc (.cv p))).fv :=
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
      ((Wff.imp (synWbr (synCtc (.cv p)) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))).fv :=
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
    @gSimpr (.classMem (.cv p) (synChwcards (synCvv)))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
  have p0001 :=
    @gSimpl (.classMem (.cv p) (synChwcards (synCvv)))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
  have p0002 := @gWppconcrete6dmcovndv D q dv_cache_0001 hyp_wppconcrete6dmpaircovndv_1
  have p0003 := @gId (.classEq (.cv q) (.cv p))
  have p0004 :=
    @gBreq1d (.classEq (.cv q) (.cv p)) (.cv q) (.cv p)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) (synClec) p0003
  have p0006 :=
    @gEleq1d (.classEq (.cv q) (.cv p)) (.cv q) (.cv p) (synCdm (synCwppconcrete6fn))
      p0003
  have p0007 :=
    @gImbi12d (.classEq (.cv q) (.cv p))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (.classMem (.cv q) (synCdm (synCwppconcrete6fn)))
      (.classMem (.cv p) (synCdm (synCwppconcrete6fn))) p0004 p0006
  have p0008 :=
    @gRspcv
      (.imp (synWbr (.cv q) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (.cv q) (synCdm (synCwppconcrete6fn))))
      (.imp (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))
      q (.cv p) (synChwcards (synCvv)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0007
  have p0009 :=
    @gCom12 (.classMem (.cv p) (synChwcards (synCvv)))
      (synWral q (synChwcards (synCvv)) (.imp (synWbr (.cv q) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (.classMem (.cv q) (synCdm (synCwppconcrete6fn)))))
      (.imp (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))
      p0008
  have p0010 := Nominal.mp p0002 p0009
  have p0011 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synChwcards (synCvv)))
      (.imp (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))
      p0001 p0010
  have p0012 :=
    @gMpd
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (.classMem (.cv p) (synCdm (synCwppconcrete6fn))) p0000 p0011
  have p0015 := @gHwcardssnc (synCvv)
  have p0016 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv p) p0015
  have p0017 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv p) (synCncs)) p0001
      p0016
  have p0018 := @gTccl D
  have p0019 := Nominal.mp hyp_wppconcrete6dmpaircovndv_1 p0018
  have p0020 := @gTccl (synCtc D)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @gTccl (synCtc (synCtc D))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @gTccl (synCtc (synCtc (synCtc D)))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @gTccl (synCtc (synCtc (synCtc (synCtc D))))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @gTccl (synCtc (synCtc (synCtc (synCtc (synCtc D)))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @gA1i
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) (synCncs))
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      p0029
  have p0031 :=
    @gJca
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) (synCncs))
      p0017 p0030
  have p0032 :=
    @gTlecg (.cv p) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))
  have p0033 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWa (.classMem (.cv p) (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) (synCncs)))
      (synWb (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (synWbr (synCtc (.cv p)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))))
      p0031 p0032
  have p0034 :=
    @gMpbid
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (synWbr (synCtc (.cv p)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      p0000 p0033
  have p0035 :=
    @gA1i
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      hyp_wppconcrete6dmpaircovndv_2
  have p0036 :=
    @gJca
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWbr (synCtc (.cv p)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      p0034 p0035
  have p0041 := @gTccl (.cv p)
  have p0042 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synCncs)) (.classMem (synCtc (.cv p)) (synCncs)) p0017 p0041
  have p0055 := @gTccl (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))
  have p0056 := Nominal.mp p0029 p0055
  have p0057 :=
    @gA1i
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (synCncs))
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      p0056
  have p0071 :=
    @gN3jca
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (synCtc (.cv p)) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) (synCncs))
      p0042 p0057 p0030
  have p0072 :=
    @gLectr (synCtc (.cv p))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))
  have p0073 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synW3a (.classMem (synCtc (.cv p)) (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (synCncs)) (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))
          (synCncs)))
      (.imp (synWa (synWbr (synCtc (.cv p)) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
          (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
            (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
        (synWbr (synCtc (.cv p)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      p0071 p0072
  have p0074 :=
    @gMpd
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWa (synWbr (synCtc (.cv p)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
        (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWbr (synCtc (.cv p)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      p0036 p0073
  have p0076 := @gHwcardstcclndv (.cv p)
  have p0077 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synChwcards (synCvv)))
      (.classMem (synCtc (.cv p)) (synChwcards (synCvv))) p0001 p0076
  have p0079 := @gId (.classEq (.cv q) (synCtc (.cv p)))
  have p0080 :=
    @gBreq1d (.classEq (.cv q) (synCtc (.cv p))) (.cv q) (synCtc (.cv p))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))) (synClec) p0079
  have p0082 :=
    @gEleq1d (.classEq (.cv q) (synCtc (.cv p))) (.cv q) (synCtc (.cv p))
      (synCdm (synCwppconcrete6fn)) p0079
  have p0083 :=
    @gImbi12d (.classEq (.cv q) (synCtc (.cv p)))
      (synWbr (.cv q) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (synWbr (synCtc (.cv p)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (.classMem (.cv q) (synCdm (synCwppconcrete6fn)))
      (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))) p0080 p0082
  have p0084 :=
    @gRspcv
      (.imp (synWbr (.cv q) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (.cv q) (synCdm (synCwppconcrete6fn))))
      (.imp (synWbr (synCtc (.cv p)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))
      q (synCtc (.cv p)) (synChwcards (synCvv)) dv_cache_0005 dv_cache_0003
      dv_cache_0006 p0083
  have p0085 :=
    @gCom12 (.classMem (synCtc (.cv p)) (synChwcards (synCvv)))
      (synWral q (synChwcards (synCvv)) (.imp (synWbr (.cv q) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
          (.classMem (.cv q) (synCdm (synCwppconcrete6fn)))))
      (.imp (synWbr (synCtc (.cv p)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))
      p0084
  have p0086 := Nominal.mp p0002 p0085
  have p0087 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (synCtc (.cv p)) (synChwcards (synCvv)))
      (.imp (synWbr (synCtc (.cv p)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))
      p0077 p0086
  have p0088 :=
    @gMpd
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (synWbr (synCtc (.cv p)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))) p0074 p0087
  have p0089 :=
    @gJca
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D))))))))
      (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
      (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))) p0012 p0088
  have p0090 :=
    @gEx (.classMem (.cv p) (synChwcards (synCvv)))
      (synWbr (.cv p) (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
      (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
        (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))
      p0089
  have p0091 :=
    @gRgen
      (.imp (synWbr (.cv p) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc D)))))))
        (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
          (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn)))))
      p (synChwcards (synCvv)) p0090
  exact p0091

/-- Checked nominal proof certificate identified upstream as `g_hncardnc1ndv`. -/
@[expose]
noncomputable def gHncardnc1ndv :
    Nominal.NPrf (.classMem (synChncard (synC1c)) (synCncs)) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gHncardnc (synC1c)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6hncard1dmcovndv`. -/
@[expose]
noncomputable def gWppconcrete6hncard1dmcovndv (p : Var) :
    Nominal.NPrf
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))) :=
  by
  have dv_cache_0001 : p ∉ ((synChncard (synC1c))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 := @gN1cex
  have p0001 := @gHncardnc (synC1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gWppconcrete6dmcovndv (synChncard (synC1c)) p dv_cache_0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as
`g_wppconcrete6hncard1dmpaircovndv`.
-/
@[expose]
noncomputable def gWppconcrete6hncard1dmpaircovndv (p : Var)
    (hyp_wppconcrete6hncard1dmpaircovndv_1 : Nominal.NPrf (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))) :
    Nominal.NPrf
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
            (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn)))))) :=
  by
  have dv_cache_0001 : p ∉ ((synChncard (synC1c))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 := @gN1cex
  have p0001 := @gHncardnc (synC1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gWppconcrete6dmpaircovndv (synChncard (synC1c)) p dv_cache_0001 p0002
      hyp_wppconcrete6hncard1dmpaircovndv_1
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hncardtcshiftcondndv`. -/
@[expose]
noncomputable def gHncardtcshiftcondndv (A : Class)
    (hyp_hncardtcshiftcondndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_hncardtcshiftcondndv_2 : Nominal.NPrf
        (synWbr (synCpw1 (synChnord A)) (synCen) (synChnord (synCpw1 A)))) :
    Nominal.NPrf (.classEq (synCtc (synChncard A)) (synChncard (synCpw1 A))) :=
  by
  have p0000 := @gHncardtc A hyp_hncardtcshiftcondndv_1
  have p0001 := @gHnordex A hyp_hncardtcshiftcondndv_1
  have p0002 := @gPw1ex (synChnord A) p0001
  have p0003 := @gEqnc (synCpw1 (synChnord A)) (synChnord (synCpw1 A)) p0002
  have p0004 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synChnord A))) (synCnc (synChnord (synCpw1 A))))
      (synWbr (synCpw1 (synChnord A)) (synCen) (synChnord (synCpw1 A)))
      hyp_hncardtcshiftcondndv_2 p0003
  have p0005 :=
    @gEqtri (synCtc (synChncard A)) (synCnc (synCpw1 (synChnord A)))
      (synCnc (synChnord (synCpw1 A))) p0000 p0004
  have p0006 := (Nominal.classEqRefl (synChncard (synCpw1 A)))
  have p0007 :=
    @gEqtr4i (synCtc (synChncard A)) (synCnc (synChnord (synCpw1 A)))
      (synChncard (synCpw1 A)) p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnsicodeliftfnexndv`. -/
@[expose]
noncomputable def gHnsicodeliftfnexndv :
    Nominal.NPrf (.classMem (synChnsicodeliftfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnsicodeliftfn))
  have p0001 := @gLnpwsirelfnex
  have p0002 := @gLnpwpw1secondfnex
  have p0003 := @gTxpex (synClnpwsirelfn) (synClnpwpw1secondfn) p0001 p0002
  have p0004 :=
    @gEqeltri (synChnsicodeliftfn) (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn))
      (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnsicodeliftfnfnndv`. -/
@[expose]
noncomputable def gHnsicodeliftfnfnndv :
    Nominal.NPrf (synWfn (synChnsicodeliftfn) (synCvv)) :=
  by
  have p0000 := @gLnpwsirelfnfn
  have p0001 := @gLnpwpw1secondfnfn
  have p0002 :=
    @gPm32i (synWfn (synClnpwsirelfn) (synCvv))
      (synWfn (synClnpwpw1secondfn) (synCvv)) p0000 p0001
  have p0003 := @gFntxp (synCvv) (synCvv) (synClnpwsirelfn) (synClnpwpw1secondfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gInidm (synCvv)
  have p0006 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn)) p0005
  have p0007 :=
    @gMpbi
      (synWfn (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn)) (synCvv)) p0004 p0006
  have p0008 := (Nominal.classEqRefl (synChnsicodeliftfn))
  have p0009 :=
    @gFneq1i (synCvv) (synChnsicodeliftfn)
      (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn)) p0008
  have p0010 :=
    @gMpbir (synWfn (synChnsicodeliftfn) (synCvv))
      (synWfn (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn)) (synCvv)) p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_sisuppdndv`. -/
@[expose]
noncomputable def gSisuppdndv (ph : Wff) (D : Class) (R : Class)
    (hyp_sisuppdndv_1 : Nominal.NPrf (.imp ph (synWss R (synCxp D D)))) :
    Nominal.NPrf (.imp ph (synWss (synCsi R) (synCxp (synCpw1 D) (synCpw1 D)))) :=
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
      ((Wff.classMem (synCop (.cv x) (.cv y)) (synCxp (synCpw1 D) (synCpw1 D)))).fv :=
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
      ((Wff.classMem (synCop (.cv x) (.cv y)) (synCxp (synCpw1 D) (synCpw1 D)))).fv :=
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
  have dv_cache_0012 : x ∉ ((synCsi R)).fv :=
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
  have dv_cache_0013 : y ∉ ((synCsi R)).fv :=
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
  have dv_cache_0014 : x ∉ ((synCxp (synCpw1 D) (synCpw1 D))).fv :=
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
  have dv_cache_0015 : y ∉ ((synCxp (synCpw1 D) (synCpw1 D))).fv :=
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
  have p0000 := (Nominal.biimpRefl (synWbr (.cv x) (synCsi R) (.cv y)))
  have p0001 :=
    @gBiimpri (synWbr (.cv x) (synCsi R) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCsi R)) p0000
  have p0002 :=
    @gBrsi z w (.cv x) (.cv y) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @gA1i
      (synWb (synWbr (.cv x) (synCsi R) (.cv y)) (synWex z (synWex w
            (synW3a (.classEq (.cv x) (synCsn (.cv z)))
              (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) R (.cv w))))))
      (.classMem (synCop (.cv x) (.cv y)) (synCsi R)) p0002
  have p0004 :=
    @gMpbid (.classMem (synCop (.cv x) (.cv y)) (synCsi R))
      (synWbr (.cv x) (synCsi R) (.cv y))
      (synWex z (synWex w (synW3a (.classEq (.cv x) (synCsn (.cv z)))
            (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) R (.cv w)))))
      p0001 p0003
  have p0005 :=
    @gA1i
      (.imp (.classMem (synCop (.cv x) (.cv y)) (synCsi R)) (synWex z (synWex w
            (synW3a (.classEq (.cv x) (synCsn (.cv z)))
              (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) R (.cv w))))))
      ph p0004
  have p0006 :=
    @gSimp3 (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
      (synWbr (.cv z) R (.cv w))
  have p0007 := (Nominal.biimpRefl (synWbr (.cv z) R (.cv w)))
  have p0008 :=
    @gA1i (synWb (synWbr (.cv z) R (.cv w)) (.classMem (synCop (.cv z) (.cv w)) R))
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      p0007
  have p0009 :=
    @gMpbid
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (synWbr (.cv z) R (.cv w)) (.classMem (synCop (.cv z) (.cv w)) R) p0006 p0008
  have p0010 :=
    @gA1i
      (.imp (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
          (synWbr (.cv z) R (.cv w))) (.classMem (synCop (.cv z) (.cv w)) R))
      ph p0009
  have p0011 := @gSseld ph R (synCxp D D) (synCop (.cv z) (.cv w)) hyp_sisuppdndv_1
  have p0012 :=
    @gSyld ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (synCop (.cv z) (.cv w)) R)
      (.classMem (synCop (.cv z) (.cv w)) (synCxp D D)) p0010 p0011
  have p0013 := @gOpelxp (.cv z) (.cv w) D D
  have p0014 :=
    @gBiimpi (.classMem (synCop (.cv z) (.cv w)) (synCxp D D))
      (synWa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0013
  have p0015 :=
    @gSyl6 ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (synCop (.cv z) (.cv w)) (synCxp D D))
      (synWa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0012 p0014
  have p0016 := @gSimpl (.classMem (.cv z) D) (.classMem (.cv w) D)
  have p0017 :=
    @gSyl6 ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (synWa (.classMem (.cv z) D) (.classMem (.cv w) D)) (.classMem (.cv z) D) p0015
      p0016
  have p0018 := @gSnelpw1 (.cv z) D
  have p0019 :=
    @gBiimpri (.classMem (synCsn (.cv z)) (synCpw1 D)) (.classMem (.cv z) D) p0018
  have p0020 :=
    @gSimp1 (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
      (synWbr (.cv z) R (.cv w))
  have p0021 :=
    @gEleq1d
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.cv x) (synCsn (.cv z)) (synCpw1 D) p0020
  have p0022 :=
    @gBiimprd
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (.cv x) (synCpw1 D)) (.classMem (synCsn (.cv z)) (synCpw1 D)) p0021
  have p0023 :=
    @gSyl5 (.classMem (.cv z) D) (.classMem (synCsn (.cv z)) (synCpw1 D))
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (.cv x) (synCpw1 D)) p0019 p0022
  have p0024 :=
    @gA1i
      (.imp (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
          (synWbr (.cv z) R (.cv w)))
        (.imp (.classMem (.cv z) D) (.classMem (.cv x) (synCpw1 D))))
      ph p0023
  have p0025 :=
    @gMpdd ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (.cv z) D) (.classMem (.cv x) (synCpw1 D)) p0017 p0024
  have p0036 := @gSimpr (.classMem (.cv z) D) (.classMem (.cv w) D)
  have p0037 :=
    @gSyl6 ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (synWa (.classMem (.cv z) D) (.classMem (.cv w) D)) (.classMem (.cv w) D) p0015
      p0036
  have p0038 := @gSnelpw1 (.cv w) D
  have p0039 :=
    @gBiimpri (.classMem (synCsn (.cv w)) (synCpw1 D)) (.classMem (.cv w) D) p0038
  have p0040 :=
    @gSimp2 (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
      (synWbr (.cv z) R (.cv w))
  have p0041 :=
    @gEleq1d
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.cv y) (synCsn (.cv w)) (synCpw1 D) p0040
  have p0042 :=
    @gBiimprd
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (.cv y) (synCpw1 D)) (.classMem (synCsn (.cv w)) (synCpw1 D)) p0041
  have p0043 :=
    @gSyl5 (.classMem (.cv w) D) (.classMem (synCsn (.cv w)) (synCpw1 D))
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (.cv y) (synCpw1 D)) p0039 p0042
  have p0044 :=
    @gA1i
      (.imp (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
          (synWbr (.cv z) R (.cv w)))
        (.imp (.classMem (.cv w) D) (.classMem (.cv y) (synCpw1 D))))
      ph p0043
  have p0045 :=
    @gMpdd ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (.cv w) D) (.classMem (.cv y) (synCpw1 D)) p0037 p0044
  have p0046 :=
    @gJcad ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)) p0025 p0045
  have p0047 := @gOpelxp (.cv x) (.cv y) (synCpw1 D) (synCpw1 D)
  have p0048 :=
    @gBiimpri (.classMem (synCop (.cv x) (.cv y)) (synCxp (synCpw1 D) (synCpw1 D)))
      (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D))) p0047
  have p0049 :=
    @gSyl6 ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (synWa (.classMem (.cv x) (synCpw1 D)) (.classMem (.cv y) (synCpw1 D)))
      (.classMem (synCop (.cv x) (.cv y)) (synCxp (synCpw1 D) (synCpw1 D))) p0046
      p0048
  have p0050 :=
    @gExlimdvv ph
      (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
        (synWbr (.cv z) R (.cv w)))
      (.classMem (synCop (.cv x) (.cv y)) (synCxp (synCpw1 D) (synCpw1 D))) z w
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0049
  have p0051 :=
    @gSyld ph (.classMem (synCop (.cv x) (.cv y)) (synCsi R))
      (synWex z (synWex w (synW3a (.classEq (.cv x) (synCsn (.cv z)))
            (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) R (.cv w)))))
      (.classMem (synCop (.cv x) (.cv y)) (synCxp (synCpw1 D) (synCpw1 D))) p0005
      p0050
  have p0052 :=
    @gRelssdv ph x y (synCsi R) (synCxp (synCpw1 D) (synCpw1 D)) dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      p0051
  exact p0052

/-- Checked nominal proof certificate identified upstream as `g_hnsicodeliftcodeclndv`. -/
@[expose]
noncomputable def gHnsicodeliftcodeclndv (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (.classMem
          (synCop (synCsi (synCfv (synC1st) (.cv u)))
            (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChwcn (synCpw1 A)))) :=
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
    Disjoint ((synCpw1 A)).fv ((synCsi (synCfv (synC1st) (.cv u)))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((synCpw1 A)).fv ((synCsi (synCfv (synC1st) (.cv u)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi];
          exact
            (show Disjoint ((A).fv) (((synCfv (synC1st) (.cv u))).fv) from
              (by
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
                                  (show u ∉ (A).fv from (by exact dv_A_u)))))),
                        (show Disjoint ((A).fv) (((synC1st)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                            exact
                              (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                (by simp))))⟩))))))
  have p0000 := @gHwcnwendv u A dv_cache_0001
  have p0001 := @gSiwendv (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0002 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWbr (synCsi (synCfv (synC1st) (.cv u))) (synCwe)
        (synCpw1 (synCfv (synC2nd) (.cv u))))
      p0000 p0001
  have p0003 := @gHwcnbase u A dv_cache_0001
  have p0004 := @gPw1ss (synCfv (synC2nd) (.cv u)) A
  have p0005 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (synWss (synCfv (synC2nd) (.cv u)) A)
      (synWss (synCpw1 (synCfv (synC2nd) (.cv u))) (synCpw1 A)) p0003 p0004
  have p0006 :=
    @gJca (.classMem (.cv u) (synChwcn A))
      (synWbr (synCsi (synCfv (synC1st) (.cv u))) (synCwe)
        (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synWss (synCpw1 (synCfv (synC2nd) (.cv u))) (synCpw1 A)) p0002 p0005
  have p0007 := @gFvex (.cv u) (synC1st)
  have p0008 := @gSiex (synCfv (synC1st) (.cv u)) p0007
  have p0009 := @gFvex (.cv u) (synC2nd)
  have p0010 := @gPw1ex (synCfv (synC2nd) (.cv u)) p0009
  have p0011 :=
    @gElhwcodes (synCpw1 A) (synCpw1 (synCfv (synC2nd) (.cv u)))
      (synCsi (synCfv (synC1st) (.cv u))) dv_cache_0002 p0008 p0010
  have p0012 :=
    @gBiimpri
      (.classMem (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChwcodes (synCpw1 A)))
      (synWa (synWbr (synCsi (synCfv (synC1st) (.cv u))) (synCwe)
          (synCpw1 (synCfv (synC2nd) (.cv u))))
        (synWss (synCpw1 (synCfv (synC2nd) (.cv u))) (synCpw1 A)))
      p0011
  have p0013 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (synWa (synWbr (synCsi (synCfv (synC1st) (.cv u))) (synCwe)
          (synCpw1 (synCfv (synC2nd) (.cv u))))
        (synWss (synCpw1 (synCfv (synC2nd) (.cv u))) (synCpw1 A)))
      (.classMem (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChwcodes (synCpw1 A)))
      p0006 p0012
  have p0014 := @gHwcnsupp u A
  have p0015 :=
    @gSisuppdndv (.classMem (.cv u) (synChwcn A)) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) p0014
  have p0020 :=
    @gOpfv1st (synCsi (synCfv (synC1st) (.cv u)))
      (synCpw1 (synCfv (synC2nd) (.cv u))) p0008 p0010
  have p0025 :=
    @gOpfv2nd (synCsi (synCfv (synC1st) (.cv u)))
      (synCpw1 (synCfv (synC2nd) (.cv u))) p0008 p0010
  have p0031 :=
    @gXpeq12i
      (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synCpw1 (synCfv (synC2nd) (.cv u)))
      (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synCpw1 (synCfv (synC2nd) (.cv u))) p0025 p0025
  have p0032 :=
    @gSseq12i
      (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synCsi (synCfv (synC1st) (.cv u)))
      (synCxp (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (.cv u)))
            (synCpw1 (synCfv (synC2nd) (.cv u))))) (synCfv (synC2nd)
          (synCop (synCsi (synCfv (synC1st) (.cv u)))
            (synCpw1 (synCfv (synC2nd) (.cv u))))))
      (synCxp (synCpw1 (synCfv (synC2nd) (.cv u))) (synCpw1 (synCfv (synC2nd) (.cv u))))
      p0020 p0031
  have p0033 :=
    @gSylibr (.classMem (.cv u) (synChwcn A))
      (synWss (synCsi (synCfv (synC1st) (.cv u)))
        (synCxp (synCpw1 (synCfv (synC2nd) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synWss (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (.cv u)))
            (synCpw1 (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd)
            (synCop (synCsi (synCfv (synC1st) (.cv u)))
              (synCpw1 (synCfv (synC2nd) (.cv u))))) (synCfv (synC2nd)
            (synCop (synCsi (synCfv (synC1st) (.cv u)))
              (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      p0015 p0032
  have p0034 :=
    @gJca (.classMem (.cv u) (synChwcn A))
      (.classMem (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChwcodes (synCpw1 A)))
      (synWss (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (.cv u)))
            (synCpw1 (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd)
            (synCop (synCsi (synCfv (synC1st) (.cv u)))
              (synCpw1 (synCfv (synC2nd) (.cv u))))) (synCfv (synC2nd)
            (synCop (synCsi (synCfv (synC1st) (.cv u)))
              (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      p0013 p0033
  have p0039 :=
    @gOpex (synCsi (synCfv (synC1st) (.cv u))) (synCpw1 (synCfv (synC2nd) (.cv u)))
      p0008 p0010
  have p0040 :=
    @gElhwcncl (synCpw1 A)
      (synCop (synCsi (synCfv (synC1st) (.cv u))) (synCpw1 (synCfv (synC2nd) (.cv u))))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @gSylibr (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (synCop (synCsi (synCfv (synC1st) (.cv u)))
            (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChwcodes (synCpw1 A))) (synWss
          (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (.cv u)))
              (synCpw1 (synCfv (synC2nd) (.cv u))))) (synCxp (synCfv (synC2nd)
              (synCop (synCsi (synCfv (synC1st) (.cv u)))
                (synCpw1 (synCfv (synC2nd) (.cv u))))) (synCfv (synC2nd)
              (synCop (synCsi (synCfv (synC1st) (.cv u)))
                (synCpw1 (synCfv (synC2nd) (.cv u))))))))
      (.classMem (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChwcn (synCpw1 A)))
      p0034 p0041
  exact p0042

/-- Checked nominal proof certificate identified upstream as `g_hnsicodeliftfnvalgndv`. -/
@[expose]
noncomputable def gHnsicodeliftfnvalgndv (D : Class) (R : Class)
    (hyp_hnsicodeliftfnvalgndv_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hnsicodeliftfnvalgndv_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (synWss R (synCxp (synCvv) (synCvv)))
        (.classEq (synCfv (synChnsicodeliftfn) (synCsn (synCop R D)))
          (synCop (synCsi R) (synCpw1 D)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnsicodeliftfn))
  have p0001 :=
    @gFveq1i (synCsn (synCop R D)) (synChnsicodeliftfn)
      (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn)) p0000
  have p0002 := @gLnpwsirelfnfn
  have p0003 := @gLnpwpw1secondfnfn
  have p0004 := @gSnex (synCop R D)
  have p0005 :=
    @gFvtxpvv (synCsn (synCop R D)) (synClnpwsirelfn) (synClnpwpw1secondfn) p0002
      p0003 p0004
  have p0006 :=
    @gEqtri (synCfv (synChnsicodeliftfn) (synCsn (synCop R D)))
      (synCfv (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn)) (synCsn (synCop R D)))
      (synCop (synCfv (synClnpwsirelfn) (synCsn (synCop R D)))
        (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D))))
      p0001 p0005
  have p0007 :=
    @gA1i
      (.classEq (synCfv (synChnsicodeliftfn) (synCsn (synCop R D)))
        (synCop (synCfv (synClnpwsirelfn) (synCsn (synCop R D)))
          (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D)))))
      (synWss R (synCxp (synCvv) (synCvv))) p0006
  have p0008 :=
    @gLnpwsirelfnvalg D R hyp_hnsicodeliftfnvalgndv_1 hyp_hnsicodeliftfnvalgndv_2
  have p0009 :=
    @gLnpwpw1secondfnval D R hyp_hnsicodeliftfnvalgndv_1 hyp_hnsicodeliftfnvalgndv_2
  have p0010 :=
    @gA1i
      (.classEq (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D))) (synCpw1 D))
      (synWss R (synCxp (synCvv) (synCvv))) p0009
  have p0011 :=
    @gOpeq12d (synWss R (synCxp (synCvv) (synCvv)))
      (synCfv (synClnpwsirelfn) (synCsn (synCop R D))) (synCsi R)
      (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D))) (synCpw1 D) p0008 p0010
  have p0012 :=
    @gEqtrd (synWss R (synCxp (synCvv) (synCvv)))
      (synCfv (synChnsicodeliftfn) (synCsn (synCop R D)))
      (synCop (synCfv (synClnpwsirelfn) (synCsn (synCop R D)))
        (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D))))
      (synCop (synCsi R) (synCpw1 D)) p0007 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end
