/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwnisodm`. -/
@[expose]
noncomputable def gHwnisodm (A : Class) :
    Nominal.NPrf (.classEq (synCdm (synChwniso A)) (synChwcn A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have dv_cache_0001 : v ∉ ((Class.cv u)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_u, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0004 : v ∉ ((Wff.classMem (.cv u) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0006 :
    v ∉
      ((synWb (synWbr (.cv u) (synChwniso A) (.cv u)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
            (synWbr (.cv u) (synChwiso A) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, or_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((synCdm (synChwniso A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0008 : u ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have p0000 := @gEldm v (.cv u) (synChwniso A) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpi (.classMem (.cv u) (synCdm (synChwniso A)))
      (synWex v (synWbr (.cv u) (synChwniso A) (.cv v))) p0000
  have p0002 := @gHwnisohwisob v u A dv_cache_0003
  have p0003 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0002
  have p0004 :=
    @gSimpld (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0003
  have p0005 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0006 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0004 p0005
  have p0007 :=
    @gExlimiv (synWbr (.cv u) (synChwniso A) (.cv v)) (.classMem (.cv u) (synChwcn A))
      v dv_cache_0004 p0006
  have p0008 :=
    @gSyl (.classMem (.cv u) (synCdm (synChwniso A)))
      (synWex v (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn A)) p0001 p0007
  have p0009 := @gPm424 (.classMem (.cv u) (synChwcn A))
  have p0010 :=
    @gBiimpi (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0009
  have p0011 := @gHwcnraw u A
  have p0012 := @gHwisorefl u A dv_cache_0005
  have p0013 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))
      (synWbr (.cv u) (synChwiso A) (.cv u)) p0011 p0012
  have p0014 :=
    @gJca (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv u)) p0010 p0013
  have p0015 := @gElex (.cv u) (synChwcn A)
  have p0016 := @gBreq2 (.cv v) (.cv u) (.cv u) (synChwniso A)
  have p0017 := @gEleq1 (.cv v) (.cv u) (synChwcn A)
  have p0018 :=
    @gAnbi2d (.classEq (.cv v) (.cv u)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0017
  have p0019 := @gBreq2 (.cv v) (.cv u) (.cv u) (synChwiso A)
  have p0020 :=
    @gAnbi12d (.classEq (.cv v) (.cv u))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv u) (synChwiso A) (.cv u))
      p0018 p0019
  have p0021 :=
    @gBibi12d (.classEq (.cv v) (.cv u)) (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv u) (synChwniso A) (.cv u))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv u)))
      p0016 p0020
  have p0023 :=
    @gVtoclg
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv v))))
      (synWb (synWbr (.cv u) (synChwniso A) (.cv u)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv u))))
      v (.cv u) (synCvv) dv_cache_0001 dv_cache_0006 p0021 p0002
  have p0024 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synCvv))
      (synWb (synWbr (.cv u) (synChwniso A) (.cv u)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv u))))
      p0015 p0023
  have p0025 :=
    @gMpbird (.classMem (.cv u) (synChwcn A)) (synWbr (.cv u) (synChwniso A) (.cv u))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv u)))
      p0014 p0024
  have p0026 := @gBreldm (.cv u) (.cv u) (synChwniso A)
  have p0027 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (synWbr (.cv u) (synChwniso A) (.cv u))
      (.classMem (.cv u) (synCdm (synChwniso A))) p0025 p0026
  have p0028 :=
    @gImpbii (.classMem (.cv u) (synCdm (synChwniso A)))
      (.classMem (.cv u) (synChwcn A)) p0008 p0027
  have p0029 :=
    @gEqriv u (synCdm (synChwniso A)) (synChwcn A) dv_cache_0007 dv_cache_0008 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_hwnisoclasseqb`. -/
@[expose]
noncomputable def gHwnisoclasseqb (v : Var) (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))) (synWb
          (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
          (synWbr (.cv u) (synChwniso A) (.cv v)))) :=
  by
  have p0000 :=
    @gSimpl (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0001 := @gHwnisoerv A
  have p0002 :=
    @gSyl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synCvv)) p0000 p0001
  have p0003 := @gHwnisodm A
  have p0004 :=
    @gA1i (.classEq (synCdm (synChwniso A)) (synChwcn A))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      p0003
  have p0005 :=
    @gSimpr (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0006 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0007 :=
    @gSyl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0005 p0006
  have p0008 := @gElex (.cv u) (synChwcn A)
  have p0009 :=
    @gSyl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synCvv)) p0007 p0008
  have p0011 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0012 :=
    @gSyl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv v) (synChwcn A)) p0005 p0011
  have p0013 :=
    @gErth2
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.cv u) (.cv v) (synChwniso A) (synCvv) (synChwcn A) p0002 p0004 p0009 p0012
  have p0014 :=
    @gBicomd
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A))) p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_hnordexg`. -/
@[expose]
noncomputable def gHnordexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCvv)) (.classMem (synChnord A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnord A))
  have p0001 := @gHwnisoexg A
  have p0002 := @gHwcnexg A
  have p0003 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwniso A) (synCvv))
      (.classMem (synChwcn A) (synCvv)) p0001 p0002
  have p0004 := @gQsexg (synChwcn A) (synChwniso A) (synCvv) (synCvv)
  have p0005 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwniso A) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synCqs (synChwcn A) (synChwniso A)) (synCvv)) p0003 p0004
  have p0006 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChnord A)
      (synCqs (synChwcn A) (synChwniso A)) (synCvv) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_hncardex`. -/
@[expose]
noncomputable def gHncardex (A : Class) :
    Nominal.NPrf (.classMem (synChncard A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncard A))
  have p0001 := @gNcex (synChnord A)
  have p0002 := @gEqeltri (synChncard A) (synCnc (synChnord A)) (synCvv) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hncardnc`. -/
@[expose]
noncomputable def gHncardnc (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCvv)) (.classMem (synChncard A) (synCncs))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncard A))
  have p0001 := (Nominal.classEqRefl (synChnord A))
  have p0002 := @gHwnisoexg A
  have p0003 := @gHwcnexg A
  have p0004 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwniso A) (synCvv))
      (.classMem (synChwcn A) (synCvv)) p0002 p0003
  have p0005 := @gQsexg (synChwcn A) (synChwniso A) (synCvv) (synCvv)
  have p0006 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwniso A) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synCqs (synChwcn A) (synChwniso A)) (synCvv)) p0004 p0005
  have p0007 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChnord A)
      (synCqs (synChwcn A) (synChwniso A)) (synCvv) p0001 p0006
  have p0008 := @gNcelncs (synChnord A) (synCvv)
  have p0009 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChnord A) (synCvv))
      (.classMem (synCnc (synChnord A)) (synCncs)) p0007 p0008
  have p0010 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChncard A) (synCnc (synChnord A))
      (synCncs) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hncardtc`. -/
@[expose]
noncomputable def gHncardtc (A : Class)
    (hyp_hncardtc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCtc (synChncard A)) (synCnc (synCpw1 (synChnord A)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncard A))
  have p0001 := @gTceq (synChncard A) (synCnc (synChnord A))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gHnordex A hyp_hncardtc_1
  have p0004 := @gTcnc (synChnord A) p0003
  have p0005 :=
    @gEqtri (synCtc (synChncard A)) (synCtc (synCnc (synChnord A)))
      (synCnc (synCpw1 (synChnord A))) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hncardtc2`. -/
@[expose]
noncomputable def gHncardtc2 (A : Class)
    (hyp_hncardtc2_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synChncard A)))
        (synCnc (synCpw1 (synCpw1 (synChnord A))))) :=
  by
  have p0000 := @gHncardtc A hyp_hncardtc2_1
  have p0001 := @gTceq (synCtc (synChncard A)) (synCnc (synCpw1 (synChnord A)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gHnordex A hyp_hncardtc2_1
  have p0004 := @gPw1ex (synChnord A) p0003
  have p0005 := @gTcnc (synCpw1 (synChnord A)) p0004
  have p0006 :=
    @gEqtri (synCtc (synCtc (synChncard A)))
      (synCtc (synCnc (synCpw1 (synChnord A))))
      (synCnc (synCpw1 (synCpw1 (synChnord A)))) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_hwcnbase`. -/
@[expose]
noncomputable def gHwcnbase (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (synWss (synCfv (synC2nd) (.cv u)) A)) :=
  by
  have dv_cache_0001 : Disjoint (A).fv ((synCfv (synC1st) (.cv u))).fv := by
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
                            (show u ∉ (A).fv from (by exact dv_A_u)))))),
                  (show Disjoint ((A).fv) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 := @gHwcnraw u A
  have p0001 := @gHwcnpair u A
  have p0002 :=
    @gEleq1d (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (synChwcodes A)
      p0001
  have p0003 :=
    @gMpbid (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      p0000 p0002
  have p0004 := @gFvex (.cv u) (synC1st)
  have p0005 := @gFvex (.cv u) (synC2nd)
  have p0006 :=
    @gElhwcodes A (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) dv_cache_0001
      p0004 p0005
  have p0007 :=
    @gBiimpi
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) A))
      p0006
  have p0008 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) A))
      p0003 p0007
  have p0009 :=
    @gSimprd (.classMem (.cv u) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) A) p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_elhwbases`. -/
@[expose]
noncomputable def gElhwbases (u : Var) (A : Class) (D : Class)
    (_dv_A_D : Disjoint A.fv D.fv) (dv_A_u : u ∉ A.fv) (dv_D_u : u ∉ D.fv) :
    Nominal.NPrf
      (synWb (.classMem D (synChwbases A))
        (synWrex u (synChwcn A) (.classEq D (synCfv (synC2nd) (.cv u))))) :=
  by
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_u, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_u,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChwbases A))
  have p0001 := @gEleq2i (synChwbases A) (synCima (synC2nd) (synChwcn A)) D p0000
  have p0002 :=
    @gElima u D (synC2nd) (synChwcn A) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 := @gN2ndfo
  have p0004 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gVex u
  have p0007 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (.classMem (.cv u) (synCvv)) p0005 p0006
  have p0008 := @gFnbrfvb (synCvv) (.cv u) D (synC2nd)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gBicomi (.classEq (synCfv (synC2nd) (.cv u)) D) (synWbr (.cv u) (synC2nd) D)
      p0009
  have p0011 := @gEqcom (synCfv (synC2nd) (.cv u)) D
  have p0012 :=
    @gBitri (synWbr (.cv u) (synC2nd) D) (.classEq (synCfv (synC2nd) (.cv u)) D)
      (.classEq D (synCfv (synC2nd) (.cv u))) p0010 p0011
  have p0013 :=
    @gRexbii (synWbr (.cv u) (synC2nd) D) (.classEq D (synCfv (synC2nd) (.cv u))) u
      (synChwcn A) p0012
  have p0014 :=
    @gBitri (.classMem D (synCima (synC2nd) (synChwcn A)))
      (synWrex u (synChwcn A) (synWbr (.cv u) (synC2nd) D))
      (synWrex u (synChwcn A) (.classEq D (synCfv (synC2nd) (.cv u)))) p0002 p0013
  have p0015 :=
    @gBitri (.classMem D (synChwbases A))
      (.classMem D (synCima (synC2nd) (synChwcn A)))
      (synWrex u (synChwcn A) (.classEq D (synCfv (synC2nd) (.cv u)))) p0001 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hwcardsexg`. -/
@[expose]
noncomputable def gHwcardsexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCvv)) (.classMem (synChwcards A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcards A))
  have p0001 := @gEnex
  have p0002 := @gA1i (.classMem (synCen) (synCvv)) (.classMem A (synCvv)) p0001
  have p0003 := (Nominal.classEqRefl (synChwbases A))
  have p0004 := @gN2ndex
  have p0005 := @gA1i (.classMem (synC2nd) (synCvv)) (.classMem A (synCvv)) p0004
  have p0006 := @gHwcnexg A
  have p0007 :=
    @gJca (.classMem A (synCvv)) (.classMem (synC2nd) (synCvv))
      (.classMem (synChwcn A) (synCvv)) p0005 p0006
  have p0008 := @gImaexg (synC2nd) (synChwcn A) (synCvv) (synCvv)
  have p0009 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synC2nd) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synCima (synC2nd) (synChwcn A)) (synCvv)) p0007 p0008
  have p0010 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChwbases A)
      (synCima (synC2nd) (synChwcn A)) (synCvv) p0003 p0009
  have p0011 :=
    @gJca (.classMem A (synCvv)) (.classMem (synCen) (synCvv))
      (.classMem (synChwbases A) (synCvv)) p0002 p0010
  have p0012 := @gQsexg (synChwbases A) (synCen) (synCvv) (synCvv)
  have p0013 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synCen) (synCvv)) (.classMem (synChwbases A) (synCvv)))
      (.classMem (synCqs (synChwbases A) (synCen)) (synCvv)) p0011 p0012
  have p0014 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChwcards A)
      (synCqs (synChwbases A) (synCen)) (synCvv) p0000 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_elhwcards`. -/
@[expose]
noncomputable def gElhwcards (A : Class) (K : Class) (d : Var)
    (_dv_A_K : Disjoint A.fv K.fv) (dv_A_d : d ∉ A.fv) (dv_K_d : d ∉ K.fv)
    (hyp_elhwcards_1 : Nominal.NPrf (.classMem K (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem K (synChwcards A))
        (synWrex d (synChwbases A) (.classEq K (synCnc (.cv d))))) :=
  by
  have dv_cache_0001 : d ∉ ((synChwbases A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases, dv_A_d,
          not_false_eq_true])
  have dv_cache_0002 : d ∉ (K).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_d, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((synCen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChwcards A))
  have p0001 := @gEleq2i (synChwcards A) (synCqs (synChwbases A) (synCen)) K p0000
  have p0002 :=
    @gElqs d (synChwbases A) K (synCen) dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_elhwcards_1
  have p0003 := (Nominal.classEqRefl (synCnc (.cv d)))
  have p0004 := @gEqeq2i (synCnc (.cv d)) (synCec (.cv d) (synCen)) K p0003
  have p0005 :=
    @gBicomi (.classEq K (synCnc (.cv d))) (.classEq K (synCec (.cv d) (synCen)))
      p0004
  have p0006 :=
    @gRexbii (.classEq K (synCec (.cv d) (synCen))) (.classEq K (synCnc (.cv d))) d
      (synChwbases A) p0005
  have p0007 :=
    @gBitri (.classMem K (synCqs (synChwbases A) (synCen)))
      (synWrex d (synChwbases A) (.classEq K (synCec (.cv d) (synCen))))
      (synWrex d (synChwbases A) (.classEq K (synCnc (.cv d)))) p0002 p0006
  have p0008 :=
    @gBitri (.classMem K (synChwcards A))
      (.classMem K (synCqs (synChwbases A) (synCen)))
      (synWrex d (synChwbases A) (.classEq K (synCnc (.cv d)))) p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hwcardssnc`. -/
@[expose]
noncomputable def gHwcardssnc (A : Class) :
    Nominal.NPrf (synWss (synChwcards A) (synCncs)) :=
  by
  let proofSupport : Finset Var := A.fv
  let k : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (h)
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (h)
  have fresh_k_ne_d : k ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_k : d ≠ k := Ne.symm fresh_k_ne_d
  have dv_cache_0001 : Disjoint (A).fv ((Class.cv k)).fv := by
    exact
      (show Disjoint (A).fv ((Class.cv k)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ k } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show k ∉ (A).fv from (by exact fresh_k_not_A))))))
  have dv_cache_0002 : d ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_k, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((synChwcards A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          fresh_k_not_A, not_false_eq_true])
  have dv_cache_0005 : k ∉ ((synCncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gVex k
  have p0001 := @gElhwcards A (.cv k) d dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 :=
    @gBiimpi (.classMem (.cv k) (synChwcards A))
      (synWrex d (synChwbases A) (.classEq (.cv k) (synCnc (.cv d)))) p0001
  have p0003 := @gRexex (.classEq (.cv k) (synCnc (.cv d))) d (synChwbases A)
  have p0004 :=
    @gSyl (.classMem (.cv k) (synChwcards A))
      (synWrex d (synChwbases A) (.classEq (.cv k) (synCnc (.cv d))))
      (synWex d (.classEq (.cv k) (synCnc (.cv d)))) p0002 p0003
  have p0005 := @gElncs d (.cv k) dv_cache_0003
  have p0006 :=
    @gBiimpri (.classMem (.cv k) (synCncs))
      (synWex d (.classEq (.cv k) (synCnc (.cv d)))) p0005
  have p0007 :=
    @gSyl (.classMem (.cv k) (synChwcards A))
      (synWex d (.classEq (.cv k) (synCnc (.cv d)))) (.classMem (.cv k) (synCncs))
      p0004 p0006
  have p0008 := @gSsriv k (synChwcards A) (synCncs) dv_cache_0004 dv_cache_0005 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_frrd`. -/
@[expose]
noncomputable def gFrrd (ph : Wff) (x : Var) (y : Var) (z : Var) (B : Class) (S : Class)
    (dv_B_x : x ∉ B.fv) (_dv_B_y : y ∉ B.fv) (_dv_B_z : z ∉ B.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_ph_x : x ∉ ph.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_frrd_1 : Nominal.NPrf (.imp ph (.classMem S (synCvv))))
    (hyp_frrd_2 : Nominal.NPrf (.imp ph (.classMem B (synCvv))))
    (hyp_frrd_3 : Nominal.NPrf
        (.imp (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
          (synWrex z (.cv x)
            (synWral y (.cv x) (.imp (synWbr (.cv y) S (.cv z)) (.objEq y z)))))) :
    Nominal.NPrf (.imp ph (synWbr S (synCfound) B)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ B.fv ∪
      S.fv
  let a : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_ne_z : r ≠ z := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_r : z ≠ r := Ne.symm fresh_r_ne_z
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classEq (.cv r) S)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, dv_S_z, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv r) S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, dv_S_y, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv r) S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, dv_S_x, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv a) B)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_a, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0006 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0007 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0008 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0009 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0010 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0016 : r ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_S, not_false_eq_true])
  have dv_cache_0017 : a ∉ (S).fv :=
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
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0018 : r ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_B, not_false_eq_true])
  have dv_cache_0019 : a ∉ (B).fv :=
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
        simp only [fresh_a_not_B, not_false_eq_true])
  have dv_cache_0020 :
    r ∉
      ((Wff.all x (.imp (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
            (synWrex z (.cv x) (synWral y (.cv x)
                (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_B, fresh_r_ne_y, fresh_r_ne_z,
          fresh_r_not_S, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0021 :
    a ∉
      ((Wff.all x (.imp (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
            (synWrex z (.cv x) (synWral y (.cv x)
                (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_not_B, fresh_a_ne_y, fresh_a_ne_z,
          fresh_a_not_S, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0022 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000_e00_recanon :
    Nominal.NPrf
      (.imp (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
        (synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWrex synWex synWral synWbr synCop synCun synCnin synWnan
          synCcompl
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      hyp_frrd_3
  have p0000 :=
    @gEx ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      p0000_e00_recanon
  have p0001 :=
    @gAlrimiv ph
      (.imp (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      x dv_cache_0001 p0000
  have p0002 :=
    @gJca ph (.classMem S (synCvv)) (.classMem B (synCvv)) hyp_frrd_1 hyp_frrd_2
  have p0003 := @gBreq (.cv y) (.cv z) (.cv r) S
  have p0004 :=
    @gImbi1d (.classEq (.cv r) S) (synWbr (.cv y) (.cv r) (.cv z))
      (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)) p0003
  have p0005 :=
    @gRexralbidv (.classEq (.cv r) S)
      (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))) z y (.cv x) (.cv x)
      dv_cache_0002 dv_cache_0003 p0004
  have p0006 :=
    @gImbi2d (.classEq (.cv r) S)
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z)))))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) p0005
  have p0007 :=
    @gAlbidv (.classEq (.cv r) S)
      (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
          (synWral y (.cv x)
            (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z))))))
      (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      x dv_cache_0004 p0006
  have p0008 := @gSseq2 (.cv a) B (.cv x)
  have p0009 :=
    @gAnbi1d (.classEq (.cv a) B) (synWss (.cv x) (.cv a)) (synWss (.cv x) B)
      (synWne (.cv x) (synC0)) p0008
  have p0010 :=
    @gImbi1d (.classEq (.cv a) B)
      (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
      (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      p0009
  have p0011 :=
    @gAlbidv (.classEq (.cv a) B)
      (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      (.imp (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      x dv_cache_0005 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFound x y z r a
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0013_e02_recanon :
    Nominal.NPrf
      (.classEq (synCfound) (synCopab r a (.all x
            (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
              (synWrex z (.cv x) (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z))
                    (.classEq (.cv y) (.cv z))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCfound synCopab synWex synWa synWss synCin synCcompl synCnin
          synWnan synWne synC0 synCdif synCvv synWrex synWral synWbr synCop
          synCun
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0012
  have p0013 :=
    @gBrabg
      (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
          (synWrex z (.cv x) (synWral y (.cv x)
              (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z)))))))
      (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
          (synWrex z (.cv x) (synWral y (.cv x)
              (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))
      (.all x (.imp (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
            (synWral y (.cv x)
              (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))
      r a S B (synCvv) (synCvv) (synCfound) dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0007 p0011
      p0013_e02_recanon
  have p0014 :=
    @gSyl ph (synWa (.classMem S (synCvv)) (.classMem B (synCvv)))
      (synWb (synWbr S (synCfound) B) (.all x
          (.imp (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
              (synWral y (.cv x)
                (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))))
      p0002 p0013
  have p0015 :=
    @gMpbird ph (synWbr S (synCfound) B)
      (.all x (.imp (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))) (synWrex z (.cv x)
            (synWral y (.cv x)
              (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))
      p0001 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwnisohwisocl`. -/
@[expose]
noncomputable def gHwnisohwisocl (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
        (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwiso A) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ≠ v := by exact (show u ≠ v from (by exact fresh_u_ne_v))
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
      ((Wff.imp (synWbr B (synChwniso A) (.cv v)) (synWbr B (synChwiso A) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, fresh_u_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0004 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0005 :
    v ∉
      ((Wff.imp (.classMem B (synCvv))
          (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwiso A) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union,
          fresh_v_not_B, fresh_v_not_C, fresh_v_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gSimpl (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0001 := @gSimpr (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0002 := @gBreq2 (.cv v) C B (synChwniso A)
  have p0003 := @gBreq2 (.cv v) C B (synChwiso A)
  have p0004 :=
    @gImbi12d (.classEq (.cv v) C) (synWbr B (synChwniso A) (.cv v))
      (synWbr B (synChwniso A) C) (synWbr B (synChwiso A) (.cv v))
      (synWbr B (synChwiso A) C) p0002 p0003
  have p0005 :=
    @gImbi2d (.classEq (.cv v) C)
      (.imp (synWbr B (synChwniso A) (.cv v)) (synWbr B (synChwiso A) (.cv v)))
      (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwiso A) C))
      (.classMem B (synCvv)) p0004
  have p0006 := @gBreq1 (.cv u) B (.cv v) (synChwniso A)
  have p0007 := @gBreq1 (.cv u) B (.cv v) (synChwiso A)
  have p0008 :=
    @gImbi12d (.classEq (.cv u) B) (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr B (synChwniso A) (.cv v)) (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWbr B (synChwiso A) (.cv v)) p0006 p0007
  have p0009 := @gHwnisohwisob v u A dv_cache_0001
  have p0010 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0009
  have p0011 :=
    @gSimprd (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0010
  have p0012 :=
    @gVtoclg
      (.imp (synWbr (.cv u) (synChwniso A) (.cv v)) (synWbr (.cv u) (synChwiso A) (.cv v)))
      (.imp (synWbr B (synChwniso A) (.cv v)) (synWbr B (synChwiso A) (.cv v))) u B
      (synCvv) dv_cache_0002 dv_cache_0003 p0008 p0011
  have p0013 :=
    @gVtoclg
      (.imp (.classMem B (synCvv))
        (.imp (synWbr B (synChwniso A) (.cv v)) (synWbr B (synChwiso A) (.cv v))))
      (.imp (.classMem B (synCvv))
        (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwiso A) C)))
      v C (synCvv) dv_cache_0004 dv_cache_0005 p0005 p0012
  have p0014 :=
    @gSyl (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classMem C (synCvv))
      (.imp (.classMem B (synCvv))
        (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwiso A) C)))
      p0001 p0013
  have p0015 :=
    @gMpd (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classMem B (synCvv))
      (.imp (synWbr B (synChwniso A) C) (synWbr B (synChwiso A) C)) p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hwisowitnesscl`. -/
@[expose]
noncomputable def gHwisowitnesscl (A : Class) (B : Class) (C : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
        (.imp (synWbr B (synChwiso A) C) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({ h } : Finset Var)
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_h : v ≠ h := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_v : h ≠ v := Ne.symm fresh_v_ne_h
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_h : u ≠ h := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_u : h ≠ u := Ne.symm fresh_u_ne_h
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : h ∉ ((Wff.classEq (.cv v) C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_v, dv_C_h, or_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((Wff.classEq (.cv u) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, dv_B_h, or_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_h, not_false_eq_true])
  have dv_cache_0004 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0005 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0006 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0007 :
    u ∉
      ((Wff.imp (synWbr B (synChwiso A) (.cv v)) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v,
          fresh_u_not_A, fresh_u_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0008 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0009 :
    v ∉
      ((Wff.imp (.classMem B (synCvv)) (.imp (synWbr B (synChwiso A) C) (synWex h
              (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
                (synCfv (synC2nd) B) (synCfv (synC2nd) C)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C,
          fresh_v_not_A, fresh_v_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gSimpl (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0001 := @gSimpr (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0002 := @gBreq2 (.cv v) C B (synChwiso A)
  have p0003 := @gFveq2 (.cv v) C (synC1st)
  have p0004 :=
    @gIsoeq3 (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) B)
      (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C) (.cv h)
  have p0005 :=
    @gSyl (.classEq (.cv v) C)
      (.classEq (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C))
      (synWb (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0003 p0004
  have p0006 := @gFveq2 (.cv v) C (synC2nd)
  have p0007 :=
    @gIsoeq5 (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C)
      (synCfv (synC1st) B) (synCfv (synC1st) C) (.cv h)
  have p0008 :=
    @gSyl (.classEq (.cv v) C)
      (.classEq (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C))
      (synWb (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      p0006 p0007
  have p0009 :=
    @gBitrd (.classEq (.cv v) C)
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) C))
      p0005 p0008
  have p0010 :=
    @gExbidv (.classEq (.cv v) C)
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) C))
      h dv_cache_0001 p0009
  have p0011 :=
    @gImbi12d (.classEq (.cv v) C) (synWbr B (synChwiso A) (.cv v))
      (synWbr B (synChwiso A) C)
      (synWex h (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      p0002 p0010
  have p0012 :=
    @gImbi2d (.classEq (.cv v) C)
      (.imp (synWbr B (synChwiso A) (.cv v)) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))))
      (.imp (synWbr B (synChwiso A) C) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
            (synCfv (synC2nd) B) (synCfv (synC2nd) C))))
      (.classMem B (synCvv)) p0011
  have p0013 := @gBreq1 (.cv u) B (.cv v) (synChwiso A)
  have p0014 := @gFveq2 (.cv u) B (synC1st)
  have p0015 :=
    @gIsoeq2 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) B)
      (.cv h)
  have p0016 :=
    @gSyl (.classEq (.cv u) B)
      (.classEq (synCfv (synC1st) (.cv u)) (synCfv (synC1st) B))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0014 p0015
  have p0017 := @gFveq2 (.cv u) B (synC2nd)
  have p0018 :=
    @gIsoeq4 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC2nd) B) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v)) (.cv h)
  have p0019 :=
    @gSyl (.classEq (.cv u) B)
      (.classEq (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B))
      (synWb (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0017 p0018
  have p0020 :=
    @gBitrd (.classEq (.cv u) B)
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      p0016 p0019
  have p0021 :=
    @gExbidv (.classEq (.cv u) B)
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      h dv_cache_0002 p0020
  have p0022 :=
    @gImbi12d (.classEq (.cv u) B) (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWbr B (synChwiso A) (.cv v))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0013 p0021
  have p0023 := @gBrhwisoany v u A h dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0024 :=
    @gBiimpi (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0023
  have p0025 :=
    @gSimprd (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0024
  have p0026 :=
    @gVtoclg
      (.imp (synWbr (.cv u) (synChwiso A) (.cv v)) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (.imp (synWbr B (synChwiso A) (.cv v)) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))))
      u B (synCvv) dv_cache_0006 dv_cache_0007 p0022 p0025
  have p0027 :=
    @gVtoclg
      (.imp (.classMem B (synCvv)) (.imp (synWbr B (synChwiso A) (.cv v)) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))))
      (.imp (.classMem B (synCvv)) (.imp (synWbr B (synChwiso A) C) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C)))))
      v C (synCvv) dv_cache_0008 dv_cache_0009 p0012 p0026
  have p0028 :=
    @gSyl (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classMem C (synCvv))
      (.imp (.classMem B (synCvv)) (.imp (synWbr B (synChwiso A) C) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C)))))
      p0001 p0027
  have p0029 :=
    @gMpd (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classMem B (synCvv))
      (.imp (synWbr B (synChwiso A) C) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
            (synCfv (synC2nd) B) (synCfv (synC2nd) C))))
      p0000 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_opfvscl`. -/
@[expose]
noncomputable def gOpfvscl (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
        (synWa (.classEq (synCfv (synC1st) (synCop B C)) B)
          (.classEq (synCfv (synC2nd) (synCop B C)) C))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((synWa (.classEq (synCfv (synC1st) (synCop B (.cv v))) B)
          (.classEq (synCfv (synC2nd) (synCop B (.cv v))) (.cv v)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0004 :
    v ∉
      ((Wff.imp (.classMem B (synCvv)) (synWa (.classEq (synCfv (synC1st) (synCop B C)) B)
            (.classEq (synCfv (synC2nd) (synCop B C)) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_v_not_B, fresh_v_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gSimpl (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0001 := @gSimpr (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0002 := @gOpeq2 (.cv v) C B
  have p0003 :=
    @gFveq2d (.classEq (.cv v) C) (synCop B (.cv v)) (synCop B C) (synC1st) p0002
  have p0004 := @gEqid B
  have p0005 := @gA1i (.classEq B B) (.classEq (.cv v) C) p0004
  have p0006 :=
    @gEqeq12d (.classEq (.cv v) C) (synCfv (synC1st) (synCop B (.cv v)))
      (synCfv (synC1st) (synCop B C)) B B p0003 p0005
  have p0008 :=
    @gFveq2d (.classEq (.cv v) C) (synCop B (.cv v)) (synCop B C) (synC2nd) p0002
  have p0009 := @gId (.classEq (.cv v) C)
  have p0010 :=
    @gEqeq12d (.classEq (.cv v) C) (synCfv (synC2nd) (synCop B (.cv v)))
      (synCfv (synC2nd) (synCop B C)) (.cv v) C p0008 p0009
  have p0011 :=
    @gAnbi12d (.classEq (.cv v) C) (.classEq (synCfv (synC1st) (synCop B (.cv v))) B)
      (.classEq (synCfv (synC1st) (synCop B C)) B)
      (.classEq (synCfv (synC2nd) (synCop B (.cv v))) (.cv v))
      (.classEq (synCfv (synC2nd) (synCop B C)) C) p0006 p0010
  have p0012 :=
    @gImbi2d (.classEq (.cv v) C)
      (synWa (.classEq (synCfv (synC1st) (synCop B (.cv v))) B)
        (.classEq (synCfv (synC2nd) (synCop B (.cv v))) (.cv v)))
      (synWa (.classEq (synCfv (synC1st) (synCop B C)) B)
        (.classEq (synCfv (synC2nd) (synCop B C)) C))
      (.classMem B (synCvv)) p0011
  have p0013 := @gOpeq1 (.cv u) B (.cv v)
  have p0014 :=
    @gFveq2d (.classEq (.cv u) B) (synCop (.cv u) (.cv v)) (synCop B (.cv v))
      (synC1st) p0013
  have p0015 := @gId (.classEq (.cv u) B)
  have p0016 :=
    @gEqeq12d (.classEq (.cv u) B) (synCfv (synC1st) (synCop (.cv u) (.cv v)))
      (synCfv (synC1st) (synCop B (.cv v))) (.cv u) B p0014 p0015
  have p0018 :=
    @gFveq2d (.classEq (.cv u) B) (synCop (.cv u) (.cv v)) (synCop B (.cv v))
      (synC2nd) p0013
  have p0019 := @gEqid (.cv v)
  have p0020 := @gA1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0019
  have p0021 :=
    @gEqeq12d (.classEq (.cv u) B) (synCfv (synC2nd) (synCop (.cv u) (.cv v)))
      (synCfv (synC2nd) (synCop B (.cv v))) (.cv v) (.cv v) p0018 p0020
  have p0022 :=
    @gAnbi12d (.classEq (.cv u) B)
      (.classEq (synCfv (synC1st) (synCop (.cv u) (.cv v))) (.cv u))
      (.classEq (synCfv (synC1st) (synCop B (.cv v))) B)
      (.classEq (synCfv (synC2nd) (synCop (.cv u) (.cv v))) (.cv v))
      (.classEq (synCfv (synC2nd) (synCop B (.cv v))) (.cv v)) p0016 p0021
  have p0023 := @gVex u
  have p0024 := @gVex v
  have p0025 := @gOpfv1st (.cv u) (.cv v) p0023 p0024
  have p0028 := @gOpfv2nd (.cv u) (.cv v) p0023 p0024
  have p0029 :=
    @gPm32i (.classEq (synCfv (synC1st) (synCop (.cv u) (.cv v))) (.cv u))
      (.classEq (synCfv (synC2nd) (synCop (.cv u) (.cv v))) (.cv v)) p0025 p0028
  have p0030 :=
    @gVtoclg
      (synWa (.classEq (synCfv (synC1st) (synCop (.cv u) (.cv v))) (.cv u))
        (.classEq (synCfv (synC2nd) (synCop (.cv u) (.cv v))) (.cv v)))
      (synWa (.classEq (synCfv (synC1st) (synCop B (.cv v))) B)
        (.classEq (synCfv (synC2nd) (synCop B (.cv v))) (.cv v)))
      u B (synCvv) dv_cache_0001 dv_cache_0002 p0022 p0029
  have p0031 :=
    @gVtoclg
      (.imp (.classMem B (synCvv))
        (synWa (.classEq (synCfv (synC1st) (synCop B (.cv v))) B)
          (.classEq (synCfv (synC2nd) (synCop B (.cv v))) (.cv v))))
      (.imp (.classMem B (synCvv)) (synWa (.classEq (synCfv (synC1st) (synCop B C)) B)
          (.classEq (synCfv (synC2nd) (synCop B C)) C)))
      v C (synCvv) dv_cache_0003 dv_cache_0004 p0012 p0030
  have p0032 :=
    @gSyl (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classMem C (synCvv))
      (.imp (.classMem B (synCvv)) (synWa (.classEq (synCfv (synC1st) (synCop B C)) B)
          (.classEq (synCfv (synC2nd) (synCop B C)) C)))
      p0001 p0031
  have p0033 :=
    @gMpd (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classMem B (synCvv))
      (synWa (.classEq (synCfv (synC1st) (synCop B C)) B)
        (.classEq (synCfv (synC2nd) (synCop B C)) C))
      p0000 p0032
  exact p0033


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part043`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_werestr`. -/
@[expose]
noncomputable def gWerestr (ph : Wff) (A : Class) (B : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_werestr_1 : Nominal.NPrf (.imp ph (synWbr R (synCwe) A)))
    (hyp_werestr_2 : Nominal.NPrf (.imp ph (synWss B A)))
    (hyp_werestr_3 : Nominal.NPrf (.imp ph (.classMem B (synCvv)))) :
    Nominal.NPrf (.imp ph (synWbr (synCin R (synCxp B B)) (synCwe) B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
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
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
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
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCin R (synCxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCin R (synCxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synCin R (synCxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_z_not_R, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0013 : z ∉ (R).fv :=
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
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0014 : y ∉ (R).fv :=
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
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0017 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0018 :
    y ∉ ((synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_ph, fresh_y_ne_x, fresh_y_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉ ((synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, fresh_z_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gBrex R A (synCwe)
  have p0001 :=
    @gSimpld (synWbr R (synCwe) A) (.classMem R (synCvv)) (.classMem A (synCvv))
      p0000
  have p0002 :=
    @gSyl ph (synWbr R (synCwe) A) (.classMem R (synCvv)) hyp_werestr_1 p0001
  have p0003 :=
    @gJca ph (.classMem B (synCvv)) (.classMem B (synCvv)) hyp_werestr_3 hyp_werestr_3
  have p0004 := @gXpexg B B (synCvv) (synCvv)
  have p0005 :=
    @gSyl ph (synWa (.classMem B (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCxp B B) (synCvv)) p0003 p0004
  have p0006 :=
    @gJca ph (.classMem R (synCvv)) (.classMem (synCxp B B) (synCvv)) p0002 p0005
  have p0007 := @gInexg R (synCxp B B) (synCvv) (synCvv)
  have p0008 :=
    @gSyl ph (synWa (.classMem R (synCvv)) (.classMem (synCxp B B) (synCvv)))
      (.classMem (synCin R (synCxp B B)) (synCvv)) p0006 p0007
  have p0009 := @gSimpl ph (.classMem (.cv x) B)
  have p0010 := (Nominal.classEqRefl (synCwe))
  have p0011 := @gBreqi R A (synCwe) (synCin (synCstrict) (synCfound)) p0010
  have p0012 := @gBrin R A (synCstrict) (synCfound)
  have p0013 :=
    @gBitri (synWbr R (synCwe) A) (synWbr R (synCin (synCstrict) (synCfound)) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0011 p0012
  have p0014 :=
    @gBiimpi (synWbr R (synCwe) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0013
  have p0015 :=
    @gSyl ph (synWbr R (synCwe) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) hyp_werestr_1 p0014
  have p0016 := @gSimpld ph (synWbr R (synCstrict) A) (synWbr R (synCfound) A) p0015
  have p0017 := @gSopc A R
  have p0018 :=
    @gSylib ph (synWbr R (synCstrict) A)
      (synWa (synWbr R (synCpartial) A) (synWbr R (synCconnex) A)) p0016 p0017
  have p0019 :=
    @gSimpld ph (synWbr R (synCpartial) A) (synWbr R (synCconnex) A) p0018
  have p0020 := @gPorta A R
  have p0021 :=
    @gSylib ph (synWbr R (synCpartial) A)
      (synW3a (synWbr R (synCref) A) (synWbr R (synCtrans) A) (synWbr R (synCantisym) A))
      p0019 p0020
  have p0022 :=
    @gSimp1d ph (synWbr R (synCref) A) (synWbr R (synCtrans) A)
      (synWbr R (synCantisym) A) p0021
  have p0023 :=
    @gSyl (synWa ph (.classMem (.cv x) B)) ph (synWbr R (synCref) A) p0009 p0022
  have p0024 := @gSselda ph B A (.cv x) hyp_werestr_2
  have p0025 := @gRefd (synWa ph (.classMem (.cv x) B)) A R (.cv x) p0023 p0024
  have p0026 := @gSimpr ph (.classMem (.cv x) B)
  have p0028 :=
    @gJca (synWa ph (.classMem (.cv x) B)) (.classMem (.cv x) B) (.classMem (.cv x) B)
      p0026 p0026
  have p0029 := @gBrinxp (.cv x) (.cv x) B B R
  have p0030 :=
    @gSyl (synWa ph (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) B))
      (synWb (synWbr (.cv x) R (.cv x)) (synWbr (.cv x) (synCin R (synCxp B B)) (.cv x)))
      p0028 p0029
  have p0031 :=
    @gMpbid (synWa ph (.classMem (.cv x) B)) (synWbr (.cv x) R (.cv x))
      (synWbr (.cv x) (synCin R (synCxp B B)) (.cv x)) p0025 p0030
  have p0032 :=
    @gSimp1 ph
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)))
  have p0045 :=
    @gSimp2d ph (synWbr R (synCref) A) (synWbr R (synCtrans) A)
      (synWbr R (synCantisym) A) p0021
  have p0046 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      ph (synWbr R (synCtrans) A) p0032 p0045
  have p0048 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      ph (synWss B A) p0032 hyp_werestr_2
  have p0049 :=
    @gSimp2 ph
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)))
  have p0050 := @gSimp1 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0051 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv x) B) p0049 p0050
  have p0052 :=
    @gSseldd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      B A (.cv x) p0048 p0051
  have p0056 := @gSimp2 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0057 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv y) B) p0049 p0056
  have p0058 :=
    @gSseldd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      B A (.cv y) p0048 p0057
  have p0062 := @gSimp3 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0063 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv z) B) p0049 p0062
  have p0064 :=
    @gSseldd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      B A (.cv z) p0048 p0063
  have p0065 :=
    @gSimp3 ph
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)))
  have p0066 :=
    @gSimpld
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)) p0065
  have p0067 := @gBrin (.cv x) (.cv y) R (synCxp B B)
  have p0068 :=
    @gSimplbi (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) (synCxp B B) (.cv y)) p0067
  have p0069 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y)) (synWbr (.cv x) R (.cv y))
      p0066 p0068
  have p0071 :=
    @gSimprd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)) p0065
  have p0072 := @gBrin (.cv y) (.cv z) R (synCxp B B)
  have p0073 :=
    @gSimplbi (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))
      (synWbr (.cv y) R (.cv z)) (synWbr (.cv y) (synCxp B B) (.cv z)) p0072
  have p0074 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)) (synWbr (.cv y) R (.cv z))
      p0071 p0073
  have p0075 :=
    @gTrd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      A R (.cv x) (.cv y) (.cv z) p0046 p0052 p0058 p0064 p0069 p0074
  have p0082 :=
    @gJca
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (.classMem (.cv x) B) (.classMem (.cv z) B) p0051 p0063
  have p0083 := @gBrinxp (.cv x) (.cv z) B B R
  have p0084 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synWa (.classMem (.cv x) B) (.classMem (.cv z) B))
      (synWb (synWbr (.cv x) R (.cv z)) (synWbr (.cv x) (synCin R (synCxp B B)) (.cv z)))
      p0082 p0083
  have p0085 :=
    @gMpbid
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))))
      (synWbr (.cv x) R (.cv z)) (synWbr (.cv x) (synCin R (synCxp B B)) (.cv z))
      p0075 p0084
  have p0086 :=
    @gSimp1 ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)))
  have p0099 :=
    @gSimp3d ph (synWbr R (synCref) A) (synWbr R (synCtrans) A)
      (synWbr R (synCantisym) A) p0021
  have p0100 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      ph (synWbr R (synCantisym) A) p0086 p0099
  have p0102 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      ph (synWss B A) p0086 hyp_werestr_2
  have p0103 :=
    @gSimp2 ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)))
  have p0104 :=
    @gSimpld
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0105 :=
    @gSseldd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      B A (.cv x) p0102 p0104
  have p0109 :=
    @gSimprd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0110 :=
    @gSseldd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      B A (.cv y) p0102 p0109
  have p0111 :=
    @gSimp3 ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)))
  have p0112 :=
    @gSimpld
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)) p0111
  have p0115 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y)) (synWbr (.cv x) R (.cv y))
      p0112 p0068
  have p0117 :=
    @gSimprd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)) p0111
  have p0118 := @gBrin (.cv y) (.cv x) R (synCxp B B)
  have p0119 :=
    @gSimplbi (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))
      (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) (synCxp B B) (.cv x)) p0118
  have p0120 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)) (synWbr (.cv y) R (.cv x))
      p0117 p0119
  have p0121 :=
    @gAntid
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))))
      A R (.cv x) (.cv y) p0100 p0105 p0110 p0115 p0120
  have p0122 := @gSimp1 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0132 :=
    @gSimprd ph (synWbr R (synCpartial) A) (synWbr R (synCconnex) A) p0018
  have p0133 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph
      (synWbr R (synCconnex) A) p0122 p0132
  have p0135 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph (synWss B A) p0122
      hyp_werestr_2
  have p0136 := @gSimp2 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0137 :=
    @gSseldd (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B A (.cv x) p0135
      p0136
  have p0140 := @gSimp3 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0141 :=
    @gSseldd (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B A (.cv y) p0135
      p0140
  have p0142 :=
    @gConnexd (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) A R (.cv x)
      (.cv y) p0133 p0137 p0141
  have p0145 :=
    @gJca (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B)
      (.classMem (.cv y) B) p0136 p0140
  have p0146 := @gBrinxp (.cv x) (.cv y) B B R
  have p0147 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWb (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y)))
      p0145 p0146
  have p0150 :=
    @gJca (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv y) B)
      (.classMem (.cv x) B) p0140 p0136
  have p0151 := @gBrinxp (.cv y) (.cv x) B B R
  have p0152 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (.classMem (.cv y) B) (.classMem (.cv x) B))
      (synWb (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)))
      p0150 p0151
  have p0153 :=
    @gOrbi12d (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
      (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x))
      p0147 p0152
  have p0154 :=
    @gMpbid (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWo (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)))
      p0142 p0153
  have p0155_e04_recanon :
    Nominal.NPrf
      (.imp (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (synWa (synWbr (.cv x) (synCin R (synCxp B B)) (.cv y))
            (synWbr (.cv y) (synCin R (synCxp B B)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0121
  have p0155 :=
    @gSod ph x y z B (synCin R (synCxp B B)) (synCvv) (synCvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0008
      hyp_werestr_3 p0031 p0085 p0155_e04_recanon p0154
  have p0165 := @gSimpl ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0166 := (Nominal.classEqRefl (synCwe))
  have p0167 := @gBreqi R A (synCwe) (synCin (synCstrict) (synCfound)) p0166
  have p0168 := @gBrin R A (synCstrict) (synCfound)
  have p0169 :=
    @gBitri (synWbr R (synCwe) A) (synWbr R (synCin (synCstrict) (synCfound)) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0167 p0168
  have p0170 :=
    @gBiimpi (synWbr R (synCwe) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0169
  have p0171 :=
    @gSyl ph (synWbr R (synCwe) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) hyp_werestr_1 p0170
  have p0172 := @gSimprd ph (synWbr R (synCstrict) A) (synWbr R (synCfound) A) p0171
  have p0173 :=
    @gSyl (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) ph
      (synWbr R (synCfound) A) p0165 p0172
  have p0174 := @gVex x
  have p0175 :=
    @gA1i (.classMem (.cv x) (synCvv))
      (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) p0174
  have p0176 := @gSimpr ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0177 :=
    @gSimpld (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWss (.cv x) B) (synWne (.cv x) (synC0)) p0176
  have p0178 := @gSimpl ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0179 :=
    @gSyl (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) ph
      (synWss B A) p0178 hyp_werestr_2
  have p0180 :=
    @gSstrd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) (.cv x) B
      A p0177 p0179
  have p0181 := @gSimpr ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0182 :=
    @gSimprd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWss (.cv x) B) (synWne (.cv x) (synC0)) p0181
  have p0183 :=
    @gFrd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) z y A R
      (synCvv) (.cv x) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 p0173 p0175 p0180 p0182
  have p0184 := @gBrin (.cv y) (.cv z) R (synCxp B B)
  have p0185 :=
    @gSimplbi (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))
      (synWbr (.cv y) R (.cv z)) (synWbr (.cv y) (synCxp B B) (.cv z)) p0184
  have p0186 :=
    @gImim1i (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))
      (synWbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)) p0185
  have p0187 :=
    @gA1i
      (.imp (.imp (synWbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))
        (.imp (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)) (.classEq (.cv y) (.cv z))))
      (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) p0186
  have p0188 :=
    @gRalimdv (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (.imp (synWbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)) (.classEq (.cv y) (.cv z)))
      y (.cv x) dv_cache_0018 p0187
  have p0189 :=
    @gReximdv (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWral y (.cv x) (.imp (synWbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z))))
      (synWral y (.cv x) (.imp (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))
          (.classEq (.cv y) (.cv z))))
      z (.cv x) dv_cache_0019 p0188
  have p0190_e00_recanon :
    Nominal.NPrf
      (.imp (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
        (synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWrex synWex synWral synWbr synCop synCun synCnin synWnan
          synCcompl
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0183
  have p0190 :=
    @gMpd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0190_e00_recanon p0189
  have p0191_e02_recanon :
    Nominal.NPrf
      (.imp (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
        (synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) (synCin R (synCxp B B)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWrex synWex synWral synWbr synCop synCun synCnin synWnan
          synCcompl synCin synCxp synCopab
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0190
  have p0191 :=
    @gFrrd ph x y z B (synCin R (synCxp B B)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0008 hyp_werestr_3 p0191_e02_recanon
  have p0192 :=
    @gJca ph (synWbr (synCin R (synCxp B B)) (synCstrict) B)
      (synWbr (synCin R (synCxp B B)) (synCfound) B) p0155 p0191
  have p0194 :=
    @gBreqi (synCin R (synCxp B B)) B (synCwe) (synCin (synCstrict) (synCfound))
      p0010
  have p0195 := @gBrin (synCin R (synCxp B B)) B (synCstrict) (synCfound)
  have p0196 :=
    @gBitri (synWbr (synCin R (synCxp B B)) (synCwe) B)
      (synWbr (synCin R (synCxp B B)) (synCin (synCstrict) (synCfound)) B)
      (synWa (synWbr (synCin R (synCxp B B)) (synCstrict) B)
        (synWbr (synCin R (synCxp B B)) (synCfound) B))
      p0194 p0195
  have p0197 :=
    @gA1i
      (synWb (synWbr (synCin R (synCxp B B)) (synCwe) B)
        (synWa (synWbr (synCin R (synCxp B B)) (synCstrict) B)
          (synWbr (synCin R (synCxp B B)) (synCfound) B)))
      ph p0196
  have p0198 :=
    @gMpbird ph (synWbr (synCin R (synCxp B B)) (synCwe) B)
      (synWa (synWbr (synCin R (synCxp B B)) (synCstrict) B)
        (synWbr (synCin R (synCxp B B)) (synCfound) B))
      p0192 p0197
  exact p0198


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part044`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_werestrndv`. -/
@[expose]
noncomputable def gWerestrndv (ph : Wff) (B : Class) (D : Class) (S : Class)
    (hyp_werestrndv_1 : Nominal.NPrf (.imp ph (synWbr S (synCwe) D)))
    (hyp_werestrndv_2 : Nominal.NPrf (.imp ph (synWss B D)))
    (hyp_werestrndv_3 : Nominal.NPrf (.imp ph (.classMem B (synCvv)))) :
    Nominal.NPrf (.imp ph (synWbr (synCin S (synCxp B B)) (synCwe) B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ B.fv ∪ D.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCin S (synCxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_S, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCin S (synCxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_S, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synCin S (synCxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_z_not_S, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0013 : z ∉ (S).fv :=
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
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0014 : y ∉ (S).fv :=
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
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0017 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0018 :
    y ∉ ((synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_ph, fresh_y_ne_x, fresh_y_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉ ((synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, fresh_z_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gBrex S D (synCwe)
  have p0001 :=
    @gSimpld (synWbr S (synCwe) D) (.classMem S (synCvv)) (.classMem D (synCvv))
      p0000
  have p0002 :=
    @gSyl ph (synWbr S (synCwe) D) (.classMem S (synCvv)) hyp_werestrndv_1 p0001
  have p0003 :=
    @gJca ph (.classMem B (synCvv)) (.classMem B (synCvv)) hyp_werestrndv_3
      hyp_werestrndv_3
  have p0004 := @gXpexg B B (synCvv) (synCvv)
  have p0005 :=
    @gSyl ph (synWa (.classMem B (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCxp B B) (synCvv)) p0003 p0004
  have p0006 :=
    @gJca ph (.classMem S (synCvv)) (.classMem (synCxp B B) (synCvv)) p0002 p0005
  have p0007 := @gInexg S (synCxp B B) (synCvv) (synCvv)
  have p0008 :=
    @gSyl ph (synWa (.classMem S (synCvv)) (.classMem (synCxp B B) (synCvv)))
      (.classMem (synCin S (synCxp B B)) (synCvv)) p0006 p0007
  have p0009 := @gSimpl ph (.classMem (.cv x) B)
  have p0010 := (Nominal.classEqRefl (synCwe))
  have p0011 := @gBreqi S D (synCwe) (synCin (synCstrict) (synCfound)) p0010
  have p0012 := @gBrin S D (synCstrict) (synCfound)
  have p0013 :=
    @gBitri (synWbr S (synCwe) D) (synWbr S (synCin (synCstrict) (synCfound)) D)
      (synWa (synWbr S (synCstrict) D) (synWbr S (synCfound) D)) p0011 p0012
  have p0014 :=
    @gBiimpi (synWbr S (synCwe) D)
      (synWa (synWbr S (synCstrict) D) (synWbr S (synCfound) D)) p0013
  have p0015 :=
    @gSyl ph (synWbr S (synCwe) D)
      (synWa (synWbr S (synCstrict) D) (synWbr S (synCfound) D)) hyp_werestrndv_1
      p0014
  have p0016 := @gSimpld ph (synWbr S (synCstrict) D) (synWbr S (synCfound) D) p0015
  have p0017 := @gSopc D S
  have p0018 :=
    @gSylib ph (synWbr S (synCstrict) D)
      (synWa (synWbr S (synCpartial) D) (synWbr S (synCconnex) D)) p0016 p0017
  have p0019 :=
    @gSimpld ph (synWbr S (synCpartial) D) (synWbr S (synCconnex) D) p0018
  have p0020 := @gPorta D S
  have p0021 :=
    @gSylib ph (synWbr S (synCpartial) D)
      (synW3a (synWbr S (synCref) D) (synWbr S (synCtrans) D) (synWbr S (synCantisym) D))
      p0019 p0020
  have p0022 :=
    @gSimp1d ph (synWbr S (synCref) D) (synWbr S (synCtrans) D)
      (synWbr S (synCantisym) D) p0021
  have p0023 :=
    @gSyl (synWa ph (.classMem (.cv x) B)) ph (synWbr S (synCref) D) p0009 p0022
  have p0024 := @gSselda ph B D (.cv x) hyp_werestrndv_2
  have p0025 := @gRefd (synWa ph (.classMem (.cv x) B)) D S (.cv x) p0023 p0024
  have p0026 := @gSimpr ph (.classMem (.cv x) B)
  have p0028 :=
    @gJca (synWa ph (.classMem (.cv x) B)) (.classMem (.cv x) B) (.classMem (.cv x) B)
      p0026 p0026
  have p0029 := @gBrinxp (.cv x) (.cv x) B B S
  have p0030 :=
    @gSyl (synWa ph (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) B))
      (synWb (synWbr (.cv x) S (.cv x)) (synWbr (.cv x) (synCin S (synCxp B B)) (.cv x)))
      p0028 p0029
  have p0031 :=
    @gMpbid (synWa ph (.classMem (.cv x) B)) (synWbr (.cv x) S (.cv x))
      (synWbr (.cv x) (synCin S (synCxp B B)) (.cv x)) p0025 p0030
  have p0032 :=
    @gSimp1 ph
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)))
  have p0045 :=
    @gSimp2d ph (synWbr S (synCref) D) (synWbr S (synCtrans) D)
      (synWbr S (synCantisym) D) p0021
  have p0046 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      ph (synWbr S (synCtrans) D) p0032 p0045
  have p0048 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      ph (synWss B D) p0032 hyp_werestrndv_2
  have p0049 :=
    @gSimp2 ph
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)))
  have p0050 := @gSimp1 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0051 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv x) B) p0049 p0050
  have p0052 :=
    @gSseldd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      B D (.cv x) p0048 p0051
  have p0056 := @gSimp2 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0057 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv y) B) p0049 p0056
  have p0058 :=
    @gSseldd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      B D (.cv y) p0048 p0057
  have p0062 := @gSimp3 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0063 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv z) B) p0049 p0062
  have p0064 :=
    @gSseldd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      B D (.cv z) p0048 p0063
  have p0065 :=
    @gSimp3 ph
      (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)))
  have p0066 :=
    @gSimpld
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)) p0065
  have p0067 := @gBrin (.cv x) (.cv y) S (synCxp B B)
  have p0068 :=
    @gSimplbi (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
      (synWbr (.cv x) S (.cv y)) (synWbr (.cv x) (synCxp B B) (.cv y)) p0067
  have p0069 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y)) (synWbr (.cv x) S (.cv y))
      p0066 p0068
  have p0071 :=
    @gSimprd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)) p0065
  have p0072 := @gBrin (.cv y) (.cv z) S (synCxp B B)
  have p0073 :=
    @gSimplbi (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))
      (synWbr (.cv y) S (.cv z)) (synWbr (.cv y) (synCxp B B) (.cv z)) p0072
  have p0074 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)) (synWbr (.cv y) S (.cv z))
      p0071 p0073
  have p0075 :=
    @gTrd
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      D S (.cv x) (.cv y) (.cv z) p0046 p0052 p0058 p0064 p0069 p0074
  have p0082 :=
    @gJca
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (.classMem (.cv x) B) (.classMem (.cv z) B) p0051 p0063
  have p0083 := @gBrinxp (.cv x) (.cv z) B B S
  have p0084 :=
    @gSyl
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synWa (.classMem (.cv x) B) (.classMem (.cv z) B))
      (synWb (synWbr (.cv x) S (.cv z)) (synWbr (.cv x) (synCin S (synCxp B B)) (.cv z)))
      p0082 p0083
  have p0085 :=
    @gMpbid
      (synW3a ph (synW3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))))
      (synWbr (.cv x) S (.cv z)) (synWbr (.cv x) (synCin S (synCxp B B)) (.cv z))
      p0075 p0084
  have p0086 :=
    @gSimp1 ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)))
  have p0099 :=
    @gSimp3d ph (synWbr S (synCref) D) (synWbr S (synCtrans) D)
      (synWbr S (synCantisym) D) p0021
  have p0100 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      ph (synWbr S (synCantisym) D) p0086 p0099
  have p0102 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      ph (synWss B D) p0086 hyp_werestrndv_2
  have p0103 :=
    @gSimp2 ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)))
  have p0104 :=
    @gSimpld
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0105 :=
    @gSseldd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      B D (.cv x) p0102 p0104
  have p0109 :=
    @gSimprd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0110 :=
    @gSseldd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      B D (.cv y) p0102 p0109
  have p0111 :=
    @gSimp3 ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)))
  have p0112 :=
    @gSimpld
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)) p0111
  have p0115 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y)) (synWbr (.cv x) S (.cv y))
      p0112 p0068
  have p0117 :=
    @gSimprd
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
      (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)) p0111
  have p0118 := @gBrin (.cv y) (.cv x) S (synCxp B B)
  have p0119 :=
    @gSimplbi (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))
      (synWbr (.cv y) S (.cv x)) (synWbr (.cv y) (synCxp B B) (.cv x)) p0118
  have p0120 :=
    @gSyl
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)) (synWbr (.cv y) S (.cv x))
      p0117 p0119
  have p0121 :=
    @gAntid
      (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
          (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))))
      D S (.cv x) (.cv y) p0100 p0105 p0110 p0115 p0120
  have p0122 := @gSimp1 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0132 :=
    @gSimprd ph (synWbr S (synCpartial) D) (synWbr S (synCconnex) D) p0018
  have p0133 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph
      (synWbr S (synCconnex) D) p0122 p0132
  have p0135 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph (synWss B D) p0122
      hyp_werestrndv_2
  have p0136 := @gSimp2 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0137 :=
    @gSseldd (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B D (.cv x) p0135
      p0136
  have p0140 := @gSimp3 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0141 :=
    @gSseldd (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B D (.cv y) p0135
      p0140
  have p0142 :=
    @gConnexd (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) D S (.cv x)
      (.cv y) p0133 p0137 p0141
  have p0145 :=
    @gJca (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B)
      (.classMem (.cv y) B) p0136 p0140
  have p0146 := @gBrinxp (.cv x) (.cv y) B B S
  have p0147 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWb (synWbr (.cv x) S (.cv y)) (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y)))
      p0145 p0146
  have p0150 :=
    @gJca (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv y) B)
      (.classMem (.cv x) B) p0140 p0136
  have p0151 := @gBrinxp (.cv y) (.cv x) B B S
  have p0152 :=
    @gSyl (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWa (.classMem (.cv y) B) (.classMem (.cv x) B))
      (synWb (synWbr (.cv y) S (.cv x)) (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)))
      p0150 p0151
  have p0153 :=
    @gOrbi12d (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (.cv x) S (.cv y)) (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
      (synWbr (.cv y) S (.cv x)) (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x))
      p0147 p0152
  have p0154 :=
    @gMpbid (synW3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWo (synWbr (.cv x) S (.cv y)) (synWbr (.cv y) S (.cv x)))
      (synWo (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
        (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)))
      p0142 p0153
  have p0155_e04_recanon :
    Nominal.NPrf
      (.imp (synW3a ph (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (synWa (synWbr (.cv x) (synCin S (synCxp B B)) (.cv y))
            (synWbr (.cv y) (synCin S (synCxp B B)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0121
  have p0155 :=
    @gSod ph x y z B (synCin S (synCxp B B)) (synCvv) (synCvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0008
      hyp_werestrndv_3 p0031 p0085 p0155_e04_recanon p0154
  have p0165 := @gSimpl ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0166 := (Nominal.classEqRefl (synCwe))
  have p0167 := @gBreqi S D (synCwe) (synCin (synCstrict) (synCfound)) p0166
  have p0168 := @gBrin S D (synCstrict) (synCfound)
  have p0169 :=
    @gBitri (synWbr S (synCwe) D) (synWbr S (synCin (synCstrict) (synCfound)) D)
      (synWa (synWbr S (synCstrict) D) (synWbr S (synCfound) D)) p0167 p0168
  have p0170 :=
    @gBiimpi (synWbr S (synCwe) D)
      (synWa (synWbr S (synCstrict) D) (synWbr S (synCfound) D)) p0169
  have p0171 :=
    @gSyl ph (synWbr S (synCwe) D)
      (synWa (synWbr S (synCstrict) D) (synWbr S (synCfound) D)) hyp_werestrndv_1
      p0170
  have p0172 := @gSimprd ph (synWbr S (synCstrict) D) (synWbr S (synCfound) D) p0171
  have p0173 :=
    @gSyl (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) ph
      (synWbr S (synCfound) D) p0165 p0172
  have p0174 := @gVex x
  have p0175 :=
    @gA1i (.classMem (.cv x) (synCvv))
      (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) p0174
  have p0176 := @gSimpr ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0177 :=
    @gSimpld (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWss (.cv x) B) (synWne (.cv x) (synC0)) p0176
  have p0178 := @gSimpl ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0179 :=
    @gSyl (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) ph
      (synWss B D) p0178 hyp_werestrndv_2
  have p0180 :=
    @gSstrd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) (.cv x) B
      D p0177 p0179
  have p0181 := @gSimpr ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))
  have p0182 :=
    @gSimprd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWss (.cv x) B) (synWne (.cv x) (synC0)) p0181
  have p0183 :=
    @gFrd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) z y D S
      (synCvv) (.cv x) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 p0173 p0175 p0180 p0182
  have p0184 := @gBrin (.cv y) (.cv z) S (synCxp B B)
  have p0185 :=
    @gSimplbi (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))
      (synWbr (.cv y) S (.cv z)) (synWbr (.cv y) (synCxp B B) (.cv z)) p0184
  have p0186 :=
    @gImim1i (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))
      (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)) p0185
  have p0187 :=
    @gA1i
      (.imp (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))
        (.imp (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)) (.classEq (.cv y) (.cv z))))
      (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0)))) p0186
  have p0188 :=
    @gRalimdv (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)) (.classEq (.cv y) (.cv z)))
      y (.cv x) dv_cache_0018 p0187
  have p0189 :=
    @gReximdv (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWral y (.cv x) (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))
      (synWral y (.cv x) (.imp (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))
          (.classEq (.cv y) (.cv z))))
      z (.cv x) dv_cache_0019 p0188
  have p0190_e00_recanon :
    Nominal.NPrf
      (.imp (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
        (synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWrex synWex synWral synWbr synCop synCun synCnin synWnan
          synCcompl
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0183
  have p0190 :=
    @gMpd (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0190_e00_recanon p0189
  have p0191_e02_recanon :
    Nominal.NPrf
      (.imp (synWa ph (synWa (synWss (.cv x) B) (synWne (.cv x) (synC0))))
        (synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) (synCin S (synCxp B B)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWrex synWex synWral synWbr synCop synCun synCnin synWnan
          synCcompl synCin synCxp synCopab
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0190
  have p0191 :=
    @gFrrd ph x y z B (synCin S (synCxp B B)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0008 hyp_werestrndv_3 p0191_e02_recanon
  have p0192 :=
    @gJca ph (synWbr (synCin S (synCxp B B)) (synCstrict) B)
      (synWbr (synCin S (synCxp B B)) (synCfound) B) p0155 p0191
  have p0194 :=
    @gBreqi (synCin S (synCxp B B)) B (synCwe) (synCin (synCstrict) (synCfound))
      p0010
  have p0195 := @gBrin (synCin S (synCxp B B)) B (synCstrict) (synCfound)
  have p0196 :=
    @gBitri (synWbr (synCin S (synCxp B B)) (synCwe) B)
      (synWbr (synCin S (synCxp B B)) (synCin (synCstrict) (synCfound)) B)
      (synWa (synWbr (synCin S (synCxp B B)) (synCstrict) B)
        (synWbr (synCin S (synCxp B B)) (synCfound) B))
      p0194 p0195
  have p0197 :=
    @gA1i
      (synWb (synWbr (synCin S (synCxp B B)) (synCwe) B)
        (synWa (synWbr (synCin S (synCxp B B)) (synCstrict) B)
          (synWbr (synCin S (synCxp B B)) (synCfound) B)))
      ph p0196
  have p0198 :=
    @gMpbird ph (synWbr (synCin S (synCxp B B)) (synCwe) B)
      (synWa (synWbr (synCin S (synCxp B B)) (synCstrict) B)
        (synWbr (synCin S (synCxp B B)) (synCfound) B))
      p0192 p0197
  exact p0198

/-- Checked nominal proof certificate identified upstream as `g_westrseg`. -/
@[expose]
noncomputable def gWestrseg (x : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWbr (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCwe)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gSimpl (synWbr R (synCwe) D) (.classMem (.cv x) D)
  have p0001 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0002 :=
    @gA1i
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) p0001
  have p0004 := @gBrex R D (synCwe)
  have p0005 :=
    @gSyl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWbr R (synCwe) D)
      (synWa (.classMem R (synCvv)) (.classMem D (synCvv))) p0000 p0004
  have p0006 :=
    @gSimprd (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem R (synCvv)) (.classMem D (synCvv)) p0005
  have p0010 :=
    @gSimpld (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem R (synCvv)) (.classMem D (synCvv)) p0005
  have p0011 := @gIdex
  have p0012 :=
    @gA1i (.classMem (synCid) (synCvv))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) p0011
  have p0013 :=
    @gJca (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (.classMem R (synCvv))
      (.classMem (synCid) (synCvv)) p0010 p0012
  have p0014 := @gDifexg R (synCid) (synCvv) (synCvv)
  have p0015 :=
    @gSyl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem R (synCvv)) (.classMem (synCid) (synCvv)))
      (.classMem (synCdif R (synCid)) (synCvv)) p0013 p0014
  have p0016 := @gCnvexg (synCdif R (synCid)) (synCvv)
  have p0017 :=
    @gSyl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem (synCdif R (synCid)) (synCvv))
      (.classMem (synCcnv (synCdif R (synCid))) (synCvv)) p0015 p0016
  have p0018 := @gSnex (.cv x)
  have p0019 :=
    @gA1i (.classMem (synCsn (.cv x)) (synCvv))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @gJca (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem (synCcnv (synCdif R (synCid))) (synCvv))
      (.classMem (synCsn (.cv x)) (synCvv)) p0017 p0019
  have p0021 :=
    @gImaexg (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) (synCvv) (synCvv)
  have p0022 :=
    @gSyl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem (synCcnv (synCdif R (synCid))) (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)))
      (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv))
      p0020 p0021
  have p0023 :=
    @gJca (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (.classMem D (synCvv))
      (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv))
      p0006 p0022
  have p0024 :=
    @gInexg D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv)
      (synCvv)
  have p0025 :=
    @gSyl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem D (synCvv))
        (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv)))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      p0023 p0024
  have p0026 :=
    @gWerestr (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) D
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) R
      dv_cache_0001 p0000 p0002 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_westrsegndv`. -/
@[expose]
noncomputable def gWestrsegndv (x : Var) (D : Class) (S : Class) :
    Nominal.NPrf
      (.imp (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D)) (synWbr (synCin S (synCxp
              (synCin D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          (synCwe)
          (synCin D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) :=
  by
  have p0000 := @gSimpl (synWbr S (synCwe) D) (.classMem (.cv x) D)
  have p0001 := @gInss1 D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))
  have p0002 :=
    @gA1i
      (synWss (synCin D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) D)
      (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D)) p0001
  have p0004 := @gBrex S D (synCwe)
  have p0005 :=
    @gSyl (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D)) (synWbr S (synCwe) D)
      (synWa (.classMem S (synCvv)) (.classMem D (synCvv))) p0000 p0004
  have p0006 :=
    @gSimprd (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (.classMem S (synCvv)) (.classMem D (synCvv)) p0005
  have p0010 :=
    @gSimpld (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (.classMem S (synCvv)) (.classMem D (synCvv)) p0005
  have p0011 := @gIdex
  have p0012 :=
    @gA1i (.classMem (synCid) (synCvv))
      (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D)) p0011
  have p0013 :=
    @gJca (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D)) (.classMem S (synCvv))
      (.classMem (synCid) (synCvv)) p0010 p0012
  have p0014 := @gDifexg S (synCid) (synCvv) (synCvv)
  have p0015 :=
    @gSyl (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem S (synCvv)) (.classMem (synCid) (synCvv)))
      (.classMem (synCdif S (synCid)) (synCvv)) p0013 p0014
  have p0016 := @gCnvexg (synCdif S (synCid)) (synCvv)
  have p0017 :=
    @gSyl (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (.classMem (synCdif S (synCid)) (synCvv))
      (.classMem (synCcnv (synCdif S (synCid))) (synCvv)) p0015 p0016
  have p0018 := @gSnex (.cv x)
  have p0019 :=
    @gA1i (.classMem (synCsn (.cv x)) (synCvv))
      (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @gJca (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (.classMem (synCcnv (synCdif S (synCid))) (synCvv))
      (.classMem (synCsn (.cv x)) (synCvv)) p0017 p0019
  have p0021 :=
    @gImaexg (synCcnv (synCdif S (synCid))) (synCsn (.cv x)) (synCvv) (synCvv)
  have p0022 :=
    @gSyl (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem (synCcnv (synCdif S (synCid))) (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)))
      (.classMem (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))) (synCvv))
      p0020 p0021
  have p0023 :=
    @gJca (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D)) (.classMem D (synCvv))
      (.classMem (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))) (synCvv))
      p0006 p0022
  have p0024 :=
    @gInexg D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))) (synCvv)
      (synCvv)
  have p0025 :=
    @gSyl (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem D (synCvv))
        (.classMem (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))) (synCvv)))
      (.classMem (synCin D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
        (synCvv))
      p0023 p0024
  have p0026 :=
    @gWerestrndv (synWa (synWbr S (synCwe) D) (.classMem (.cv x) D))
      (synCin D (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) D S p0000
      p0002 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_strictsegnel`. -/
@[expose]
noncomputable def gStrictsegnel (x : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.neg (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) :=
  by
  have p0000 := @gEqid (.cv x)
  have p0001 := @gVex x
  have p0002 := @gIdeq (.cv x) (.cv x) p0001
  have p0003 :=
    @gMpbir (synWbr (.cv x) (synCid) (.cv x)) (.classEq (.cv x) (.cv x)) p0000 p0002
  have p0004 := @gNotnoti (synWbr (.cv x) (synCid) (.cv x)) p0003
  have p0005 :=
    @gIntnan (.neg (synWbr (.cv x) (synCid) (.cv x))) (synWbr (.cv x) R (.cv x)) p0004
  have p0006 := @gBrdif (.cv x) (.cv x) R (synCid)
  have p0007 :=
    @gMtbir (synWbr (.cv x) (synCdif R (synCid)) (.cv x))
      (synWa (synWbr (.cv x) R (.cv x)) (.neg (synWbr (.cv x) (synCid) (.cv x))))
      p0005 p0006
  have p0008 := @gEliniseg (synCdif R (synCid)) (.cv x) (.cv x)
  have p0009 :=
    @gMtbir
      (.classMem (.cv x) (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synWbr (.cv x) (synCdif R (synCid)) (.cv x)) p0007 p0008
  have p0010 :=
    @gIntnan
      (.classMem (.cv x) (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (.classMem (.cv x) D) p0009
  have p0011 :=
    @gElin (.cv x) D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0012 :=
    @gMtbir
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv x)
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0010 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part045`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_elstrictseg`. -/
@[expose]
noncomputable def gElstrictseg (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (synWb (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synWa (.classMem (.cv y) D)
          (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))) :=
  by
  have p0000 :=
    @gElin (.cv y) D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0001 := @gEliniseg (synCdif R (synCid)) (.cv x) (.cv y)
  have p0002 := @gBrdif (.cv y) (.cv x) R (synCid)
  have p0003 := @gVex x
  have p0004 := @gIdeq (.cv y) (.cv x) p0003
  have p0005 :=
    @gNotbii (synWbr (.cv y) (synCid) (.cv x)) (.classEq (.cv y) (.cv x)) p0004
  have p0006 := (Nominal.biimpRefl (synWne (.cv y) (.cv x)))
  have p0007 :=
    @gBitr4i (.neg (synWbr (.cv y) (synCid) (.cv x))) (.neg (.classEq (.cv y) (.cv x)))
      (synWne (.cv y) (.cv x)) p0005 p0006
  have p0008 :=
    @gAnbi2i (.neg (synWbr (.cv y) (synCid) (.cv x))) (synWne (.cv y) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0007
  have p0009 :=
    @gBitri (synWbr (.cv y) (synCdif R (synCid)) (.cv x))
      (synWa (synWbr (.cv y) R (.cv x)) (.neg (synWbr (.cv y) (synCid) (.cv x))))
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))) p0002 p0008
  have p0010 :=
    @gBitri
      (.classMem (.cv y) (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synWbr (.cv y) (synCdif R (synCid)) (.cv x))
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))) p0001 p0009
  have p0011 :=
    @gAnbi2i
      (.classMem (.cv y) (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))) (.classMem (.cv y) D)
      p0010
  have p0012 :=
    @gBitri
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv y)
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0000 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_strictsegdown`. -/
@[expose]
noncomputable def gStrictsegdown (x : Var) (y : Var) (z : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) :=
  by
  have p0000 :=
    @gSimp2 (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv z) D))
      (synWbr (.cv z) R (.cv y))
  have p0001 :=
    @gSimprd
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z) D) p0000
  have p0002 :=
    @gSimp1 (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv z) D))
      (synWbr (.cv z) R (.cv y))
  have p0003 :=
    @gSimpld
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCwe) D) (.classMem (.cv x) D) p0002
  have p0004 := (Nominal.classEqRefl (synCwe))
  have p0005 := @gBreqi R D (synCwe) (synCin (synCstrict) (synCfound)) p0004
  have p0006 := @gBrin R D (synCstrict) (synCfound)
  have p0007 :=
    @gBitri (synWbr R (synCwe) D) (synWbr R (synCin (synCstrict) (synCfound)) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0005 p0006
  have p0008 :=
    @gBiimpi (synWbr R (synCwe) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0007
  have p0009 :=
    @gSyl
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCwe) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0003 p0008
  have p0010 :=
    @gSimpld
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCstrict) D) (synWbr R (synCfound) D) p0009
  have p0011 := @gSopc D R
  have p0012 :=
    @gSylib
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCstrict) D)
      (synWa (synWbr R (synCpartial) D) (synWbr R (synCconnex) D)) p0010 p0011
  have p0013 :=
    @gSimpld
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCpartial) D) (synWbr R (synCconnex) D) p0012
  have p0014 := @gPorta D R
  have p0015 :=
    @gSylib
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCpartial) D)
      (synW3a (synWbr R (synCref) D) (synWbr R (synCtrans) D) (synWbr R (synCantisym) D))
      p0013 p0014
  have p0016 :=
    @gSimp2d
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCref) D) (synWbr R (synCtrans) D) (synWbr R (synCantisym) D)
      p0015
  have p0020 :=
    @gSimpld
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z) D) p0000
  have p0021 :=
    @gElin (.cv y) D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0022 := @gEliniseg (synCdif R (synCid)) (.cv x) (.cv y)
  have p0023 := @gBrdif (.cv y) (.cv x) R (synCid)
  have p0024 := @gVex x
  have p0025 := @gIdeq (.cv y) (.cv x) p0024
  have p0026 :=
    @gNotbii (synWbr (.cv y) (synCid) (.cv x)) (.classEq (.cv y) (.cv x)) p0025
  have p0027 := (Nominal.biimpRefl (synWne (.cv y) (.cv x)))
  have p0028 :=
    @gBitr4i (.neg (synWbr (.cv y) (synCid) (.cv x))) (.neg (.classEq (.cv y) (.cv x)))
      (synWne (.cv y) (.cv x)) p0026 p0027
  have p0029 :=
    @gAnbi2i (.neg (synWbr (.cv y) (synCid) (.cv x))) (synWne (.cv y) (.cv x))
      (synWbr (.cv y) R (.cv x)) p0028
  have p0030 :=
    @gBitri (synWbr (.cv y) (synCdif R (synCid)) (.cv x))
      (synWa (synWbr (.cv y) R (.cv x)) (.neg (synWbr (.cv y) (synCid) (.cv x))))
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))) p0023 p0029
  have p0031 :=
    @gBitri
      (.classMem (.cv y) (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synWbr (.cv y) (synCdif R (synCid)) (.cv x))
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))) p0022 p0030
  have p0032 :=
    @gAnbi2i
      (.classMem (.cv y) (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))) (.classMem (.cv y) D)
      p0031
  have p0033 :=
    @gBitri
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv y)
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0021 p0032
  have p0034 :=
    @gBiimpi
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0033
  have p0035 :=
    @gSyl
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0020 p0034
  have p0036 :=
    @gSimpld
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv y) D) (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
      p0035
  have p0038 :=
    @gSimprd
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCwe) D) (.classMem (.cv x) D) p0002
  have p0039 :=
    @gSimp3 (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv z) D))
      (synWbr (.cv z) R (.cv y))
  have p0057 :=
    @gSimprd
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv y) D) (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
      p0035
  have p0058 :=
    @gSimpld
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)) p0057
  have p0059 :=
    @gTrd
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      D R (.cv z) (.cv y) (.cv x) p0016 p0001 p0036 p0038 p0039 p0058
  have p0078 :=
    @gSimprd
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)) p0057
  have p0079 :=
    @gSimpl
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classEq (.cv z) (.cv x))
  have p0094 :=
    @gSimp3d
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCref) D) (synWbr R (synCtrans) D) (synWbr R (synCantisym) D)
      p0015
  have p0095 :=
    @gSyl
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr R (synCantisym) D) p0079 p0094
  have p0099 :=
    @gSyl
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv x) D) p0079 p0038
  have p0119 :=
    @gSyl
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv y) D) p0079 p0036
  have p0120 :=
    @gSimpr
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classEq (.cv z) (.cv x))
  have p0123 :=
    @gSyl
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr (.cv z) R (.cv y)) p0079 p0039
  have p0124 :=
    @gEqbrtrrd
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (.cv z) (.cv x) (.cv y) R p0120 p0123
  have p0145 :=
    @gSyl
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr (.cv y) R (.cv x)) p0079 p0058
  have p0146 :=
    @gAntid
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      D R (.cv x) (.cv y) p0095 p0099 p0119 p0124 p0145
  have p0147 :=
    @gEqcomd
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (.cv x) (.cv y) p0146
  have p0149 :=
    @gBiimpi (synWne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))) p0027
  have p0150 :=
    @gA1i (.imp (synWne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))))
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      p0149
  have p0151 :=
    @gMt2d
      (synWa (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa
            (.classMem (.cv y)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (synWne (.cv y) (.cv x)) (.classEq (.cv y) (.cv x)) p0147 p0150
  have p0152 :=
    @gEx
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classEq (.cv z) (.cv x)) (.neg (synWne (.cv y) (.cv x))) p0151
  have p0153 :=
    @gNecon2ad
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWne (.cv y) (.cv x)) (.cv z) (.cv x) p0152
  have p0154 :=
    @gMpd
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWne (.cv y) (.cv x)) (synWne (.cv z) (.cv x)) p0078 p0153
  have p0155 :=
    @gJca
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0059 p0154
  have p0156 :=
    @gJca
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0001 p0155
  have p0157 := @gElstrictseg x z D R
  have p0158 :=
    @gBiimpri
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0157
  have p0159 :=
    @gSyl
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0156 p0158
  exact p0159


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part046`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_strictsegnoiso`. -/
@[expose]
noncomputable def gStrictsegnoiso (x : Var) (D : Class) (R : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
          (.classMem H (synCvv))) (.neg (synWiso H R (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) D
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ H.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_H : w ∉ H.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have dv_cache_0001 : w ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((synCin H R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_w_not_H, fresh_w_not_R, or_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((synWa (synWfn H D) (.classMem (.cv x) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0004 : w ∉ ((synCfv H (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, or_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((synWbr (.cv x) R (synCfv H (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, fresh_w_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0007 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synCdif D (synCdm (synCin H R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_H, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synCdif D (synCdm (synCin H R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_z_not_D, fresh_z_not_H, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((synWa (synWfn H D) (.classMem (.cv y) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0013 : w ∉ ((synCfv H (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, or_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((synWbr (.cv y) R (synCfv H (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, fresh_w_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0015 : z ∉ ((synCfv H (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_H, or_false, not_false_eq_true])
  have dv_cache_0016 :
    z ∉
      ((Wff.imp (synWbr (synCfv H (.cv y)) R (.cv y))
          (.classEq (synCfv H (.cv y)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_H, fresh_z_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0017 :
    w ∉ ((synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0018 : w ∉ ((synCfv H (synCfv H (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, or_false, not_false_eq_true])
  have dv_cache_0019 :
    w ∉ ((synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, fresh_w_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0020 :
    y ∉
      ((Wff.neg (synWiso H R (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) D
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x, fresh_y_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 :
    y ∉
      ((synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
            (.classMem H (synCvv))) (synWiso H R (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) D
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_not_D, fresh_y_ne_x, fresh_y_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  let syntaxFormula0000 : Wff :=
    (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (.classMem H (synCvv)))
  let syntaxClass0001 : Class :=
    (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxClass0002 : Class := (synCin R syntaxClass0001)
  let syntaxFormula0003 : Wff :=
    (synWiso H R syntaxClass0002 D
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0004 : Wff := (synWa syntaxFormula0000 syntaxFormula0003)
  let syntaxFormula0005 : Wff :=
    (synWa syntaxFormula0004 (synWbr (.cv x) R (synCfv H (.cv x))))
  let syntaxFormula0006 : Wff :=
    (synWf1o H D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0007 : Wff :=
    (synWf H D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0008 : Wff := (synWa syntaxFormula0007 (.classMem (.cv x) D))
  let syntaxFormula0009 : Wff :=
    (.classMem (synCfv H (.cv x))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0010 : Wff :=
    (synWa (synWbr (synCfv H (.cv x)) R (.cv x))
      (.neg (synWbr (synCfv H (.cv x)) (synCid) (.cv x))))
  let syntaxFormula0011 : Wff :=
    (synWa (synWbr (synCfv H (.cv x)) R (.cv x)) (synWne (synCfv H (.cv x)) (.cv x)))
  let syntaxFormula0012 : Wff :=
    (.classMem (synCfv H (.cv x))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
  let syntaxFormula0013 : Wff :=
    (synWa (.classMem (synCfv H (.cv x)) D) syntaxFormula0012)
  let syntaxFormula0014 : Wff :=
    (synWa (.classMem (synCfv H (.cv x)) D) syntaxFormula0011)
  let syntaxFormula0015 : Wff :=
    (synWex w (synWa (.classEq (.cv w) (synCfv H (.cv x))) (synWbr (.cv x) R (.cv w))))
  let syntaxFormula0016 : Wff :=
    (synWral z (synCdif D (synCdm (synCin H R)))
      (.imp (synWbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  let syntaxFormula0017 : Wff :=
    (synW3a syntaxFormula0004 (.classMem (.cv y) (synCdif D (synCdm (synCin H R))))
      syntaxFormula0016)
  let syntaxFormula0018 : Wff := (synWa syntaxFormula0007 (.classMem (.cv y) D))
  let syntaxFormula0019 : Wff :=
    (.classMem (synCfv H (.cv y))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0020 : Wff :=
    (synWa (synWbr (synCfv H (.cv y)) R (.cv x))
      (.neg (synWbr (synCfv H (.cv y)) (synCid) (.cv x))))
  let syntaxFormula0021 : Wff :=
    (synWa (synWbr (synCfv H (.cv y)) R (.cv x)) (synWne (synCfv H (.cv y)) (.cv x)))
  let syntaxFormula0022 : Wff :=
    (.classMem (synCfv H (.cv y))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
  let syntaxFormula0023 : Wff :=
    (synWa (.classMem (synCfv H (.cv y)) D) syntaxFormula0022)
  let syntaxFormula0024 : Wff :=
    (synWa (.classMem (synCfv H (.cv y)) D) syntaxFormula0021)
  let syntaxFormula0025 : Wff :=
    (.classMem (synCfv H (synCfv H (.cv y)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0026 : Wff :=
    (synWa syntaxFormula0017 (.neg (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))))
  let syntaxFormula0027 : Wff :=
    (synWb (.classMem (.cv y) (synCdm (synCin H R)))
      (synWex w (synWbr (.cv y) (synCin H R) (.cv w))))
  let syntaxFormula0028 : Wff :=
    (synWb (synWbr (.cv y) (synCin H R) (.cv w))
      (synWa (synWbr (.cv y) H (.cv w)) (synWbr (.cv y) R (.cv w))))
  let syntaxFormula0029 : Wff :=
    (synWex w (synWa (.classEq (synCfv H (.cv y)) (.cv w)) (synWbr (.cv y) R (.cv w))))
  let syntaxFormula0030 : Wff :=
    (synWex w (synWa (.classEq (.cv w) (synCfv H (.cv y))) (synWbr (.cv y) R (.cv w))))
  let syntaxFormula0031 : Wff := (synWb syntaxFormula0029 syntaxFormula0030)
  let syntaxFormula0032 : Wff :=
    (synWb syntaxFormula0030 (synWbr (.cv y) R (synCfv H (.cv y))))
  let syntaxFormula0033 : Wff :=
    (synWb (.classMem (.cv y) (synCdm (synCin H R))) (synWbr (.cv y) R (synCfv H (.cv y))))
  let syntaxFormula0034 : Wff :=
    (synWa syntaxFormula0017
      (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R)))))
  let syntaxFormula0035 : Wff :=
    (synWa syntaxFormula0017 (.classEq (synCfv H (.cv y)) (.cv y)))
  let syntaxFormula0036 : Wff :=
    (synWa (.classEq (synCfv H (synCfv H (.cv y))) (.cv w))
      (synWbr (synCfv H (.cv y)) R (.cv w)))
  let syntaxFormula0037 : Wff :=
    (synWa (.classEq (.cv w) (synCfv H (synCfv H (.cv y))))
      (synWbr (synCfv H (.cv y)) R (.cv w)))
  let syntaxFormula0038 : Wff := (synWex w syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (synWbr (synCfv H (synCfv H (.cv y))) syntaxClass0002 (synCfv H (.cv y)))
  let syntaxFormula0040 : Wff :=
    (synWf1 H D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0041 : Wff := (.neg syntaxFormula0003)
  have p0000 := @gSimpl syntaxFormula0000 syntaxFormula0003
  have p0001 :=
    @gSimpl (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem H (synCvv))
  have p0002 :=
    @gSyl syntaxFormula0004 syntaxFormula0000
      (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) p0000 p0001
  have p0003 := @gSimpl (synWbr R (synCwe) D) (.classMem (.cv x) D)
  have p0004 :=
    @gSyl syntaxFormula0004 (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWbr R (synCwe) D) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCwe))
  have p0006 := @gBreqi R D (synCwe) (synCin (synCstrict) (synCfound)) p0005
  have p0007 := @gBrin R D (synCstrict) (synCfound)
  have p0008 :=
    @gBitri (synWbr R (synCwe) D) (synWbr R (synCin (synCstrict) (synCfound)) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0006 p0007
  have p0009 :=
    @gBiimpi (synWbr R (synCwe) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0008
  have p0010 :=
    @gSyl syntaxFormula0004 (synWbr R (synCwe) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0004 p0009
  have p0011 :=
    @gSimprd syntaxFormula0004 (synWbr R (synCstrict) D) (synWbr R (synCfound) D)
      p0010
  have p0017 := @gBrex R D (synCwe)
  have p0018 :=
    @gSyl syntaxFormula0004 (synWbr R (synCwe) D)
      (synWa (.classMem R (synCvv)) (.classMem D (synCvv))) p0004 p0017
  have p0019 :=
    @gSimprd syntaxFormula0004 (.classMem R (synCvv)) (.classMem D (synCvv)) p0018
  have p0021 :=
    @gSimpr (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem H (synCvv))
  have p0022 :=
    @gSyl syntaxFormula0004 syntaxFormula0000 (.classMem H (synCvv)) p0000 p0021
  have p0030 :=
    @gSimpld syntaxFormula0004 (.classMem R (synCvv)) (.classMem D (synCvv)) p0018
  have p0031 :=
    @gJca syntaxFormula0004 (.classMem H (synCvv)) (.classMem R (synCvv)) p0022 p0030
  have p0032 := @gInexg H R (synCvv) (synCvv)
  have p0033 :=
    @gSyl syntaxFormula0004 (synWa (.classMem H (synCvv)) (.classMem R (synCvv)))
      (.classMem (synCin H R) (synCvv)) p0031 p0032
  have p0034 := @gDmexg (synCin H R) (synCvv)
  have p0035 :=
    @gSyl syntaxFormula0004 (.classMem (synCin H R) (synCvv))
      (.classMem (synCdm (synCin H R)) (synCvv)) p0033 p0034
  have p0036 :=
    @gJca syntaxFormula0004 (.classMem D (synCvv))
      (.classMem (synCdm (synCin H R)) (synCvv)) p0019 p0035
  have p0037 := @gDifexg D (synCdm (synCin H R)) (synCvv) (synCvv)
  have p0038 :=
    @gSyl syntaxFormula0004
      (synWa (.classMem D (synCvv)) (.classMem (synCdm (synCin H R)) (synCvv)))
      (.classMem (synCdif D (synCdm (synCin H R))) (synCvv)) p0036 p0037
  have p0039 := @gDifss D (synCdm (synCin H R))
  have p0040 :=
    @gA1i (synWss (synCdif D (synCdm (synCin H R))) D) syntaxFormula0004 p0039
  have p0044 := @gSimpr (synWbr R (synCwe) D) (.classMem (.cv x) D)
  have p0045 :=
    @gSyl syntaxFormula0004 (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (.classMem (.cv x) D) p0002 p0044
  have p0046 := @gSimpl syntaxFormula0004 (synWbr (.cv x) R (synCfv H (.cv x)))
  have p0058 :=
    @gSimpld syntaxFormula0004 (synWbr R (synCstrict) D) (synWbr R (synCfound) D)
      p0010
  have p0059 := @gSopc D R
  have p0060 :=
    @gSylib syntaxFormula0004 (synWbr R (synCstrict) D)
      (synWa (synWbr R (synCpartial) D) (synWbr R (synCconnex) D)) p0058 p0059
  have p0061 :=
    @gSimpld syntaxFormula0004 (synWbr R (synCpartial) D) (synWbr R (synCconnex) D)
      p0060
  have p0062 := @gPorta D R
  have p0063 :=
    @gSylib syntaxFormula0004 (synWbr R (synCpartial) D)
      (synW3a (synWbr R (synCref) D) (synWbr R (synCtrans) D) (synWbr R (synCantisym) D))
      p0061 p0062
  have p0064 :=
    @gSimp3d syntaxFormula0004 (synWbr R (synCref) D) (synWbr R (synCtrans) D)
      (synWbr R (synCantisym) D) p0063
  have p0065 :=
    @gSyl syntaxFormula0005 syntaxFormula0004 (synWbr R (synCantisym) D) p0046 p0064
  have p0072 :=
    @gSyl syntaxFormula0005 syntaxFormula0004 (.classMem (.cv x) D) p0046 p0045
  have p0074 := @gSimpr syntaxFormula0000 syntaxFormula0003
  have p0075 :=
    @gIsof1o D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      R syntaxClass0002 H
  have p0076 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0006 p0074 p0075
  have p0077 :=
    @gF1of D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) H
  have p0078 := @gSyl syntaxFormula0004 syntaxFormula0006 syntaxFormula0007 p0076 p0077
  have p0084 :=
    @gJca syntaxFormula0004 syntaxFormula0007 (.classMem (.cv x) D) p0078 p0045
  have p0085 :=
    @gFfvelrn D
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (.cv x) H
  have p0086 := @gSyl syntaxFormula0004 syntaxFormula0008 syntaxFormula0009 p0084 p0085
  have p0087 :=
    @gElin (synCfv H (.cv x)) D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0088 := @gEliniseg (synCdif R (synCid)) (.cv x) (synCfv H (.cv x))
  have p0089 := @gBrdif (synCfv H (.cv x)) (.cv x) R (synCid)
  have p0090 := @gVex x
  have p0091 := @gIdeq (synCfv H (.cv x)) (.cv x) p0090
  have p0092 :=
    @gNotbii (synWbr (synCfv H (.cv x)) (synCid) (.cv x))
      (.classEq (synCfv H (.cv x)) (.cv x)) p0091
  have p0093 := (Nominal.biimpRefl (synWne (synCfv H (.cv x)) (.cv x)))
  have p0094 :=
    @gBitr4i (.neg (synWbr (synCfv H (.cv x)) (synCid) (.cv x)))
      (.neg (.classEq (synCfv H (.cv x)) (.cv x))) (synWne (synCfv H (.cv x)) (.cv x))
      p0092 p0093
  have p0095 :=
    @gAnbi2i (.neg (synWbr (synCfv H (.cv x)) (synCid) (.cv x)))
      (synWne (synCfv H (.cv x)) (.cv x)) (synWbr (synCfv H (.cv x)) R (.cv x)) p0094
  have p0096 :=
    @gBitri (synWbr (synCfv H (.cv x)) (synCdif R (synCid)) (.cv x))
      syntaxFormula0010 syntaxFormula0011 p0089 p0095
  have p0097 :=
    @gBitri syntaxFormula0012
      (synWbr (synCfv H (.cv x)) (synCdif R (synCid)) (.cv x)) syntaxFormula0011 p0088
      p0096
  have p0098 :=
    @gAnbi2i syntaxFormula0012 syntaxFormula0011 (.classMem (synCfv H (.cv x)) D) p0097
  have p0099 := @gBitri syntaxFormula0009 syntaxFormula0013 syntaxFormula0014 p0087 p0098
  have p0100 := @gBiimpi syntaxFormula0009 syntaxFormula0014 p0099
  have p0101 := @gSyl syntaxFormula0004 syntaxFormula0009 syntaxFormula0014 p0086 p0100
  have p0102 :=
    @gSimpld syntaxFormula0004 (.classMem (synCfv H (.cv x)) D) syntaxFormula0011 p0101
  have p0103 :=
    @gSyl syntaxFormula0005 syntaxFormula0004 (.classMem (synCfv H (.cv x)) D) p0046
      p0102
  have p0104 := @gSimpr syntaxFormula0004 (synWbr (.cv x) R (synCfv H (.cv x)))
  have p0134 :=
    @gSimprd syntaxFormula0004 (.classMem (synCfv H (.cv x)) D) syntaxFormula0011 p0101
  have p0135 :=
    @gSimpld syntaxFormula0004 (synWbr (synCfv H (.cv x)) R (.cv x))
      (synWne (synCfv H (.cv x)) (.cv x)) p0134
  have p0136 :=
    @gSyl syntaxFormula0005 syntaxFormula0004 (synWbr (synCfv H (.cv x)) R (.cv x))
      p0046 p0135
  have p0137 :=
    @gAntid syntaxFormula0005 D R (.cv x) (synCfv H (.cv x)) p0065 p0072 p0103 p0104
      p0136
  have p0138 := @gEqcomd syntaxFormula0005 (.cv x) (synCfv H (.cv x)) p0137
  have p0169 :=
    @gSimprd syntaxFormula0004 (synWbr (synCfv H (.cv x)) R (.cv x))
      (synWne (synCfv H (.cv x)) (.cv x)) p0134
  have p0170 :=
    @gSyl syntaxFormula0005 syntaxFormula0004 (synWne (synCfv H (.cv x)) (.cv x)) p0046
      p0169
  have p0171 :=
    @gPm221ddne syntaxFormula0005 (.neg (synWbr (.cv x) R (synCfv H (.cv x))))
      (synCfv H (.cv x)) (.cv x) p0138 p0170
  have p0172 :=
    @gPm201da syntaxFormula0004 (synWbr (.cv x) R (synCfv H (.cv x))) p0171
  have p0176 :=
    @gF1ofn D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      H
  have p0177 := @gSyl syntaxFormula0004 syntaxFormula0006 (synWfn H D) p0076 p0176
  have p0183 := @gJca syntaxFormula0004 (synWfn H D) (.classMem (.cv x) D) p0177 p0045
  have p0184 := @gEldm w (.cv x) (synCin H R) dv_cache_0001 dv_cache_0002
  have p0185 :=
    @gA1i
      (synWb (.classMem (.cv x) (synCdm (synCin H R)))
        (synWex w (synWbr (.cv x) (synCin H R) (.cv w))))
      (synWa (synWfn H D) (.classMem (.cv x) D)) p0184
  have p0186 := @gBrin (.cv x) (.cv w) H R
  have p0187 :=
    @gA1i
      (synWb (synWbr (.cv x) (synCin H R) (.cv w))
        (synWa (synWbr (.cv x) H (.cv w)) (synWbr (.cv x) R (.cv w))))
      (synWa (synWfn H D) (.classMem (.cv x) D)) p0186
  have p0188 := @gFnbrfvb D (.cv x) (.cv w) H
  have p0189 :=
    @gBicomd (synWa (synWfn H D) (.classMem (.cv x) D))
      (.classEq (synCfv H (.cv x)) (.cv w)) (synWbr (.cv x) H (.cv w)) p0188
  have p0190 :=
    @gAnbi1d (synWa (synWfn H D) (.classMem (.cv x) D)) (synWbr (.cv x) H (.cv w))
      (.classEq (synCfv H (.cv x)) (.cv w)) (synWbr (.cv x) R (.cv w)) p0189
  have p0191 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv x) D))
      (synWbr (.cv x) (synCin H R) (.cv w))
      (synWa (synWbr (.cv x) H (.cv w)) (synWbr (.cv x) R (.cv w)))
      (synWa (.classEq (synCfv H (.cv x)) (.cv w)) (synWbr (.cv x) R (.cv w))) p0187
      p0190
  have p0192 :=
    @gExbidv (synWa (synWfn H D) (.classMem (.cv x) D))
      (synWbr (.cv x) (synCin H R) (.cv w))
      (synWa (.classEq (synCfv H (.cv x)) (.cv w)) (synWbr (.cv x) R (.cv w))) w
      dv_cache_0003 p0191
  have p0193 := @gEqcom (synCfv H (.cv x)) (.cv w)
  have p0194 :=
    @gAnbi1i (.classEq (synCfv H (.cv x)) (.cv w))
      (.classEq (.cv w) (synCfv H (.cv x))) (synWbr (.cv x) R (.cv w)) p0193
  have p0195 :=
    @gExbii (synWa (.classEq (synCfv H (.cv x)) (.cv w)) (synWbr (.cv x) R (.cv w)))
      (synWa (.classEq (.cv w) (synCfv H (.cv x))) (synWbr (.cv x) R (.cv w))) w p0194
  have p0196 :=
    @gA1i
      (synWb (synWex w
          (synWa (.classEq (synCfv H (.cv x)) (.cv w)) (synWbr (.cv x) R (.cv w))))
        syntaxFormula0015)
      (synWa (synWfn H D) (.classMem (.cv x) D)) p0195
  have p0197 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv x) D))
      (synWex w (synWbr (.cv x) (synCin H R) (.cv w)))
      (synWex w (synWa (.classEq (synCfv H (.cv x)) (.cv w)) (synWbr (.cv x) R (.cv w))))
      syntaxFormula0015 p0192 p0196
  have p0198 := @gFvex (.cv x) H
  have p0199 := @gBreq2 (.cv w) (synCfv H (.cv x)) (.cv x) R
  have p0200 :=
    @gCeqsexv (synWbr (.cv x) R (.cv w)) (synWbr (.cv x) R (synCfv H (.cv x))) w
      (synCfv H (.cv x)) dv_cache_0004 dv_cache_0005 p0198 p0199
  have p0201 :=
    @gA1i (synWb syntaxFormula0015 (synWbr (.cv x) R (synCfv H (.cv x))))
      (synWa (synWfn H D) (.classMem (.cv x) D)) p0200
  have p0202 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv x) D))
      (synWex w (synWbr (.cv x) (synCin H R) (.cv w))) syntaxFormula0015
      (synWbr (.cv x) R (synCfv H (.cv x))) p0197 p0201
  have p0203 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv x) D))
      (.classMem (.cv x) (synCdm (synCin H R)))
      (synWex w (synWbr (.cv x) (synCin H R) (.cv w)))
      (synWbr (.cv x) R (synCfv H (.cv x))) p0185 p0202
  have p0204 :=
    @gSyl syntaxFormula0004 (synWa (synWfn H D) (.classMem (.cv x) D))
      (synWb (.classMem (.cv x) (synCdm (synCin H R)))
        (synWbr (.cv x) R (synCfv H (.cv x))))
      p0183 p0203
  have p0205 :=
    @gBiimpd syntaxFormula0004 (.classMem (.cv x) (synCdm (synCin H R)))
      (synWbr (.cv x) R (synCfv H (.cv x))) p0204
  have p0206 :=
    @gMtod syntaxFormula0004 (.classMem (.cv x) (synCdm (synCin H R)))
      (synWbr (.cv x) R (synCfv H (.cv x))) p0172 p0205
  have p0207 :=
    @gJca syntaxFormula0004 (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (synCdm (synCin H R)))) p0045 p0206
  have p0208 := @gEldif (.cv x) D (synCdm (synCin H R))
  have p0209 :=
    @gBiimpri (.classMem (.cv x) (synCdif D (synCdm (synCin H R))))
      (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (synCdm (synCin H R)))))
      p0208
  have p0210 :=
    @gSyl syntaxFormula0004
      (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (synCdm (synCin H R)))))
      (.classMem (.cv x) (synCdif D (synCdm (synCin H R)))) p0207 p0209
  have p0211 := @gNe0i (synCdif D (synCdm (synCin H R))) (.cv x)
  have p0212 :=
    @gSyl syntaxFormula0004 (.classMem (.cv x) (synCdif D (synCdm (synCin H R))))
      (synWne (synCdif D (synCdm (synCin H R))) (synC0)) p0210 p0211
  have p0213 :=
    @gFrd syntaxFormula0004 y z D R (synCvv) (synCdif D (synCdm (synCin H R)))
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0011 p0038
      p0040 p0212
  have p0214 :=
    @gSimp1 syntaxFormula0004 (.classMem (.cv y) (synCdif D (synCdm (synCin H R))))
      syntaxFormula0016
  have p0233 :=
    @gSyl syntaxFormula0017 syntaxFormula0004 (synWbr R (synCantisym) D) p0214 p0064
  have p0240 := @gSyl syntaxFormula0017 syntaxFormula0004 syntaxFormula0007 p0214 p0078
  have p0241 :=
    @gSimp2 syntaxFormula0004 (.classMem (.cv y) (synCdif D (synCdm (synCin H R))))
      syntaxFormula0016
  have p0242 := @gEldifi (.cv y) D (synCdm (synCin H R))
  have p0243 :=
    @gSyl syntaxFormula0017 (.classMem (.cv y) (synCdif D (synCdm (synCin H R))))
      (.classMem (.cv y) D) p0241 p0242
  have p0244 :=
    @gJca syntaxFormula0017 syntaxFormula0007 (.classMem (.cv y) D) p0240 p0243
  have p0245 :=
    @gFfvelrn D
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (.cv y) H
  have p0246 := @gSyl syntaxFormula0017 syntaxFormula0018 syntaxFormula0019 p0244 p0245
  have p0247 :=
    @gElin (synCfv H (.cv y)) D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0248 := @gEliniseg (synCdif R (synCid)) (.cv x) (synCfv H (.cv y))
  have p0249 := @gBrdif (synCfv H (.cv y)) (.cv x) R (synCid)
  have p0251 := @gIdeq (synCfv H (.cv y)) (.cv x) p0090
  have p0252 :=
    @gNotbii (synWbr (synCfv H (.cv y)) (synCid) (.cv x))
      (.classEq (synCfv H (.cv y)) (.cv x)) p0251
  have p0253 := (Nominal.biimpRefl (synWne (synCfv H (.cv y)) (.cv x)))
  have p0254 :=
    @gBitr4i (.neg (synWbr (synCfv H (.cv y)) (synCid) (.cv x)))
      (.neg (.classEq (synCfv H (.cv y)) (.cv x))) (synWne (synCfv H (.cv y)) (.cv x))
      p0252 p0253
  have p0255 :=
    @gAnbi2i (.neg (synWbr (synCfv H (.cv y)) (synCid) (.cv x)))
      (synWne (synCfv H (.cv y)) (.cv x)) (synWbr (synCfv H (.cv y)) R (.cv x)) p0254
  have p0256 :=
    @gBitri (synWbr (synCfv H (.cv y)) (synCdif R (synCid)) (.cv x))
      syntaxFormula0020 syntaxFormula0021 p0249 p0255
  have p0257 :=
    @gBitri syntaxFormula0022
      (synWbr (synCfv H (.cv y)) (synCdif R (synCid)) (.cv x)) syntaxFormula0021 p0248
      p0256
  have p0258 :=
    @gAnbi2i syntaxFormula0022 syntaxFormula0021 (.classMem (synCfv H (.cv y)) D) p0257
  have p0259 := @gBitri syntaxFormula0019 syntaxFormula0023 syntaxFormula0024 p0247 p0258
  have p0260 := @gBiimpi syntaxFormula0019 syntaxFormula0024 p0259
  have p0261 := @gSyl syntaxFormula0017 syntaxFormula0019 syntaxFormula0024 p0246 p0260
  have p0262 :=
    @gSimpld syntaxFormula0017 (.classMem (synCfv H (.cv y)) D) syntaxFormula0021 p0261
  have p0299 :=
    @gJca syntaxFormula0017 syntaxFormula0007 (.classMem (synCfv H (.cv y)) D) p0240
      p0262
  have p0300 :=
    @gFfvelrn D
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv H (.cv y)) H
  have p0301 :=
    @gSyl syntaxFormula0017 (synWa syntaxFormula0007 (.classMem (synCfv H (.cv y)) D))
      syntaxFormula0025 p0299 p0300
  have p0302 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0303 :=
    @gSseli (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D
      (synCfv H (synCfv H (.cv y))) p0302
  have p0304 :=
    @gSyl syntaxFormula0017 syntaxFormula0025
      (.classMem (synCfv H (synCfv H (.cv y))) D) p0301 p0303
  have p0305 := @gId (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
  have p0306 :=
    @gA1i
      (.imp (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
        (.classMem (synCfv H (.cv y)) (synCdm (synCin H R))))
      syntaxFormula0017 p0305
  have p0307 :=
    @gSimpl syntaxFormula0017
      (.neg (.classMem (synCfv H (.cv y)) (synCdm (synCin H R))))
  have p0337 :=
    @gSyl syntaxFormula0026 syntaxFormula0017 (.classMem (synCfv H (.cv y)) D) p0307
      p0262
  have p0338 :=
    @gSimpr syntaxFormula0017
      (.neg (.classMem (synCfv H (.cv y)) (synCdm (synCin H R))))
  have p0339 :=
    @gJca syntaxFormula0026 (.classMem (synCfv H (.cv y)) D)
      (.neg (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))) p0337 p0338
  have p0340 := @gEldif (synCfv H (.cv y)) D (synCdm (synCin H R))
  have p0341 :=
    @gBiimpri (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R))))
      (synWa (.classMem (synCfv H (.cv y)) D)
        (.neg (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))))
      p0340
  have p0342 :=
    @gSyl syntaxFormula0026
      (synWa (.classMem (synCfv H (.cv y)) D)
        (.neg (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))))
      (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R)))) p0339 p0341
  have p0344 :=
    @gSimpl syntaxFormula0017
      (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R))))
  have p0346 := @gEldifn (.cv y) D (synCdm (synCin H R))
  have p0347 :=
    @gSyl syntaxFormula0017 (.classMem (.cv y) (synCdif D (synCdm (synCin H R))))
      (.neg (.classMem (.cv y) (synCdm (synCin H R)))) p0241 p0346
  have p0354 := @gSyl syntaxFormula0017 syntaxFormula0004 (synWfn H D) p0214 p0177
  have p0358 := @gJca syntaxFormula0017 (synWfn H D) (.classMem (.cv y) D) p0354 p0243
  have p0359 := @gEldm w (.cv y) (synCin H R) dv_cache_0011 dv_cache_0002
  have p0360 :=
    @gA1i syntaxFormula0027 (synWa (synWfn H D) (.classMem (.cv y) D)) p0359
  have p0361 := @gBrin (.cv y) (.cv w) H R
  have p0362 :=
    @gA1i syntaxFormula0028 (synWa (synWfn H D) (.classMem (.cv y) D)) p0361
  have p0363 := @gFnbrfvb D (.cv y) (.cv w) H
  have p0364 :=
    @gBicomd (synWa (synWfn H D) (.classMem (.cv y) D))
      (.classEq (synCfv H (.cv y)) (.cv w)) (synWbr (.cv y) H (.cv w)) p0363
  have p0365 :=
    @gAnbi1d (synWa (synWfn H D) (.classMem (.cv y) D)) (synWbr (.cv y) H (.cv w))
      (.classEq (synCfv H (.cv y)) (.cv w)) (synWbr (.cv y) R (.cv w)) p0364
  have p0366 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv y) D))
      (synWbr (.cv y) (synCin H R) (.cv w))
      (synWa (synWbr (.cv y) H (.cv w)) (synWbr (.cv y) R (.cv w)))
      (synWa (.classEq (synCfv H (.cv y)) (.cv w)) (synWbr (.cv y) R (.cv w))) p0362
      p0365
  have p0367 :=
    @gExbidv (synWa (synWfn H D) (.classMem (.cv y) D))
      (synWbr (.cv y) (synCin H R) (.cv w))
      (synWa (.classEq (synCfv H (.cv y)) (.cv w)) (synWbr (.cv y) R (.cv w))) w
      dv_cache_0012 p0366
  have p0368 := @gEqcom (synCfv H (.cv y)) (.cv w)
  have p0369 :=
    @gAnbi1i (.classEq (synCfv H (.cv y)) (.cv w))
      (.classEq (.cv w) (synCfv H (.cv y))) (synWbr (.cv y) R (.cv w)) p0368
  have p0370 :=
    @gExbii (synWa (.classEq (synCfv H (.cv y)) (.cv w)) (synWbr (.cv y) R (.cv w)))
      (synWa (.classEq (.cv w) (synCfv H (.cv y))) (synWbr (.cv y) R (.cv w))) w p0369
  have p0371 :=
    @gA1i syntaxFormula0031 (synWa (synWfn H D) (.classMem (.cv y) D)) p0370
  have p0372 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv y) D))
      (synWex w (synWbr (.cv y) (synCin H R) (.cv w))) syntaxFormula0029
      syntaxFormula0030 p0367 p0371
  have p0373 := @gFvex (.cv y) H
  have p0374 := @gBreq2 (.cv w) (synCfv H (.cv y)) (.cv y) R
  have p0375 :=
    @gCeqsexv (synWbr (.cv y) R (.cv w)) (synWbr (.cv y) R (synCfv H (.cv y))) w
      (synCfv H (.cv y)) dv_cache_0013 dv_cache_0014 p0373 p0374
  have p0376 :=
    @gA1i syntaxFormula0032 (synWa (synWfn H D) (.classMem (.cv y) D)) p0375
  have p0377 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv y) D))
      (synWex w (synWbr (.cv y) (synCin H R) (.cv w))) syntaxFormula0030
      (synWbr (.cv y) R (synCfv H (.cv y))) p0372 p0376
  have p0378 :=
    @gBitrd (synWa (synWfn H D) (.classMem (.cv y) D))
      (.classMem (.cv y) (synCdm (synCin H R)))
      (synWex w (synWbr (.cv y) (synCin H R) (.cv w)))
      (synWbr (.cv y) R (synCfv H (.cv y))) p0360 p0377
  have p0379 :=
    @gSyl syntaxFormula0017 (synWa (synWfn H D) (.classMem (.cv y) D))
      syntaxFormula0033 p0358 p0378
  have p0380 :=
    @gBiimprd syntaxFormula0017 (.classMem (.cv y) (synCdm (synCin H R)))
      (synWbr (.cv y) R (synCfv H (.cv y))) p0379
  have p0381 :=
    @gMtod syntaxFormula0017 (synWbr (.cv y) R (synCfv H (.cv y)))
      (.classMem (.cv y) (synCdm (synCin H R))) p0347 p0380
  have p0397 :=
    @gSimprd syntaxFormula0004 (synWbr R (synCpartial) D) (synWbr R (synCconnex) D)
      p0060
  have p0398 :=
    @gSyl syntaxFormula0017 syntaxFormula0004 (synWbr R (synCconnex) D) p0214 p0397
  have p0431 :=
    @gConnexd syntaxFormula0017 D R (.cv y) (synCfv H (.cv y)) p0398 p0243 p0262
  have p0432 :=
    @gOrd syntaxFormula0017 (synWbr (.cv y) R (synCfv H (.cv y)))
      (synWbr (synCfv H (.cv y)) R (.cv y)) p0431
  have p0433 :=
    @gMpd syntaxFormula0017 (.neg (synWbr (.cv y) R (synCfv H (.cv y))))
      (synWbr (synCfv H (.cv y)) R (.cv y)) p0381 p0432
  have p0434 :=
    @gSyl syntaxFormula0034 syntaxFormula0017 (synWbr (synCfv H (.cv y)) R (.cv y))
      p0344 p0433
  have p0436 :=
    @gSimp3 syntaxFormula0004 (.classMem (.cv y) (synCdif D (synCdm (synCin H R))))
      syntaxFormula0016
  have p0437 := @gSyl syntaxFormula0034 syntaxFormula0017 syntaxFormula0016 p0344 p0436
  have p0438 :=
    @gSimpr syntaxFormula0017
      (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R))))
  have p0439 :=
    @gJca syntaxFormula0034 syntaxFormula0016
      (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R)))) p0437 p0438
  have p0440 := @gBreq1 (.cv z) (synCfv H (.cv y)) (.cv y) R
  have p0441 := @gEqeq1 (.cv z) (synCfv H (.cv y)) (.cv y)
  have p0442 :=
    @gImbi12d (.classEq (.cv z) (synCfv H (.cv y))) (synWbr (.cv z) R (.cv y))
      (synWbr (synCfv H (.cv y)) R (.cv y)) (.classEq (.cv z) (.cv y))
      (.classEq (synCfv H (.cv y)) (.cv y)) p0440 p0441
  have p0443 :=
    @gRspccva (.imp (synWbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))
      (.imp (synWbr (synCfv H (.cv y)) R (.cv y)) (.classEq (synCfv H (.cv y)) (.cv y)))
      z (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R))) dv_cache_0015
      dv_cache_0009 dv_cache_0016 p0442
  have p0444 :=
    @gSyl syntaxFormula0034
      (synWa syntaxFormula0016
        (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R)))))
      (.imp (synWbr (synCfv H (.cv y)) R (.cv y)) (.classEq (synCfv H (.cv y)) (.cv y)))
      p0439 p0443
  have p0445 :=
    @gMpd syntaxFormula0034 (synWbr (synCfv H (.cv y)) R (.cv y))
      (.classEq (synCfv H (.cv y)) (.cv y)) p0434 p0444
  have p0447 := @gSimpr syntaxFormula0017 (.classEq (synCfv H (.cv y)) (.cv y))
  have p0448 := @gSimpl syntaxFormula0017 (.classEq (synCfv H (.cv y)) (.cv y))
  have p0538 :=
    @gSyl syntaxFormula0035 syntaxFormula0017 (synWbr (synCfv H (.cv y)) R (.cv y))
      p0448 p0433
  have p0539 :=
    @gEqbrtrrd syntaxFormula0035 (synCfv H (.cv y)) (.cv y) (.cv y) R p0447 p0538
  have p0541 :=
    @gBreqtrrd syntaxFormula0035 (.cv y) (.cv y) (synCfv H (.cv y)) R p0539 p0447
  have p0580 :=
    @gSyl syntaxFormula0035 syntaxFormula0017
      (.neg (synWbr (.cv y) R (synCfv H (.cv y)))) p0448 p0381
  have p0581 :=
    @gPm221dd syntaxFormula0035 (synWbr (.cv y) R (synCfv H (.cv y)))
      (.neg (.classEq (synCfv H (.cv y)) (.cv y))) p0541 p0580
  have p0582 := @gPm201da syntaxFormula0017 (.classEq (synCfv H (.cv y)) (.cv y)) p0581
  have p0583 := (Nominal.biimpRefl (synWne (synCfv H (.cv y)) (.cv y)))
  have p0584 :=
    @gBiimpri (synWne (synCfv H (.cv y)) (.cv y))
      (.neg (.classEq (synCfv H (.cv y)) (.cv y))) p0583
  have p0585 :=
    @gSyl syntaxFormula0017 (.neg (.classEq (synCfv H (.cv y)) (.cv y)))
      (synWne (synCfv H (.cv y)) (.cv y)) p0582 p0584
  have p0586 :=
    @gSyl syntaxFormula0034 syntaxFormula0017 (synWne (synCfv H (.cv y)) (.cv y)) p0344
      p0585
  have p0587 :=
    @gPm221ddne syntaxFormula0034
      (.neg (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R)))))
      (synCfv H (.cv y)) (.cv y) p0445 p0586
  have p0588 :=
    @gPm201da syntaxFormula0017
      (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R)))) p0587
  have p0589 :=
    @gSyl syntaxFormula0026 syntaxFormula0017
      (.neg (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R))))) p0307
      p0588
  have p0590 :=
    @gPm221dd syntaxFormula0026
      (.classMem (synCfv H (.cv y)) (synCdif D (synCdm (synCin H R))))
      (.classMem (synCfv H (.cv y)) (synCdm (synCin H R))) p0342 p0589
  have p0591 :=
    @gEx syntaxFormula0017 (.neg (.classMem (synCfv H (.cv y)) (synCdm (synCin H R))))
      (.classMem (synCfv H (.cv y)) (synCdm (synCin H R))) p0590
  have p0592 :=
    @gPm261d syntaxFormula0017 (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
      (.classMem (synCfv H (.cv y)) (synCdm (synCin H R))) p0306 p0591
  have p0629 :=
    @gJca syntaxFormula0017 (synWfn H D) (.classMem (synCfv H (.cv y)) D) p0354 p0262
  have p0630 := @gEldm w (synCfv H (.cv y)) (synCin H R) dv_cache_0013 dv_cache_0002
  have p0631 :=
    @gA1i
      (synWb (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
        (synWex w (synWbr (synCfv H (.cv y)) (synCin H R) (.cv w))))
      (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D)) p0630
  have p0632 := @gBrin (synCfv H (.cv y)) (.cv w) H R
  have p0633 :=
    @gA1i
      (synWb (synWbr (synCfv H (.cv y)) (synCin H R) (.cv w))
        (synWa (synWbr (synCfv H (.cv y)) H (.cv w))
          (synWbr (synCfv H (.cv y)) R (.cv w))))
      (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D)) p0632
  have p0634 := @gFnbrfvb D (synCfv H (.cv y)) (.cv w) H
  have p0635 :=
    @gBicomd (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (.classEq (synCfv H (synCfv H (.cv y))) (.cv w))
      (synWbr (synCfv H (.cv y)) H (.cv w)) p0634
  have p0636 :=
    @gAnbi1d (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (synWbr (synCfv H (.cv y)) H (.cv w))
      (.classEq (synCfv H (synCfv H (.cv y))) (.cv w))
      (synWbr (synCfv H (.cv y)) R (.cv w)) p0635
  have p0637 :=
    @gBitrd (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (synWbr (synCfv H (.cv y)) (synCin H R) (.cv w))
      (synWa (synWbr (synCfv H (.cv y)) H (.cv w)) (synWbr (synCfv H (.cv y)) R (.cv w)))
      syntaxFormula0036 p0633 p0636
  have p0638 :=
    @gExbidv (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (synWbr (synCfv H (.cv y)) (synCin H R) (.cv w)) syntaxFormula0036 w
      dv_cache_0017 p0637
  have p0639 := @gEqcom (synCfv H (synCfv H (.cv y))) (.cv w)
  have p0640 :=
    @gAnbi1i (.classEq (synCfv H (synCfv H (.cv y))) (.cv w))
      (.classEq (.cv w) (synCfv H (synCfv H (.cv y))))
      (synWbr (synCfv H (.cv y)) R (.cv w)) p0639
  have p0641 := @gExbii syntaxFormula0036 syntaxFormula0037 w p0640
  have p0642 :=
    @gA1i (synWb (synWex w syntaxFormula0036) syntaxFormula0038)
      (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D)) p0641
  have p0643 :=
    @gBitrd (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (synWex w (synWbr (synCfv H (.cv y)) (synCin H R) (.cv w)))
      (synWex w syntaxFormula0036) syntaxFormula0038 p0638 p0642
  have p0644 := @gFvex (synCfv H (.cv y)) H
  have p0645 := @gBreq2 (.cv w) (synCfv H (synCfv H (.cv y))) (synCfv H (.cv y)) R
  have p0646 :=
    @gCeqsexv (synWbr (synCfv H (.cv y)) R (.cv w))
      (synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y)))) w
      (synCfv H (synCfv H (.cv y))) dv_cache_0018 dv_cache_0019 p0644 p0645
  have p0647 :=
    @gA1i
      (synWb syntaxFormula0038 (synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y)))))
      (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D)) p0646
  have p0648 :=
    @gBitrd (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (synWex w (synWbr (synCfv H (.cv y)) (synCin H R) (.cv w))) syntaxFormula0038
      (synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y)))) p0643 p0647
  have p0649 :=
    @gBitrd (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
      (synWex w (synWbr (synCfv H (.cv y)) (synCin H R) (.cv w)))
      (synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y)))) p0631 p0648
  have p0650 :=
    @gSyl syntaxFormula0017 (synWa (synWfn H D) (.classMem (synCfv H (.cv y)) D))
      (synWb (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
        (synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y)))))
      p0629 p0649
  have p0651 :=
    @gBiimpd syntaxFormula0017 (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
      (synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y)))) p0650
  have p0652 :=
    @gMpd syntaxFormula0017 (.classMem (synCfv H (.cv y)) (synCdm (synCin H R)))
      (synWbr (synCfv H (.cv y)) R (synCfv H (synCfv H (.cv y)))) p0592 p0651
  have p0744 := @gSyl syntaxFormula0017 syntaxFormula0004 syntaxFormula0003 p0214 p0074
  have p0777 :=
    @gJca syntaxFormula0017 (.classMem (synCfv H (.cv y)) D) (.classMem (.cv y) D) p0262
      p0243
  have p0778 :=
    @gJca syntaxFormula0017 syntaxFormula0003
      (synWa (.classMem (synCfv H (.cv y)) D) (.classMem (.cv y) D)) p0744 p0777
  have p0779 :=
    @gIsorel D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv H (.cv y)) (.cv y) R syntaxClass0002 H
  have p0780 :=
    @gSyl syntaxFormula0017
      (synWa syntaxFormula0003
        (synWa (.classMem (synCfv H (.cv y)) D) (.classMem (.cv y) D)))
      (synWb (synWbr (synCfv H (.cv y)) R (.cv y)) syntaxFormula0039) p0778 p0779
  have p0833 := @gJca syntaxFormula0017 syntaxFormula0025 syntaxFormula0019 p0301 p0246
  have p0834 :=
    @gBrinxp (synCfv H (synCfv H (.cv y))) (synCfv H (.cv y))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) R
  have p0835 :=
    @gSyl syntaxFormula0017 (synWa syntaxFormula0025 syntaxFormula0019)
      (synWb (synWbr (synCfv H (synCfv H (.cv y))) R (synCfv H (.cv y))) syntaxFormula0039)
      p0833 p0834
  have p0836 :=
    @gBitr4d syntaxFormula0017 (synWbr (synCfv H (.cv y)) R (.cv y)) syntaxFormula0039
      (synWbr (synCfv H (synCfv H (.cv y))) R (synCfv H (.cv y))) p0780 p0835
  have p0837 :=
    @gBiimpd syntaxFormula0017 (synWbr (synCfv H (.cv y)) R (.cv y))
      (synWbr (synCfv H (synCfv H (.cv y))) R (synCfv H (.cv y))) p0836
  have p0838 :=
    @gMpd syntaxFormula0017 (synWbr (synCfv H (.cv y)) R (.cv y))
      (synWbr (synCfv H (synCfv H (.cv y))) R (synCfv H (.cv y))) p0433 p0837
  have p0839 :=
    @gAntid syntaxFormula0017 D R (synCfv H (.cv y)) (synCfv H (synCfv H (.cv y)))
      p0233 p0262 p0304 p0652 p0838
  have p0840 :=
    @gEqcomd syntaxFormula0017 (synCfv H (.cv y)) (synCfv H (synCfv H (.cv y))) p0839
  have p0845 :=
    @gF1of1 D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      H
  have p0846 := @gSyl syntaxFormula0004 syntaxFormula0006 syntaxFormula0040 p0076 p0845
  have p0847 := @gSyl syntaxFormula0017 syntaxFormula0004 syntaxFormula0040 p0214 p0846
  have p0881 :=
    @gJca syntaxFormula0017 syntaxFormula0040
      (synWa (.classMem (synCfv H (.cv y)) D) (.classMem (.cv y) D)) p0847 p0777
  have p0882 :=
    @gF1fveq D (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv H (.cv y)) (.cv y) H
  have p0883 :=
    @gSyl syntaxFormula0017
      (synWa syntaxFormula0040
        (synWa (.classMem (synCfv H (.cv y)) D) (.classMem (.cv y) D)))
      (synWb (.classEq (synCfv H (synCfv H (.cv y))) (synCfv H (.cv y)))
        (.classEq (synCfv H (.cv y)) (.cv y)))
      p0881 p0882
  have p0884 :=
    @gBiimpd syntaxFormula0017
      (.classEq (synCfv H (synCfv H (.cv y))) (synCfv H (.cv y)))
      (.classEq (synCfv H (.cv y)) (.cv y)) p0883
  have p0885 :=
    @gMpd syntaxFormula0017
      (.classEq (synCfv H (synCfv H (.cv y))) (synCfv H (.cv y)))
      (.classEq (synCfv H (.cv y)) (.cv y)) p0840 p0884
  have p1025 :=
    @gPm221ddne syntaxFormula0017 syntaxFormula0041 (synCfv H (.cv y)) (.cv y) p0885
      p0585
  have p1026 :=
    @gN3exp syntaxFormula0004 (.classMem (.cv y) (synCdif D (synCdm (synCin H R))))
      syntaxFormula0016 syntaxFormula0041 p1025
  have p1027 :=
    @gRexlimdv syntaxFormula0004 syntaxFormula0016 syntaxFormula0041 y
      (synCdif D (synCdm (synCin H R))) dv_cache_0020 dv_cache_0021 p1026
  have p1028_e00_recanon :
    Nominal.NPrf
      (.imp syntaxFormula0004
        (synWrex y (synCdif D (synCdm (synCin H R))) syntaxFormula0016)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWa, synCin, synCcompl, synCnin, synWnan, synCopab, synWex,
          synWrex, synCdif, synCdm, synCrn, synCima, synCvv, synCcnv, synWral,
          synWbr, synCop, synCun]
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0213
  have p1028 :=
    @gMpd syntaxFormula0004
      (synWrex y (synCdif D (synCdm (synCin H R))) syntaxFormula0016)
      syntaxFormula0041 p1028_e00_recanon p1027
  have p1029 := @gPm201da syntaxFormula0000 syntaxFormula0003 p1028
  exact p1029


end NFChoice.DirectNominalPrf.WPPReplay

end
