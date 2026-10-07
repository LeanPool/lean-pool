/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part032`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodestrictextendndv`. -/
@[expose]
noncomputable def gHnwcutcodestrictextendndv (x : Var) (z : Var) (w : Var) (v : Var)
    (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) (dv_w_z : w ≠ z)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A))))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
              (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x))))) (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x)) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv z))))) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z))))) :=
  by
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, dv_A_z, (Ne.symm dv_u_z), (Ne.symm dv_v_z),
          (Ne.symm dv_w_z), (Ne.symm dv_x_z), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
  have p0001 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
  have p0002 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
  have p0003 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0004 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0003
  have p0005 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem A (synCvv)) p0002 p0004
  have p0006 := @gHwnisoer A
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synChwcn A)) p0005
      p0006
  have p0010 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0003
  have p0011 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0010
  have p0012 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0011
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (synChwcn A)) p0002 p0012
  have p0018 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0011
  have p0019 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (synChwcn A)) p0002 p0018
  have p0021 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0022 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0021
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0002 p0022
  have p0024 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      p0019 p0023
  have p0025 := @gHnwcutcodeambientndv x v A dv_cache_0001
  have p0026 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChwcn A))
      p0024 p0025
  have p0030 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0010
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv w) (synChwcn A)) p0002 p0030
  have p0032 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
  have p0033 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv w)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z)))
      p0032
  have p0034 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv w) (synChwcn A)) (.classMem (.cv z) (synCfv (synC2nd) (.cv w)))
      p0031 p0033
  have p0035 := @gHnwcutcodeambientndv z w A dv_cache_0002
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (.classMem (.cv w) (synChwcn A))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv w))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
          (.cv z)) (synChwcn A))
      p0034 p0035
  have p0039 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0021
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0002 p0039
  have p0042 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv w)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z)))
      p0032
  have p0043 :=
    @gErtrd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv w))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synChwcn A) (synChwniso A) (.cv u)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))
      p0007 p0013 p0026 p0036 p0040 p0042
  have p0044 :=
    @gExp32
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv w)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z)))
      p0043
  have p0045 :=
    @gReximdvai
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z)))
      z (synCfv (synC2nd) (.cv w)) dv_cache_0003 p0044
  have p0046 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.imp (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0001 p0045
  have p0047 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0000 p0046
  exact p0047

/-- Checked nominal proof certificate identified upstream as `g_hncodecmptransisonisondv`. -/
@[expose]
noncomputable def gHncodecmptransisonisondv (w : Var) (v : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv) (_dv_A_w : w ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
          (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWbr (.cv u) (synChncodecmpset A) (.cv w))) :=
  by
  let proofSupport : Finset Var :=
    ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_w : z ≠ w := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_A : z ∉ A.fv := by
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
  have dv_cache_0002 : z ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_u, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0001 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0000
  have p0002 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0001
  have p0003 := @gHwnisoer A
  have p0004 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synChwcn A)) p0002
      p0003
  have p0007 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0001
  have p0008 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0007
  have p0009 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0008
  have p0014 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0008
  have p0018 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0007
  have p0020 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0000
  have p0021 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0022 :=
    @gErtrd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synChwcn A) (synChwniso A) (.cv u) (.cv v) (.cv w) p0004 p0009 p0014 p0018 p0020
      p0021
  have p0023 :=
    @gOrc (synWbr (.cv u) (synChwniso A) (.cv w))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv u) (synChwniso A) (.cv w))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0022 p0023
  have p0034 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0009 p0018
  have p0035 :=
    @gHncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv w))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv w))
          (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv z))))))
      p0034 p0035
  have p0037 :=
    @gBiimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0036
  have p0038 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0024 p0037
  exact p0038


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part033`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmptransisoncutndv`. -/
@[expose]
noncomputable def gHncodecmptransisoncutndv (y : Var) (w : Var) (v : Var) (u : Var)
    (A : Class) (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_u_y : u ≠ y) (dv_v_y : v ≠ y) (dv_w_y : w ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
          (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv y))))) (synWbr (.cv u) (synChncodecmpset A) (.cv w))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : w ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((Class.cv z)).fv ((synCfv (synC1st) (.cv w))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv z)).fv ((synCfv (synC1st) (.cv w))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var)) ((((Class.cv w)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ z } : Finset Var)) (((Class.cv w)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ z } : Finset Var)) (({ w } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show z ∉ ({ w } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show z ≠ w from (by exact fresh_z_ne_w)))))))),
                  (show Disjoint (({ z } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ z } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
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
  have dv_cache_0004 : z ∉ ((synCfv (synC2nd) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
            (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_ne_y, fresh_z_ne_w, fresh_z_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉
      ((synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_w_y), (Ne.symm dv_u_y),
          fresh_y_ne_z, dv_A_y, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWbr (.cv u) (synChwniso A) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_u_y), (Ne.symm dv_v_y),
          (Ne.symm dv_w_y), compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_u, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
  have p0001 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      p0000
  have p0002 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
  have p0003 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0004 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      p0002 p0003
  have p0005 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0004
  have p0006 := @gHwnisoer A
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synChwcn A)) p0005
      p0006
  have p0011 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0004
  have p0012 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0011
  have p0013 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0012
  have p0019 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0012
  have p0024 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0011
  have p0027 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv w) (synChwcn A)) (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      p0024 p0001
  have p0028 := @gHnwcutcodeambientndv y w A dv_cache_0001
  have p0029 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv w) (synChwcn A))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv w))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
          (.cv y)) (synChwcn A))
      p0027 p0028
  have p0031 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0002 p0031
  have p0034 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      p0000
  have p0035 :=
    @gErtrd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synChwcn A) (synChwniso A) (.cv u) (.cv v)
      (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))
      p0007 p0013 p0019 p0029 p0032 p0034
  have p0036 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      p0001 p0035
  have p0037 :=
    @gHnwcutcodeeq3 (.cv z) (.cv y) (synCfv (synC2nd) (.cv w))
      (synCfv (synC1st) (.cv w)) dv_cache_0002
  have p0038 :=
    @gBreq2d (.classEq (.cv z) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))
      (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))
      (.cv u) (synChwniso A) p0037
  have p0039 :=
    @gRspcev
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      z (.cv y) (synCfv (synC2nd) (.cv w)) dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0038
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0036 p0039
  have p0041 :=
    @gExp32
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0040
  have p0042 :=
    @gRexlimdv
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      y (synCfv (synC2nd) (.cv w)) dv_cache_0006 dv_cache_0007 p0041
  have p0043 :=
    @gImp
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0042
  have p0044 :=
    @gOlc
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      (synWbr (.cv u) (synChwniso A) (.cv w))
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0043 p0044
  have p0046 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
  have p0048 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      p0046 p0003
  have p0049 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0048
  have p0050 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0049
  have p0051 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0050
  have p0056 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0049
  have p0057 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0051 p0056
  have p0058 :=
    @gHncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0059 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv w))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv w))
          (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv z))))))
      p0057 p0058
  have p0060 :=
    @gBiimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0059
  have p0061 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0045 p0060
  exact p0061


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part034`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmptranscutonisondv`. -/
@[expose]
noncomputable def gHncodecmptranscutonisondv (x : Var) (w : Var) (v : Var) (u : Var)
    (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) (dv_w_x : w ≠ x) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
              (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x))))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWbr (.cv u) (synChncodecmpset A) (.cv w))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_w : z ≠ w := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0004 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0005 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0007 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0008 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0009 :
    x ∉
      ((synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_w_x), (Ne.symm dv_u_x),
          fresh_x_ne_z, dv_A_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWbr (.cv v) (synChwniso A) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, (Ne.symm dv_u_x), (Ne.symm dv_v_x),
          (Ne.symm dv_w_x), compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_u, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0001 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      p0000 p0001
  have p0003 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0004 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0002 p0003
  have p0008 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0002
  have p0009 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0008
  have p0010 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0009
  have p0015 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0008
  have p0016 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0010 p0015
  have p0018 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0019 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv v) (synChwniso A) (.cv w)) p0000 p0018
  have p0021 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0003
  have p0022 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0019 p0021
  have p0023 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWa (synWbr (.cv v) (synChwniso A) (.cv w))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      p0016 p0022
  have p0024 :=
    @gHnwcutcodetransportndv x z w v A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0025 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv v) (synChwniso A) (.cv w))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0023 p0024
  have p0026 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0004 p0025
  have p0027 :=
    @gHnwcutcodestrictextendndv x z w v u A dv_cache_0007 dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0008 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0026 p0027
  have p0029 :=
    @gExp32
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0028
  have p0030 :=
    @gRexlimdv
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      x (synCfv (synC2nd) (.cv v)) dv_cache_0009 dv_cache_0010 p0029
  have p0031 :=
    @gImp
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0030
  have p0032 :=
    @gOlc
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      (synWbr (.cv u) (synChwniso A) (.cv w))
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0031 p0032
  have p0034 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      p0034 p0001
  have p0037 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0036
  have p0038 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0037
  have p0039 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0038
  have p0044 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0037
  have p0045 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0039 p0044
  have p0046 :=
    @gHncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0003 dv_cache_0011
      dv_cache_0012
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv w))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv w))
          (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv z))))))
      p0045 p0046
  have p0048 :=
    @gBiimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0047
  have p0049 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0033 p0048
  have p0050 :=
    @gExp31
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0049
  have p0051 :=
    @gCom23
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0050
  have p0052 :=
    @gImp31
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0051
  exact p0052


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmptranscutoncutndv`. -/
@[expose]
noncomputable def gHncodecmptranscutoncutndv (x : Var) (y : Var) (w : Var) (v : Var)
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y)
    (dv_v_x : v ≠ x) (dv_v_y : v ≠ y) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
              (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
            (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv y))))) (synWbr (.cv u) (synChncodecmpset A) (.cv w))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ w } : Finset Var) ∪
          ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0004 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0005 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0007 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0008 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0009 :
    y ∉
      ((synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_w_y), (Ne.symm dv_u_y),
          fresh_y_ne_z, dv_A_y, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_u_y), (Ne.symm dv_v_y),
          (Ne.symm dv_w_y), (Ne.symm dv_x_y), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    x ∉
      ((Wff.imp (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv y)))) (synWrex z (synCfv (synC2nd) (.cv w))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_w_x), (Ne.symm dv_v_x),
          dv_x_y, dv_A_x, (Ne.symm dv_u_x), fresh_x_ne_z, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, (Ne.symm dv_u_x), (Ne.symm dv_v_x),
          (Ne.symm dv_w_x), compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv u)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_u, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
  have p0002 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0003 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      p0000 p0002
  have p0004 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0003
  have p0005 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0004
  have p0006 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0005
  have p0011 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0004
  have p0012 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0006 p0011
  have p0013 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
  have p0014 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      p0013
  have p0015 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w))) p0012 p0014
  have p0017 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      p0013
  have p0019 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0000 p0019
  have p0021 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0020
  have p0022 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0017 p0021
  have p0023 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv w))))
      (synWa (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      p0015 p0022
  have p0024 :=
    @gHnwcutcodetransportintocutndv x y z w v A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0025 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa
          (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))) (synWa
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0023 p0024
  have p0026 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0000 p0025
  have p0027 :=
    @gHnwcutcodestrictextendndv x z w v u A dv_cache_0007 dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0008 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0026 p0027
  have p0029 :=
    @gExp32
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv w)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0028
  have p0030 :=
    @gRexlimdv
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      y (synCfv (synC2nd) (.cv w)) dv_cache_0009 dv_cache_0010 p0029
  have p0031 :=
    @gExp32
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (.imp (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0030
  have p0032 :=
    @gRexlimdv
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (.imp (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      x (synCfv (synC2nd) (.cv v)) dv_cache_0011 dv_cache_0012 p0031
  have p0033 :=
    @gImp31
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      p0032
  have p0034 :=
    @gOlc
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      (synWbr (.cv u) (synChwniso A) (.cv w))
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv z))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0033 p0034
  have p0036 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
  have p0037 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0036
  have p0038 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0037
  have p0039 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0038
  have p0040 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0039
  have p0044 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0038
  have p0045 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0040 p0044
  have p0046 :=
    @gHncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0003 dv_cache_0013
      dv_cache_0014
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv w))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv w))
          (synWrex z (synCfv (synC2nd) (.cv w)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv z))))))
      p0045 p0046
  have p0048 :=
    @gBiimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      p0047
  have p0049 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv w)) (synWrex z (synCfv (synC2nd) (.cv w))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv z)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0035 p0048
  exact p0049


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsettransptndv`. -/
@[expose]
noncomputable def gHncodecmpsettransptndv (w : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
            (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
        (synWbr (.cv u) (synChncodecmpset A) (.cv w))) :=
  by
  let proofSupport : Finset Var :=
    ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_w : x ≠ w := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_w : y ≠ w := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0007 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0008 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0009 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0010 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0011 : v ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0012 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0013 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0014 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0015 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0016 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv w)))
  have p0001 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv w)))
  have p0002 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv w)) p0001
  have p0004 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0000
  have p0005 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0004
  have p0006 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0005
  have p0010 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0005
  have p0011 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0006 p0010
  have p0012 :=
    @gHncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0011 p0012
  have p0014 :=
    @gBiimpd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0013
  have p0015 :=
    @gMpd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0002 p0014
  have p0016 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0000 p0015
  have p0017 :=
    @gAndi
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0018 :=
    @gA1i
      (synWb (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A))))
          (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
            (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x)))))) (synWo (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
          (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
              (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x)))))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      p0017
  have p0019 :=
    @gMpbid
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (synWo (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0016 p0018
  have p0021 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv w)) p0001
  have p0028 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0004
  have p0029 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0010 p0028
  have p0030 :=
    @gHncodecmpsetstrictcutsemclndv y A (.cv v) (.cv w) dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0031 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWb (synWbr (.cv v) (synChncodecmpset A) (.cv w))
        (synWo (synWbr (.cv v) (synChwniso A) (.cv w))
          (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv y))))))
      p0029 p0030
  have p0032 :=
    @gBiimpd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWbr (.cv v) (synChncodecmpset A) (.cv w))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv w)) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      p0031
  have p0033 :=
    @gMpd
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWbr (.cv v) (synChncodecmpset A) (.cv w))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv w)) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      p0021 p0032
  have p0034 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWo (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
        (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv w)) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      p0019 p0033
  have p0035 :=
    @gHncodecmptransisonisondv w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0036 :=
    @gHncodecmptransisoncutndv y w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0004 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0037 :=
    @gJaodan
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      p0035 p0036
  have p0038 :=
    @gHncodecmptranscutonisondv x w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0001 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0039 :=
    @gHncodecmptranscutoncutndv x y w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0001 dv_cache_0004 dv_cache_0013 dv_cache_0010 dv_cache_0014 dv_cache_0011
      dv_cache_0015 dv_cache_0012 dv_cache_0016
  have p0040 :=
    @gJaodan
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      p0038 p0039
  have p0041 :=
    @gJaoian
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv w)) (synWrex y (synCfv (synC2nd) (.cv w))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0037 p0040
  have p0042 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (synWo (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWbr (.cv u) (synChwniso A) (.cv v)))
          (synWa (synWa (.classMem A (synCvv)) (synWa
                (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
                (.classMem (.cv w) (synChwcn A)))) (synWrex x (synCfv (synC2nd) (.cv v))
              (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x)))))) (synWo (synWbr (.cv v) (synChwniso A) (.cv w))
          (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
                (.cv y))))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0034 p0041
  exact p0042

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsettransndv`. -/
@[expose]
noncomputable def gHncodecmpsettransndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv))
        (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
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
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
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
  have dv_cache_0005 : v ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_w_not_A, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((synChncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0008 : v ∉ ((synChncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((synChncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_w_not_A, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_v_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_w_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0014 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0015 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have p0000 := @gHncodecmpsetexg A
  have p0001 := @gHwcnexg A
  have p0002 :=
    @gSimp1 (.classMem A (synCvv))
      (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv w) (synChwcn A)))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv w)))
  have p0003 :=
    @gSimp2 (.classMem A (synCvv))
      (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv w) (synChwcn A)))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv w)))
  have p0004 :=
    @gSimp1d
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv w) (synChwcn A)) p0003
  have p0006 :=
    @gSimp2d
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv w) (synChwcn A)) p0003
  have p0007 :=
    @gJca
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0004 p0006
  have p0009 :=
    @gSimp3d
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv w) (synChwcn A)) p0003
  have p0010 :=
    @gJca
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0007 p0009
  have p0011 :=
    @gJca
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv w) (synChwcn A)))
      p0002 p0010
  have p0012 :=
    @gSimp3 (.classMem A (synCvv))
      (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv w) (synChwcn A)))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv w)))
  have p0013 :=
    @gJca
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv w) (synChwcn A))))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv w)))
      p0011 p0012
  have p0014 :=
    @gHncodecmpsettransptndv w v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0015 :=
    @gSyl
      (synW3a (.classMem A (synCvv))
        (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv w) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWbr (.cv v) (synChncodecmpset A) (.cv w))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv w)) p0013 p0014
  have p0016 :=
    @gTrrd (.classMem A (synCvv)) u v w (synChwcn A) (synChncodecmpset A) (synCvv)
      (synCvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 p0000 p0001 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeselfnoisondv`. -/
@[expose]
noncomputable def gHnwcutcodeselfnoisondv (x : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.neg
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_x : h ≠ x := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    h ∉
      ((synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, fresh_h_not_A, fresh_h_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
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
  have dv_cache_0004 : h ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_u, not_false_eq_true])
  have dv_cache_0005 :
    h ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_x, fresh_h_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0001 := @gHwcnweclndv A (.cv u)
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0000
      p0001
  have p0003 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0004 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0002 p0003
  have p0005 := @gVex h
  have p0006 :=
    @gA1i (.classMem (.cv h) (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0005
  have p0007 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv h) (synCvv)) p0004 p0006
  have p0008 :=
    @gStrictsegnoiso x (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) (.cv h)
  have p0009 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (synWa
          (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classMem (.cv h) (synCvv)))
      (.neg (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCin (synCfv (synC1st) (.cv u))
            (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0007 p0008
  have p0010 :=
    @gNexdv
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCin (synCfv (synC1st) (.cv u))
          (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      h dv_cache_0001 p0009
  have p0012 := @gHnwcutcodeambientndv x u A dv_cache_0002
  have p0013 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0000 p0012
  have p0014 :=
    @gHwnisodirectisobclndv A (.cv u)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      h dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0015 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)))
      (synWb (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))))))
      p0013 p0014
  have p0016 := @gHnwcutcodepartsndv x u A dv_cache_0002
  have p0017 :=
    @gSimpld
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0016
  have p0018 :=
    @gIsoeq3 (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st) (.cv u))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (.cv h)
  have p0019 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))) (synWiso (.cv h) (synCfv (synC1st) (.cv u))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0017 p0018
  have p0021 :=
    @gSimprd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0016
  have p0022 :=
    @gIsoeq5 (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCfv (synC1st) (.cv u))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (.cv h)
  have p0023 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv u))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))) (synWiso (.cv h) (synCfv (synC1st) (.cv u))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0021 p0022
  have p0024 :=
    @gBitrd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCin (synCfv (synC1st) (.cv u))
          (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCin (synCfv (synC1st) (.cv u))
          (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0019 p0023
  have p0025 :=
    @gExbidv
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCin (synCfv (synC1st) (.cv u))
          (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      h dv_cache_0001 p0024
  have p0026 :=
    @gBitrd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0015 p0025
  have p0027 :=
    @gBiimpd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0026
  have p0028 :=
    @gMtod
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCfv (synC2nd) (.cv u))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0010 p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end
