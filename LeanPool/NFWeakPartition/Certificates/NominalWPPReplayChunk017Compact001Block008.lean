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

@[expose]
noncomputable def g_hnwcutcodestrictextendndv (x : Var) (z : Var) (w : Var) (v : Var)
    (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) (dv_w_z : w ≠ z)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A))))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv z))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
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
      ((syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0002 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0003 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0004 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem A (syn_cvv)) p0002 p0004
  have p0006 := @g_hwnisoer A
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0005
      p0006
  have p0010 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0003
  have p0011 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0010
  have p0012 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0011
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A)) p0002 p0012
  have p0018 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0011
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (syn_chwcn A)) p0002 p0018
  have p0021 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0022 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0002 p0022
  have p0024 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      p0019 p0023
  have p0025 := @g_hnwcutcodeambientndv x v A dv_cache_0001
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chwcn A))
      p0024 p0025
  have p0030 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0010
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv w) (syn_chwcn A)) p0002 p0030
  have p0032 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0033 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))
      p0032
  have p0034 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w)))
      p0031 p0033
  have p0035 := @g_hnwcutcodeambientndv z w A dv_cache_0002
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (.classMem (.cv w) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
          (.cv z)) (syn_chwcn A))
      p0034 p0035
  have p0039 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0021
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0002 p0039
  have p0042 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))
      p0032
  have p0043 :=
    @g_ertrd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_chwcn A) (syn_chwniso A) (.cv u)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))
      p0007 p0013 p0026 p0036 p0040 p0042
  have p0044 :=
    @g_exp32
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))
      p0043
  have p0045 :=
    @g_reximdvai
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))
      z (syn_cfv (syn_c2nd) (.cv w)) dv_cache_0003 p0044
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.imp (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0001 p0045
  have p0047 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0000 p0046
  exact p0047

@[expose]
noncomputable def g_hncodecmptransisonisondv (w : Var) (v : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv) (_dv_A_w : w ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
          (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))) :=
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
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0001 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0000
  have p0002 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0001
  have p0003 := @g_hwnisoer A
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0002
      p0003
  have p0007 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0001
  have p0008 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0007
  have p0009 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0008
  have p0014 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0008
  have p0018 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0007
  have p0020 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0000
  have p0021 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0022 :=
    @g_ertrd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_chwcn A) (syn_chwniso A) (.cv u) (.cv v) (.cv w) p0004 p0009 p0014 p0018 p0020
      p0021
  have p0023 :=
    @g_orc (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0022 p0023
  have p0034 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0009 p0018
  have p0035 :=
    @g_hncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv z))))))
      p0034 p0035
  have p0037 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0036
  have p0038 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0024 p0037
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

@[expose]
noncomputable def g_hncodecmptransisoncutndv (y : Var) (w : Var) (v : Var) (u : Var)
    (A : Class) (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_u_y : u ≠ y) (dv_v_y : v ≠ y) (dv_w_y : w ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv y))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))) :=
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
  have dv_cache_0002 : Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st) (.cv w))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st) (.cv w))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var)) ((((Class.cv w)).fv) ∪ (((syn_c1st)).fv))
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
                  (show Disjoint (({ z } : Finset Var)) (((syn_c1st)).fv) from
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
  have dv_cache_0004 : z ∉ ((syn_cfv (syn_c2nd) (.cv w))).fv :=
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
      ((syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
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
      ((syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
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
      ((syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))).fv :=
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
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
  have p0001 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
  have p0003 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      p0002 p0003
  have p0005 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0004
  have p0006 := @g_hwnisoer A
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0005
      p0006
  have p0011 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0004
  have p0012 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0011
  have p0013 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0012
  have p0019 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0012
  have p0024 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0011
  have p0027 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      p0024 p0001
  have p0028 := @g_hnwcutcodeambientndv y w A dv_cache_0001
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv w) (syn_chwcn A))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
          (.cv y)) (syn_chwcn A))
      p0027 p0028
  have p0031 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0002 p0031
  have p0034 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      p0000
  have p0035 :=
    @g_ertrd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_chwcn A) (syn_chwniso A) (.cv u) (.cv v)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))
      p0007 p0013 p0019 p0029 p0032 p0034
  have p0036 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      p0001 p0035
  have p0037 :=
    @g_hnwcutcodeeq3 (.cv z) (.cv y) (syn_cfv (syn_c2nd) (.cv w))
      (syn_cfv (syn_c1st) (.cv w)) dv_cache_0002
  have p0038 :=
    @g_breq2d (.classEq (.cv z) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))
      (.cv u) (syn_chwniso A) p0037
  have p0039 :=
    @g_rspcev
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      z (.cv y) (syn_cfv (syn_c2nd) (.cv w)) dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0036 p0039
  have p0041 :=
    @g_exp32
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0040
  have p0042 :=
    @g_rexlimdv
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      y (syn_cfv (syn_c2nd) (.cv w)) dv_cache_0006 dv_cache_0007 p0041
  have p0043 :=
    @g_imp
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0042
  have p0044 :=
    @g_olc
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0043 p0044
  have p0046 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      p0046 p0003
  have p0049 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0048
  have p0050 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0049
  have p0051 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0050
  have p0056 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0049
  have p0057 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0051 p0056
  have p0058 :=
    @g_hncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv z))))))
      p0057 p0058
  have p0060 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0059
  have p0061 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0045 p0060
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

@[expose]
noncomputable def g_hncodecmptranscutonisondv (x : Var) (w : Var) (v : Var) (u : Var)
    (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) (dv_w_x : w ≠ x) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))) :=
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
      ((syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
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
      ((syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))).fv :=
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
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0001 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      p0000 p0001
  have p0003 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0004 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0002 p0003
  have p0008 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0002
  have p0009 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0008
  have p0010 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0009
  have p0015 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0008
  have p0016 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0010 p0015
  have p0018 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) p0000 p0018
  have p0021 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0003
  have p0022 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0019 p0021
  have p0023 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      p0016 p0022
  have p0024 :=
    @g_hnwcutcodetransportndv x z w v A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0023 p0024
  have p0026 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0004 p0025
  have p0027 :=
    @g_hnwcutcodestrictextendndv x z w v u A dv_cache_0007 dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0008 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0026 p0027
  have p0029 :=
    @g_exp32
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0028
  have p0030 :=
    @g_rexlimdv
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      x (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0009 dv_cache_0010 p0029
  have p0031 :=
    @g_imp
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0030
  have p0032 :=
    @g_olc
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0031 p0032
  have p0034 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      p0034 p0001
  have p0037 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0036
  have p0038 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0037
  have p0039 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0038
  have p0044 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0037
  have p0045 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0039 p0044
  have p0046 :=
    @g_hncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0003 dv_cache_0011
      dv_cache_0012
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv z))))))
      p0045 p0046
  have p0048 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0047
  have p0049 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0033 p0048
  have p0050 :=
    @g_exp31
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0049
  have p0051 :=
    @g_com23
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0050
  have p0052 :=
    @g_imp31
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0051
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

@[expose]
noncomputable def g_hncodecmptranscutoncutndv (x : Var) (y : Var) (w : Var) (v : Var)
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y)
    (dv_v_x : v ≠ x) (dv_v_y : v ≠ y) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
            (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv y))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))) :=
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
      ((syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
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
      ((syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
      ((Wff.imp (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv y)))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
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
      ((syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))).fv :=
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
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
  have p0002 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      p0000 p0002
  have p0004 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0003
  have p0005 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0004
  have p0006 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0005
  have p0011 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0004
  have p0012 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0006 p0011
  have p0013 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
  have p0014 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      p0013
  have p0015 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))) p0012 p0014
  have p0017 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      p0013
  have p0019 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0000 p0019
  have p0021 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0020
  have p0022 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0017 p0021
  have p0023 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w))))
      (syn_wa (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      p0015 p0022
  have p0024 :=
    @g_hnwcutcodetransportintocutndv x y z w v A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))) (syn_wa
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0023 p0024
  have p0026 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0000 p0025
  have p0027 :=
    @g_hnwcutcodestrictextendndv x z w v u A dv_cache_0007 dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0008 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0026 p0027
  have p0029 :=
    @g_exp32
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0028
  have p0030 :=
    @g_rexlimdv
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      y (syn_cfv (syn_c2nd) (.cv w)) dv_cache_0009 dv_cache_0010 p0029
  have p0031 :=
    @g_exp32
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (.imp (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0030
  have p0032 :=
    @g_rexlimdv
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (.imp (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      x (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0011 dv_cache_0012 p0031
  have p0033 :=
    @g_imp31
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      p0032
  have p0034 :=
    @g_olc
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0033 p0034
  have p0036 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
  have p0037 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0036
  have p0038 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0037
  have p0039 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0038
  have p0040 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0039
  have p0044 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0038
  have p0045 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0040 p0044
  have p0046 :=
    @g_hncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0003 dv_cache_0013
      dv_cache_0014
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv z))))))
      p0045 p0046
  have p0048 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      p0047
  have p0049 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv z)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0035 p0048
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

@[expose]
noncomputable def g_hncodecmpsettransptndv (w : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
            (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
        (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))) :=
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
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0001 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0002 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)) p0001
  have p0004 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0000
  have p0005 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0004
  have p0006 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0005
  have p0010 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0005
  have p0011 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0006 p0010
  have p0012 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0011 p0012
  have p0014 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0013
  have p0015 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0002 p0014
  have p0016 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0000 p0015
  have p0017 :=
    @g_andi
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0018 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A))))
          (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
            (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))))) (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
          (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      p0017
  have p0019 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0016 p0018
  have p0021 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)) p0001
  have p0028 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0004
  have p0029 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0010 p0028
  have p0030 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv w) dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))
        (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv y))))))
      p0029 p0030
  have p0032 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      p0031
  have p0033 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      p0021 p0032
  have p0034 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
        (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      p0019 p0033
  have p0035 :=
    @g_hncodecmptransisonisondv w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0036 :=
    @g_hncodecmptransisoncutndv y w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0004 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0037 :=
    @g_jaodan
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      p0035 p0036
  have p0038 :=
    @g_hncodecmptranscutonisondv x w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0001 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0039 :=
    @g_hncodecmptranscutoncutndv x y w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0001 dv_cache_0004 dv_cache_0013 dv_cache_0010 dv_cache_0014 dv_cache_0011
      dv_cache_0015 dv_cache_0012 dv_cache_0016
  have p0040 :=
    @g_jaodan
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      p0038 p0039
  have p0041 :=
    @g_jaoian
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w))
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0037 p0040
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
          (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))))) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
          (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
                (.cv y))))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0034 p0041
  exact p0042

@[expose]
noncomputable def g_hncodecmpsettransndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv))
        (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) :=
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
  have dv_cache_0005 : v ∉ ((syn_chwcn A)).fv :=
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
  have dv_cache_0006 : w ∉ ((syn_chwcn A)).fv :=
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
  have dv_cache_0007 : u ∉ ((syn_chncodecmpset A)).fv :=
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
  have dv_cache_0008 : v ∉ ((syn_chncodecmpset A)).fv :=
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
  have dv_cache_0009 : w ∉ ((syn_chncodecmpset A)).fv :=
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
  have dv_cache_0010 : u ∉ ((Wff.classMem A (syn_cvv))).fv :=
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
  have dv_cache_0011 : v ∉ ((Wff.classMem A (syn_cvv))).fv :=
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
  have dv_cache_0012 : w ∉ ((Wff.classMem A (syn_cvv))).fv :=
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
  have p0000 := @g_hncodecmpsetexg A
  have p0001 := @g_hwcnexg A
  have p0002 :=
    @g_simp1 (.classMem A (syn_cvv))
      (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv w) (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0003 :=
    @g_simp2 (.classMem A (syn_cvv))
      (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv w) (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0004 :=
    @g_simp1d
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv w) (syn_chwcn A)) p0003
  have p0006 :=
    @g_simp2d
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv w) (syn_chwcn A)) p0003
  have p0007 :=
    @g_jca
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0004 p0006
  have p0009 :=
    @g_simp3d
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv w) (syn_chwcn A)) p0003
  have p0010 :=
    @g_jca
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0007 p0009
  have p0011 :=
    @g_jca
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv w) (syn_chwcn A)))
      p0002 p0010
  have p0012 :=
    @g_simp3 (.classMem A (syn_cvv))
      (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv w) (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0013 :=
    @g_jca
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv w) (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
      p0011 p0012
  have p0014 :=
    @g_hncodecmpsettransptndv w v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0015 :=
    @g_syl
      (syn_w3a (.classMem A (syn_cvv))
        (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv w) (syn_chwcn A))))
        (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0013 p0014
  have p0016 :=
    @g_trrd (.classMem A (syn_cvv)) u v w (syn_chwcn A) (syn_chncodecmpset A) (syn_cvv)
      (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
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

@[expose]
noncomputable def g_hnwcutcodeselfnoisondv (x : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.neg
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
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
      ((syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
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
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0001 := @g_hwcnweclndv A (.cv u)
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0000
      p0001
  have p0003 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0004 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0002 p0003
  have p0005 := @g_vex h
  have p0006 :=
    @g_a1i (.classMem (.cv h) (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0005
  have p0007 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv h) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_strictsegnoiso x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (.cv h)
  have p0009 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (syn_wa
          (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv h) (syn_cvv)))
      (.neg (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u))
            (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0007 p0008
  have p0010 :=
    @g_nexdv
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      h dv_cache_0001 p0009
  have p0012 := @g_hnwcutcodeambientndv x u A dv_cache_0002
  have p0013 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0000 p0012
  have p0014 :=
    @g_hwnisodirectisobclndv A (.cv u)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      h dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0015 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))))))
      p0013 p0014
  have p0016 := @g_hnwcutcodepartsndv x u A dv_cache_0002
  have p0017 :=
    @g_simpld
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0016
  have p0018 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (.cv h)
  have p0019 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0017 p0018
  have p0021 :=
    @g_simprd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0016
  have p0022 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cfv (syn_c1st) (.cv u))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (.cv h)
  have p0023 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0021 p0022
  have p0024 :=
    @g_bitrd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0019 p0023
  have p0025 :=
    @g_exbidv
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      h dv_cache_0001 p0024
  have p0026 :=
    @g_bitrd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0015 p0025
  have p0027 :=
    @g_biimpd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0026
  have p0028 :=
    @g_mtod
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0010 p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end
