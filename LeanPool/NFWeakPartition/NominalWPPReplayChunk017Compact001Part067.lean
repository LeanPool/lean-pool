/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block015

/-! NF weak partition development: NominalWPPReplayChunk017Compact001Part067. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppstopfixedhitcontrgrowfixdndv (ph : Wff) (ps : Wff) (ch : Wff)
    (x : Var) (y : Var) (C : Class) (k : Var) (m : Var) (n : Var) (F : Class) (I : Class)
    (p : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv)
    (dv_C_p : p ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_F_x : x ∉ F.fv)
    (dv_F_y : y ∉ F.fv) (dv_I_k : k ∉ I.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv)
    (_dv_I_p : p ∉ I.fv) (dv_I_x : x ∉ I.fv) (dv_I_y : y ∉ I.fv) (dv_ch_n : n ∉ ch.fv)
    (_dv_ch_p : p ∉ ch.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_k_m : k ≠ m)
    (dv_k_n : k ≠ n) (_dv_k_p : k ≠ p) (dv_k_x : k ≠ x) (dv_k_y : k ≠ y) (dv_m_n : m ≠ n)
    (_dv_m_p : m ≠ p) (dv_m_x : m ≠ x) (_dv_m_y : m ≠ y) (_dv_n_p : n ≠ p)
    (dv_n_ph : n ∉ ph.fv) (dv_n_ps : n ∉ ps.fv) (dv_n_x : n ≠ x) (dv_n_y : n ≠ y)
    (_dv_p_ph : p ∉ ph.fv) (_dv_p_ps : p ∉ ps.fv) (_dv_p_x : p ≠ x) (dv_p_y : p ≠ y)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_wppstopfixedhitcontrgrowfixdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopfixedhitcontrgrowfixdndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_3 :
      Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C))
    (hyp_wppstopfixedhitcontrgrowfixdndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_6 : Nominal.NPrf
        (syn_wral x (syn_cdm (syn_cwppstopstep F C))
          (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_7 :
      Nominal.NPrf (.classMem I (syn_chwcards (syn_cvv))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_9 : Nominal.NPrf (syn_wral y (syn_chwcards (syn_cvv))
          (.imp (syn_wbr C (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_10 : Nominal.NPrf (.imp ph
          (syn_wa (.classMem (.cv m) (syn_cnnc))
            (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C))
              (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_11 : Nominal.NPrf (.imp ps
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C)))
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_12 : Nominal.NPrf (.imp ch
          (syn_wral y (syn_cdm (syn_cwppstopstep F C))
            (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
              (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))) :
    Nominal.NPrf
      (.imp (.classEq I (syn_ctc I))
        (.imp (syn_wa ph (syn_wa ps ch)) (.neg (.classEq (syn_c0c) (syn_c0c))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ C.fv ∪
                ({ k } : Finset Var) ∪
              ({ m } : Finset Var) ∪
            ({ n } : Finset Var) ∪
          F.fv ∪
        I.fv ∪
      ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let s : Var := freshVar proofSupport 2
  let d : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let z : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_q : y ≠ q := Ne.symm fresh_q_ne_y
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_q_ne_k : q ≠ k := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_q : n ≠ q := Ne.symm fresh_q_ne_n
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_I : q ∉ I.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_ph : r ∉ ph.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                          (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_r_not_ps : r ∉ ps.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                          (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_r_not_ch : r ∉ ch.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_r_ne_n : r ≠ n := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_r : n ≠ r := Ne.symm fresh_r_ne_n
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_I : r ∉ I.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_s_ne_k : s ≠ k := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_s : k ≠ s := Ne.symm fresh_s_ne_k
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_d_ne_k : d ≠ k := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_d : k ≠ d := Ne.symm fresh_d_ne_k
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_k : a ≠ k := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_z_ne_k : z ≠ k := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have fresh_r_ne_z : r ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_z_ne_r : z ≠ r := Ne.symm fresh_r_ne_z
  have fresh_r_ne_b : r ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_r : b ≠ r := Ne.symm fresh_r_ne_b
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have dv_cache_0001 : n ∉ ((syn_wa (.classEq I (syn_ctc I)) ph)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_I_n,
          dv_n_ph, or_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_wa (.classEq I (syn_ctc I)) ps)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_I_n,
          dv_n_ps, or_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 :
    d ∉ ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    s ∉ ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    d ∉
      ((syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_cwe) (syn_c0)) (.classEq (syn_c0c) (syn_cnc (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    s ∉
      ((syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_cwe) (syn_c0)) (.classEq (syn_c0c) (syn_cnc (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0010 : s ∉ ((Wff.classEq (.cv k) (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Wff.classEq (.cv k) (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 : d ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0013 : k ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show k ≠ s from (by exact fresh_k_ne_s))
  have dv_cache_0014 : k ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 :
    k ∉
      ((syn_wb (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
              (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
                (.classEq (syn_c0c) (syn_cnc (.cv d)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_s, fresh_k_ne_d,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 :
    x ∉
      ((syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
          (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0018 :
    x ∉
      ((Wff.classMem (syn_c0c)
          (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
            (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
  have dv_cache_0020 :
    x ∉
      ((Wff.classMem (.cv y)
          (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
            (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0023 : a ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0024 : z ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_b, not_false_eq_true])
  have dv_cache_0025 : z ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0026 : a ∉ ((Class.cv b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_b, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((syn_cnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0028 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0029 : x ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0030 : b ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show b ≠ r from (by exact fresh_b_ne_r))
  have dv_cache_0031 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0032 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0033 : b ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show b ≠ z from (by exact fresh_b_ne_z))
  have dv_cache_0034 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0035 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0036 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0037 : x ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0038 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0039 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0040 : r ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0041 : b ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0042 : r ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0043 : b ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0044 :
    r ∉
      ((syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp
                (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a))
                  (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)))
                (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_a,
          fresh_r_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0045 :
    b ∉
      ((syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp
                (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a))
                  (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)))
                (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a,
          fresh_b_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0046 : r ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (show r ≠ b from (by exact fresh_r_ne_b))
  have dv_cache_0047 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0048 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0049 : a ∉ ((syn_cplc (.cv y) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0050 : z ∉ ((syn_cplc (.cv y) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0051 : z ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_k, not_false_eq_true])
  have dv_cache_0052 :
    x ∉
      ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a))
            (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, fresh_x_ne_a, fresh_x_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0053 :
    z ∉
      ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
            (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0054 :
    a ∉
      ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
            (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0055 : x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0056 : a ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_k, not_false_eq_true])
  have dv_cache_0057 :
    x ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a))
            (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)))
          (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, fresh_x_ne_a, fresh_x_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0058 :
    z ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
          (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0059 :
    a ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))
          (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_k, fresh_a_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0060 : n ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0061 : q ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0062 :
    q ∉
      ((Wff.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_n, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I,
          fresh_q_ne_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0063 :
    n ∉
      ((Wff.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_q, dv_C_n, dv_F_n, dv_I_n, (Ne.symm dv_k_n),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0064 : q ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_y, not_false_eq_true])
  have dv_cache_0065 :
    q ∉
      ((Wff.imp (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_y, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I,
          fresh_q_ne_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0066 : q ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_q_not_C, fresh_q_not_F, or_false, not_false_eq_true])
  have dv_cache_0067 : q ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_q_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0068 :
    q ∉
      ((Wff.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv
                (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wbr (syn_cfv
              (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))
            (syn_clec) (syn_ctc C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_C, fresh_q_ne_y, fresh_q_not_F, fresh_q_not_I,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0069 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0070 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0071 : p ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact (show p ≠ y from (by exact dv_p_y))
  have dv_cache_0072 :
    y ∉
      ((syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
            (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_C_y, dv_F_y, dv_I_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0073 : y ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0074 :
    y ∉
      ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))
          (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv
                (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv
                (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_C_y, dv_F_y, dv_I_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0075 :
    q ∉
      ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C))
          (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv
                (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv
                (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_y, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0076 :
    x ∉
      ((Wff.classMem (syn_cplc (.cv y) (syn_c1c))
          (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
            (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0077 :
    y ∉
      ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps)
            (syn_wa (.classEq I (syn_ctc I)) ch)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_I_y,
          dv_ph_y, dv_ps_y, dv_ch_y, or_false, not_false_eq_true])
  have dv_cache_0078 : y ∉ (syn_wtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0079 :
    y ∉
      ((Class.cab x (.classMem (.cv x)
            (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, dv_F_y,
          dv_I_y, (Ne.symm dv_k_y), compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0080 : x ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_n_x), not_false_eq_true])
  have dv_cache_0081 :
    x ∉
      ((Wff.classMem (.cv n)
          (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
            (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_n_x), dv_C_x, dv_F_x, dv_I_x,
          (Ne.symm dv_k_x), compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0082 :
    n ∉
      ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps)
            (syn_wa (.classEq I (syn_ctc I)) ch)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_I_n,
          dv_n_ph, dv_n_ps, dv_ch_n, or_false, not_false_eq_true])
  have dv_cache_0083 : n ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_k_n), not_false_eq_true])
  have dv_cache_0084 :
    n ∉
      ((Wff.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv
              (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
              (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
                (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_k_n), dv_C_n, dv_F_n, dv_I_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0085 : y ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0086 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0087 : y ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0088 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0089 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0090 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0091 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0092 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0093 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0094 : a ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0095 :
    r ∉
      ((syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc)
            (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
              (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0096 :
    a ∉
      ((syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc)
            (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
              (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0097 : y ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_n_y), not_false_eq_true])
  have dv_cache_0098 : y ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_k_y), not_false_eq_true])
  have dv_cache_0099 :
    x ∉
      ((syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_n_x), dv_x_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0100 :
    y ∉
      ((syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_n_y), (Ne.symm dv_k_y),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0101 : q ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_n, not_false_eq_true])
  have dv_cache_0102 :
    q ∉
      ((Wff.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_n, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I,
          fresh_q_ne_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0103 :
    q ∉
      ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_n, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0104 :
    n ∉
      ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_q, dv_C_n, dv_F_n, dv_I_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0105 :
    y ∉
      ((syn_cfv (syn_cfrec (syn_cwppstopstep F C)
            (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, dv_C_y, dv_F_y, dv_I_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0106 : y ∉ ((syn_cdm (syn_cwppstopstep F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_y, dv_F_y, or_false, not_false_eq_true])
  have dv_cache_0107 :
    y ∉
      ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec)
            (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_y, fresh_y_ne_r, dv_F_y, dv_I_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0108 : y ∉ ((Wff.classMem (.cv r) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0109 :
    r ∉
      ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps)
            (syn_wa (.classEq I (syn_ctc I)) ch)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_r_not_I, fresh_r_not_ph, fresh_r_not_ps, fresh_r_not_ch, or_false,
          not_false_eq_true])
  have dv_cache_0110 : k ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_k, dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0111 : m ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_m, dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0112 : n ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0113 : q ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_q_not_C, fresh_q_not_F, or_false, not_false_eq_true])
  have dv_cache_0114 : r ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0115 : k ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_k, not_false_eq_true])
  have dv_cache_0116 : m ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_m, not_false_eq_true])
  have dv_cache_0117 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0118 : q ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_C, not_false_eq_true])
  have dv_cache_0119 : r ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_C, not_false_eq_true])
  have dv_cache_0120 : k ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_I_k,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0121 : m ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_I_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0122 : n ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_I_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0123 : r ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_r_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0124 : k ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_k,
          not_false_eq_true])
  have dv_cache_0125 : m ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_m,
          not_false_eq_true])
  have dv_cache_0126 : n ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_n,
          not_false_eq_true])
  have dv_cache_0127 : q ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_q_not_C,
          not_false_eq_true])
  have dv_cache_0128 : r ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_r_not_C,
          not_false_eq_true])
  have dv_cache_0129 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0130 : k ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129
    exact (show k ≠ n from (by exact dv_k_n))
  have dv_cache_0131 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0132 : n ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
    exact (show n ≠ q from (by exact fresh_n_ne_q))
  have dv_cache_0133 : n ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132
    exact (show n ≠ r from (by exact fresh_n_ne_r))
  have dv_cache_0134 : x ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_x, dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0135 : x ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_x,
          dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0136 : x ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_I_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0137 : n ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_m_n), not_false_eq_true])
  have dv_cache_0138 :
    n ∉
      ((syn_wb (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C)
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv m))
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_m_n), dv_C_n, dv_F_n, dv_I_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0139 : n ∉ ((syn_ctc (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_m_n), not_false_eq_true])
  have dv_cache_0140 :
    n ∉
      ((Wff.imp (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_m_n), dv_C_n, dv_F_n, dv_I_n,
          (Ne.symm dv_k_n), compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0141 : x ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_k_x), not_false_eq_true])
  have dv_cache_0142 : n ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_n_x,
          not_false_eq_true])
  have dv_cache_0143 :
    n ∉
      ((syn_wb (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C)
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv x))
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, dv_n_x, dv_C_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0144 :
    n ∉
      ((Wff.imp (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C)
              (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C))
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, dv_n_x, dv_C_n, dv_F_n, dv_I_n, (Ne.symm dv_m_n),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0145 :
    x ∉ ((syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_m_x), (Ne.symm dv_k_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0146 :
    x ∉
      ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps)
            (syn_wa (.classEq I (syn_ctc I)) ch)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_I_x,
          dv_ph_x, dv_ps_x, dv_ch_x, or_false, not_false_eq_true])
  have dv_cache_0147 :
    y ∉
      ((syn_cfv (syn_cfrec (syn_cwppstopstep F C)
            (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, dv_F_y, dv_I_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0148 :
    y ∉
      ((Wff.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (syn_cfv
              (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
              (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, Finset.mem_union,
          Finset.mem_singleton, dv_C_y, (Ne.symm dv_x_y), dv_F_y, dv_I_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0149 : y ∉ ((Wff.classMem (.cv x) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0150 : x ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_m_x), not_false_eq_true])
  have dv_cache_0151 :
    x ∉
      ((Wff.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wne (syn_cfv
              (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
              (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                  (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, Finset.mem_union,
          Finset.mem_singleton, dv_C_x, (Ne.symm dv_m_x), dv_F_x, dv_I_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  let syntaxFormula0000 : Wff :=
    (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))
  let syntaxFormula0001 : Wff :=
    (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0000)
  let syntaxFormula0002 : Wff :=
    (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxFormula0003 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0002)
  let syntaxFormula0004 : Wff :=
    (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C)) syntaxFormula0003)
  let syntaxFormula0005 : Wff := (syn_wa (.classMem (.cv m) (syn_cnnc)) syntaxFormula0004)
  let syntaxClass0006 : Class :=
    (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)
  let syntaxFormula0007 : Wff := (.classMem (.cv n) syntaxClass0006)
  let syntaxFormula0008 : Wff :=
    (.imp syntaxFormula0007 (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxFormula0009 : Wff := (.classMem (.cv m) syntaxClass0006)
  let syntaxFormula0010 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0008)
  let syntaxFormula0011 : Wff := (syn_wa syntaxFormula0009 syntaxFormula0010)
  let syntaxFormula0012 : Wff := (syn_wa (.classMem (.cv m) (syn_cnnc)) syntaxFormula0011)
  let syntaxFormula0013 : Wff :=
    (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C)))
  let syntaxFormula0014 : Wff :=
    (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C)))
  let syntaxFormula0015 : Wff :=
    (.imp syntaxFormula0014 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxFormula0016 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0015)
  let syntaxFormula0017 : Wff := (syn_wa syntaxFormula0013 syntaxFormula0016)
  let syntaxFormula0018 : Wff := (syn_wa (.classMem (.cv k) (syn_cnnc)) syntaxFormula0017)
  let syntaxClass0019 : Class :=
    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))
  let syntaxFormula0020 : Wff := (.classMem (.cv n) syntaxClass0019)
  let syntaxFormula0021 : Wff :=
    (.imp syntaxFormula0020 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxFormula0022 : Wff := (.classMem (.cv k) syntaxClass0019)
  let syntaxFormula0023 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0021)
  let syntaxFormula0024 : Wff := (syn_wa syntaxFormula0022 syntaxFormula0023)
  let syntaxFormula0025 : Wff := (syn_wa (.classMem (.cv k) (syn_cnnc)) syntaxFormula0024)
  let syntaxClass0026 : Class :=
    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))
  let syntaxFormula0027 : Wff :=
    (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))
  let syntaxClass0028 : Class :=
    (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  let syntaxClass0029 : Class :=
    (syn_cfrec (syn_cwppstopstep F (syn_ctc C))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))
  let syntaxClass0030 : Class := (syn_ccnv syntaxClass0028)
  let syntaxClass0031 : Class := (syn_ccnv syntaxClass0029)
  let syntaxClass0032 : Class :=
    (syn_cima syntaxClass0031 (syn_cima (syn_clec) (syn_csn (syn_ctc C))))
  let syntaxFormula0033 : Wff :=
    (.classEq (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  let syntaxFormula0034 : Wff := (syn_wa (.classEq (.cv d) (syn_c0)) syntaxFormula0033)
  let syntaxFormula0035 : Wff :=
    (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d))))
  let syntaxFormula0036 : Wff :=
    (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
  let syntaxFormula0037 : Wff := (syn_wex s syntaxFormula0036)
  let syntaxFormula0038 : Wff := (syn_wex s syntaxFormula0035)
  let syntaxFormula0039 : Wff := (syn_wex d syntaxFormula0038)
  let syntaxFormula0040 : Wff :=
    (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
  let syntaxFormula0041 : Wff :=
    (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv)))
  let syntaxFormula0042 : Wff :=
    (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C)))
      (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
  let syntaxClass0043 : Class := (syn_cfv syntaxClass0028 (.cv k))
  let syntaxFormula0044 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0043)
  let syntaxClass0045 : Class :=
    (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)
  let syntaxFormula0046 : Wff := (.classMem (.cv x) syntaxClass0045)
  let syntaxClass0047 : Class := (.cab x syntaxFormula0046)
  let syntaxFormula0048 : Wff := (.classMem syntaxClass0047 (syn_cvv))
  let syntaxFormula0049 : Wff :=
    (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C)))
  let syntaxClass0050 : Class := (syn_cfv syntaxClass0028 (syn_c0c))
  let syntaxClass0051 : Class :=
    (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  let syntaxClass0052 : Class := (syn_cfv syntaxClass0051 (syn_c0c))
  let syntaxFormula0053 : Wff := (.classEq syntaxClass0052 syntaxClass0050)
  let syntaxFormula0054 : Wff := (.classMem (syn_c0c) syntaxClass0045)
  let syntaxFormula0055 : Wff := (.classMem (syn_c0c) syntaxClass0047)
  let syntaxFormula0056 : Wff := (.classMem (.cv y) syntaxClass0045)
  let syntaxFormula0057 : Wff :=
    (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0049
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))))
  let syntaxFormula0058 : Wff :=
    (syn_w3a (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxClass0059 : Class := (syn_cfv syntaxClass0051 (syn_cplc (.cv y) (syn_c1c)))
  let syntaxClass0060 : Class := (syn_cfv syntaxClass0051 (.cv y))
  let syntaxClass0061 : Class := (syn_cfv (syn_cwppstopstep F C) syntaxClass0060)
  let syntaxFormula0062 : Wff := (.classEq syntaxClass0059 syntaxClass0061)
  let syntaxFormula0063 : Wff :=
    (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y))
      (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c))))
  let syntaxFormula0064 : Wff :=
    (syn_wa (.classMem (.cv y) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxFormula0065 : Wff :=
    (syn_w3a (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc)))
  let syntaxFormula0066 : Wff :=
    (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)))
  let syntaxFormula0067 : Wff :=
    (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z)))
      (syn_wbr (.cv x) (.cv r) (.cv z)))
  let syntaxFormula0068 : Wff :=
    (.imp syntaxFormula0066 (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))
  let syntaxFormula0069 : Wff := (syn_wral z (.cv b) syntaxFormula0067)
  let syntaxFormula0070 : Wff := (syn_wral z (.cv b) syntaxFormula0068)
  let syntaxFormula0071 : Wff := (syn_wral z (syn_cnnc) syntaxFormula0068)
  let syntaxFormula0072 : Wff := (syn_wral a (.cv b) syntaxFormula0070)
  let syntaxFormula0073 : Wff := (syn_wral a (syn_cnnc) syntaxFormula0071)
  let syntaxFormula0074 : Wff :=
    (syn_wral x (.cv b) (syn_wral a (.cv b) syntaxFormula0069))
  let syntaxFormula0075 : Wff := (syn_wral x (.cv b) syntaxFormula0072)
  let syntaxFormula0076 : Wff := (syn_wral x (syn_cnnc) syntaxFormula0073)
  let syntaxFormula0077 : Wff :=
    (syn_wb (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) syntaxFormula0076)
  let syntaxFormula0078 : Wff :=
    (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)))
  let syntaxFormula0079 : Wff := (syn_wa syntaxFormula0078 (.classMem (.cv k) (syn_cnnc)))
  let syntaxFormula0080 : Wff :=
    (syn_w3a (.classMem (.cv y) (syn_cnnc))
      (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
  let syntaxFormula0081 : Wff :=
    (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)))
  let syntaxFormula0082 : Wff :=
    (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))
  let syntaxFormula0083 : Wff :=
    (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxFormula0084 : Wff :=
    (.imp syntaxFormula0083 (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxFormula0085 : Wff := (syn_wa (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056)
  let syntaxFormula0086 : Wff :=
    (syn_wa syntaxFormula0085 (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxFormula0087 : Wff :=
    (syn_w3a (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxClass0088 : Class := (syn_cfv syntaxClass0028 (.cv y))
  let syntaxFormula0089 : Wff := (.classEq syntaxClass0060 syntaxClass0088)
  let syntaxClass0090 : Class := (syn_cfv (syn_cwppstopstep F C) syntaxClass0088)
  let syntaxFormula0091 : Wff := (.classEq syntaxClass0061 syntaxClass0090)
  let syntaxFormula0092 : Wff := (.classEq syntaxClass0059 syntaxClass0090)
  let syntaxFormula0093 : Wff := (syn_wb syntaxFormula0062 syntaxFormula0092)
  let syntaxFormula0094 : Wff :=
    (syn_wa syntaxFormula0064 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
  let syntaxFormula0095 : Wff :=
    (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
  let syntaxFormula0096 : Wff := (syn_wa syntaxFormula0095 (.classMem (.cv y) (syn_cnnc)))
  let syntaxFormula0097 : Wff :=
    (syn_w3a (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))
      (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
  let syntaxFormula0098 : Wff :=
    (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)))
  let syntaxFormula0099 : Wff :=
    (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))
  let syntaxFormula0100 : Wff :=
    (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
  let syntaxFormula0101 : Wff :=
    (.imp syntaxFormula0100
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
  let syntaxFormula0102 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0088)
  let syntaxFormula0103 : Wff := (.classMem (.cv y) syntaxClass0026)
  let syntaxFormula0104 : Wff := (syn_wa (.classMem (.cv y) (syn_cnnc)) syntaxFormula0102)
  let syntaxFormula0105 : Wff := (.classMem (.cv q) syntaxClass0019)
  let syntaxFormula0106 : Wff :=
    (.imp syntaxFormula0105 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))
  let syntaxFormula0107 : Wff := (syn_wral q (syn_cnnc) syntaxFormula0106)
  let syntaxFormula0108 : Wff := (.classMem (.cv q) syntaxClass0026)
  let syntaxFormula0109 : Wff :=
    (.imp syntaxFormula0108 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))
  let syntaxFormula0110 : Wff := (syn_wral q (syn_cnnc) syntaxFormula0109)
  let syntaxFormula0111 : Wff :=
    (.imp syntaxFormula0103 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
  let syntaxFormula0112 : Wff := (.imp syntaxFormula0102 syntaxFormula0103)
  let syntaxFormula0113 : Wff :=
    (.imp syntaxFormula0102 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
  let syntaxFormula0114 : Wff := (.neg syntaxFormula0102)
  let syntaxFormula0115 : Wff := (.neg syntaxFormula0114)
  let syntaxClass0116 : Class := (syn_cfv syntaxClass0028 (.cv q))
  let syntaxFormula0117 : Wff := (.classMem syntaxClass0116 (syn_chwcards (syn_cvv)))
  let syntaxFormula0118 : Wff := (syn_wa (.classMem (.cv q) (syn_cnnc)) syntaxFormula0117)
  let syntaxFormula0119 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0116)
  let syntaxFormula0120 : Wff := (syn_wbr syntaxClass0116 (syn_clec) (syn_ctc C))
  let syntaxFormula0121 : Wff := (syn_wo syntaxFormula0119 syntaxFormula0120)
  let syntaxFormula0122 : Wff := (.neg syntaxFormula0119)
  let syntaxFormula0123 : Wff := (.imp syntaxFormula0122 syntaxFormula0120)
  let syntaxFormula0124 : Wff := (syn_wbr syntaxClass0088 (syn_clec) (syn_ctc C))
  let syntaxFormula0125 : Wff := (.imp syntaxFormula0114 syntaxFormula0124)
  let syntaxFormula0126 : Wff :=
    (syn_w3a (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) syntaxFormula0040
      syntaxFormula0042)
  let syntaxFormula0127 : Wff :=
    (.classMem syntaxClass0116 (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
  let syntaxFormula0128 : Wff :=
    (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y))
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)))
  let syntaxFormula0129 : Wff :=
    (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) syntaxFormula0128)
  let syntaxFormula0130 : Wff := (.classEq (.cv y) syntaxClass0116)
  let syntaxClass0131 : Class := (syn_cfv (syn_cwppstopstep F C) syntaxClass0116)
  let syntaxClass0132 : Class :=
    (syn_cfv (syn_cwppstopstep F (syn_ctc C)) syntaxClass0116)
  let syntaxFormula0133 : Wff := (.classEq syntaxClass0131 syntaxClass0132)
  let syntaxFormula0134 : Wff := (.imp syntaxFormula0120 syntaxFormula0133)
  let syntaxClass0135 : Class :=
    (syn_cfv (syn_cwppstopstep F (syn_ctc C)) syntaxClass0088)
  let syntaxFormula0136 : Wff := (.classEq syntaxClass0090 syntaxClass0135)
  let syntaxFormula0137 : Wff := (.imp syntaxFormula0124 syntaxFormula0136)
  let syntaxFormula0138 : Wff := (.classEq syntaxClass0059 syntaxClass0135)
  let syntaxFormula0139 : Wff := (syn_wb syntaxFormula0092 syntaxFormula0138)
  let syntaxClass0140 : Class := (syn_cfv syntaxClass0028 (syn_cplc (.cv y) (syn_c1c)))
  let syntaxFormula0141 : Wff := (.classEq syntaxClass0059 syntaxClass0140)
  let syntaxFormula0142 : Wff := (.classMem (syn_cplc (.cv y) (syn_c1c)) syntaxClass0045)
  let syntaxFormula0143 : Wff :=
    (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      syntaxFormula0141)
  let syntaxFormula0144 : Wff := (.imp syntaxFormula0056 syntaxFormula0142)
  let syntaxFormula0145 : Wff := (.classMem (.cv y) syntaxClass0047)
  let syntaxFormula0146 : Wff := (.classMem (syn_cplc (.cv y) (syn_c1c)) syntaxClass0047)
  let syntaxFormula0147 : Wff := (.imp syntaxFormula0145 syntaxFormula0146)
  let syntaxFormula0148 : Wff := (syn_wa syntaxFormula0048 syntaxFormula0055)
  let syntaxFormula0149 : Wff := (syn_wral y (syn_cnnc) syntaxFormula0147)
  let syntaxFormula0150 : Wff := (syn_wa syntaxFormula0148 syntaxFormula0149)
  let syntaxFormula0151 : Wff :=
    (syn_w3a syntaxFormula0048 syntaxFormula0055 syntaxFormula0149)
  let syntaxFormula0152 : Wff := (syn_wss (syn_cnnc) syntaxClass0047)
  let syntaxFormula0153 : Wff := (.classMem (.cv n) syntaxClass0047)
  let syntaxFormula0154 : Wff := (.classMem (.cv n) syntaxClass0045)
  let syntaxClass0155 : Class := (syn_cfv syntaxClass0051 (.cv n))
  let syntaxClass0156 : Class := (syn_cfv syntaxClass0028 (.cv n))
  let syntaxFormula0157 : Wff := (.classEq syntaxClass0155 syntaxClass0156)
  let syntaxFormula0158 : Wff :=
    (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0157)
  let syntaxClass0159 : Class := (syn_cfv syntaxClass0051 (.cv k))
  let syntaxFormula0160 : Wff := (.classEq syntaxClass0159 syntaxClass0043)
  let syntaxFormula0161 : Wff :=
    (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0160)
  let syntaxFormula0162 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0159)
  let syntaxClass0163 : Class :=
    (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (syn_ctc C))
  let syntaxFormula0164 : Wff := (.classMem (.cv k) syntaxClass0163)
  let syntaxFormula0165 : Wff := (.classEq syntaxClass0043 syntaxClass0159)
  let syntaxFormula0166 : Wff := (.classMem (.cv n) syntaxClass0163)
  let syntaxFormula0167 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0166)
  let syntaxFormula0168 : Wff :=
    (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  let syntaxFormula0169 : Wff := (syn_wral y (syn_cnnc) syntaxFormula0168)
  let syntaxFormula0170 : Wff := (syn_wral x (syn_cnnc) syntaxFormula0169)
  let syntaxFormula0171 : Wff :=
    (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxFormula0172 : Wff := (.imp syntaxFormula0170 syntaxFormula0171)
  let syntaxFormula0173 : Wff :=
    (.imp syntaxFormula0167 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxFormula0174 : Wff :=
    (syn_wa syntaxFormula0167 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxFormula0175 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0155)
  let syntaxFormula0176 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0175)
  let syntaxFormula0177 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0156)
  let syntaxFormula0178 : Wff := (syn_wb syntaxFormula0175 syntaxFormula0177)
  let syntaxFormula0179 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0177)
  let syntaxFormula0180 : Wff := (.classMem (.cv n) syntaxClass0026)
  let syntaxFormula0181 : Wff :=
    (.imp syntaxFormula0180 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxFormula0182 : Wff :=
    (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0173)
  let syntaxFormula0183 : Wff := (.neg syntaxFormula0173)
  let syntaxFormula0184 : Wff :=
    (.imp syntaxFormula0183 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)))
  let syntaxFormula0185 : Wff := (.imp syntaxFormula0183 syntaxFormula0173)
  let syntaxFormula0186 : Wff :=
    (.imp syntaxFormula0166 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  let syntaxClass0187 : Class := (syn_cfv syntaxClass0029 (.cv k))
  let syntaxFormula0188 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0186)
  let syntaxFormula0189 : Wff := (.classEq syntaxClass0187 syntaxClass0159)
  let syntaxFormula0190 : Wff := (syn_wa syntaxFormula0009 syntaxFormula0164)
  let syntaxFormula0191 : Wff :=
    (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      syntaxFormula0190)
  let syntaxFormula0192 : Wff := (syn_wa syntaxFormula0010 syntaxFormula0188)
  let syntaxFormula0193 : Wff :=
    (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wbr (syn_ctc C) (syn_clec) C))
  let syntaxFormula0194 : Wff :=
    (.classMem syntaxClass0155 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxFormula0195 : Wff := (.classMem syntaxClass0155 (syn_chwcards (syn_cvv)))
  let syntaxFormula0196 : Wff := (.classMem syntaxClass0155 (syn_cncs))
  let syntaxClass0197 : Class := (syn_cfv syntaxClass0051 (.cv q))
  let syntaxFormula0198 : Wff := (.classMem syntaxClass0197 (syn_cncs))
  let syntaxFormula0199 : Wff := (syn_wral q (syn_cnnc) syntaxFormula0198)
  let syntaxFormula0200 : Wff := (syn_wa syntaxFormula0057 syntaxFormula0193)
  let syntaxFormula0201 : Wff := (syn_wa syntaxFormula0191 syntaxFormula0192)
  let syntaxFormula0202 : Wff := (syn_wa syntaxFormula0200 syntaxFormula0199)
  let syntaxFormula0203 : Wff :=
    (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))
  let syntaxFormula0204 : Wff :=
    (syn_wral y (syn_cdm (syn_cwppstopstep F C)) syntaxFormula0203)
  let syntaxClass0205 : Class := (syn_cfv syntaxClass0051 (.cv r))
  let syntaxFormula0206 : Wff := (.classEq (.cv y) syntaxClass0205)
  let syntaxFormula0207 : Wff := (syn_wa (.classMem (.cv r) (syn_cnnc)) syntaxFormula0206)
  let syntaxClass0208 : Class := (syn_cfv (syn_cwppstopstep F C) syntaxClass0205)
  let syntaxFormula0209 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0205)
  let syntaxFormula0210 : Wff := (syn_wbr C (syn_clec) syntaxClass0208)
  let syntaxFormula0211 : Wff := (.imp syntaxFormula0209 syntaxFormula0210)
  let syntaxFormula0212 : Wff := (syn_wral r (syn_cnnc) syntaxFormula0211)
  let syntaxFormula0213 : Wff :=
    (syn_w3a syntaxFormula0201 syntaxFormula0202 syntaxFormula0212)
  let syntaxFormula0214 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0196)
  let syntaxFormula0215 : Wff := (syn_wbr C (syn_clec) syntaxClass0155)
  let syntaxFormula0216 : Wff :=
    (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) syntaxFormula0196)
  let syntaxClass0217 : Class := (syn_ctc syntaxClass0155)
  let syntaxClass0218 : Class := (syn_cfv syntaxClass0029 (syn_ctc (.cv n)))
  let syntaxFormula0219 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0218)
  let syntaxFormula0220 : Wff :=
    (syn_wa (.classMem (syn_ctc (.cv n)) (syn_cnnc)) syntaxFormula0219)
  let syntaxFormula0221 : Wff := (.classMem (syn_ctc (.cv n)) syntaxClass0019)
  let syntaxFormula0222 : Wff := (syn_wb syntaxFormula0007 syntaxFormula0221)
  let syntaxFormula0223 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0222)
  let syntaxFormula0224 : Wff := (.classMem (syn_ctc (.cv m)) syntaxClass0019)
  let syntaxFormula0225 : Wff := (syn_wb syntaxFormula0009 syntaxFormula0224)
  let syntaxFormula0226 : Wff :=
    (.imp syntaxFormula0224 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))))
  let syntaxFormula0227 : Wff := (.classMem (syn_ctc (.cv x)) syntaxClass0019)
  let syntaxFormula0228 : Wff := (.classMem (.cv x) syntaxClass0006)
  let syntaxFormula0229 : Wff := (syn_wb syntaxFormula0228 syntaxFormula0227)
  let syntaxFormula0230 : Wff := (syn_wa (.classMem (.cv x) (syn_cnnc)) syntaxFormula0010)
  let syntaxFormula0231 : Wff :=
    (syn_wo (.classEq (.cv m) (syn_ctc (.cv m)))
      (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))))
  let syntaxClass0232 : Class := (syn_cfv syntaxClass0051 (.cv m))
  let syntaxFormula0233 : Wff := (syn_wbr C (syn_clec) syntaxClass0232)
  let syntaxClass0234 : Class := (syn_cfv syntaxClass0051 (.cv x))
  let syntaxFormula0235 : Wff :=
    (.classMem syntaxClass0234 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxFormula0236 : Wff := (.classEq (.cv y) syntaxClass0234)
  let syntaxFormula0237 : Wff := (syn_wa (.classMem (.cv x) (syn_cnnc)) syntaxFormula0236)
  let syntaxClass0238 : Class := (syn_ctc syntaxClass0234)
  let syntaxFormula0239 : Wff := (syn_wbr C (syn_clec) syntaxClass0234)
  let syntaxFormula0240 : Wff := (syn_wne syntaxClass0234 syntaxClass0238)
  let syntaxFormula0241 : Wff := (.imp syntaxFormula0239 syntaxFormula0240)
  let syntaxClass0242 : Class := (syn_ctc syntaxClass0232)
  let syntaxFormula0243 : Wff := (syn_wne syntaxClass0232 syntaxClass0242)
  let syntaxFormula0244 : Wff := (.imp syntaxFormula0233 syntaxFormula0243)
  let syntaxFormula0245 : Wff := (.classEq syntaxClass0232 syntaxClass0242)
  let syntaxFormula0246 : Wff := (.neg syntaxFormula0245)
  let syntaxFormula0247 : Wff := (.classEq syntaxClass0242 syntaxClass0159)
  let syntaxFormula0248 : Wff := (.classEq syntaxClass0242 syntaxClass0232)
  have p0000 := @g_simpl (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))
  have p0001 := @g_simpr (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))
  have p0002 := @g_simpl ph (syn_wa ps ch)
  have p0003 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)))
      (syn_wa ph (syn_wa ps ch)) ph p0001 p0002
  have p0004 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)))
      (.classEq I (syn_ctc I)) ph p0000 p0003
  have p0005 := @g_simpr ph (syn_wa ps ch)
  have p0006 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)))
      (syn_wa ph (syn_wa ps ch)) (syn_wa ps ch) p0001 p0005
  have p0007 := @g_simpl ps ch
  have p0008 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa ps ch) ps
      p0006 p0007
  have p0009 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)))
      (.classEq I (syn_ctc I)) ps p0000 p0008
  have p0010 := @g_simpr ps ch
  have p0011 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa ps ch) ch
      p0006 p0010
  have p0012 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)))
      (.classEq I (syn_ctc I)) ch p0000 p0011
  have p0013 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)))
      (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch) p0009
      p0012
  have p0014 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)))
      (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0000 p0004 p0013
  have p0015 :=
    @g_ex (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)) syntaxFormula0001 p0014
  have p0016 := @g_eqid (.cv m)
  have p0017 := @g_a1i (.classEq (.cv m) (.cv m)) syntaxFormula0001 p0016
  have p0018 := @g_simpl (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0000
  have p0019 := @g_simpr (.classEq I (syn_ctc I)) ph
  have p0020 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ph) ph syntaxFormula0005 p0019
      hyp_wppstopfixedhitcontrgrowfixdndv_10
  have p0021 := @g_iftrue (.classEq I (syn_ctc I)) I (syn_c0c)
  have p0022 :=
    @g_eqcomd (.classEq I (syn_ctc I)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I
      p0021
  have p0023 :=
    @g_adantr (.classEq I (syn_ctc I))
      (.classEq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) ph p0022
  have p0024 :=
    @g_wpphitstartcongrndv C (syn_cwppstopstep F C) I
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0025 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ph)
      (.classEq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
      (.classEq (syn_cwpphit (syn_cwppstopstep F C) I C) syntaxClass0006) p0023 p0024
  have p0026 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ph)
      (syn_cwpphit (syn_cwppstopstep F C) I C) syntaxClass0006 (.cv m) p0025
  have p0027 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ph)
      (syn_cwpphit (syn_cwppstopstep F C) I C) syntaxClass0006 (.cv n) p0025
  have p0028 :=
    @g_imbi1d (syn_wa (.classEq I (syn_ctc I)) ph)
      (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) syntaxFormula0007
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)) p0027
  have p0029 :=
    @g_ralbidv (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0002 syntaxFormula0008 n
      (syn_cnnc) dv_cache_0001 p0028
  have p0030 :=
    @g_anbi12d (syn_wa (.classEq I (syn_ctc I)) ph)
      (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C)) syntaxFormula0009
      syntaxFormula0003 syntaxFormula0010 p0026 p0029
  have p0031 :=
    @g_anbi2d (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0004 syntaxFormula0011
      (.classMem (.cv m) (syn_cnnc)) p0030
  have p0032 :=
    @g_mpbid (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0005 syntaxFormula0012
      p0020 p0031
  have p0033 :=
    @g_syl syntaxFormula0001 (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0012 p0018
      p0032
  have p0034 :=
    @g_simpld syntaxFormula0001 (.classMem (.cv m) (syn_cnnc)) syntaxFormula0011 p0033
  have p0035 := @g_simpr (syn_wa (.classEq I (syn_ctc I)) ph) syntaxFormula0000
  have p0036 :=
    @g_simpl (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)
  have p0037 :=
    @g_syl syntaxFormula0001 syntaxFormula0000 (syn_wa (.classEq I (syn_ctc I)) ps) p0035
      p0036
  have p0038 := @g_simpr (.classEq I (syn_ctc I)) ps
  have p0039 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ps) ps syntaxFormula0018 p0038
      hyp_wppstopfixedhitcontrgrowfixdndv_11
  have p0040 := @g_tceq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0041 :=
    @g_syl (.classEq I (syn_ctc I))
      (.classEq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
      (.classEq (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))
      p0022 p0040
  have p0042 :=
    @g_adantr (.classEq I (syn_ctc I))
      (.classEq (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) ps
      p0041
  have p0043 :=
    @g_wpphitstartcongrndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I)
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  have p0044 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ps)
      (.classEq (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))
      (.classEq (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))
        syntaxClass0019)
      p0042 p0043
  have p0045 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ps)
      (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))
      syntaxClass0019 (.cv k) p0044
  have p0046 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ps)
      (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))
      syntaxClass0019 (.cv n) p0044
  have p0047 :=
    @g_imbi1d (syn_wa (.classEq I (syn_ctc I)) ps) syntaxFormula0014 syntaxFormula0020
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0046
  have p0048 :=
    @g_ralbidv (syn_wa (.classEq I (syn_ctc I)) ps) syntaxFormula0015 syntaxFormula0021 n
      (syn_cnnc) dv_cache_0002 p0047
  have p0049 :=
    @g_anbi12d (syn_wa (.classEq I (syn_ctc I)) ps) syntaxFormula0013 syntaxFormula0022
      syntaxFormula0016 syntaxFormula0023 p0045 p0048
  have p0050 :=
    @g_anbi2d (syn_wa (.classEq I (syn_ctc I)) ps) syntaxFormula0017 syntaxFormula0024
      (.classMem (.cv k) (syn_cnnc)) p0049
  have p0051 :=
    @g_mpbid (syn_wa (.classEq I (syn_ctc I)) ps) syntaxFormula0018 syntaxFormula0025
      p0039 p0050
  have p0052 :=
    @g_syl syntaxFormula0001 (syn_wa (.classEq I (syn_ctc I)) ps) syntaxFormula0025 p0037
      p0051
  have p0053 :=
    @g_simpld syntaxFormula0001 (.classMem (.cv k) (syn_cnnc)) syntaxFormula0024 p0052
  have p0054 :=
    @g_jca syntaxFormula0001 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
      p0034 p0053
  have p0055 :=
    @g_simprd syntaxFormula0001 (.classMem (.cv m) (syn_cnnc)) syntaxFormula0011 p0033
  have p0056 := @g_simpld syntaxFormula0001 syntaxFormula0009 syntaxFormula0010 p0055
  have p0057 :=
    @g_simprd syntaxFormula0001 (.classMem (.cv k) (syn_cnnc)) syntaxFormula0024 p0052
  have p0058 := @g_simpld syntaxFormula0001 syntaxFormula0022 syntaxFormula0023 p0057
  have p0059 := (Nominal.classEqRefl syntaxClass0026)
  have p0060 := @g_eqid (syn_cwppstopstep F (syn_ctc C))
  have p0061 := @g_id (.classEq I (syn_ctc I))
  have p0062 := @g_tceq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I
  have p0063 :=
    @g_syl (.classEq I (syn_ctc I))
      (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I)
      (.classEq (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc I))
      p0021 p0062
  have p0064 :=
    @g_eqcomd (.classEq I (syn_ctc I))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc I) p0063
  have p0065 :=
    @g_n_3eqtrd (.classEq I (syn_ctc I)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I
      (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0021 p0061
      p0064
  have p0066 := @g_iffalse (.classEq I (syn_ctc I)) I (syn_c0c)
  have p0067 := @g_tc0c
  have p0068 := @g_eqcomi (syn_ctc (syn_c0c)) (syn_c0c) p0067
  have p0069 :=
    @g_a1i (.classEq (syn_c0c) (syn_ctc (syn_c0c))) (.neg (.classEq I (syn_ctc I))) p0068
  have p0070 := @g_tceq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_c0c)
  have p0071 :=
    @g_syl (.neg (.classEq I (syn_ctc I)))
      (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_c0c))
      (.classEq (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc (syn_c0c)))
      p0066 p0070
  have p0072 :=
    @g_eqcomd (.neg (.classEq I (syn_ctc I)))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc (syn_c0c)) p0071
  have p0073 :=
    @g_n_3eqtrd (.neg (.classEq I (syn_ctc I)))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_c0c) (syn_ctc (syn_c0c))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0066 p0069 p0072
  have p0074 := @g_pm2_61i (.classEq I (syn_ctc I)) syntaxFormula0027 p0065 p0073
  have p0075 :=
    @g_pm3_2i (.classEq (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C)))
      syntaxFormula0027 p0060 p0074
  have p0076 :=
    @g_freceq12 (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  have p0077 := Nominal.mp p0075 p0076
  have p0078 := @g_cnveqi syntaxClass0028 syntaxClass0029 p0077
  have p0079 :=
    @g_imaeq1i syntaxClass0030 syntaxClass0031 (syn_cima (syn_clec) (syn_csn (syn_ctc C)))
      p0078
  have p0080 :=
    @g_eqtri syntaxClass0026
      (syn_cima syntaxClass0030 (syn_cima (syn_clec) (syn_csn (syn_ctc C))))
      syntaxClass0032 p0059 p0079
  have p0081 := (Nominal.classEqRefl syntaxClass0019)
  have p0082 := @g_eqtr4i syntaxClass0026 syntaxClass0032 syntaxClass0019 p0080 p0081
  have p0083 :=
    @g_syl6eleqr syntaxFormula0001 (.cv k) syntaxClass0019 syntaxClass0026 p0058 p0082
  have p0084 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0085 := @g_wecomparisondefaultemptywe
  have p0086 := @g_df0c2
  have p0087 :=
    @g_pm3_2i
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (.classEq (syn_c0c) (syn_cnc (syn_c0))) p0085 p0086
  have p0088 := @g_n_0ex
  have p0089 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      (syn_cwe)
  have p0090 := Nominal.mp p0085 p0089
  have p0091 :=
    @g_simpli
      (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv))
      (.classMem (syn_c0) (syn_cvv)) p0090
  have p0092 := @g_simpr (.classEq (.cv d) (syn_c0)) syntaxFormula0033
  have p0093 := @g_simpl (.classEq (.cv d) (syn_c0)) syntaxFormula0033
  have p0094 :=
    @g_breq12d syntaxFormula0034 (.cv s)
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (.cv d) (syn_c0)
      (syn_cwe) p0092 p0093
  have p0095 := @g_nceqd syntaxFormula0034 (.cv d) (syn_c0) p0093
  have p0096 :=
    @g_eqeq2d syntaxFormula0034 (syn_cnc (.cv d)) (syn_cnc (syn_c0)) (syn_c0c) p0095
  have p0097 :=
    @g_anbi12d syntaxFormula0034 (syn_wbr (.cv s) (syn_cwe) (.cv d))
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (.classEq (syn_c0c) (syn_cnc (.cv d))) (.classEq (syn_c0c) (syn_cnc (syn_c0))) p0094
      p0096
  have p0098 :=
    @g_spc2ev syntaxFormula0035
      (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
          (syn_c0)) (.classEq (syn_c0c) (syn_cnc (syn_c0))))
      d s (syn_c0) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0088 p0091 p0097
  have p0099 := Nominal.mp p0087 p0098
  have p0100 := @g_n_0cex
  have p0101 := @g_id (.classEq (.cv k) (syn_c0c))
  have p0102 :=
    @g_eleq1d (.classEq (.cv k) (syn_c0c)) (.cv k) (syn_c0c) (syn_chwcards (syn_cvv))
      p0101
  have p0104 :=
    @g_eqeq1d (.classEq (.cv k) (syn_c0c)) (.cv k) (syn_c0c) (syn_cnc (.cv d)) p0101
  have p0105 :=
    @g_anbi2d (.classEq (.cv k) (syn_c0c)) (.classEq (.cv k) (syn_cnc (.cv d)))
      (.classEq (syn_c0c) (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0104
  have p0106 :=
    @g_exbidv (.classEq (.cv k) (syn_c0c)) syntaxFormula0036 syntaxFormula0035 s
      dv_cache_0010 p0105
  have p0107 :=
    @g_exbidv (.classEq (.cv k) (syn_c0c)) syntaxFormula0037 syntaxFormula0038 d
      dv_cache_0011 p0106
  have p0108 :=
    @g_bibi12d (.classEq (.cv k) (syn_c0c)) (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) (syn_wex d syntaxFormula0037)
      syntaxFormula0039 p0102 p0107
  have p0109 := @g_elhwcardswev k s d dv_cache_0012 dv_cache_0009 dv_cache_0013
  have p0110 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d syntaxFormula0037))
      (syn_wb (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) syntaxFormula0039) k
      (syn_c0c) (syn_cvv) dv_cache_0014 dv_cache_0015 p0108 p0109
  have p0111 := Nominal.mp p0100 p0110
  have p0112 :=
    @g_mpbir (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) syntaxFormula0039 p0099 p0111
  have p0113 :=
    @g_pm3_2i (.classMem I (syn_chwcards (syn_cvv)))
      (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) hyp_wppstopfixedhitcontrgrowfixdndv_7
      p0112
  have p0114 := @g_ifcl (.classEq I (syn_ctc I)) I (syn_c0c) (syn_chwcards (syn_cvv))
  have p0115 := Nominal.mp p0113 p0114
  have p0116 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0117 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0116
  have p0118 := @g_biimpri syntaxFormula0040 syntaxFormula0041 p0117
  have p0119 := Nominal.mp p0115 p0118
  have p0120 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0121 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns))
      syntaxFormula0040 syntaxFormula0042 p0084 p0119 p0120
  have p0122 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv k)
  have p0123 := Nominal.mp p0121 p0122
  have p0124 :=
    @g_sylib syntaxFormula0001 (.classMem (.cv k) syntaxClass0026)
      (syn_wa (.classMem (.cv k) (syn_cnnc)) syntaxFormula0044) p0083 p0123
  have p0125 :=
    @g_simprd syntaxFormula0001 (.classMem (.cv k) (syn_cnnc)) syntaxFormula0044 p0124
  have p0126 := @g_finlewe
  have p0127 := @g_wppweref (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0128 := Nominal.mp p0126 p0127
  have p0129 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc))
      (.classMem (.cv k) (syn_cnnc)) p0128
  have p0130 := @g_id (.classMem (.cv k) (syn_cnnc))
  have p0131 :=
    @g_refd (.classMem (.cv k) (syn_cnnc)) (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv k)
      p0129 p0130
  have p0132 :=
    @g_syl syntaxFormula0001 (.classMem (.cv k) (syn_cnnc))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) p0053 p0131
  have p0133 := @g_tru
  have p0134 :=
    @g_wppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0135 :=
    @g_wppfrecprefixeqexndv k (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0134 p0084
  have p0136 := @g_abid2 x syntaxClass0045 dv_cache_0016
  have p0137 := @g_eleq1i syntaxClass0047 syntaxClass0045 (syn_cvv) p0136
  have p0138 :=
    @g_mpbir syntaxFormula0048 (.classMem syntaxClass0045 (syn_cvv)) p0135 p0137
  have p0139 := @g_a1i syntaxFormula0048 syn_wtru p0138
  have p0140 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0141 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0140
  have p0142 := @g_biimpri syntaxFormula0049 syntaxFormula0041 p0141
  have p0143 := Nominal.mp p0115 p0142
  have p0144 :=
    @g_wppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0145 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0049
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0134
      p0143 p0144
  have p0146 :=
    @g_wpporbit0ndv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0147 := Nominal.mp p0145 p0146
  have p0149 :=
    @g_wpporbit0ndv (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0150 := Nominal.mp p0121 p0149
  have p0151 :=
    @g_eqcomi syntaxClass0050 (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0150
  have p0152 :=
    @g_eqtri syntaxClass0052 (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      syntaxClass0050 p0147 p0151
  have p0153 :=
    @g_a1i syntaxFormula0053 (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv k)) p0152
  have p0154 := @g_peano1
  have p0155 :=
    @g_wppfrecprefixeqvalndv (syn_c0c) k (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0156 := Nominal.mp p0154 p0155
  have p0157 :=
    @g_mpbir syntaxFormula0054
      (.imp (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0053) p0153
      p0156
  have p0158 := @g_a1i syntaxFormula0054 syn_wtru p0157
  have p0160 := @g_id (.classEq (.cv x) (syn_c0c))
  have p0161 :=
    @g_eleq1d (.classEq (.cv x) (syn_c0c)) (.cv x) (syn_c0c) syntaxClass0045 p0160
  have p0162 :=
    @g_elab syntaxFormula0046 syntaxFormula0054 x (syn_c0c) dv_cache_0017 dv_cache_0018
      p0100 p0161
  have p0163 := @g_sylibr syn_wtru syntaxFormula0054 syntaxFormula0055 p0158 p0162
  have p0164 := @g_jca syn_wtru syntaxFormula0048 syntaxFormula0055 p0139 p0163
  have p0165 := @g_vex y
  have p0166 := @g_id (.classEq (.cv x) (.cv y))
  have p0167 := @g_eleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) syntaxClass0045 p0166
  have p0168 :=
    @g_elab syntaxFormula0046 syntaxFormula0056 x (.cv y) dv_cache_0019 dv_cache_0020
      p0165 p0167
  have p0170 := @g_a1i syntaxFormula0057 syntaxFormula0058 p0145
  have p0171 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0172 :=
    @g_jca syntaxFormula0058 syntaxFormula0057 (.classMem (.cv y) (syn_cnnc)) p0170 p0171
  have p0173 :=
    @g_wpporbitsucndv (syn_cwppstopstep F C)
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv y)
  have p0174 :=
    @g_syl syntaxFormula0058 (syn_wa syntaxFormula0057 (.classMem (.cv y) (syn_cnnc)))
      syntaxFormula0062 p0172 p0173
  have p0176 :=
    @g_simp2 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0177 :=
    @g_jca syntaxFormula0058 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056 p0171 p0176
  have p0179 :=
    @g_simp3 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0180 :=
    @g_jca syntaxFormula0058 (.classMem (.cv y) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0171 p0179
  have p0181 :=
    @g_simpr (.classMem (.cv y) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0182 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0186 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc))
      (.classMem (.cv y) (syn_cnnc)) p0128
  have p0187 := @g_id (.classMem (.cv y) (syn_cnnc))
  have p0188 :=
    @g_refd (.classMem (.cv y) (syn_cnnc)) (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv y)
      p0186 p0187
  have p0189 :=
    @g_orc (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y))
      (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c)))
  have p0190 :=
    @g_syl (.classMem (.cv y) (syn_cnnc))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) syntaxFormula0063 p0188 p0189
  have p0193 :=
    @g_jca (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
      (.classMem (.cv y) (syn_cnnc)) p0187 p0187
  have p0194 := @g_kqfinsucsplit (.cv y) (.cv y)
  have p0195 :=
    @g_syl (.classMem (.cv y) (syn_cnnc))
      (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
        syntaxFormula0063)
      p0193 p0194
  have p0196 :=
    @g_mpbird (.classMem (.cv y) (syn_cnnc))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
      syntaxFormula0063 p0190 p0195
  have p0197 :=
    @g_syl syntaxFormula0064 (.classMem (.cv y) (syn_cnnc))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) p0182 p0196
  have p0198 :=
    @g_a1d syntaxFormula0064
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0197
  have p0199 :=
    @g_ancom (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
  have p0201 := @g_wppwepo (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0202 := Nominal.mp p0126 p0201
  have p0203 := @g_porta (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0204 :=
    @g_mpbi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc))
      syntaxFormula0065 p0202 p0203
  have p0205 :=
    @g_simp2 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
  have p0206 := Nominal.mp p0204 p0205
  have p0207 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) syntaxFormula0064
      p0206
  have p0208 := @g_brex (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_ctrans)
  have p0209 := @g_breq (.cv x) (.cv a) (.cv r) (syn_ckqrel (syn_clefin))
  have p0210 := @g_breq (.cv a) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0211 :=
    @g_anbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin)))
      (syn_wbr (.cv x) (.cv r) (.cv a))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv a) (.cv r) (.cv z))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0209 p0210
  have p0212 := @g_breq (.cv x) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0213 :=
    @g_imbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin)))
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z)))
      syntaxFormula0066 (syn_wbr (.cv x) (.cv r) (.cv z))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) p0211 p0212
  have p0214 :=
    @g_ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) syntaxFormula0067
      syntaxFormula0068 z (.cv b) dv_cache_0021 p0213
  have p0215 :=
    @g_n_2ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) syntaxFormula0069
      syntaxFormula0070 x a (.cv b) (.cv b) dv_cache_0022 dv_cache_0023 p0214
  have p0216 :=
    @g_raleq syntaxFormula0068 z (.cv b) (syn_cnnc) dv_cache_0024 dv_cache_0025
  have p0217 :=
    @g_raleqbi1dv syntaxFormula0070 syntaxFormula0071 a (.cv b) (syn_cnnc) dv_cache_0026
      dv_cache_0027 p0216
  have p0218 :=
    @g_raleqbi1dv syntaxFormula0072 syntaxFormula0073 x (.cv b) (syn_cnnc) dv_cache_0028
      dv_cache_0029 p0217
  have p0219 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x a z r b
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
  have p0220 :=
    @g_brabg syntaxFormula0074 syntaxFormula0075 syntaxFormula0076 r b
      (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cvv) (syn_cvv) (syn_ctrans) dv_cache_0040
      dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
      p0215 p0218 p0219
  have p0221 :=
    @g_syl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc))
      (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem (syn_cnnc) (syn_cvv)))
      syntaxFormula0077 p0208 p0220
  have p0222 :=
    @g_ibi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) syntaxFormula0076
      p0221
  have p0223 :=
    @g_syl syntaxFormula0064 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc))
      syntaxFormula0076 p0207 p0222
  have p0226 := @g_peano2 (.cv y)
  have p0227 :=
    @g_syl syntaxFormula0064 (.classMem (.cv y) (syn_cnnc))
      (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0182 p0226
  have p0228 :=
    @g_jca syntaxFormula0064 (.classMem (.cv y) (syn_cnnc))
      (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0182 p0227
  have p0229 :=
    @g_a1d syntaxFormula0001 (.classMem (.cv k) (syn_cnnc)) syntaxFormula0064 p0053
  have p0230 := @g_pm3_2 syntaxFormula0078 (.classMem (.cv k) (syn_cnnc))
  have p0231 :=
    @g_syl9 syntaxFormula0001 syntaxFormula0064 (.classMem (.cv k) (syn_cnnc))
      syntaxFormula0078 syntaxFormula0079 p0229 p0230
  have p0232 :=
    @g_syl5 syntaxFormula0064 syntaxFormula0078 syntaxFormula0001
      (.imp syntaxFormula0064 syntaxFormula0079) p0228 p0231
  have p0233 := @g_pm2_43d syntaxFormula0001 syntaxFormula0064 syntaxFormula0079 p0232
  have p0234 := (Nominal.biimpRefl syntaxFormula0080)
  have p0235 :=
    @g_syl6ibr syntaxFormula0001 syntaxFormula0064 syntaxFormula0079 syntaxFormula0080
      p0233 p0234
  have p0236 := @g_breq1 (.cv x) (.cv y) (.cv a) (syn_ckqrel (syn_clefin))
  have p0237 :=
    @g_anbi1d (.classEq (.cv x) (.cv y))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0236
  have p0238 := @g_breq1 (.cv x) (.cv y) (.cv z) (syn_ckqrel (syn_clefin))
  have p0239 :=
    @g_imbi12d (.classEq (.cv x) (.cv y)) syntaxFormula0066 syntaxFormula0081
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0237 p0238
  have p0240 :=
    @g_breq2 (.cv a) (syn_cplc (.cv y) (syn_c1c)) (.cv y) (syn_ckqrel (syn_clefin))
  have p0241 :=
    @g_breq1 (.cv a) (syn_cplc (.cv y) (syn_c1c)) (.cv z) (syn_ckqrel (syn_clefin))
  have p0242 :=
    @g_anbi12d (.classEq (.cv a) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0240 p0241
  have p0243 :=
    @g_imbi1d (.classEq (.cv a) (syn_cplc (.cv y) (syn_c1c))) syntaxFormula0081
      syntaxFormula0082 (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0242
  have p0244 :=
    @g_breq2 (.cv z) (.cv k) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0245 :=
    @g_anbi2d (.classEq (.cv z) (.cv k))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) p0244
  have p0246 := @g_breq2 (.cv z) (.cv k) (.cv y) (syn_ckqrel (syn_clefin))
  have p0247 :=
    @g_imbi12d (.classEq (.cv z) (.cv k)) syntaxFormula0082 syntaxFormula0083
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0245 p0246
  have p0248 :=
    @g_rspc3v syntaxFormula0068 syntaxFormula0084
      (.imp syntaxFormula0081 (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
      (.imp syntaxFormula0082 (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))) x a z
      (.cv y) (syn_cplc (.cv y) (syn_c1c)) (.cv k) (syn_cnnc) (syn_cnnc) (syn_cnnc)
      dv_cache_0019 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
      dv_cache_0029 dv_cache_0029 dv_cache_0027 dv_cache_0029 dv_cache_0027 dv_cache_0025
      dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0037 dv_cache_0038 dv_cache_0039
      p0239 p0243 p0247
  have p0249 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0064 syntaxFormula0080
      (.imp syntaxFormula0076 syntaxFormula0084) p0235 p0248
  have p0250 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0064 syntaxFormula0076 syntaxFormula0084 p0223
      p0249
  have p0251 :=
    @g_syl7bi
      (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))))
      syntaxFormula0083 syntaxFormula0001 syntaxFormula0064
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0199 p0250
  have p0252 :=
    @g_exp4a syntaxFormula0001 syntaxFormula0064
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0251
  have p0253 :=
    Nominal.ax2 (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0254 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0064
      (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
        (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))))
      (.imp (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))))
        (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
          (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))))
      p0252 p0253
  have p0255 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0064
      (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))))
      (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))
      p0198 p0254
  have p0256 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0064
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0181 p0255
  have p0257 :=
    @g_syl5 syntaxFormula0058 syntaxFormula0064 syntaxFormula0001
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0180 p0256
  have p0258 :=
    @g_pm3_2 syntaxFormula0085 (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0259 :=
    @g_syl9 syntaxFormula0001 syntaxFormula0058
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0085
      syntaxFormula0086 p0257 p0258
  have p0260 :=
    @g_syl5 syntaxFormula0058 syntaxFormula0085 syntaxFormula0001
      (.imp syntaxFormula0058 syntaxFormula0086) p0177 p0259
  have p0261 := @g_pm2_43d syntaxFormula0001 syntaxFormula0058 syntaxFormula0086 p0260
  have p0262 := (Nominal.biimpRefl syntaxFormula0087)
  have p0263 :=
    @g_syl6ibr syntaxFormula0001 syntaxFormula0058 syntaxFormula0086 syntaxFormula0087
      p0261 p0262
  have p0264 :=
    @g_wppfrecprefixeqvalndv (.cv y) k (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0265 :=
    @g_biimpd (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0089) p0264
  have p0266 :=
    @g_n_3imp (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0089 p0265
  have p0267 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0087 syntaxFormula0089 p0263
      p0266
  have p0268 := @g_fveq2 syntaxClass0060 syntaxClass0088 (syn_cwppstopstep F C)
  have p0269 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0089 syntaxFormula0091 p0267
      p0268
  have p0270 := @g_eqeq2 syntaxClass0061 syntaxClass0090 syntaxClass0059
  have p0271 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0091 syntaxFormula0093 p0269
      p0270
  have p0272 := @g_bi1 syntaxFormula0062 syntaxFormula0092
  have p0273 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0093
      (.imp syntaxFormula0062 syntaxFormula0092) p0271 p0272
  have p0274 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0058 syntaxFormula0062 syntaxFormula0092 p0174
      p0273
  have p0279 := @g_kqfinsucnle (.cv y)
  have p0280 :=
    @g_syl syntaxFormula0064 (.classMem (.cv y) (syn_cnnc))
      (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
      p0182 p0279
  have p0281 := @g_notnot2 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0282 :=
    @g_simpr syntaxFormula0064 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0283 :=
    @g_simpl syntaxFormula0064 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0285 :=
    @g_syl syntaxFormula0094 syntaxFormula0064
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0283 p0181
  have p0286 :=
    @g_a1d syntaxFormula0094
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0285
  have p0287 :=
    @g_ancom (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0295 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) syntaxFormula0094
      p0206
  have p0311 :=
    @g_syl syntaxFormula0094 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc))
      syntaxFormula0076 p0295 p0222
  have p0316 :=
    @g_syl syntaxFormula0094 syntaxFormula0064
      (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0283 p0227
  have p0318 :=
    @g_syl5 syntaxFormula0094 syntaxFormula0064 syntaxFormula0001
      (.classMem (.cv k) (syn_cnnc)) p0283 p0229
  have p0319 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))
      (.classMem (.cv k) (syn_cnnc))
  have p0320 :=
    @g_syl9 syntaxFormula0001 syntaxFormula0094 (.classMem (.cv k) (syn_cnnc))
      (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) syntaxFormula0095 p0318 p0319
  have p0321 :=
    @g_syl5 syntaxFormula0094 (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))
      syntaxFormula0001 (.imp syntaxFormula0094 syntaxFormula0095) p0316 p0320
  have p0322 := @g_pm2_43d syntaxFormula0001 syntaxFormula0094 syntaxFormula0095 p0321
  have p0325 :=
    @g_syl syntaxFormula0094 syntaxFormula0064 (.classMem (.cv y) (syn_cnnc)) p0283 p0182
  have p0326 := @g_pm3_2 syntaxFormula0095 (.classMem (.cv y) (syn_cnnc))
  have p0327 :=
    @g_syl5 syntaxFormula0094 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0095
      syntaxFormula0096 p0325 p0326
  have p0328 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0094 syntaxFormula0095
      (.imp syntaxFormula0094 syntaxFormula0096) p0322 p0327
  have p0329 := @g_pm2_43d syntaxFormula0001 syntaxFormula0094 syntaxFormula0096 p0328
  have p0330 := (Nominal.biimpRefl syntaxFormula0097)
  have p0331 :=
    @g_syl6ibr syntaxFormula0001 syntaxFormula0094 syntaxFormula0096 syntaxFormula0097
      p0329 p0330
  have p0332 :=
    @g_breq1 (.cv x) (syn_cplc (.cv y) (syn_c1c)) (.cv a) (syn_ckqrel (syn_clefin))
  have p0333 :=
    @g_anbi1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0332
  have p0334 :=
    @g_breq1 (.cv x) (syn_cplc (.cv y) (syn_c1c)) (.cv z) (syn_ckqrel (syn_clefin))
  have p0335 :=
    @g_imbi12d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) syntaxFormula0066
      syntaxFormula0098 (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0333 p0334
  have p0336 :=
    @g_breq2 (.cv a) (.cv k) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0337 := @g_breq1 (.cv a) (.cv k) (.cv z) (syn_ckqrel (syn_clefin))
  have p0338 :=
    @g_anbi12d (.classEq (.cv a) (.cv k))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)) p0336 p0337
  have p0339 :=
    @g_imbi1d (.classEq (.cv a) (.cv k)) syntaxFormula0098 syntaxFormula0099
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0338
  have p0340 := @g_breq2 (.cv z) (.cv y) (.cv k) (syn_ckqrel (syn_clefin))
  have p0341 :=
    @g_anbi2d (.classEq (.cv z) (.cv y))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0340
  have p0342 :=
    @g_breq2 (.cv z) (.cv y) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0343 :=
    @g_imbi12d (.classEq (.cv z) (.cv y)) syntaxFormula0099 syntaxFormula0100
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0341 p0342
  have p0344 :=
    @g_rspc3v syntaxFormula0068 syntaxFormula0101
      (.imp syntaxFormula0098
        (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))
      (.imp syntaxFormula0099
        (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))
      x a z (syn_cplc (.cv y) (syn_c1c)) (.cv k) (.cv y) (syn_cnnc) (syn_cnnc) (syn_cnnc)
      dv_cache_0055 dv_cache_0049 dv_cache_0050 dv_cache_0056 dv_cache_0051 dv_cache_0048
      dv_cache_0029 dv_cache_0029 dv_cache_0027 dv_cache_0029 dv_cache_0027 dv_cache_0025
      dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0037 dv_cache_0038 dv_cache_0039
      p0335 p0339 p0343
  have p0345 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0094 syntaxFormula0097
      (.imp syntaxFormula0076 syntaxFormula0101) p0331 p0344
  have p0346 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0094 syntaxFormula0076 syntaxFormula0101 p0311
      p0345
  have p0347 :=
    @g_syl7bi
      (syn_wa (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)))
      syntaxFormula0100 syntaxFormula0001 syntaxFormula0094
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0287 p0346
  have p0348 :=
    @g_exp4a syntaxFormula0001 syntaxFormula0094
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0347
  have p0349 :=
    Nominal.ax2 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0350 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0094
      (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
        (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
          (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))))
      (.imp (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)))
        (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
          (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0348 p0349
  have p0351 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0094
      (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)))
      (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
      p0286 p0350
  have p0352 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0094
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0282 p0351
  have p0353 :=
    @g_exp3a syntaxFormula0001 syntaxFormula0064
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0352
  have p0354 :=
    @g_syl7 (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) syntaxFormula0001
      syntaxFormula0064
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0281 p0353
  have p0355 :=
    @g_notnot1 (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0356 :=
    @g_syl8 syntaxFormula0001 syntaxFormula0064
      (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))))
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
      (.neg (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0354 p0355
  have p0357 :=
    Nominal.ax3 (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
      (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
  have p0358 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0064
      (.imp (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (.neg (.neg
            (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))))
      (.imp (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
        (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0356 p0357
  have p0359 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0064
      (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
      (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0280 p0358
  have p0360 := @g_notnot2 syntaxFormula0102
  have p0362 := @g_pm3_2 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0102
  have p0364 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv y)
  have p0365 := Nominal.mp p0121 p0364
  have p0366 := @g_biimpri syntaxFormula0103 syntaxFormula0104 p0365
  have p0367 :=
    @g_syl6 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0102 syntaxFormula0104
      syntaxFormula0103 p0362 p0366
  have p0368 := @g_simprd syntaxFormula0001 syntaxFormula0022 syntaxFormula0023 p0057
  have p0369 := @g_id (.classEq (.cv n) (.cv q))
  have p0370 := @g_eleq1d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) syntaxClass0019 p0369
  have p0371 := @g_id (.classEq (.cv n) (.cv q))
  have p0372 :=
    @g_breq2d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) (.cv k) (syn_ckqrel (syn_clefin))
      p0371
  have p0373 :=
    @g_imbi12d (.classEq (.cv n) (.cv q)) syntaxFormula0020 syntaxFormula0105
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) p0370 p0372
  have p0374_e00_recanon :
    Nominal.NPrf (.imp (.objEq n q) (syn_wb syntaxFormula0021 syntaxFormula0106)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wbr, syn_cop, syn_cun, syn_cnin,
          syn_wnan, syn_ccompl, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0373
  have p0374 :=
    @g_cbvralv syntaxFormula0021 syntaxFormula0106 n q (syn_cnnc) dv_cache_0060
      dv_cache_0061 dv_cache_0062 dv_cache_0063 p0374_e00_recanon
  have p0375 := @g_sylib syntaxFormula0001 syntaxFormula0023 syntaxFormula0107 p0368 p0374
  have p0386 := @g_eleq2i syntaxClass0026 syntaxClass0019 (.cv q) p0082
  have p0387 :=
    @g_imbi1i syntaxFormula0108 syntaxFormula0105
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) p0386
  have p0388 := @g_ralbii syntaxFormula0109 syntaxFormula0106 q (syn_cnnc) p0387
  have p0389 :=
    @g_sylibr syntaxFormula0001 syntaxFormula0107 syntaxFormula0110 p0375 p0388
  have p0390 := @g_id (.classEq (.cv q) (.cv y))
  have p0391 := @g_eleq1d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) syntaxClass0026 p0390
  have p0393 :=
    @g_breq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (.cv k) (syn_ckqrel (syn_clefin))
      p0390
  have p0394 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) syntaxFormula0108 syntaxFormula0103
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0391 p0393
  have p0395 :=
    @g_rspcv syntaxFormula0109 syntaxFormula0111 q (.cv y) (syn_cnnc) dv_cache_0064
      dv_cache_0061 dv_cache_0065 p0394
  have p0396 :=
    @g_syl5com syntaxFormula0001 syntaxFormula0110 (.classMem (.cv y) (syn_cnnc))
      syntaxFormula0111 p0389 p0395
  have p0397 :=
    @g_a1dd syntaxFormula0001 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0111
      syntaxFormula0102 p0396
  have p0398 :=
    Nominal.ax2 syntaxFormula0102 syntaxFormula0103
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0399 :=
    @g_syl6 syntaxFormula0001 (.classMem (.cv y) (syn_cnnc))
      (.imp syntaxFormula0102 syntaxFormula0111)
      (.imp syntaxFormula0112 syntaxFormula0113) p0397 p0398
  have p0400 :=
    @g_mpdi syntaxFormula0001 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0112
      syntaxFormula0113 p0367 p0399
  have p0401 :=
    @g_syl5 syntaxFormula0064 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0001
      syntaxFormula0113 p0182 p0400
  have p0402 :=
    @g_syl7 syntaxFormula0115 syntaxFormula0102 syntaxFormula0001 syntaxFormula0064
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0360 p0401
  have p0403 := @g_notnot1 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0404 :=
    @g_syl8 syntaxFormula0001 syntaxFormula0064 syntaxFormula0115
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
      (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) p0402 p0403
  have p0405 :=
    Nominal.ax3 syntaxFormula0114
      (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
  have p0406 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0064
      (.imp syntaxFormula0115 (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))))
      (.imp (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) syntaxFormula0114)
      p0404 p0405
  have p0407 :=
    @g_mpdd syntaxFormula0001 syntaxFormula0064
      (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) syntaxFormula0114 p0359
      p0406
  have p0416 :=
    @g_wpporbithwcldmndv (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) q dv_cache_0066 dv_cache_0067 p0084
      p0119 p0120 p0116
  have p0417 := @g_hwcardstcclndv C
  have p0418 := Nominal.mp hyp_wppstopfixedhitcontrgrowfixdndv_3 p0417
  have p0419 :=
    @g_a1i (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) syntaxFormula0118 p0418
  have p0420 := @g_simpr (.classMem (.cv q) (syn_cnnc)) syntaxFormula0117
  have p0421 :=
    @g_jca syntaxFormula0118 (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
      syntaxFormula0117 p0419 p0420
  have p0422 := @g_hwcardslecconnexndv (syn_ctc C) syntaxClass0116
  have p0423 :=
    @g_syl syntaxFormula0118
      (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) syntaxFormula0117)
      syntaxFormula0121 p0421 p0422
  have p0424 := @g_notnot syntaxFormula0119
  have p0425 := @g_biimpi syntaxFormula0119 (.neg syntaxFormula0122) p0424
  have p0426 := @g_pm2_21 syntaxFormula0122 syntaxFormula0120
  have p0427 :=
    @g_syl syntaxFormula0119 (.neg syntaxFormula0122) syntaxFormula0123 p0425 p0426
  have p0428 := @g_id syntaxFormula0120
  have p0429 := @g_a1d syntaxFormula0120 syntaxFormula0120 syntaxFormula0122 p0428
  have p0430 := @g_jaoi syntaxFormula0119 syntaxFormula0123 syntaxFormula0120 p0427 p0429
  have p0431 := @g_syl syntaxFormula0118 syntaxFormula0121 syntaxFormula0123 p0423 p0430
  have p0432 := @g_ralimiaa syntaxFormula0117 syntaxFormula0123 q (syn_cnnc) p0431
  have p0433 := Nominal.mp p0416 p0432
  have p0435 := @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) syntaxClass0028 p0390
  have p0436 :=
    @g_breq2d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088 (syn_ctc C)
      (syn_clec) p0435
  have p0437 :=
    @g_notbid (.classEq (.cv q) (.cv y)) syntaxFormula0119 syntaxFormula0102 p0436
  have p0440 :=
    @g_breq1d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088 (syn_ctc C)
      (syn_clec) p0435
  have p0441 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) syntaxFormula0122 syntaxFormula0114
      syntaxFormula0120 syntaxFormula0124 p0437 p0440
  have p0442 :=
    @g_rspcv syntaxFormula0123 syntaxFormula0125 q (.cv y) (syn_cnnc) dv_cache_0064
      dv_cache_0061 dv_cache_0068 p0441
  have p0443 :=
    @g_mpi (.classMem (.cv y) (syn_cnnc)) (syn_wral q (syn_cnnc) syntaxFormula0123)
      syntaxFormula0125 p0433 p0442
  have p0444 :=
    @g_syl syntaxFormula0064 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0125 p0182 p0443
  have p0445 :=
    @g_sylcom syntaxFormula0001 syntaxFormula0064 syntaxFormula0114 syntaxFormula0124
      p0407 p0444
  have p0454 := @g_a1i syntaxFormula0126 (.classMem (.cv q) (syn_cnnc)) p0121
  have p0455 := @g_id (.classMem (.cv q) (syn_cnnc))
  have p0456 :=
    @g_jca (.classMem (.cv q) (syn_cnnc)) syntaxFormula0126 (.classMem (.cv q) (syn_cnnc))
      p0454 p0455
  have p0457 :=
    @g_frecdomfv (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv q)
  have p0458 :=
    @g_syl (.classMem (.cv q) (syn_cnnc))
      (syn_wa syntaxFormula0126 (.classMem (.cv q) (syn_cnnc))) syntaxFormula0127 p0456
      p0457
  have p0460 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv))
      syntaxClass0116 p0116
  have p0461 := @g_biimpi syntaxFormula0127 syntaxFormula0117 p0460
  have p0462 :=
    @g_syl (.classMem (.cv q) (syn_cnnc)) syntaxFormula0127 syntaxFormula0117 p0458 p0461
  have p0463 :=
    @g_wppstopstepsamebelowdndv y C F p dv_cache_0069 dv_cache_0070 dv_cache_0071
      hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
      hyp_wppstopfixedhitcontrgrowfixdndv_3 hyp_wppstopfixedhitcontrgrowfixdndv_4
      hyp_wppstopfixedhitcontrgrowfixdndv_5
  have p0464 := @g_rgen syntaxFormula0129 y (syn_chwcards (syn_cvv)) p0463
  have p0465 := @g_id syntaxFormula0130
  have p0466 :=
    @g_breq1d syntaxFormula0130 (.cv y) syntaxClass0116 (syn_ctc C) (syn_clec) p0465
  have p0468 :=
    @g_fveq2d syntaxFormula0130 (.cv y) syntaxClass0116 (syn_cwppstopstep F C) p0465
  have p0470 :=
    @g_fveq2d syntaxFormula0130 (.cv y) syntaxClass0116 (syn_cwppstopstep F (syn_ctc C))
      p0465
  have p0471 :=
    @g_eqeq12d syntaxFormula0130 (syn_cfv (syn_cwppstopstep F C) (.cv y)) syntaxClass0131
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) syntaxClass0132 p0468 p0470
  have p0472 :=
    @g_imbi12d syntaxFormula0130 (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
      syntaxFormula0120 syntaxFormula0128 syntaxFormula0133 p0466 p0471
  have p0473 :=
    @g_rspcv syntaxFormula0129 syntaxFormula0134 y syntaxClass0116
      (syn_chwcards (syn_cvv)) dv_cache_0072 dv_cache_0073 dv_cache_0074 p0472
  have p0474 :=
    @g_mpi syntaxFormula0117 (syn_wral y (syn_chwcards (syn_cvv)) syntaxFormula0129)
      syntaxFormula0134 p0464 p0473
  have p0475 :=
    @g_syl (.classMem (.cv q) (syn_cnnc)) syntaxFormula0117 syntaxFormula0134 p0462 p0474
  have p0476 := @g_rgen syntaxFormula0134 q (syn_cnnc) p0475
  have p0482 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088
      (syn_cwppstopstep F C) p0435
  have p0485 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088
      (syn_cwppstopstep F (syn_ctc C)) p0435
  have p0486 :=
    @g_eqeq12d (.classEq (.cv q) (.cv y)) syntaxClass0131 syntaxClass0090 syntaxClass0132
      syntaxClass0135 p0482 p0485
  have p0487 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) syntaxFormula0120 syntaxFormula0124
      syntaxFormula0133 syntaxFormula0136 p0440 p0486
  have p0488 :=
    @g_rspcv syntaxFormula0134 syntaxFormula0137 q (.cv y) (syn_cnnc) dv_cache_0064
      dv_cache_0061 dv_cache_0075 p0487
  have p0489 :=
    @g_mpi (.classMem (.cv y) (syn_cnnc)) (syn_wral q (syn_cnnc) syntaxFormula0134)
      syntaxFormula0137 p0476 p0488
  have p0490 :=
    @g_syl syntaxFormula0064 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0137 p0182 p0489
  have p0491 :=
    @g_sylcom syntaxFormula0001 syntaxFormula0064 syntaxFormula0124 syntaxFormula0136
      p0445 p0490
  have p0492 :=
    @g_syl5 syntaxFormula0058 syntaxFormula0064 syntaxFormula0001 syntaxFormula0136 p0180
      p0491
  have p0493 := @g_eqeq2 syntaxClass0090 syntaxClass0135 syntaxClass0059
  have p0494 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0136 syntaxFormula0139 p0492
      p0493
  have p0495 := @g_bi1 syntaxFormula0092 syntaxFormula0138
  have p0496 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0139
      (.imp syntaxFormula0092 syntaxFormula0138) p0494 p0495
  have p0497 :=
    @g_mpdd syntaxFormula0001 syntaxFormula0058 syntaxFormula0092 syntaxFormula0138 p0274
      p0496
  have p0499 := @g_a1i syntaxFormula0126 syntaxFormula0058 p0121
  have p0501 :=
    @g_jca syntaxFormula0058 syntaxFormula0126 (.classMem (.cv y) (syn_cnnc)) p0499 p0171
  have p0502 :=
    @g_wpporbitsucndv (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv y)
  have p0503 :=
    @g_syl syntaxFormula0058 (syn_wa syntaxFormula0126 (.classMem (.cv y) (syn_cnnc)))
      (.classEq syntaxClass0140 syntaxClass0135) p0501 p0502
  have p0504 := @g_eqcomd syntaxFormula0058 syntaxClass0140 syntaxClass0135 p0503
  have p0505 :=
    @g_eqeq2d syntaxFormula0058 syntaxClass0135 syntaxClass0140 syntaxClass0059 p0504
  have p0506 :=
    @g_mpbidi syntaxFormula0058 syntaxFormula0138 syntaxFormula0141 syntaxFormula0001
      p0497 p0505
  have p0507 :=
    @g_n_3expd syntaxFormula0001 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056
      (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
      syntaxFormula0141 p0506
  have p0509 :=
    @g_wppfrecprefixeqvalndv (syn_cplc (.cv y) (syn_c1c)) k (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0510 :=
    @g_syl (.classMem (.cv y) (syn_cnnc))
      (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))
      (syn_wb syntaxFormula0142 syntaxFormula0143) p0226 p0509
  have p0511 :=
    @g_biimprd (.classMem (.cv y) (syn_cnnc)) syntaxFormula0142 syntaxFormula0143 p0510
  have p0512 :=
    @g_a1d (.classMem (.cv y) (syn_cnnc)) (.imp syntaxFormula0143 syntaxFormula0142)
      syntaxFormula0056 p0511
  have p0513 :=
    @g_a2d (.classMem (.cv y) (syn_cnnc)) syntaxFormula0056 syntaxFormula0143
      syntaxFormula0142 p0512
  have p0514 :=
    @g_sylcom syntaxFormula0001 (.classMem (.cv y) (syn_cnnc))
      (.imp syntaxFormula0056 syntaxFormula0143) syntaxFormula0144 p0507 p0513
  have p0515 :=
    @g_adantrd syntaxFormula0001 (.classMem (.cv y) (syn_cnnc)) syntaxFormula0144 syn_wtru
      p0514
  have p0516 :=
    @g_syl7bi syntaxFormula0145 syntaxFormula0056 syntaxFormula0001
      (syn_wa (.classMem (.cv y) (syn_cnnc)) syn_wtru) syntaxFormula0142 p0168 p0515
  have p0517 := @g_n_1cex
  have p0518 := @g_addcex (.cv y) (syn_c1c) p0165 p0517
  have p0519 := @g_id (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
  have p0520 :=
    @g_eleq1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.cv x)
      (syn_cplc (.cv y) (syn_c1c)) syntaxClass0045 p0519
  have p0521 :=
    @g_elab syntaxFormula0046 syntaxFormula0142 x (syn_cplc (.cv y) (syn_c1c))
      dv_cache_0055 dv_cache_0076 p0518 p0520
  have p0522 := @g_biimpri syntaxFormula0146 syntaxFormula0142 p0521
  have p0523 :=
    @g_syl8 syntaxFormula0001 (syn_wa (.classMem (.cv y) (syn_cnnc)) syn_wtru)
      syntaxFormula0145 syntaxFormula0142 syntaxFormula0146 p0516 p0522
  have p0524 :=
    @g_ancomsd syntaxFormula0001 (.classMem (.cv y) (syn_cnnc)) syn_wtru syntaxFormula0147
      p0523
  have p0525 :=
    @g_exp3a syntaxFormula0001 syn_wtru (.classMem (.cv y) (syn_cnnc)) syntaxFormula0147
      p0524
  have p0526 :=
    @g_ralrimdv syntaxFormula0001 syn_wtru syntaxFormula0147 y (syn_cnnc) dv_cache_0077
      dv_cache_0078 p0525
  have p0527 := @g_pm3_2 syntaxFormula0148 syntaxFormula0149
  have p0528 :=
    @g_syl9 syntaxFormula0001 syn_wtru syntaxFormula0149 syntaxFormula0148
      syntaxFormula0150 p0526 p0527
  have p0529 :=
    @g_syl5 syn_wtru syntaxFormula0148 syntaxFormula0001 (.imp syn_wtru syntaxFormula0150)
      p0164 p0528
  have p0530 := @g_pm2_43d syntaxFormula0001 syn_wtru syntaxFormula0150 p0529
  have p0531 := (Nominal.biimpRefl syntaxFormula0151)
  have p0532 :=
    @g_syl6ibr syntaxFormula0001 syn_wtru syntaxFormula0150 syntaxFormula0151 p0530 p0531
  have p0533 := @g_peano5 y syntaxClass0047 (syn_cvv) dv_cache_0079
  have p0534 :=
    @g_syl6 syntaxFormula0001 syn_wtru syntaxFormula0151 syntaxFormula0152 p0532 p0533
  have p0535 := @g_ssel (syn_cnnc) syntaxClass0047 (.cv n)
  have p0536 :=
    @g_syl6 syntaxFormula0001 syn_wtru syntaxFormula0152
      (.imp (.classMem (.cv n) (syn_cnnc)) syntaxFormula0153) p0534 p0535
  have p0537 :=
    @g_com23 syntaxFormula0001 syn_wtru (.classMem (.cv n) (syn_cnnc)) syntaxFormula0153
      p0536
  have p0538 :=
    @g_imp3a syntaxFormula0001 (.classMem (.cv n) (syn_cnnc)) syn_wtru syntaxFormula0153
      p0537
  have p0539 := @g_id (.classEq (.cv x) (.cv n))
  have p0540 := @g_eleq1d (.classEq (.cv x) (.cv n)) (.cv x) (.cv n) syntaxClass0045 p0539
  have p0541 :=
    @g_elabg syntaxFormula0046 syntaxFormula0154 x (.cv n) (syn_cnnc) dv_cache_0080
      dv_cache_0081 p0540
  have p0542 :=
    @g_adantr (.classMem (.cv n) (syn_cnnc)) (syn_wb syntaxFormula0153 syntaxFormula0154)
      syn_wtru p0541
  have p0543 :=
    @g_mpbidi (syn_wa (.classMem (.cv n) (syn_cnnc)) syn_wtru) syntaxFormula0153
      syntaxFormula0154 syntaxFormula0001 p0538 p0542
  have p0544 :=
    @g_mpan2i syntaxFormula0001 (.classMem (.cv n) (syn_cnnc)) syn_wtru syntaxFormula0154
      p0133 p0543
  have p0545 :=
    @g_wppfrecprefixeqvalndv (.cv n) k (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0546 :=
    @g_mpbidi (.classMem (.cv n) (syn_cnnc)) syntaxFormula0154 syntaxFormula0158
      syntaxFormula0001 p0544 p0545
  have p0547 :=
    @g_ralrimiv syntaxFormula0001 syntaxFormula0158 n (syn_cnnc) dv_cache_0082 p0546
  have p0548 := @g_id (.classEq (.cv n) (.cv k))
  have p0549 :=
    @g_breq1d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (.cv k) (syn_ckqrel (syn_clefin))
      p0548
  have p0551 := @g_fveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) syntaxClass0051 p0548
  have p0553 := @g_fveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) syntaxClass0028 p0548
  have p0554 :=
    @g_eqeq12d (.classEq (.cv n) (.cv k)) syntaxClass0155 syntaxClass0159 syntaxClass0156
      syntaxClass0043 p0551 p0553
  have p0555 :=
    @g_imbi12d (.classEq (.cv n) (.cv k))
      (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0157
      syntaxFormula0160 p0549 p0554
  have p0556 :=
    @g_rspcv syntaxFormula0158 syntaxFormula0161 n (.cv k) (syn_cnnc) dv_cache_0083
      dv_cache_0060 dv_cache_0084 p0555
  have p0557 :=
    @g_syl5com syntaxFormula0001 (syn_wral n (syn_cnnc) syntaxFormula0158)
      (.classMem (.cv k) (syn_cnnc)) syntaxFormula0161 p0547 p0556
  have p0558 :=
    @g_mpd syntaxFormula0001 (.classMem (.cv k) (syn_cnnc)) syntaxFormula0161 p0053 p0557
  have p0559 :=
    @g_mpd syntaxFormula0001 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k))
      syntaxFormula0160 p0132 p0558
  have p0560 := @g_eqcomd syntaxFormula0001 syntaxClass0159 syntaxClass0043 p0559
  have p0561 :=
    @g_breq2d syntaxFormula0001 syntaxClass0043 syntaxClass0159 (syn_ctc C) (syn_clec)
      p0560
  have p0562 := @g_mpbid syntaxFormula0001 syntaxFormula0044 syntaxFormula0162 p0125 p0561
  have p0563 :=
    @g_jca syntaxFormula0001 (.classMem (.cv k) (syn_cnnc)) syntaxFormula0162 p0053 p0562
  have p0565 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F C)
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv k)
  have p0566 := Nominal.mp p0145 p0565
  have p0567 :=
    @g_sylibr syntaxFormula0001 (syn_wa (.classMem (.cv k) (syn_cnnc)) syntaxFormula0162)
      syntaxFormula0164 p0563 p0566
  have p0568 := @g_jca syntaxFormula0001 syntaxFormula0164 syntaxFormula0165 p0567 p0560
  have p0569 := @g_simpl syntaxFormula0164 syntaxFormula0165
  have p0570 :=
    @g_syl syntaxFormula0001 (syn_wa syntaxFormula0164 syntaxFormula0165)
      syntaxFormula0164 p0568 p0569
  have p0572 := @g_wppweconnex (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0573 := Nominal.mp p0126 p0572
  have p0574 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) syntaxFormula0167
      p0573
  have p0575 := @g_brex (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cconnex)
  have p0576 := @g_breq (.cv x) (.cv y) (.cv r) (syn_ckqrel (syn_clefin))
  have p0577 := @g_breq (.cv y) (.cv x) (.cv r) (syn_ckqrel (syn_clefin))
  have p0578 :=
    @g_orbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin)))
      (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (.cv r) (.cv x))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) p0576 p0577
  have p0579 :=
    @g_n_2ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin)))
      (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      syntaxFormula0168 x y (.cv a) (.cv a) dv_cache_0022 dv_cache_0085 p0578
  have p0580 :=
    @g_raleq syntaxFormula0168 y (.cv a) (syn_cnnc) dv_cache_0086 dv_cache_0087
  have p0581 :=
    @g_raleqbi1dv (syn_wral y (.cv a) syntaxFormula0168) syntaxFormula0169 x (.cv a)
      (syn_cnnc) dv_cache_0088 dv_cache_0029 p0580
  have p0582 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex x y r a
      dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0034 dv_cache_0092 dv_cache_0093
  have p0583 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      (syn_wral x (.cv a) (syn_wral y (.cv a) syntaxFormula0168)) syntaxFormula0170 r a
      (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cvv) (syn_cvv) (syn_cconnex) dv_cache_0040
      dv_cache_0094 dv_cache_0042 dv_cache_0027 dv_cache_0095 dv_cache_0096 dv_cache_0035
      p0579 p0581 p0582
  have p0584 :=
    @g_syl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))
      (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem (syn_cnnc) (syn_cvv)))
      (syn_wb (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) syntaxFormula0170)
      p0575 p0583
  have p0585 :=
    @g_ibi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) syntaxFormula0170
      p0584
  have p0586 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0166
  have p0587 :=
    @g_a1d syntaxFormula0001 (.classMem (.cv k) (syn_cnnc)) syntaxFormula0167 p0053
  have p0588 := @g_breq1 (.cv x) (.cv n) (.cv y) (syn_ckqrel (syn_clefin))
  have p0589 := @g_breq2 (.cv x) (.cv n) (.cv y) (syn_ckqrel (syn_clefin))
  have p0590 :=
    @g_orbi12d (.classEq (.cv x) (.cv n))
      (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n)) p0588 p0589
  have p0591 := @g_breq2 (.cv y) (.cv k) (.cv n) (syn_ckqrel (syn_clefin))
  have p0592 := @g_breq1 (.cv y) (.cv k) (.cv n) (syn_ckqrel (syn_clefin))
  have p0593 :=
    @g_orbi12d (.classEq (.cv y) (.cv k))
      (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0591 p0592
  have p0594 :=
    @g_rspc2v syntaxFormula0168 syntaxFormula0171
      (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n)))
      x y (.cv n) (.cv k) (syn_cnnc) (syn_cnnc) dv_cache_0080 dv_cache_0097 dv_cache_0098
      dv_cache_0029 dv_cache_0029 dv_cache_0087 dv_cache_0099 dv_cache_0100 dv_cache_0093
      p0590 p0593
  have p0595 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) syntaxFormula0172
      p0594
  have p0596 :=
    @g_syl9 syntaxFormula0001 syntaxFormula0167 (.classMem (.cv k) (syn_cnnc))
      (.classMem (.cv n) (syn_cnnc)) syntaxFormula0172 p0587 p0595
  have p0597 :=
    @g_syl5 syntaxFormula0167 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0001
      (.imp syntaxFormula0167 syntaxFormula0172) p0586 p0596
  have p0598 := @g_pm2_43d syntaxFormula0001 syntaxFormula0167 syntaxFormula0172 p0597
  have p0599 :=
    @g_syl7 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) syntaxFormula0170
      syntaxFormula0001 syntaxFormula0167 syntaxFormula0171 p0585 p0598
  have p0600 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0167
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) syntaxFormula0171 p0574
      p0599
  have p0601 :=
    @g_pm2_53 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
  have p0602 := @g_id (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
  have p0603 :=
    @g_a1i
      (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
      syntaxFormula0167 p0602
  have p0604 :=
    @g_com12 syntaxFormula0167 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0603
  have p0605 :=
    @g_syl6 syntaxFormula0171 (.neg (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) syntaxFormula0173 p0601 p0604
  have p0606 :=
    @g_con1d syntaxFormula0171 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      syntaxFormula0173 p0605
  have p0607 :=
    @g_simpl syntaxFormula0167 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0609 :=
    @g_syl syntaxFormula0174 syntaxFormula0167 (.classMem (.cv n) (syn_cnnc)) p0607 p0586
  have p0611 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0166
  have p0612 := @g_syl syntaxFormula0174 syntaxFormula0167 syntaxFormula0166 p0607 p0611
  have p0620 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F C)
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n)
  have p0621 := Nominal.mp p0145 p0620
  have p0622 := @g_biimpi syntaxFormula0166 syntaxFormula0176 p0621
  have p0623 := @g_syl syntaxFormula0174 syntaxFormula0166 syntaxFormula0176 p0612 p0622
  have p0624 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0175
  have p0625 := @g_syl syntaxFormula0174 syntaxFormula0176 syntaxFormula0175 p0623 p0624
  have p0626 :=
    @g_simpr syntaxFormula0167 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0630 :=
    @g_syl5 syntaxFormula0174 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0001
      syntaxFormula0158 p0609 p0546
  have p0631 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0174
      (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0157 p0626 p0630
  have p0632 := @g_breq2 syntaxClass0155 syntaxClass0156 (syn_ctc C) (syn_clec)
  have p0633 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0174 syntaxFormula0157 syntaxFormula0178 p0631
      p0632
  have p0634 := @g_bi1 syntaxFormula0175 syntaxFormula0177
  have p0635 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0174 syntaxFormula0178
      (.imp syntaxFormula0175 syntaxFormula0177) p0633 p0634
  have p0636 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0174 syntaxFormula0175 syntaxFormula0177 p0625
      p0635
  have p0637 := @g_pm3_2 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0177
  have p0638 :=
    @g_syl9 syntaxFormula0001 syntaxFormula0174 syntaxFormula0177
      (.classMem (.cv n) (syn_cnnc)) syntaxFormula0179 p0636 p0637
  have p0639 :=
    @g_syl5 syntaxFormula0174 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0001
      (.imp syntaxFormula0174 syntaxFormula0179) p0609 p0638
  have p0640 := @g_pm2_43d syntaxFormula0001 syntaxFormula0174 syntaxFormula0179 p0639
  have p0648 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n)
  have p0649 := Nominal.mp p0121 p0648
  have p0650 := @g_biimpri syntaxFormula0180 syntaxFormula0179 p0649
  have p0651 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0174 syntaxFormula0179 syntaxFormula0180 p0640
      p0650
  have p0655 := @g_id (.classEq (.cv q) (.cv n))
  have p0656 := @g_eleq1d (.classEq (.cv q) (.cv n)) (.cv q) (.cv n) syntaxClass0026 p0655
  have p0658 :=
    @g_breq2d (.classEq (.cv q) (.cv n)) (.cv q) (.cv n) (.cv k) (syn_ckqrel (syn_clefin))
      p0655
  have p0659 :=
    @g_imbi12d (.classEq (.cv q) (.cv n)) syntaxFormula0108 syntaxFormula0180
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0656 p0658
  have p0660 :=
    @g_rspcv syntaxFormula0109 syntaxFormula0181 q (.cv n) (syn_cnnc) dv_cache_0101
      dv_cache_0061 dv_cache_0102 p0659
  have p0661 :=
    @g_syl5com syntaxFormula0001 syntaxFormula0110 (.classMem (.cv n) (syn_cnnc))
      syntaxFormula0181 p0389 p0660
  have p0662 :=
    @g_syl5 syntaxFormula0174 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0001
      syntaxFormula0181 p0609 p0661
  have p0663 :=
    @g_mpdd syntaxFormula0001 syntaxFormula0174 syntaxFormula0180
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0651 p0662
  have p0664 :=
    @g_exp3a syntaxFormula0001 syntaxFormula0167
      (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0663
  have p0665 :=
    @g_com23 syntaxFormula0001 syntaxFormula0167
      (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0664
  have p0666 := @g_a1d syntaxFormula0001 syntaxFormula0182 syntaxFormula0171 p0665
  have p0667 :=
    @g_a1dd syntaxFormula0001 syntaxFormula0171 syntaxFormula0182 syntaxFormula0183 p0666
  have p0668 :=
    Nominal.ax2 syntaxFormula0183 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
      syntaxFormula0173
  have p0669 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0171 (.imp syntaxFormula0183 syntaxFormula0182)
      (.imp syntaxFormula0184 syntaxFormula0185) p0667 p0668
  have p0670 :=
    @g_mpdi syntaxFormula0001 syntaxFormula0171 syntaxFormula0184 syntaxFormula0185 p0606
      p0669
  have p0671 := @g_pm2_18 syntaxFormula0173
  have p0672 :=
    @g_syl6 syntaxFormula0001 syntaxFormula0171 syntaxFormula0185 syntaxFormula0173 p0670
      p0671
  have p0673 :=
    @g_com23 syntaxFormula0001 syntaxFormula0171 syntaxFormula0167
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0672
  have p0674 :=
    @g_mpdd syntaxFormula0001 syntaxFormula0167 syntaxFormula0171
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0600 p0673
  have p0675 :=
    @g_exp3a syntaxFormula0001 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0166
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0674
  have p0676 :=
    @g_ralrimiv syntaxFormula0001 syntaxFormula0186 n (syn_cnnc) dv_cache_0082 p0675
  have p0681 := @g_fveq1i (.cv k) syntaxClass0028 syntaxClass0029 p0077
  have p0682 := @g_eqcomi syntaxClass0043 syntaxClass0187 p0681
  have p0683 :=
    @g_syl5eq syntaxFormula0001 syntaxClass0187 syntaxClass0043 syntaxClass0159 p0682
      p0560
  have p0684 :=
    @g_n_3jca syntaxFormula0001 syntaxFormula0164 syntaxFormula0188 syntaxFormula0189
      p0570 p0676 p0683
  have p0685 :=
    @g_simp1d syntaxFormula0001 syntaxFormula0164 syntaxFormula0188 syntaxFormula0189
      p0684
  have p0686 := @g_jca syntaxFormula0001 syntaxFormula0009 syntaxFormula0164 p0056 p0685
  have p0687 :=
    @g_jca syntaxFormula0001
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      syntaxFormula0190 p0054 p0686
  have p0688 := @g_simprd syntaxFormula0001 syntaxFormula0009 syntaxFormula0010 p0055
  have p0689 := @g_jca syntaxFormula0001 syntaxFormula0010 syntaxFormula0188 p0688 p0676
  have p0690 := @g_jca syntaxFormula0001 syntaxFormula0191 syntaxFormula0192 p0687 p0689
  have p0698 := @g_hwcardssnc (syn_cvv)
  have p0699 :=
    @g_sselii (syn_chwcards (syn_cvv)) (syn_cncs) C p0698
      hyp_wppstopfixedhitcontrgrowfixdndv_3
  have p0700 := @g_tccl C
  have p0701 := Nominal.mp p0699 p0700
  have p0702 :=
    @g_n_3pm3_2i (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wbr (syn_ctc C) (syn_clec) C) p0701 p0699 hyp_wppstopfixedhitcontrgrowfixdndv_4
  have p0703 := @g_pm3_2i syntaxFormula0057 syntaxFormula0193 p0145 p0702
  have p0711 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (.cv n)
  have p0712 :=
    @g_mpan syntaxFormula0057 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0194 p0145 p0711
  have p0714 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) syntaxClass0155
      p0140
  have p0715 := @g_biimpi syntaxFormula0194 syntaxFormula0195 p0714
  have p0716 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0194 syntaxFormula0195 p0712 p0715
  have p0718 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) syntaxClass0155 p0698
  have p0719 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0195 syntaxFormula0196 p0716 p0718
  have p0720 := @g_rgen syntaxFormula0196 n (syn_cnnc) p0719
  have p0721 := @g_id (.classEq (.cv n) (.cv q))
  have p0722 := @g_fveq2d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) syntaxClass0051 p0721
  have p0723 :=
    @g_eleq1d (.classEq (.cv n) (.cv q)) syntaxClass0155 syntaxClass0197 (syn_cncs) p0722
  have p0724_e00_recanon :
    Nominal.NPrf (.imp (.objEq n q) (syn_wb syntaxFormula0196 syntaxFormula0198)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wex, syn_wa, syn_csn, syn_cop, syn_cun, syn_cnin, syn_wnan,
          syn_ccompl, syn_wrex, syn_cphi, syn_cin, syn_copab, syn_cvv, syn_cplc, syn_c1c,
          syn_cif, syn_wo, syn_c0c, syn_cncs, syn_cqs, syn_cen]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0723
  have p0724 :=
    @g_cbvralv syntaxFormula0196 syntaxFormula0198 n q (syn_cnnc) dv_cache_0060
      dv_cache_0061 dv_cache_0103 dv_cache_0104 p0724_e00_recanon
  have p0725 :=
    @g_mpbi (syn_wral n (syn_cnnc) syntaxFormula0196) syntaxFormula0199 p0720 p0724
  have p0726 := @g_pm3_2i syntaxFormula0200 syntaxFormula0199 p0703 p0725
  have p0727 := @g_jctir syntaxFormula0001 syntaxFormula0201 syntaxFormula0202 p0690 p0726
  have p0729 :=
    @g_simpr (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)
  have p0730 :=
    @g_syl syntaxFormula0001 syntaxFormula0000 (syn_wa (.classEq I (syn_ctc I)) ch) p0035
      p0729
  have p0731 := @g_simpr (.classEq I (syn_ctc I)) ch
  have p0732 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ch) ch syntaxFormula0204 p0731
      hyp_wppstopfixedhitcontrgrowfixdndv_12
  have p0733 :=
    @g_syl syntaxFormula0001 (syn_wa (.classEq I (syn_ctc I)) ch) syntaxFormula0204 p0730
      p0732
  have p0741 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (.cv r)
  have p0742 :=
    @g_mpan syntaxFormula0057 (.classMem (.cv r) (syn_cnnc))
      (.classMem syntaxClass0205 (syn_cdm (syn_cwppstopstep F C))) p0145 p0741
  have p0743 := @g_simpr (.classMem (.cv r) (syn_cnnc)) syntaxFormula0206
  have p0744 :=
    @g_breq2d syntaxFormula0207 (.cv y) syntaxClass0205 (syn_ctc C) (syn_clec) p0743
  have p0746 :=
    @g_fveq2d syntaxFormula0207 (.cv y) syntaxClass0205 (syn_cwppstopstep F C) p0743
  have p0747 :=
    @g_breq2d syntaxFormula0207 (syn_cfv (syn_cwppstopstep F C) (.cv y)) syntaxClass0208 C
      (syn_clec) p0746
  have p0748 :=
    @g_imbi12d syntaxFormula0207 (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      syntaxFormula0209 (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))
      syntaxFormula0210 p0744 p0747
  have p0749 :=
    @g_rspcdv (.classMem (.cv r) (syn_cnnc)) syntaxFormula0203 syntaxFormula0211 y
      syntaxClass0205 (syn_cdm (syn_cwppstopstep F C)) dv_cache_0105 dv_cache_0106
      dv_cache_0107 dv_cache_0108 p0742 p0748
  have p0750 :=
    @g_syl5com syntaxFormula0001 syntaxFormula0204 (.classMem (.cv r) (syn_cnnc))
      syntaxFormula0211 p0733 p0749
  have p0751 :=
    @g_ralrimiv syntaxFormula0001 syntaxFormula0211 r (syn_cnnc) dv_cache_0109 p0750
  have p0752 := (Nominal.biimpRefl syntaxFormula0213)
  have p0753 :=
    @g_sylanbrc syntaxFormula0001 (syn_wa syntaxFormula0201 syntaxFormula0202)
      syntaxFormula0212 syntaxFormula0213 p0727 p0751 p0752
  have p0754 :=
    @g_wpphitminadjndv k m n (syn_cwppstopstep F C) C
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C) r q dv_cache_0110
      dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116
      dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122
      dv_cache_0067 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127
      dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133
  have p0755 :=
    @g_syl syntaxFormula0001 syntaxFormula0213
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0753 p0754
  have p0756 := @g_a1i (.classMem C (syn_cncs)) syntaxFormula0214 p0699
  have p0757 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0196
  have p0758 :=
    @g_jca syntaxFormula0214 (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc)) p0756
      p0757
  have p0759 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0196
  have p0760 :=
    @g_jca syntaxFormula0214
      (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) syntaxFormula0196
      p0758 p0759
  have p0762 :=
    @g_elwpphitvndv C (syn_cwppstopstep F C)
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n)
  have p0763 := Nominal.mp p0145 p0762
  have p0764 :=
    @g_a1i
      (syn_wb syntaxFormula0007 (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0215))
      syntaxFormula0216 p0763
  have p0765 :=
    @g_simpl (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc)))
      syntaxFormula0196
  have p0766 := @g_simpr (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))
  have p0767 :=
    @g_syl syntaxFormula0216
      (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc)))
      (.classMem (.cv n) (syn_cnnc)) p0765 p0766
  have p0771 := @g_nntccl (.cv n)
  have p0772 :=
    @g_syl syntaxFormula0216 (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0767 p0771
  have p0773 :=
    @g_n_2thd syntaxFormula0216 (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0767 p0772
  have p0775 := @g_simpl (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))
  have p0776 :=
    @g_syl syntaxFormula0216
      (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc)))
      (.classMem C (syn_cncs)) p0765 p0775
  have p0777 :=
    @g_simpr (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc)))
      syntaxFormula0196
  have p0778 :=
    @g_jca syntaxFormula0216 (.classMem C (syn_cncs)) syntaxFormula0196 p0776 p0777
  have p0779 := @g_tlecg C syntaxClass0155
  have p0780 :=
    @g_syl syntaxFormula0216 (syn_wa (.classMem C (syn_cncs)) syntaxFormula0196)
      (syn_wb syntaxFormula0215 (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0217)) p0778
      p0779
  have p0785 :=
    @g_eqeltrri (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_chwcards (syn_cvv))
      p0074 p0115
  have p0787 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0116
  have p0788 :=
    @g_biimpri
      (.classMem (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
        (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
      (.classMem (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
        (syn_chwcards (syn_cvv)))
      p0787
  have p0789 := Nominal.mp p0785 p0788
  have p0791 :=
    @g_frectchom0 x (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n) dv_cache_0134 dv_cache_0135
      dv_cache_0136 p0134 p0143 p0144 p0084 p0789 p0120
      hyp_wppstopfixedhitcontrgrowfixdndv_6
  have p0792 :=
    @g_syl syntaxFormula0216 (.classMem (.cv n) (syn_cnnc))
      (.classEq syntaxClass0217 syntaxClass0218) p0767 p0791
  have p0793 :=
    @g_breq2d syntaxFormula0216 syntaxClass0217 syntaxClass0218 (syn_ctc C) (syn_clec)
      p0792
  have p0794 :=
    @g_bitrd syntaxFormula0216 syntaxFormula0215
      (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0217) syntaxFormula0219 p0780 p0793
  have p0795 :=
    @g_anbi12d syntaxFormula0216 (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_ctc (.cv n)) (syn_cnnc)) syntaxFormula0215 syntaxFormula0219 p0773
      p0794
  have p0796 :=
    @g_bitrd syntaxFormula0216 syntaxFormula0007
      (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0215) syntaxFormula0220 p0764
      p0795
  have p0797 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns))
      (.classMem (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
        (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
      syntaxFormula0042 p0084 p0789 p0120
  have p0798 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C))
      (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc (.cv n))
  have p0799 := Nominal.mp p0797 p0798
  have p0800 :=
    @g_a1i (syn_wb syntaxFormula0221 syntaxFormula0220) syntaxFormula0216 p0799
  have p0801 := @g_bicomd syntaxFormula0216 syntaxFormula0221 syntaxFormula0220 p0800
  have p0802 :=
    @g_bitrd syntaxFormula0216 syntaxFormula0007 syntaxFormula0220 syntaxFormula0221 p0796
      p0801
  have p0803 := @g_syl syntaxFormula0214 syntaxFormula0216 syntaxFormula0222 p0760 p0802
  have p0804 := @g_ralimiaa syntaxFormula0196 syntaxFormula0222 n (syn_cnnc) p0803
  have p0805 := Nominal.mp p0720 p0804
  have p0806 :=
    @g_jctir syntaxFormula0001 (.classMem (.cv m) (syn_cnnc)) syntaxFormula0223 p0034
      p0805
  have p0807 := @g_id (.classEq (.cv n) (.cv m))
  have p0808 := @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) syntaxClass0006 p0807
  have p0809 := @g_tceq (.cv n) (.cv m)
  have p0810 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (syn_ctc (.cv n)) (syn_ctc (.cv m))
      syntaxClass0019 p0809
  have p0811 :=
    @g_bibi12d (.classEq (.cv n) (.cv m)) syntaxFormula0007 syntaxFormula0009
      syntaxFormula0221 syntaxFormula0224 p0808 p0810
  have p0812 :=
    @g_rspcva syntaxFormula0222 syntaxFormula0225 n (.cv m) (syn_cnnc) dv_cache_0137
      dv_cache_0060 dv_cache_0138 p0811
  have p0813 :=
    @g_syl syntaxFormula0001 (syn_wa (.classMem (.cv m) (syn_cnnc)) syntaxFormula0223)
      syntaxFormula0225 p0806 p0812
  have p0814 := @g_mpbid syntaxFormula0001 syntaxFormula0009 syntaxFormula0224 p0056 p0813
  have p0815 := @g_nntccl (.cv m)
  have p0816 :=
    @g_syl syntaxFormula0001 (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0034 p0815
  have p0817 :=
    @g_jca syntaxFormula0001 (.classMem (syn_ctc (.cv m)) (syn_cnnc)) syntaxFormula0023
      p0816 p0368
  have p0818 := @g_id (.classEq (.cv n) (syn_ctc (.cv m)))
  have p0819 :=
    @g_eleq1d (.classEq (.cv n) (syn_ctc (.cv m))) (.cv n) (syn_ctc (.cv m))
      syntaxClass0019 p0818
  have p0821 :=
    @g_breq2d (.classEq (.cv n) (syn_ctc (.cv m))) (.cv n) (syn_ctc (.cv m)) (.cv k)
      (syn_ckqrel (syn_clefin)) p0818
  have p0822 :=
    @g_imbi12d (.classEq (.cv n) (syn_ctc (.cv m))) syntaxFormula0020 syntaxFormula0224
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))) p0819 p0821
  have p0823 :=
    @g_rspcva syntaxFormula0021 syntaxFormula0226 n (syn_ctc (.cv m)) (syn_cnnc)
      dv_cache_0139 dv_cache_0060 dv_cache_0140 p0822
  have p0824 :=
    @g_syl syntaxFormula0001
      (syn_wa (.classMem (syn_ctc (.cv m)) (syn_cnnc)) syntaxFormula0023)
      syntaxFormula0226 p0817 p0823
  have p0825 :=
    @g_mpd syntaxFormula0001 syntaxFormula0224
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))) p0814 p0824
  have p0826 := @g_nntcpreim x (.cv k) dv_cache_0141
  have p0827 :=
    @g_syl syntaxFormula0001 (.classMem (.cv k) (syn_cnnc))
      (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) (.cv k))) p0053 p0826
  have p0828 :=
    @g_a1d syntaxFormula0001 syntaxFormula0022
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0058
  have p0829 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))
  have p0830 :=
    @g_eleq1d (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_ctc (.cv x)) (.cv k) syntaxClass0019 p0829
  have p0831 :=
    @g_biimprd
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0227 syntaxFormula0022 p0830
  have p0832 :=
    @g_sylcom syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0022 syntaxFormula0227 p0828 p0831
  have p0833 :=
    @g_simpl (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))
  have p0834 :=
    @g_a1i syntaxFormula0223
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0805
  have p0835 :=
    @g_jca (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (.classMem (.cv x) (syn_cnnc)) syntaxFormula0223 p0833 p0834
  have p0836 := @g_id (.classEq (.cv n) (.cv x))
  have p0837 := @g_eleq1d (.classEq (.cv n) (.cv x)) (.cv n) (.cv x) syntaxClass0006 p0836
  have p0838 := @g_tceq (.cv n) (.cv x)
  have p0839 :=
    @g_eleq1d (.classEq (.cv n) (.cv x)) (syn_ctc (.cv n)) (syn_ctc (.cv x))
      syntaxClass0019 p0838
  have p0840 :=
    @g_bibi12d (.classEq (.cv n) (.cv x)) syntaxFormula0007 syntaxFormula0228
      syntaxFormula0221 syntaxFormula0227 p0837 p0839
  have p0841 :=
    @g_rspcva syntaxFormula0222 syntaxFormula0229 n (.cv x) (syn_cnnc) dv_cache_0142
      dv_cache_0060 dv_cache_0143 p0840
  have p0842 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) syntaxFormula0223) syntaxFormula0229 p0835
      p0841
  have p0843 :=
    @g_biimprd
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0228 syntaxFormula0227 p0842
  have p0844 :=
    @g_sylcom syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0227 syntaxFormula0228 p0832 p0843
  have p0846 :=
    @g_a1d syntaxFormula0001 syntaxFormula0010
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0688
  have p0847 := @g_pm3_2 (.classMem (.cv x) (syn_cnnc)) syntaxFormula0010
  have p0848 :=
    @g_syl9 syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0010 (.classMem (.cv x) (syn_cnnc)) syntaxFormula0230 p0846 p0847
  have p0849 :=
    @g_syl5 (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (.classMem (.cv x) (syn_cnnc)) syntaxFormula0001
      (.imp (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
        syntaxFormula0230)
      p0833 p0848
  have p0850 :=
    @g_pm2_43d syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0230 p0849
  have p0854 :=
    @g_breq2d (.classEq (.cv n) (.cv x)) (.cv n) (.cv x) (.cv m) (syn_ckqrel (syn_clefin))
      p0836
  have p0855 :=
    @g_imbi12d (.classEq (.cv n) (.cv x)) syntaxFormula0007 syntaxFormula0228
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) p0837 p0854
  have p0856 :=
    @g_rspcva syntaxFormula0008
      (.imp syntaxFormula0228 (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))) n
      (.cv x) (syn_cnnc) dv_cache_0142 dv_cache_0060 dv_cache_0144 p0855
  have p0857 :=
    @g_syl6 syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0230
      (.imp syntaxFormula0228 (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))) p0850
      p0856
  have p0858 :=
    @g_mpdd syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      syntaxFormula0228 (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) p0844 p0857
  have p0859 :=
    @g_a1d syntaxFormula0001 (.classMem (.cv m) (syn_cnnc))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0034
  have p0861 := @g_pm3_2 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
  have p0862 :=
    @g_syl5 (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))) p0833 p0861
  have p0863 :=
    @g_syl6 syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (.classMem (.cv m) (syn_cnnc))
      (.imp (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
        (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))))
      p0859 p0862
  have p0864 :=
    @g_pm2_43d syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))) p0863
  have p0865 := @g_kqlefintcb (.cv m) (.cv x)
  have p0866 :=
    @g_syl6 syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)))
      (syn_wb (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))
        (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x))))
      p0864 p0865
  have p0867 :=
    @g_bi1 (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x)))
  have p0868 :=
    @g_syl6 syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_wb (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))
        (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x))))
      (.imp (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))
        (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x))))
      p0866 p0867
  have p0869 :=
    @g_mpdd syntaxFormula0001
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x))) p0858 p0868
  have p0871 :=
    @g_breq2d (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_ctc (.cv x)) (.cv k) (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) p0829
  have p0872 :=
    @g_mpbidi (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x)))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) syntaxFormula0001
      p0869 p0871
  have p0873 :=
    @g_exp3a syntaxFormula0001 (.classMem (.cv x) (syn_cnnc))
      (.classEq (syn_ctc (.cv x)) (.cv k))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) p0872
  have p0874 :=
    @g_rexlimdv syntaxFormula0001 (.classEq (syn_ctc (.cv x)) (.cv k))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) x (syn_cnnc)
      dv_cache_0145 dv_cache_0146 p0873
  have p0875 :=
    @g_mpd syntaxFormula0001 (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) (.cv k)))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) p0827 p0874
  have p0876 :=
    @g_jca syntaxFormula0001 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m)))
      (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) p0825 p0875
  have p0877 :=
    @g_jca syntaxFormula0001 (.classMem (.cv k) (syn_cnnc))
      (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0053 p0816
  have p0878 := @g_kqfinantinn (.cv k) (syn_ctc (.cv m))
  have p0879 :=
    @g_syl syntaxFormula0001
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)))
      (.imp (syn_wa (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m)))
          (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)))
        (.classEq (.cv k) (syn_ctc (.cv m))))
      p0877 p0878
  have p0880 :=
    @g_mpd syntaxFormula0001
      (syn_wa (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m)))
        (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)))
      (.classEq (.cv k) (syn_ctc (.cv m))) p0876 p0879
  have p0881 := @g_eqeq2d syntaxFormula0001 (.cv k) (syn_ctc (.cv m)) (.cv m) p0880
  have p0882 := @g_addceq1d syntaxFormula0001 (.cv k) (syn_ctc (.cv m)) (syn_c1c) p0880
  have p0883 :=
    @g_eqeq2d syntaxFormula0001 (syn_cplc (.cv k) (syn_c1c))
      (syn_cplc (syn_ctc (.cv m)) (syn_c1c)) (.cv m) p0882
  have p0884 :=
    @g_orbi12d syntaxFormula0001 (.classEq (.cv m) (.cv k))
      (.classEq (.cv m) (syn_ctc (.cv m))) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0881 p0883
  have p0885 :=
    @g_mpbid syntaxFormula0001
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      syntaxFormula0231 p0755 p0884
  have p0887 :=
    @g_elwpphitvndv C (syn_cwppstopstep F C)
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv m)
  have p0888 := Nominal.mp p0145 p0887
  have p0889 :=
    @g_sylib syntaxFormula0001 syntaxFormula0009
      (syn_wa (.classMem (.cv m) (syn_cnnc)) syntaxFormula0233) p0056 p0888
  have p0890 := @g_simpr (.classMem (.cv m) (syn_cnnc)) syntaxFormula0233
  have p0891 :=
    @g_syl syntaxFormula0001 (syn_wa (.classMem (.cv m) (syn_cnnc)) syntaxFormula0233)
      syntaxFormula0233 p0889 p0890
  have p0899 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
      (.cv x)
  have p0900 :=
    @g_mpan syntaxFormula0057 (.classMem (.cv x) (syn_cnnc)) syntaxFormula0235 p0145 p0899
  have p0902 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) syntaxClass0234
      p0140
  have p0903 :=
    @g_biimpi syntaxFormula0235 (.classMem syntaxClass0234 (syn_chwcards (syn_cvv))) p0902
  have p0904 :=
    @g_syl (.classMem (.cv x) (syn_cnnc)) syntaxFormula0235
      (.classMem syntaxClass0234 (syn_chwcards (syn_cvv))) p0900 p0903
  have p0905 := @g_simpr (.classMem (.cv x) (syn_cnnc)) syntaxFormula0236
  have p0906 := @g_breq2d syntaxFormula0237 (.cv y) syntaxClass0234 C (syn_clec) p0905
  have p0909 := @g_tceq (.cv y) syntaxClass0234
  have p0910 :=
    @g_syl syntaxFormula0237 syntaxFormula0236
      (.classEq (syn_ctc (.cv y)) syntaxClass0238) p0905 p0909
  have p0911 :=
    @g_neeq12d syntaxFormula0237 (.cv y) syntaxClass0234 (syn_ctc (.cv y)) syntaxClass0238
      p0905 p0910
  have p0912 :=
    @g_imbi12d syntaxFormula0237 (syn_wbr C (syn_clec) (.cv y)) syntaxFormula0239
      (syn_wne (.cv y) (syn_ctc (.cv y))) syntaxFormula0240 p0906 p0911
  have p0913 :=
    @g_rspcdv (.classMem (.cv x) (syn_cnnc))
      (.imp (syn_wbr C (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y))))
      syntaxFormula0241 y syntaxClass0234 (syn_chwcards (syn_cvv)) dv_cache_0147
      dv_cache_0073 dv_cache_0148 dv_cache_0149 p0904 p0912
  have p0914 :=
    @g_mpi (.classMem (.cv x) (syn_cnnc))
      (syn_wral y (syn_chwcards (syn_cvv))
        (.imp (syn_wbr C (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y)))))
      syntaxFormula0241 hyp_wppstopfixedhitcontrgrowfixdndv_9 p0913
  have p0915 := @g_rgen syntaxFormula0241 x (syn_cnnc) p0914
  have p0916 := @g_id (.classEq (.cv x) (.cv m))
  have p0917 := @g_fveq2d (.classEq (.cv x) (.cv m)) (.cv x) (.cv m) syntaxClass0051 p0916
  have p0918 :=
    @g_breq2d (.classEq (.cv x) (.cv m)) syntaxClass0234 syntaxClass0232 C (syn_clec)
      p0917
  have p0923 := @g_tceq syntaxClass0234 syntaxClass0232
  have p0924 :=
    @g_syl (.classEq (.cv x) (.cv m)) (.classEq syntaxClass0234 syntaxClass0232)
      (.classEq syntaxClass0238 syntaxClass0242) p0917 p0923
  have p0925 :=
    @g_neeq12d (.classEq (.cv x) (.cv m)) syntaxClass0234 syntaxClass0232 syntaxClass0238
      syntaxClass0242 p0917 p0924
  have p0926 :=
    @g_imbi12d (.classEq (.cv x) (.cv m)) syntaxFormula0239 syntaxFormula0233
      syntaxFormula0240 syntaxFormula0243 p0918 p0925
  have p0927 :=
    @g_rspcv syntaxFormula0241 syntaxFormula0244 x (.cv m) (syn_cnnc) dv_cache_0150
      dv_cache_0029 dv_cache_0151 p0926
  have p0928 :=
    @g_mpi (.classMem (.cv m) (syn_cnnc)) (syn_wral x (syn_cnnc) syntaxFormula0241)
      syntaxFormula0244 p0915 p0927
  have p0929 :=
    @g_syl syntaxFormula0001 (.classMem (.cv m) (syn_cnnc)) syntaxFormula0244 p0034 p0928
  have p0930 := @g_mpd syntaxFormula0001 syntaxFormula0233 syntaxFormula0243 p0891 p0929
  have p0931 := (Nominal.biimpRefl syntaxFormula0243)
  have p0932 := @g_sylib syntaxFormula0001 syntaxFormula0243 syntaxFormula0246 p0930 p0931
  have p0933 :=
    @g_frectchom0 x (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C))
      (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv m) dv_cache_0134 dv_cache_0135
      dv_cache_0136 p0134 p0143 p0144 p0084 p0789 p0120
      hyp_wppstopfixedhitcontrgrowfixdndv_6
  have p0934 :=
    @g_syl syntaxFormula0001 (.classMem (.cv m) (syn_cnnc))
      (.classEq syntaxClass0242 (syn_cfv syntaxClass0029 (syn_ctc (.cv m)))) p0034 p0933
  have p0935 := @g_eqcomd syntaxFormula0001 (.cv k) (syn_ctc (.cv m)) p0880
  have p0936 :=
    @g_fveq2d syntaxFormula0001 (syn_ctc (.cv m)) (.cv k) syntaxClass0029 p0935
  have p0937 :=
    @g_eqtrd syntaxFormula0001 syntaxClass0242 (syn_cfv syntaxClass0029 (syn_ctc (.cv m)))
      syntaxClass0187 p0934 p0936
  have p0938 :=
    @g_eqtrd syntaxFormula0001 syntaxClass0242 syntaxClass0187 syntaxClass0159 p0937 p0683
  have p0939 :=
    @g_a1d syntaxFormula0001 syntaxFormula0247 (.classEq (.cv m) (.cv k)) p0938
  have p0940 := @g_id (.classEq (.cv m) (.cv k))
  have p0941 := @g_eqcomd (.classEq (.cv m) (.cv k)) (.cv m) (.cv k) p0940
  have p0942 := @g_fveq2d (.classEq (.cv m) (.cv k)) (.cv k) (.cv m) syntaxClass0051 p0941
  have p0943 :=
    @g_eqeq2d (.classEq (.cv m) (.cv k)) syntaxClass0159 syntaxClass0232 syntaxClass0242
      p0942
  have p0944 :=
    @g_mpbidi (.classEq (.cv m) (.cv k)) syntaxFormula0247 syntaxFormula0248
      syntaxFormula0001 p0939 p0943
  have p0945 := @g_eqcom syntaxClass0242 syntaxClass0232
  have p0946 :=
    @g_syl6ib syntaxFormula0001 (.classEq (.cv m) (.cv k)) syntaxFormula0248
      syntaxFormula0245 p0944 p0945
  have p0947 := @g_necon3bd syntaxFormula0001 syntaxFormula0245 (.cv m) (.cv k) p0946
  have p0948 :=
    @g_mpd syntaxFormula0001 syntaxFormula0246 (syn_wne (.cv m) (.cv k)) p0932 p0947
  have p0949 := @g_neeq2d syntaxFormula0001 (.cv k) (syn_ctc (.cv m)) (.cv m) p0880
  have p0950 :=
    @g_mpbid syntaxFormula0001 (syn_wne (.cv m) (.cv k))
      (syn_wne (.cv m) (syn_ctc (.cv m))) p0948 p0949
  have p0951 := (Nominal.biimpRefl (syn_wne (.cv m) (syn_ctc (.cv m))))
  have p0952 :=
    @g_sylib syntaxFormula0001 (syn_wne (.cv m) (syn_ctc (.cv m)))
      (.neg (.classEq (.cv m) (syn_ctc (.cv m)))) p0950 p0951
  have p0953 := @g_nchoicelem1 (.cv m)
  have p0954 :=
    @g_syl syntaxFormula0001 (.classMem (.cv m) (syn_cnnc))
      (.neg (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))) p0034 p0953
  have p0955 :=
    @g_jca syntaxFormula0001 (.neg (.classEq (.cv m) (syn_ctc (.cv m))))
      (.neg (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))) p0952 p0954
  have p0956 :=
    @g_pm4_56 (.classEq (.cv m) (syn_ctc (.cv m)))
      (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
  have p0957 :=
    @g_sylib syntaxFormula0001
      (syn_wa (.neg (.classEq (.cv m) (syn_ctc (.cv m))))
        (.neg (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))))
      (.neg syntaxFormula0231) p0955 p0956
  have p0958 :=
    @g_pm2_21dd syntaxFormula0001 syntaxFormula0231 (.neg (.classEq (.cv m) (.cv m)))
      p0885 p0957
  have p0959 :=
    @g_a1d syntaxFormula0001 (.neg (.classEq (.cv m) (.cv m)))
      (.classEq (syn_c0c) (syn_c0c)) p0958
  have p0960 :=
    @g_mt2d syntaxFormula0001 (.classEq (syn_c0c) (syn_c0c)) (.classEq (.cv m) (.cv m))
      p0017 p0959
  have p0961 :=
    @g_syl6 (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)) syntaxFormula0001
      (.neg (.classEq (syn_c0c) (syn_c0c))) p0015 p0960
  exact p0961


end NFChoice.DirectNominalPrf.WPPReplay
