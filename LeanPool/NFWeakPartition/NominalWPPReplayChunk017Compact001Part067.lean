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

/-- Checked nominal proof certificate identified upstream as
`g_wppstopfixedhitcontrgrowfixdndv`.
-/
@[expose]
noncomputable def gWppstopfixedhitcontrgrowfixdndv (ph : Wff) (ps : Wff) (ch : Wff)
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
    (hyp_wppstopfixedhitcontrgrowfixdndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopfixedhitcontrgrowfixdndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_3 :
      Nominal.NPrf (.classMem C (synChwcards (synCvv))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_4 : Nominal.NPrf (synWbr (synCtc C) (synClec) C))
    (hyp_wppstopfixedhitcontrgrowfixdndv_5 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_6 : Nominal.NPrf
        (synWral x (synCdm (synCwppstopstep F C))
          (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
            (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_7 :
      Nominal.NPrf (.classMem I (synChwcards (synCvv))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_9 : Nominal.NPrf (synWral y (synChwcards (synCvv))
          (.imp (synWbr C (synClec) (.cv y)) (synWne (.cv y) (synCtc (.cv y))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_10 : Nominal.NPrf (.imp ph
          (synWa (.classMem (.cv m) (synCnnc))
            (synWa (.classMem (.cv m) (synCwpphit (synCwppstopstep F C) I C))
              (synWral n (synCnnc)
                (.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F C) I C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_11 : Nominal.NPrf (.imp ps
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C)) (synCtc I) (synCtc C)))
              (synWral n (synCnnc) (.imp (.classMem (.cv n)
                    (synCwpphit (synCwppstopstep F (synCtc C)) (synCtc I) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))))))
    (hyp_wppstopfixedhitcontrgrowfixdndv_12 : Nominal.NPrf (.imp ch
          (synWral y (synCdm (synCwppstopstep F C))
            (.imp (synWbr (synCtc C) (synClec) (.cv y))
              (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))) :
    Nominal.NPrf
      (.imp (.classEq I (synCtc I))
        (.imp (synWa ph (synWa ps ch)) (.neg (.classEq (synC0c) (synC0c))))) :=
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
  have dv_cache_0001 : n ∉ ((synWa (.classEq I (synCtc I)) ph)).fv := by
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
  have dv_cache_0002 : n ∉ ((synWa (.classEq I (synCtc I)) ps)).fv :=
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
  have dv_cache_0003 : d ∉ ((synC0)).fv :=
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
  have dv_cache_0004 : s ∉ ((synC0)).fv :=
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
    d ∉ ((synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))).fv :=
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
    s ∉ ((synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))).fv :=
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
      ((synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synCwe) (synC0)) (.classEq (synC0c) (synCnc (synC0))))).fv :=
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
      ((synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synCwe) (synC0)) (.classEq (synC0c) (synCnc (synC0))))).fv :=
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
  have dv_cache_0010 : s ∉ ((Wff.classEq (.cv k) (synC0c))).fv :=
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
  have dv_cache_0011 : d ∉ ((Wff.classEq (.cv k) (synC0c))).fv :=
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
  have dv_cache_0014 : k ∉ ((synC0c)).fv :=
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
      ((synWb (.classMem (synC0c) (synChwcards (synCvv))) (synWex d (synWex s
              (synWa (synWbr (.cv s) (synCwe) (.cv d))
                (.classEq (synC0c) (synCnc (.cv d)))))))).fv :=
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
      ((synCwppfrecprefixeq (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
          (synCif (.classEq I (synCtc I)) I (synC0c)) k)).fv :=
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
  have dv_cache_0017 : x ∉ ((synC0c)).fv :=
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
      ((Wff.classMem (synC0c)
          (synCwppfrecprefixeq (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
            (synCif (.classEq I (synCtc I)) I (synC0c)) k))).fv :=
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
          (synCwppfrecprefixeq (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
            (synCif (.classEq I (synCtc I)) I (synC0c)) k))).fv :=
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
  have dv_cache_0021 : z ∉ ((Wff.classEq (.cv r) (synCkqrel (synClefin)))).fv :=
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
  have dv_cache_0022 : x ∉ ((Wff.classEq (.cv r) (synCkqrel (synClefin)))).fv :=
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
  have dv_cache_0023 : a ∉ ((Wff.classEq (.cv r) (synCkqrel (synClefin)))).fv :=
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
  have dv_cache_0025 : z ∉ ((synCnnc)).fv :=
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
  have dv_cache_0027 : a ∉ ((synCnnc)).fv :=
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
  have dv_cache_0029 : x ∉ ((synCnnc)).fv :=
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
  have dv_cache_0040 : r ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0041 : b ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0042 : r ∉ ((synCnnc)).fv :=
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
  have dv_cache_0043 : b ∉ ((synCnnc)).fv :=
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
      ((synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
                (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                  (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
                (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))).fv :=
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
      ((synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
                (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                  (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
                (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))).fv :=
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
  have dv_cache_0049 : a ∉ ((synCplc (.cv y) (synC1c))).fv :=
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
  have dv_cache_0050 : z ∉ ((synCplc (.cv y) (synC1c))).fv :=
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
      ((Wff.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
            (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))).fv :=
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
      ((Wff.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))).fv :=
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
      ((Wff.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))).fv :=
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
  have dv_cache_0055 : x ∉ ((synCplc (.cv y) (synC1c))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
            (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))).fv :=
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
  have dv_cache_0060 : n ∉ ((synCnnc)).fv :=
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
  have dv_cache_0061 : q ∉ ((synCnnc)).fv :=
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
      ((Wff.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))).fv :=
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
      ((Wff.imp (.classMem (.cv q) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCif (.classEq I (synCtc I)) I (synC0c)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))).fv :=
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
  have dv_cache_0066 : q ∉ ((synCwppstopstep F (synCtc C))).fv :=
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
  have dv_cache_0067 : q ∉ ((synCif (.classEq I (synCtc I)) I (synC0c))).fv :=
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
      ((Wff.imp (.neg (synWbr (synCtc C) (synClec) (synCfv
                (synCfrec (synCwppstopstep F (synCtc C))
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv y)))) (synWbr (synCfv
              (synCfrec (synCwppstopstep F (synCtc C))
                (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv y))
            (synClec) (synCtc C)))).fv :=
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
      ((synCfv (synCfrec (synCwppstopstep F (synCtc C))
            (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv q))).fv :=
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
  have dv_cache_0073 : y ∉ ((synChwcards (synCvv))).fv :=
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
      ((Wff.imp (synWbr (synCfv (synCfrec (synCwppstopstep F (synCtc C))
                (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv q)) (synClec) (synCtc C))
          (.classEq (synCfv (synCwppstopstep F C) (synCfv
                (synCfrec (synCwppstopstep F (synCtc C))
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv q)))
            (synCfv (synCwppstopstep F (synCtc C)) (synCfv
                (synCfrec (synCwppstopstep F (synCtc C))
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv q)))))).fv :=
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
      ((Wff.imp (synWbr (synCfv (synCfrec (synCwppstopstep F (synCtc C))
                (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv y)) (synClec) (synCtc C))
          (.classEq (synCfv (synCwppstopstep F C) (synCfv
                (synCfrec (synCwppstopstep F (synCtc C))
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv y)))
            (synCfv (synCwppstopstep F (synCtc C)) (synCfv
                (synCfrec (synCwppstopstep F (synCtc C))
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv y)))))).fv :=
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
      ((Wff.classMem (synCplc (.cv y) (synC1c))
          (synCwppfrecprefixeq (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
            (synCif (.classEq I (synCtc I)) I (synC0c)) k))).fv :=
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
      ((synWa (synWa (.classEq I (synCtc I)) ph) (synWa (synWa (.classEq I (synCtc I)) ps)
            (synWa (.classEq I (synCtc I)) ch)))).fv :=
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
  have dv_cache_0078 : y ∉ (synWtru).fv :=
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
            (synCwppfrecprefixeq (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
              (synCif (.classEq I (synCtc I)) I (synC0c)) k)))).fv :=
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
          (synCwppfrecprefixeq (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
            (synCif (.classEq I (synCtc I)) I (synC0c)) k))).fv :=
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
      ((synWa (synWa (.classEq I (synCtc I)) ph) (synWa (synWa (.classEq I (synCtc I)) ps)
            (synWa (.classEq I (synCtc I)) ch)))).fv :=
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
      ((Wff.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k)) (.classEq (synCfv
              (synCfrec (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c)))
              (.cv k)) (synCfv (synCfrec (synCwppstopstep F (synCtc C))
                (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv k))))).fv :=
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
  have dv_cache_0085 : y ∉ ((Wff.classEq (.cv r) (synCkqrel (synClefin)))).fv :=
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
  have dv_cache_0087 : y ∉ ((synCnnc)).fv :=
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
  have dv_cache_0094 : a ∉ ((synCkqrel (synClefin))).fv :=
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
      ((synWral x (synCnnc) (synWral y (synCnnc)
            (synWo (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
              (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))))).fv :=
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
      ((synWral x (synCnnc) (synWral y (synCnnc)
            (synWo (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
              (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))))).fv :=
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
      ((synWo (synWbr (.cv n) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv n)))).fv :=
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
      ((synWo (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))).fv :=
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
      ((Wff.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCif (.classEq I (synCtc I)) I (synC0c)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))).fv :=
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
      ((Wff.classMem (synCfv (synCfrec (synCwppstopstep F C)
              (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv n)) (synCncs))).fv :=
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
      ((Wff.classMem (synCfv (synCfrec (synCwppstopstep F C)
              (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv q)) (synCncs))).fv :=
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
      ((synCfv (synCfrec (synCwppstopstep F C)
            (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv r))).fv :=
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
  have dv_cache_0106 : y ∉ ((synCdm (synCwppstopstep F C))).fv :=
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
      ((Wff.imp (synWbr (synCtc C) (synClec) (synCfv (synCfrec (synCwppstopstep F C)
                (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv r))) (synWbr C (synClec)
            (synCfv (synCwppstopstep F C) (synCfv (synCfrec (synCwppstopstep F C)
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv r)))))).fv :=
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
  have dv_cache_0108 : y ∉ ((Wff.classMem (.cv r) (synCnnc))).fv :=
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
      ((synWa (synWa (.classEq I (synCtc I)) ph) (synWa (synWa (.classEq I (synCtc I)) ps)
            (synWa (.classEq I (synCtc I)) ch)))).fv :=
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
  have dv_cache_0110 : k ∉ ((synCwppstopstep F C)).fv :=
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
  have dv_cache_0111 : m ∉ ((synCwppstopstep F C)).fv :=
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
  have dv_cache_0112 : n ∉ ((synCwppstopstep F C)).fv :=
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
  have dv_cache_0113 : q ∉ ((synCwppstopstep F C)).fv :=
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
  have dv_cache_0114 : r ∉ ((synCwppstopstep F C)).fv :=
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
  have dv_cache_0120 : k ∉ ((synCif (.classEq I (synCtc I)) I (synC0c))).fv :=
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
  have dv_cache_0121 : m ∉ ((synCif (.classEq I (synCtc I)) I (synC0c))).fv :=
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
  have dv_cache_0122 : n ∉ ((synCif (.classEq I (synCtc I)) I (synC0c))).fv :=
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
  have dv_cache_0123 : r ∉ ((synCif (.classEq I (synCtc I)) I (synC0c))).fv :=
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
  have dv_cache_0124 : k ∉ ((synCtc C)).fv :=
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
  have dv_cache_0125 : m ∉ ((synCtc C)).fv :=
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
  have dv_cache_0126 : n ∉ ((synCtc C)).fv :=
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
  have dv_cache_0127 : q ∉ ((synCtc C)).fv :=
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
  have dv_cache_0128 : r ∉ ((synCtc C)).fv :=
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
  have dv_cache_0134 : x ∉ ((synCwppstopstep F C)).fv :=
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
  have dv_cache_0135 : x ∉ ((synCwppstopstep F (synCtc C))).fv :=
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
  have dv_cache_0136 : x ∉ ((synCif (.classEq I (synCtc I)) I (synC0c))).fv :=
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
      ((synWb (.classMem (.cv m) (synCwpphit (synCwppstopstep F C)
              (synCif (.classEq I (synCtc I)) I (synC0c)) C)) (.classMem (synCtc (.cv m))
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc C))))).fv :=
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
  have dv_cache_0139 : n ∉ ((synCtc (.cv m))).fv :=
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
      ((Wff.imp (.classMem (synCtc (.cv m)) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (synCtc (.cv m))))).fv :=
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
      ((synWb (.classMem (.cv x) (synCwpphit (synCwppstopstep F C)
              (synCif (.classEq I (synCtc I)) I (synC0c)) C)) (.classMem (synCtc (.cv x))
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc C))))).fv :=
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
      ((Wff.imp (.classMem (.cv x) (synCwpphit (synCwppstopstep F C)
              (synCif (.classEq I (synCtc I)) I (synC0c)) C))
          (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x)))).fv :=
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
    x ∉ ((synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k))).fv :=
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
      ((synWa (synWa (.classEq I (synCtc I)) ph) (synWa (synWa (.classEq I (synCtc I)) ps)
            (synWa (.classEq I (synCtc I)) ch)))).fv :=
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
      ((synCfv (synCfrec (synCwppstopstep F C)
            (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv x))).fv :=
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
      ((Wff.imp (synWbr C (synClec) (synCfv (synCfrec (synCwppstopstep F C)
                (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv x))) (synWne (synCfv
              (synCfrec (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c)))
              (.cv x)) (synCtc (synCfv (synCfrec (synCwppstopstep F C)
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv x)))))).fv :=
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
  have dv_cache_0149 : y ∉ ((Wff.classMem (.cv x) (synCnnc))).fv :=
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
      ((Wff.imp (synWbr C (synClec) (synCfv (synCfrec (synCwppstopstep F C)
                (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv m))) (synWne (synCfv
              (synCfrec (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c)))
              (.cv m)) (synCtc (synCfv (synCfrec (synCwppstopstep F C)
                  (synCif (.classEq I (synCtc I)) I (synC0c))) (.cv m)))))).fv :=
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
    (synWa (synWa (.classEq I (synCtc I)) ps) (synWa (.classEq I (synCtc I)) ch))
  let syntaxFormula0001 : Wff :=
    (synWa (synWa (.classEq I (synCtc I)) ph) syntaxFormula0000)
  let syntaxFormula0002 : Wff :=
    (.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F C) I C))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))
  let syntaxFormula0003 : Wff := (synWral n (synCnnc) syntaxFormula0002)
  let syntaxFormula0004 : Wff :=
    (synWa (.classMem (.cv m) (synCwpphit (synCwppstopstep F C) I C)) syntaxFormula0003)
  let syntaxFormula0005 : Wff := (synWa (.classMem (.cv m) (synCnnc)) syntaxFormula0004)
  let syntaxClass0006 : Class :=
    (synCwpphit (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c)) C)
  let syntaxFormula0007 : Wff := (.classMem (.cv n) syntaxClass0006)
  let syntaxFormula0008 : Wff :=
    (.imp syntaxFormula0007 (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))
  let syntaxFormula0009 : Wff := (.classMem (.cv m) syntaxClass0006)
  let syntaxFormula0010 : Wff := (synWral n (synCnnc) syntaxFormula0008)
  let syntaxFormula0011 : Wff := (synWa syntaxFormula0009 syntaxFormula0010)
  let syntaxFormula0012 : Wff := (synWa (.classMem (.cv m) (synCnnc)) syntaxFormula0011)
  let syntaxFormula0013 : Wff :=
    (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C)) (synCtc I) (synCtc C)))
  let syntaxFormula0014 : Wff :=
    (.classMem (.cv n) (synCwpphit (synCwppstopstep F (synCtc C)) (synCtc I) (synCtc C)))
  let syntaxFormula0015 : Wff :=
    (.imp syntaxFormula0014 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
  let syntaxFormula0016 : Wff := (synWral n (synCnnc) syntaxFormula0015)
  let syntaxFormula0017 : Wff := (synWa syntaxFormula0013 syntaxFormula0016)
  let syntaxFormula0018 : Wff := (synWa (.classMem (.cv k) (synCnnc)) syntaxFormula0017)
  let syntaxClass0019 : Class :=
    (synCwpphit (synCwppstopstep F (synCtc C))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc C))
  let syntaxFormula0020 : Wff := (.classMem (.cv n) syntaxClass0019)
  let syntaxFormula0021 : Wff :=
    (.imp syntaxFormula0020 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
  let syntaxFormula0022 : Wff := (.classMem (.cv k) syntaxClass0019)
  let syntaxFormula0023 : Wff := (synWral n (synCnnc) syntaxFormula0021)
  let syntaxFormula0024 : Wff := (synWa syntaxFormula0022 syntaxFormula0023)
  let syntaxFormula0025 : Wff := (synWa (.classMem (.cv k) (synCnnc)) syntaxFormula0024)
  let syntaxClass0026 : Class :=
    (synCwpphit (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (synCtc C))
  let syntaxFormula0027 : Wff :=
    (.classEq (synCif (.classEq I (synCtc I)) I (synC0c))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))))
  let syntaxClass0028 : Class :=
    (synCfrec (synCwppstopstep F (synCtc C)) (synCif (.classEq I (synCtc I)) I (synC0c)))
  let syntaxClass0029 : Class :=
    (synCfrec (synCwppstopstep F (synCtc C))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))))
  let syntaxClass0030 : Class := (synCcnv syntaxClass0028)
  let syntaxClass0031 : Class := (synCcnv syntaxClass0029)
  let syntaxClass0032 : Class :=
    (synCima syntaxClass0031 (synCima (synClec) (synCsn (synCtc C))))
  let syntaxFormula0033 : Wff :=
    (.classEq (.cv s) (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
  let syntaxFormula0034 : Wff := (synWa (.classEq (.cv d) (synC0)) syntaxFormula0033)
  let syntaxFormula0035 : Wff :=
    (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (synC0c) (synCnc (.cv d))))
  let syntaxFormula0036 : Wff :=
    (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
  let syntaxFormula0037 : Wff := (synWex s syntaxFormula0036)
  let syntaxFormula0038 : Wff := (synWex s syntaxFormula0035)
  let syntaxFormula0039 : Wff := (synWex d syntaxFormula0038)
  let syntaxFormula0040 : Wff :=
    (.classMem (synCif (.classEq I (synCtc I)) I (synC0c))
      (synCdm (synCwppstopstep F (synCtc C))))
  let syntaxFormula0041 : Wff :=
    (.classMem (synCif (.classEq I (synCtc I)) I (synC0c)) (synChwcards (synCvv)))
  let syntaxFormula0042 : Wff :=
    (synWss (synCrn (synCwppstopstep F (synCtc C)))
      (synCdm (synCwppstopstep F (synCtc C))))
  let syntaxClass0043 : Class := (synCfv syntaxClass0028 (.cv k))
  let syntaxFormula0044 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0043)
  let syntaxClass0045 : Class :=
    (synCwppfrecprefixeq (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) k)
  let syntaxFormula0046 : Wff := (.classMem (.cv x) syntaxClass0045)
  let syntaxClass0047 : Class := (.cab x syntaxFormula0046)
  let syntaxFormula0048 : Wff := (.classMem syntaxClass0047 (synCvv))
  let syntaxFormula0049 : Wff :=
    (.classMem (synCif (.classEq I (synCtc I)) I (synC0c)) (synCdm (synCwppstopstep F C)))
  let syntaxClass0050 : Class := (synCfv syntaxClass0028 (synC0c))
  let syntaxClass0051 : Class :=
    (synCfrec (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c)))
  let syntaxClass0052 : Class := (synCfv syntaxClass0051 (synC0c))
  let syntaxFormula0053 : Wff := (.classEq syntaxClass0052 syntaxClass0050)
  let syntaxFormula0054 : Wff := (.classMem (synC0c) syntaxClass0045)
  let syntaxFormula0055 : Wff := (.classMem (synC0c) syntaxClass0047)
  let syntaxFormula0056 : Wff := (.classMem (.cv y) syntaxClass0045)
  let syntaxFormula0057 : Wff :=
    (synW3a (.classMem (synCwppstopstep F C) (synCfuns)) syntaxFormula0049
      (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C))))
  let syntaxFormula0058 : Wff :=
    (synW3a (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
  let syntaxClass0059 : Class := (synCfv syntaxClass0051 (synCplc (.cv y) (synC1c)))
  let syntaxClass0060 : Class := (synCfv syntaxClass0051 (.cv y))
  let syntaxClass0061 : Class := (synCfv (synCwppstopstep F C) syntaxClass0060)
  let syntaxFormula0062 : Wff := (.classEq syntaxClass0059 syntaxClass0061)
  let syntaxFormula0063 : Wff :=
    (synWo (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y))
      (.classEq (.cv y) (synCplc (.cv y) (synC1c))))
  let syntaxFormula0064 : Wff :=
    (synWa (.classMem (.cv y) (synCnnc))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
  let syntaxFormula0065 : Wff :=
    (synW3a (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCantisym) (synCnnc)))
  let syntaxFormula0066 : Wff :=
    (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
  let syntaxFormula0067 : Wff :=
    (.imp (synWa (synWbr (.cv x) (.cv r) (.cv a)) (synWbr (.cv a) (.cv r) (.cv z)))
      (synWbr (.cv x) (.cv r) (.cv z)))
  let syntaxFormula0068 : Wff :=
    (.imp syntaxFormula0066 (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))
  let syntaxFormula0069 : Wff := (synWral z (.cv b) syntaxFormula0067)
  let syntaxFormula0070 : Wff := (synWral z (.cv b) syntaxFormula0068)
  let syntaxFormula0071 : Wff := (synWral z (synCnnc) syntaxFormula0068)
  let syntaxFormula0072 : Wff := (synWral a (.cv b) syntaxFormula0070)
  let syntaxFormula0073 : Wff := (synWral a (synCnnc) syntaxFormula0071)
  let syntaxFormula0074 : Wff :=
    (synWral x (.cv b) (synWral a (.cv b) syntaxFormula0069))
  let syntaxFormula0075 : Wff := (synWral x (.cv b) syntaxFormula0072)
  let syntaxFormula0076 : Wff := (synWral x (synCnnc) syntaxFormula0073)
  let syntaxFormula0077 : Wff :=
    (synWb (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc)) syntaxFormula0076)
  let syntaxFormula0078 : Wff :=
    (synWa (.classMem (.cv y) (synCnnc)) (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)))
  let syntaxFormula0079 : Wff := (synWa syntaxFormula0078 (.classMem (.cv k) (synCnnc)))
  let syntaxFormula0080 : Wff :=
    (synW3a (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) (.classMem (.cv k) (synCnnc)))
  let syntaxFormula0081 : Wff :=
    (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
  let syntaxFormula0082 : Wff :=
    (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
  let syntaxFormula0083 : Wff :=
    (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
  let syntaxFormula0084 : Wff :=
    (.imp syntaxFormula0083 (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
  let syntaxFormula0085 : Wff := (synWa (.classMem (.cv y) (synCnnc)) syntaxFormula0056)
  let syntaxFormula0086 : Wff :=
    (synWa syntaxFormula0085 (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
  let syntaxFormula0087 : Wff :=
    (synW3a (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
  let syntaxClass0088 : Class := (synCfv syntaxClass0028 (.cv y))
  let syntaxFormula0089 : Wff := (.classEq syntaxClass0060 syntaxClass0088)
  let syntaxClass0090 : Class := (synCfv (synCwppstopstep F C) syntaxClass0088)
  let syntaxFormula0091 : Wff := (.classEq syntaxClass0061 syntaxClass0090)
  let syntaxFormula0092 : Wff := (.classEq syntaxClass0059 syntaxClass0090)
  let syntaxFormula0093 : Wff := (synWb syntaxFormula0062 syntaxFormula0092)
  let syntaxFormula0094 : Wff :=
    (synWa syntaxFormula0064 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
  let syntaxFormula0095 : Wff :=
    (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) (.classMem (.cv k) (synCnnc)))
  let syntaxFormula0096 : Wff := (synWa syntaxFormula0095 (.classMem (.cv y) (synCnnc)))
  let syntaxFormula0097 : Wff :=
    (synW3a (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (.classMem (.cv k) (synCnnc)) (.classMem (.cv y) (synCnnc)))
  let syntaxFormula0098 : Wff :=
    (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
  let syntaxFormula0099 : Wff :=
    (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
  let syntaxFormula0100 : Wff :=
    (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
  let syntaxFormula0101 : Wff :=
    (.imp syntaxFormula0100
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
  let syntaxFormula0102 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0088)
  let syntaxFormula0103 : Wff := (.classMem (.cv y) syntaxClass0026)
  let syntaxFormula0104 : Wff := (synWa (.classMem (.cv y) (synCnnc)) syntaxFormula0102)
  let syntaxFormula0105 : Wff := (.classMem (.cv q) syntaxClass0019)
  let syntaxFormula0106 : Wff :=
    (.imp syntaxFormula0105 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))
  let syntaxFormula0107 : Wff := (synWral q (synCnnc) syntaxFormula0106)
  let syntaxFormula0108 : Wff := (.classMem (.cv q) syntaxClass0026)
  let syntaxFormula0109 : Wff :=
    (.imp syntaxFormula0108 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))
  let syntaxFormula0110 : Wff := (synWral q (synCnnc) syntaxFormula0109)
  let syntaxFormula0111 : Wff :=
    (.imp syntaxFormula0103 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
  let syntaxFormula0112 : Wff := (.imp syntaxFormula0102 syntaxFormula0103)
  let syntaxFormula0113 : Wff :=
    (.imp syntaxFormula0102 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
  let syntaxFormula0114 : Wff := (.neg syntaxFormula0102)
  let syntaxFormula0115 : Wff := (.neg syntaxFormula0114)
  let syntaxClass0116 : Class := (synCfv syntaxClass0028 (.cv q))
  let syntaxFormula0117 : Wff := (.classMem syntaxClass0116 (synChwcards (synCvv)))
  let syntaxFormula0118 : Wff := (synWa (.classMem (.cv q) (synCnnc)) syntaxFormula0117)
  let syntaxFormula0119 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0116)
  let syntaxFormula0120 : Wff := (synWbr syntaxClass0116 (synClec) (synCtc C))
  let syntaxFormula0121 : Wff := (synWo syntaxFormula0119 syntaxFormula0120)
  let syntaxFormula0122 : Wff := (.neg syntaxFormula0119)
  let syntaxFormula0123 : Wff := (.imp syntaxFormula0122 syntaxFormula0120)
  let syntaxFormula0124 : Wff := (synWbr syntaxClass0088 (synClec) (synCtc C))
  let syntaxFormula0125 : Wff := (.imp syntaxFormula0114 syntaxFormula0124)
  let syntaxFormula0126 : Wff :=
    (synW3a (.classMem (synCwppstopstep F (synCtc C)) (synCfuns)) syntaxFormula0040
      syntaxFormula0042)
  let syntaxFormula0127 : Wff :=
    (.classMem syntaxClass0116 (synCdm (synCwppstopstep F (synCtc C))))
  let syntaxFormula0128 : Wff :=
    (.classEq (synCfv (synCwppstopstep F C) (.cv y))
      (synCfv (synCwppstopstep F (synCtc C)) (.cv y)))
  let syntaxFormula0129 : Wff :=
    (.imp (synWbr (.cv y) (synClec) (synCtc C)) syntaxFormula0128)
  let syntaxFormula0130 : Wff := (.classEq (.cv y) syntaxClass0116)
  let syntaxClass0131 : Class := (synCfv (synCwppstopstep F C) syntaxClass0116)
  let syntaxClass0132 : Class :=
    (synCfv (synCwppstopstep F (synCtc C)) syntaxClass0116)
  let syntaxFormula0133 : Wff := (.classEq syntaxClass0131 syntaxClass0132)
  let syntaxFormula0134 : Wff := (.imp syntaxFormula0120 syntaxFormula0133)
  let syntaxClass0135 : Class :=
    (synCfv (synCwppstopstep F (synCtc C)) syntaxClass0088)
  let syntaxFormula0136 : Wff := (.classEq syntaxClass0090 syntaxClass0135)
  let syntaxFormula0137 : Wff := (.imp syntaxFormula0124 syntaxFormula0136)
  let syntaxFormula0138 : Wff := (.classEq syntaxClass0059 syntaxClass0135)
  let syntaxFormula0139 : Wff := (synWb syntaxFormula0092 syntaxFormula0138)
  let syntaxClass0140 : Class := (synCfv syntaxClass0028 (synCplc (.cv y) (synC1c)))
  let syntaxFormula0141 : Wff := (.classEq syntaxClass0059 syntaxClass0140)
  let syntaxFormula0142 : Wff := (.classMem (synCplc (.cv y) (synC1c)) syntaxClass0045)
  let syntaxFormula0143 : Wff :=
    (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      syntaxFormula0141)
  let syntaxFormula0144 : Wff := (.imp syntaxFormula0056 syntaxFormula0142)
  let syntaxFormula0145 : Wff := (.classMem (.cv y) syntaxClass0047)
  let syntaxFormula0146 : Wff := (.classMem (synCplc (.cv y) (synC1c)) syntaxClass0047)
  let syntaxFormula0147 : Wff := (.imp syntaxFormula0145 syntaxFormula0146)
  let syntaxFormula0148 : Wff := (synWa syntaxFormula0048 syntaxFormula0055)
  let syntaxFormula0149 : Wff := (synWral y (synCnnc) syntaxFormula0147)
  let syntaxFormula0150 : Wff := (synWa syntaxFormula0148 syntaxFormula0149)
  let syntaxFormula0151 : Wff :=
    (synW3a syntaxFormula0048 syntaxFormula0055 syntaxFormula0149)
  let syntaxFormula0152 : Wff := (synWss (synCnnc) syntaxClass0047)
  let syntaxFormula0153 : Wff := (.classMem (.cv n) syntaxClass0047)
  let syntaxFormula0154 : Wff := (.classMem (.cv n) syntaxClass0045)
  let syntaxClass0155 : Class := (synCfv syntaxClass0051 (.cv n))
  let syntaxClass0156 : Class := (synCfv syntaxClass0028 (.cv n))
  let syntaxFormula0157 : Wff := (.classEq syntaxClass0155 syntaxClass0156)
  let syntaxFormula0158 : Wff :=
    (.imp (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0157)
  let syntaxClass0159 : Class := (synCfv syntaxClass0051 (.cv k))
  let syntaxFormula0160 : Wff := (.classEq syntaxClass0159 syntaxClass0043)
  let syntaxFormula0161 : Wff :=
    (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0160)
  let syntaxFormula0162 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0159)
  let syntaxClass0163 : Class :=
    (synCwpphit (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c))
      (synCtc C))
  let syntaxFormula0164 : Wff := (.classMem (.cv k) syntaxClass0163)
  let syntaxFormula0165 : Wff := (.classEq syntaxClass0043 syntaxClass0159)
  let syntaxFormula0166 : Wff := (.classMem (.cv n) syntaxClass0163)
  let syntaxFormula0167 : Wff := (synWa (.classMem (.cv n) (synCnnc)) syntaxFormula0166)
  let syntaxFormula0168 : Wff :=
    (synWo (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
  let syntaxFormula0169 : Wff := (synWral y (synCnnc) syntaxFormula0168)
  let syntaxFormula0170 : Wff := (synWral x (synCnnc) syntaxFormula0169)
  let syntaxFormula0171 : Wff :=
    (synWo (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
  let syntaxFormula0172 : Wff := (.imp syntaxFormula0170 syntaxFormula0171)
  let syntaxFormula0173 : Wff :=
    (.imp syntaxFormula0167 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
  let syntaxFormula0174 : Wff :=
    (synWa syntaxFormula0167 (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k)))
  let syntaxFormula0175 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0155)
  let syntaxFormula0176 : Wff := (synWa (.classMem (.cv n) (synCnnc)) syntaxFormula0175)
  let syntaxFormula0177 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0156)
  let syntaxFormula0178 : Wff := (synWb syntaxFormula0175 syntaxFormula0177)
  let syntaxFormula0179 : Wff := (synWa (.classMem (.cv n) (synCnnc)) syntaxFormula0177)
  let syntaxFormula0180 : Wff := (.classMem (.cv n) syntaxClass0026)
  let syntaxFormula0181 : Wff :=
    (.imp syntaxFormula0180 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
  let syntaxFormula0182 : Wff :=
    (.imp (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0173)
  let syntaxFormula0183 : Wff := (.neg syntaxFormula0173)
  let syntaxFormula0184 : Wff :=
    (.imp syntaxFormula0183 (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k)))
  let syntaxFormula0185 : Wff := (.imp syntaxFormula0183 syntaxFormula0173)
  let syntaxFormula0186 : Wff :=
    (.imp syntaxFormula0166 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
  let syntaxClass0187 : Class := (synCfv syntaxClass0029 (.cv k))
  let syntaxFormula0188 : Wff := (synWral n (synCnnc) syntaxFormula0186)
  let syntaxFormula0189 : Wff := (.classEq syntaxClass0187 syntaxClass0159)
  let syntaxFormula0190 : Wff := (synWa syntaxFormula0009 syntaxFormula0164)
  let syntaxFormula0191 : Wff :=
    (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      syntaxFormula0190)
  let syntaxFormula0192 : Wff := (synWa syntaxFormula0010 syntaxFormula0188)
  let syntaxFormula0193 : Wff :=
    (synW3a (.classMem (synCtc C) (synCncs)) (.classMem C (synCncs))
      (synWbr (synCtc C) (synClec) C))
  let syntaxFormula0194 : Wff :=
    (.classMem syntaxClass0155 (synCdm (synCwppstopstep F C)))
  let syntaxFormula0195 : Wff := (.classMem syntaxClass0155 (synChwcards (synCvv)))
  let syntaxFormula0196 : Wff := (.classMem syntaxClass0155 (synCncs))
  let syntaxClass0197 : Class := (synCfv syntaxClass0051 (.cv q))
  let syntaxFormula0198 : Wff := (.classMem syntaxClass0197 (synCncs))
  let syntaxFormula0199 : Wff := (synWral q (synCnnc) syntaxFormula0198)
  let syntaxFormula0200 : Wff := (synWa syntaxFormula0057 syntaxFormula0193)
  let syntaxFormula0201 : Wff := (synWa syntaxFormula0191 syntaxFormula0192)
  let syntaxFormula0202 : Wff := (synWa syntaxFormula0200 syntaxFormula0199)
  let syntaxFormula0203 : Wff :=
    (.imp (synWbr (synCtc C) (synClec) (.cv y))
      (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))
  let syntaxFormula0204 : Wff :=
    (synWral y (synCdm (synCwppstopstep F C)) syntaxFormula0203)
  let syntaxClass0205 : Class := (synCfv syntaxClass0051 (.cv r))
  let syntaxFormula0206 : Wff := (.classEq (.cv y) syntaxClass0205)
  let syntaxFormula0207 : Wff := (synWa (.classMem (.cv r) (synCnnc)) syntaxFormula0206)
  let syntaxClass0208 : Class := (synCfv (synCwppstopstep F C) syntaxClass0205)
  let syntaxFormula0209 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0205)
  let syntaxFormula0210 : Wff := (synWbr C (synClec) syntaxClass0208)
  let syntaxFormula0211 : Wff := (.imp syntaxFormula0209 syntaxFormula0210)
  let syntaxFormula0212 : Wff := (synWral r (synCnnc) syntaxFormula0211)
  let syntaxFormula0213 : Wff :=
    (synW3a syntaxFormula0201 syntaxFormula0202 syntaxFormula0212)
  let syntaxFormula0214 : Wff := (synWa (.classMem (.cv n) (synCnnc)) syntaxFormula0196)
  let syntaxFormula0215 : Wff := (synWbr C (synClec) syntaxClass0155)
  let syntaxFormula0216 : Wff :=
    (synWa (synWa (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc))) syntaxFormula0196)
  let syntaxClass0217 : Class := (synCtc syntaxClass0155)
  let syntaxClass0218 : Class := (synCfv syntaxClass0029 (synCtc (.cv n)))
  let syntaxFormula0219 : Wff := (synWbr (synCtc C) (synClec) syntaxClass0218)
  let syntaxFormula0220 : Wff :=
    (synWa (.classMem (synCtc (.cv n)) (synCnnc)) syntaxFormula0219)
  let syntaxFormula0221 : Wff := (.classMem (synCtc (.cv n)) syntaxClass0019)
  let syntaxFormula0222 : Wff := (synWb syntaxFormula0007 syntaxFormula0221)
  let syntaxFormula0223 : Wff := (synWral n (synCnnc) syntaxFormula0222)
  let syntaxFormula0224 : Wff := (.classMem (synCtc (.cv m)) syntaxClass0019)
  let syntaxFormula0225 : Wff := (synWb syntaxFormula0009 syntaxFormula0224)
  let syntaxFormula0226 : Wff :=
    (.imp syntaxFormula0224 (synWbr (.cv k) (synCkqrel (synClefin)) (synCtc (.cv m))))
  let syntaxFormula0227 : Wff := (.classMem (synCtc (.cv x)) syntaxClass0019)
  let syntaxFormula0228 : Wff := (.classMem (.cv x) syntaxClass0006)
  let syntaxFormula0229 : Wff := (synWb syntaxFormula0228 syntaxFormula0227)
  let syntaxFormula0230 : Wff := (synWa (.classMem (.cv x) (synCnnc)) syntaxFormula0010)
  let syntaxFormula0231 : Wff :=
    (synWo (.classEq (.cv m) (synCtc (.cv m)))
      (.classEq (.cv m) (synCplc (synCtc (.cv m)) (synC1c))))
  let syntaxClass0232 : Class := (synCfv syntaxClass0051 (.cv m))
  let syntaxFormula0233 : Wff := (synWbr C (synClec) syntaxClass0232)
  let syntaxClass0234 : Class := (synCfv syntaxClass0051 (.cv x))
  let syntaxFormula0235 : Wff :=
    (.classMem syntaxClass0234 (synCdm (synCwppstopstep F C)))
  let syntaxFormula0236 : Wff := (.classEq (.cv y) syntaxClass0234)
  let syntaxFormula0237 : Wff := (synWa (.classMem (.cv x) (synCnnc)) syntaxFormula0236)
  let syntaxClass0238 : Class := (synCtc syntaxClass0234)
  let syntaxFormula0239 : Wff := (synWbr C (synClec) syntaxClass0234)
  let syntaxFormula0240 : Wff := (synWne syntaxClass0234 syntaxClass0238)
  let syntaxFormula0241 : Wff := (.imp syntaxFormula0239 syntaxFormula0240)
  let syntaxClass0242 : Class := (synCtc syntaxClass0232)
  let syntaxFormula0243 : Wff := (synWne syntaxClass0232 syntaxClass0242)
  let syntaxFormula0244 : Wff := (.imp syntaxFormula0233 syntaxFormula0243)
  let syntaxFormula0245 : Wff := (.classEq syntaxClass0232 syntaxClass0242)
  let syntaxFormula0246 : Wff := (.neg syntaxFormula0245)
  let syntaxFormula0247 : Wff := (.classEq syntaxClass0242 syntaxClass0159)
  let syntaxFormula0248 : Wff := (.classEq syntaxClass0242 syntaxClass0232)
  have p0000 := @gSimpl (.classEq I (synCtc I)) (synWa ph (synWa ps ch))
  have p0001 := @gSimpr (.classEq I (synCtc I)) (synWa ph (synWa ps ch))
  have p0002 := @gSimpl ph (synWa ps ch)
  have p0003 :=
    @gSyl (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch)))
      (synWa ph (synWa ps ch)) ph p0001 p0002
  have p0004 :=
    @gJca (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch)))
      (.classEq I (synCtc I)) ph p0000 p0003
  have p0005 := @gSimpr ph (synWa ps ch)
  have p0006 :=
    @gSyl (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch)))
      (synWa ph (synWa ps ch)) (synWa ps ch) p0001 p0005
  have p0007 := @gSimpl ps ch
  have p0008 :=
    @gSyl (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch))) (synWa ps ch) ps
      p0006 p0007
  have p0009 :=
    @gJca (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch)))
      (.classEq I (synCtc I)) ps p0000 p0008
  have p0010 := @gSimpr ps ch
  have p0011 :=
    @gSyl (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch))) (synWa ps ch) ch
      p0006 p0010
  have p0012 :=
    @gJca (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch)))
      (.classEq I (synCtc I)) ch p0000 p0011
  have p0013 :=
    @gJca (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch)))
      (synWa (.classEq I (synCtc I)) ps) (synWa (.classEq I (synCtc I)) ch) p0009
      p0012
  have p0014 :=
    @gJca (synWa (.classEq I (synCtc I)) (synWa ph (synWa ps ch)))
      (synWa (.classEq I (synCtc I)) ph) syntaxFormula0000 p0004 p0013
  have p0015 :=
    @gEx (.classEq I (synCtc I)) (synWa ph (synWa ps ch)) syntaxFormula0001 p0014
  have p0016 := @gEqid (.cv m)
  have p0017 := @gA1i (.classEq (.cv m) (.cv m)) syntaxFormula0001 p0016
  have p0018 := @gSimpl (synWa (.classEq I (synCtc I)) ph) syntaxFormula0000
  have p0019 := @gSimpr (.classEq I (synCtc I)) ph
  have p0020 :=
    @gSyl (synWa (.classEq I (synCtc I)) ph) ph syntaxFormula0005 p0019
      hyp_wppstopfixedhitcontrgrowfixdndv_10
  have p0021 := @gIftrue (.classEq I (synCtc I)) I (synC0c)
  have p0022 :=
    @gEqcomd (.classEq I (synCtc I)) (synCif (.classEq I (synCtc I)) I (synC0c)) I
      p0021
  have p0023 :=
    @gAdantr (.classEq I (synCtc I))
      (.classEq I (synCif (.classEq I (synCtc I)) I (synC0c))) ph p0022
  have p0024 :=
    @gWpphitstartcongrndv C (synCwppstopstep F C) I
      (synCif (.classEq I (synCtc I)) I (synC0c))
  have p0025 :=
    @gSyl (synWa (.classEq I (synCtc I)) ph)
      (.classEq I (synCif (.classEq I (synCtc I)) I (synC0c)))
      (.classEq (synCwpphit (synCwppstopstep F C) I C) syntaxClass0006) p0023 p0024
  have p0026 :=
    @gEleq2d (synWa (.classEq I (synCtc I)) ph)
      (synCwpphit (synCwppstopstep F C) I C) syntaxClass0006 (.cv m) p0025
  have p0027 :=
    @gEleq2d (synWa (.classEq I (synCtc I)) ph)
      (synCwpphit (synCwppstopstep F C) I C) syntaxClass0006 (.cv n) p0025
  have p0028 :=
    @gImbi1d (synWa (.classEq I (synCtc I)) ph)
      (.classMem (.cv n) (synCwpphit (synCwppstopstep F C) I C)) syntaxFormula0007
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)) p0027
  have p0029 :=
    @gRalbidv (synWa (.classEq I (synCtc I)) ph) syntaxFormula0002 syntaxFormula0008 n
      (synCnnc) dv_cache_0001 p0028
  have p0030 :=
    @gAnbi12d (synWa (.classEq I (synCtc I)) ph)
      (.classMem (.cv m) (synCwpphit (synCwppstopstep F C) I C)) syntaxFormula0009
      syntaxFormula0003 syntaxFormula0010 p0026 p0029
  have p0031 :=
    @gAnbi2d (synWa (.classEq I (synCtc I)) ph) syntaxFormula0004 syntaxFormula0011
      (.classMem (.cv m) (synCnnc)) p0030
  have p0032 :=
    @gMpbid (synWa (.classEq I (synCtc I)) ph) syntaxFormula0005 syntaxFormula0012
      p0020 p0031
  have p0033 :=
    @gSyl syntaxFormula0001 (synWa (.classEq I (synCtc I)) ph) syntaxFormula0012 p0018
      p0032
  have p0034 :=
    @gSimpld syntaxFormula0001 (.classMem (.cv m) (synCnnc)) syntaxFormula0011 p0033
  have p0035 := @gSimpr (synWa (.classEq I (synCtc I)) ph) syntaxFormula0000
  have p0036 :=
    @gSimpl (synWa (.classEq I (synCtc I)) ps) (synWa (.classEq I (synCtc I)) ch)
  have p0037 :=
    @gSyl syntaxFormula0001 syntaxFormula0000 (synWa (.classEq I (synCtc I)) ps) p0035
      p0036
  have p0038 := @gSimpr (.classEq I (synCtc I)) ps
  have p0039 :=
    @gSyl (synWa (.classEq I (synCtc I)) ps) ps syntaxFormula0018 p0038
      hyp_wppstopfixedhitcontrgrowfixdndv_11
  have p0040 := @gTceq I (synCif (.classEq I (synCtc I)) I (synC0c))
  have p0041 :=
    @gSyl (.classEq I (synCtc I))
      (.classEq I (synCif (.classEq I (synCtc I)) I (synC0c)))
      (.classEq (synCtc I) (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))))
      p0022 p0040
  have p0042 :=
    @gAdantr (.classEq I (synCtc I))
      (.classEq (synCtc I) (synCtc (synCif (.classEq I (synCtc I)) I (synC0c)))) ps
      p0041
  have p0043 :=
    @gWpphitstartcongrndv (synCtc C) (synCwppstopstep F (synCtc C)) (synCtc I)
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c)))
  have p0044 :=
    @gSyl (synWa (.classEq I (synCtc I)) ps)
      (.classEq (synCtc I) (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))))
      (.classEq (synCwpphit (synCwppstopstep F (synCtc C)) (synCtc I) (synCtc C))
        syntaxClass0019)
      p0042 p0043
  have p0045 :=
    @gEleq2d (synWa (.classEq I (synCtc I)) ps)
      (synCwpphit (synCwppstopstep F (synCtc C)) (synCtc I) (synCtc C))
      syntaxClass0019 (.cv k) p0044
  have p0046 :=
    @gEleq2d (synWa (.classEq I (synCtc I)) ps)
      (synCwpphit (synCwppstopstep F (synCtc C)) (synCtc I) (synCtc C))
      syntaxClass0019 (.cv n) p0044
  have p0047 :=
    @gImbi1d (synWa (.classEq I (synCtc I)) ps) syntaxFormula0014 syntaxFormula0020
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0046
  have p0048 :=
    @gRalbidv (synWa (.classEq I (synCtc I)) ps) syntaxFormula0015 syntaxFormula0021 n
      (synCnnc) dv_cache_0002 p0047
  have p0049 :=
    @gAnbi12d (synWa (.classEq I (synCtc I)) ps) syntaxFormula0013 syntaxFormula0022
      syntaxFormula0016 syntaxFormula0023 p0045 p0048
  have p0050 :=
    @gAnbi2d (synWa (.classEq I (synCtc I)) ps) syntaxFormula0017 syntaxFormula0024
      (.classMem (.cv k) (synCnnc)) p0049
  have p0051 :=
    @gMpbid (synWa (.classEq I (synCtc I)) ps) syntaxFormula0018 syntaxFormula0025
      p0039 p0050
  have p0052 :=
    @gSyl syntaxFormula0001 (synWa (.classEq I (synCtc I)) ps) syntaxFormula0025 p0037
      p0051
  have p0053 :=
    @gSimpld syntaxFormula0001 (.classMem (.cv k) (synCnnc)) syntaxFormula0024 p0052
  have p0054 :=
    @gJca syntaxFormula0001 (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))
      p0034 p0053
  have p0055 :=
    @gSimprd syntaxFormula0001 (.classMem (.cv m) (synCnnc)) syntaxFormula0011 p0033
  have p0056 := @gSimpld syntaxFormula0001 syntaxFormula0009 syntaxFormula0010 p0055
  have p0057 :=
    @gSimprd syntaxFormula0001 (.classMem (.cv k) (synCnnc)) syntaxFormula0024 p0052
  have p0058 := @gSimpld syntaxFormula0001 syntaxFormula0022 syntaxFormula0023 p0057
  have p0059 := (Nominal.classEqRefl syntaxClass0026)
  have p0060 := @gEqid (synCwppstopstep F (synCtc C))
  have p0061 := @gId (.classEq I (synCtc I))
  have p0062 := @gTceq (synCif (.classEq I (synCtc I)) I (synC0c)) I
  have p0063 :=
    @gSyl (.classEq I (synCtc I))
      (.classEq (synCif (.classEq I (synCtc I)) I (synC0c)) I)
      (.classEq (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc I))
      p0021 p0062
  have p0064 :=
    @gEqcomd (.classEq I (synCtc I))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc I) p0063
  have p0065 :=
    @gN3eqtrd (.classEq I (synCtc I)) (synCif (.classEq I (synCtc I)) I (synC0c)) I
      (synCtc I) (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) p0021 p0061
      p0064
  have p0066 := @gIffalse (.classEq I (synCtc I)) I (synC0c)
  have p0067 := @gTc0c
  have p0068 := @gEqcomi (synCtc (synC0c)) (synC0c) p0067
  have p0069 :=
    @gA1i (.classEq (synC0c) (synCtc (synC0c))) (.neg (.classEq I (synCtc I))) p0068
  have p0070 := @gTceq (synCif (.classEq I (synCtc I)) I (synC0c)) (synC0c)
  have p0071 :=
    @gSyl (.neg (.classEq I (synCtc I)))
      (.classEq (synCif (.classEq I (synCtc I)) I (synC0c)) (synC0c))
      (.classEq (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc (synC0c)))
      p0066 p0070
  have p0072 :=
    @gEqcomd (.neg (.classEq I (synCtc I)))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc (synC0c)) p0071
  have p0073 :=
    @gN3eqtrd (.neg (.classEq I (synCtc I)))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (synC0c) (synCtc (synC0c))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) p0066 p0069 p0072
  have p0074 := @gPm261i (.classEq I (synCtc I)) syntaxFormula0027 p0065 p0073
  have p0075 :=
    @gPm32i (.classEq (synCwppstopstep F (synCtc C)) (synCwppstopstep F (synCtc C)))
      syntaxFormula0027 p0060 p0074
  have p0076 :=
    @gFreceq12 (synCwppstopstep F (synCtc C)) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c)))
  have p0077 := Nominal.mp p0075 p0076
  have p0078 := @gCnveqi syntaxClass0028 syntaxClass0029 p0077
  have p0079 :=
    @gImaeq1i syntaxClass0030 syntaxClass0031 (synCima (synClec) (synCsn (synCtc C)))
      p0078
  have p0080 :=
    @gEqtri syntaxClass0026
      (synCima syntaxClass0030 (synCima (synClec) (synCsn (synCtc C))))
      syntaxClass0032 p0059 p0079
  have p0081 := (Nominal.classEqRefl syntaxClass0019)
  have p0082 := @gEqtr4i syntaxClass0026 syntaxClass0032 syntaxClass0019 p0080 p0081
  have p0083 :=
    @gSyl6eleqr syntaxFormula0001 (.cv k) syntaxClass0019 syntaxClass0026 p0058 p0082
  have p0084 :=
    @gWppstopstepfunsndv (synCtc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0085 := @gWecomparisondefaultemptywe
  have p0086 := @gDf0c2
  have p0087 :=
    @gPm32i
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (.classEq (synC0c) (synCnc (synC0))) p0085 p0086
  have p0088 := @gN0ex
  have p0089 :=
    @gBrex (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      (synCwe)
  have p0090 := Nominal.mp p0085 p0089
  have p0091 :=
    @gSimpli
      (.classMem (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCvv))
      (.classMem (synC0) (synCvv)) p0090
  have p0092 := @gSimpr (.classEq (.cv d) (synC0)) syntaxFormula0033
  have p0093 := @gSimpl (.classEq (.cv d) (synC0)) syntaxFormula0033
  have p0094 :=
    @gBreq12d syntaxFormula0034 (.cv s)
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (.cv d) (synC0)
      (synCwe) p0092 p0093
  have p0095 := @gNceqd syntaxFormula0034 (.cv d) (synC0) p0093
  have p0096 :=
    @gEqeq2d syntaxFormula0034 (synCnc (.cv d)) (synCnc (synC0)) (synC0c) p0095
  have p0097 :=
    @gAnbi12d syntaxFormula0034 (synWbr (.cv s) (synCwe) (.cv d))
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (.classEq (synC0c) (synCnc (.cv d))) (.classEq (synC0c) (synCnc (synC0))) p0094
      p0096
  have p0098 :=
    @gSpc2ev syntaxFormula0035
      (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
          (synC0)) (.classEq (synC0c) (synCnc (synC0))))
      d s (synC0) (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0088 p0091 p0097
  have p0099 := Nominal.mp p0087 p0098
  have p0100 := @gN0cex
  have p0101 := @gId (.classEq (.cv k) (synC0c))
  have p0102 :=
    @gEleq1d (.classEq (.cv k) (synC0c)) (.cv k) (synC0c) (synChwcards (synCvv))
      p0101
  have p0104 :=
    @gEqeq1d (.classEq (.cv k) (synC0c)) (.cv k) (synC0c) (synCnc (.cv d)) p0101
  have p0105 :=
    @gAnbi2d (.classEq (.cv k) (synC0c)) (.classEq (.cv k) (synCnc (.cv d)))
      (.classEq (synC0c) (synCnc (.cv d))) (synWbr (.cv s) (synCwe) (.cv d)) p0104
  have p0106 :=
    @gExbidv (.classEq (.cv k) (synC0c)) syntaxFormula0036 syntaxFormula0035 s
      dv_cache_0010 p0105
  have p0107 :=
    @gExbidv (.classEq (.cv k) (synC0c)) syntaxFormula0037 syntaxFormula0038 d
      dv_cache_0011 p0106
  have p0108 :=
    @gBibi12d (.classEq (.cv k) (synC0c)) (.classMem (.cv k) (synChwcards (synCvv)))
      (.classMem (synC0c) (synChwcards (synCvv))) (synWex d syntaxFormula0037)
      syntaxFormula0039 p0102 p0107
  have p0109 := @gElhwcardswev k s d dv_cache_0012 dv_cache_0009 dv_cache_0013
  have p0110 :=
    @gVtoclg
      (synWb (.classMem (.cv k) (synChwcards (synCvv))) (synWex d syntaxFormula0037))
      (synWb (.classMem (synC0c) (synChwcards (synCvv))) syntaxFormula0039) k
      (synC0c) (synCvv) dv_cache_0014 dv_cache_0015 p0108 p0109
  have p0111 := Nominal.mp p0100 p0110
  have p0112 :=
    @gMpbir (.classMem (synC0c) (synChwcards (synCvv))) syntaxFormula0039 p0099 p0111
  have p0113 :=
    @gPm32i (.classMem I (synChwcards (synCvv)))
      (.classMem (synC0c) (synChwcards (synCvv))) hyp_wppstopfixedhitcontrgrowfixdndv_7
      p0112
  have p0114 := @gIfcl (.classEq I (synCtc I)) I (synC0c) (synChwcards (synCvv))
  have p0115 := Nominal.mp p0113 p0114
  have p0116 :=
    @gWppstopstepdmndv (synCtc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0117 :=
    @gEleq2i (synCdm (synCwppstopstep F (synCtc C))) (synChwcards (synCvv))
      (synCif (.classEq I (synCtc I)) I (synC0c)) p0116
  have p0118 := @gBiimpri syntaxFormula0040 syntaxFormula0041 p0117
  have p0119 := Nominal.mp p0115 p0118
  have p0120 :=
    @gWppstopsteprndmndv (synCtc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0121 :=
    @gN3pm32i (.classMem (synCwppstopstep F (synCtc C)) (synCfuns))
      syntaxFormula0040 syntaxFormula0042 p0084 p0119 p0120
  have p0122 :=
    @gElwpphitvndv (synCtc C) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv k)
  have p0123 := Nominal.mp p0121 p0122
  have p0124 :=
    @gSylib syntaxFormula0001 (.classMem (.cv k) syntaxClass0026)
      (synWa (.classMem (.cv k) (synCnnc)) syntaxFormula0044) p0083 p0123
  have p0125 :=
    @gSimprd syntaxFormula0001 (.classMem (.cv k) (synCnnc)) syntaxFormula0044 p0124
  have p0126 := @gFinlewe
  have p0127 := @gWppweref (synCnnc) (synCkqrel (synClefin))
  have p0128 := Nominal.mp p0126 p0127
  have p0129 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (.classMem (.cv k) (synCnnc)) p0128
  have p0130 := @gId (.classMem (.cv k) (synCnnc))
  have p0131 :=
    @gRefd (.classMem (.cv k) (synCnnc)) (synCnnc) (synCkqrel (synClefin)) (.cv k)
      p0129 p0130
  have p0132 :=
    @gSyl syntaxFormula0001 (.classMem (.cv k) (synCnnc))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k)) p0053 p0131
  have p0133 := @gTru
  have p0134 :=
    @gWppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0135 :=
    @gWppfrecprefixeqexndv k (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) p0134 p0084
  have p0136 := @gAbid2 x syntaxClass0045 dv_cache_0016
  have p0137 := @gEleq1i syntaxClass0047 syntaxClass0045 (synCvv) p0136
  have p0138 :=
    @gMpbir syntaxFormula0048 (.classMem syntaxClass0045 (synCvv)) p0135 p0137
  have p0139 := @gA1i syntaxFormula0048 synWtru p0138
  have p0140 :=
    @gWppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0141 :=
    @gEleq2i (synCdm (synCwppstopstep F C)) (synChwcards (synCvv))
      (synCif (.classEq I (synCtc I)) I (synC0c)) p0140
  have p0142 := @gBiimpri syntaxFormula0049 syntaxFormula0041 p0141
  have p0143 := Nominal.mp p0115 p0142
  have p0144 :=
    @gWppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1
      hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0145 :=
    @gN3pm32i (.classMem (synCwppstopstep F C) (synCfuns)) syntaxFormula0049
      (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C))) p0134
      p0143 p0144
  have p0146 :=
    @gWpporbit0ndv (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c))
  have p0147 := Nominal.mp p0145 p0146
  have p0149 :=
    @gWpporbit0ndv (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c))
  have p0150 := Nominal.mp p0121 p0149
  have p0151 :=
    @gEqcomi syntaxClass0050 (synCif (.classEq I (synCtc I)) I (synC0c)) p0150
  have p0152 :=
    @gEqtri syntaxClass0052 (synCif (.classEq I (synCtc I)) I (synC0c))
      syntaxClass0050 p0147 p0151
  have p0153 :=
    @gA1i syntaxFormula0053 (synWbr (synC0c) (synCkqrel (synClefin)) (.cv k)) p0152
  have p0154 := @gPeano1
  have p0155 :=
    @gWppfrecprefixeqvalndv (synC0c) k (synCwppstopstep F C)
      (synCwppstopstep F (synCtc C)) (synCif (.classEq I (synCtc I)) I (synC0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0156 := Nominal.mp p0154 p0155
  have p0157 :=
    @gMpbir syntaxFormula0054
      (.imp (synWbr (synC0c) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0053) p0153
      p0156
  have p0158 := @gA1i syntaxFormula0054 synWtru p0157
  have p0160 := @gId (.classEq (.cv x) (synC0c))
  have p0161 :=
    @gEleq1d (.classEq (.cv x) (synC0c)) (.cv x) (synC0c) syntaxClass0045 p0160
  have p0162 :=
    @gElab syntaxFormula0046 syntaxFormula0054 x (synC0c) dv_cache_0017 dv_cache_0018
      p0100 p0161
  have p0163 := @gSylibr synWtru syntaxFormula0054 syntaxFormula0055 p0158 p0162
  have p0164 := @gJca synWtru syntaxFormula0048 syntaxFormula0055 p0139 p0163
  have p0165 := @gVex y
  have p0166 := @gId (.classEq (.cv x) (.cv y))
  have p0167 := @gEleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) syntaxClass0045 p0166
  have p0168 :=
    @gElab syntaxFormula0046 syntaxFormula0056 x (.cv y) dv_cache_0019 dv_cache_0020
      p0165 p0167
  have p0170 := @gA1i syntaxFormula0057 syntaxFormula0058 p0145
  have p0171 :=
    @gSimp1 (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0172 :=
    @gJca syntaxFormula0058 syntaxFormula0057 (.classMem (.cv y) (synCnnc)) p0170 p0171
  have p0173 :=
    @gWpporbitsucndv (synCwppstopstep F C)
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv y)
  have p0174 :=
    @gSyl syntaxFormula0058 (synWa syntaxFormula0057 (.classMem (.cv y) (synCnnc)))
      syntaxFormula0062 p0172 p0173
  have p0176 :=
    @gSimp2 (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0177 :=
    @gJca syntaxFormula0058 (.classMem (.cv y) (synCnnc)) syntaxFormula0056 p0171 p0176
  have p0179 :=
    @gSimp3 (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0180 :=
    @gJca syntaxFormula0058 (.classMem (.cv y) (synCnnc))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0171 p0179
  have p0181 :=
    @gSimpr (.classMem (.cv y) (synCnnc))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0182 :=
    @gSimpl (.classMem (.cv y) (synCnnc))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0186 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (.classMem (.cv y) (synCnnc)) p0128
  have p0187 := @gId (.classMem (.cv y) (synCnnc))
  have p0188 :=
    @gRefd (.classMem (.cv y) (synCnnc)) (synCnnc) (synCkqrel (synClefin)) (.cv y)
      p0186 p0187
  have p0189 :=
    @gOrc (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y))
      (.classEq (.cv y) (synCplc (.cv y) (synC1c)))
  have p0190 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y)) syntaxFormula0063 p0188 p0189
  have p0193 :=
    @gJca (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCnnc)) p0187 p0187
  have p0194 := @gKqfinsucsplit (.cv y) (.cv y)
  have p0195 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (synWa (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWb (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
        syntaxFormula0063)
      p0193 p0194
  have p0196 :=
    @gMpbird (.classMem (.cv y) (synCnnc))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      syntaxFormula0063 p0190 p0195
  have p0197 :=
    @gSyl syntaxFormula0064 (.classMem (.cv y) (synCnnc))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))) p0182 p0196
  have p0198 :=
    @gA1d syntaxFormula0064
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0197
  have p0199 :=
    @gAncom (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
  have p0201 := @gWppwepo (synCnnc) (synCkqrel (synClefin))
  have p0202 := Nominal.mp p0126 p0201
  have p0203 := @gPorta (synCnnc) (synCkqrel (synClefin))
  have p0204 :=
    @gMpbi (synWbr (synCkqrel (synClefin)) (synCpartial) (synCnnc))
      syntaxFormula0065 p0202 p0203
  have p0205 :=
    @gSimp2 (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCantisym) (synCnnc))
  have p0206 := Nominal.mp p0204 p0205
  have p0207 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc)) syntaxFormula0064
      p0206
  have p0208 := @gBrex (synCkqrel (synClefin)) (synCnnc) (synCtrans)
  have p0209 := @gBreq (.cv x) (.cv a) (.cv r) (synCkqrel (synClefin))
  have p0210 := @gBreq (.cv a) (.cv z) (.cv r) (synCkqrel (synClefin))
  have p0211 :=
    @gAnbi12d (.classEq (.cv r) (synCkqrel (synClefin)))
      (synWbr (.cv x) (.cv r) (.cv a))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (.cv r) (.cv z))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)) p0209 p0210
  have p0212 := @gBreq (.cv x) (.cv z) (.cv r) (synCkqrel (synClefin))
  have p0213 :=
    @gImbi12d (.classEq (.cv r) (synCkqrel (synClefin)))
      (synWa (synWbr (.cv x) (.cv r) (.cv a)) (synWbr (.cv a) (.cv r) (.cv z)))
      syntaxFormula0066 (synWbr (.cv x) (.cv r) (.cv z))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)) p0211 p0212
  have p0214 :=
    @gRalbidv (.classEq (.cv r) (synCkqrel (synClefin))) syntaxFormula0067
      syntaxFormula0068 z (.cv b) dv_cache_0021 p0213
  have p0215 :=
    @gN2ralbidv (.classEq (.cv r) (synCkqrel (synClefin))) syntaxFormula0069
      syntaxFormula0070 x a (.cv b) (.cv b) dv_cache_0022 dv_cache_0023 p0214
  have p0216 :=
    @gRaleq syntaxFormula0068 z (.cv b) (synCnnc) dv_cache_0024 dv_cache_0025
  have p0217 :=
    @gRaleqbi1dv syntaxFormula0070 syntaxFormula0071 a (.cv b) (synCnnc) dv_cache_0026
      dv_cache_0027 p0216
  have p0218 :=
    @gRaleqbi1dv syntaxFormula0072 syntaxFormula0073 x (.cv b) (synCnnc) dv_cache_0028
      dv_cache_0029 p0217
  have p0219 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTrans x a z r b
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
  have p0220 :=
    @gBrabg syntaxFormula0074 syntaxFormula0075 syntaxFormula0076 r b
      (synCkqrel (synClefin)) (synCnnc) (synCvv) (synCvv) (synCtrans) dv_cache_0040
      dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
      p0215 p0218 p0219
  have p0221 :=
    @gSyl (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWa (.classMem (synCkqrel (synClefin)) (synCvv)) (.classMem (synCnnc) (synCvv)))
      syntaxFormula0077 p0208 p0220
  have p0222 :=
    @gIbi (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc)) syntaxFormula0076
      p0221
  have p0223 :=
    @gSyl syntaxFormula0064 (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      syntaxFormula0076 p0207 p0222
  have p0226 := @gPeano2 (.cv y)
  have p0227 :=
    @gSyl syntaxFormula0064 (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) p0182 p0226
  have p0228 :=
    @gJca syntaxFormula0064 (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) p0182 p0227
  have p0229 :=
    @gA1d syntaxFormula0001 (.classMem (.cv k) (synCnnc)) syntaxFormula0064 p0053
  have p0230 := @g_pm3_2 syntaxFormula0078 (.classMem (.cv k) (synCnnc))
  have p0231 :=
    @gSyl9 syntaxFormula0001 syntaxFormula0064 (.classMem (.cv k) (synCnnc))
      syntaxFormula0078 syntaxFormula0079 p0229 p0230
  have p0232 :=
    @gSyl5 syntaxFormula0064 syntaxFormula0078 syntaxFormula0001
      (.imp syntaxFormula0064 syntaxFormula0079) p0228 p0231
  have p0233 := @gPm243d syntaxFormula0001 syntaxFormula0064 syntaxFormula0079 p0232
  have p0234 := (Nominal.biimpRefl syntaxFormula0080)
  have p0235 :=
    @gSyl6ibr syntaxFormula0001 syntaxFormula0064 syntaxFormula0079 syntaxFormula0080
      p0233 p0234
  have p0236 := @gBreq1 (.cv x) (.cv y) (.cv a) (synCkqrel (synClefin))
  have p0237 :=
    @gAnbi1d (.classEq (.cv x) (.cv y))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)) p0236
  have p0238 := @gBreq1 (.cv x) (.cv y) (.cv z) (synCkqrel (synClefin))
  have p0239 :=
    @gImbi12d (.classEq (.cv x) (.cv y)) syntaxFormula0066 syntaxFormula0081
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)) p0237 p0238
  have p0240 :=
    @gBreq2 (.cv a) (synCplc (.cv y) (synC1c)) (.cv y) (synCkqrel (synClefin))
  have p0241 :=
    @gBreq1 (.cv a) (synCplc (.cv y) (synC1c)) (.cv z) (synCkqrel (synClefin))
  have p0242 :=
    @gAnbi12d (.classEq (.cv a) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)) p0240 p0241
  have p0243 :=
    @gImbi1d (.classEq (.cv a) (synCplc (.cv y) (synC1c))) syntaxFormula0081
      syntaxFormula0082 (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)) p0242
  have p0244 :=
    @gBreq2 (.cv z) (.cv k) (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin))
  have p0245 :=
    @gAnbi2d (.classEq (.cv z) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))) p0244
  have p0246 := @gBreq2 (.cv z) (.cv k) (.cv y) (synCkqrel (synClefin))
  have p0247 :=
    @gImbi12d (.classEq (.cv z) (.cv k)) syntaxFormula0082 syntaxFormula0083
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0245 p0246
  have p0248 :=
    @gRspc3v syntaxFormula0068 syntaxFormula0084
      (.imp syntaxFormula0081 (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))
      (.imp syntaxFormula0082 (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))) x a z
      (.cv y) (synCplc (.cv y) (synC1c)) (.cv k) (synCnnc) (synCnnc) (synCnnc)
      dv_cache_0019 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
      dv_cache_0029 dv_cache_0029 dv_cache_0027 dv_cache_0029 dv_cache_0027 dv_cache_0025
      dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0037 dv_cache_0038 dv_cache_0039
      p0239 p0243 p0247
  have p0249 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0064 syntaxFormula0080
      (.imp syntaxFormula0076 syntaxFormula0084) p0235 p0248
  have p0250 :=
    @gMpdi syntaxFormula0001 syntaxFormula0064 syntaxFormula0076 syntaxFormula0084 p0223
      p0249
  have p0251 :=
    @gSyl7bi
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))))
      syntaxFormula0083 syntaxFormula0001 syntaxFormula0064
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0199 p0250
  have p0252 :=
    @gExp4a syntaxFormula0001 syntaxFormula0064
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0251
  have p0253 :=
    Nominal.ax2 (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))
  have p0254 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0064
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))))
      (.imp (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))))
        (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))))
      p0252 p0253
  have p0255 :=
    @gMpdi syntaxFormula0001 syntaxFormula0064
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))))
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      p0198 p0254
  have p0256 :=
    @gMpdi syntaxFormula0001 syntaxFormula0064
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0181 p0255
  have p0257 :=
    @gSyl5 syntaxFormula0058 syntaxFormula0064 syntaxFormula0001
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0180 p0256
  have p0258 :=
    @g_pm3_2 syntaxFormula0085 (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))
  have p0259 :=
    @gSyl9 syntaxFormula0001 syntaxFormula0058
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0085
      syntaxFormula0086 p0257 p0258
  have p0260 :=
    @gSyl5 syntaxFormula0058 syntaxFormula0085 syntaxFormula0001
      (.imp syntaxFormula0058 syntaxFormula0086) p0177 p0259
  have p0261 := @gPm243d syntaxFormula0001 syntaxFormula0058 syntaxFormula0086 p0260
  have p0262 := (Nominal.biimpRefl syntaxFormula0087)
  have p0263 :=
    @gSyl6ibr syntaxFormula0001 syntaxFormula0058 syntaxFormula0086 syntaxFormula0087
      p0261 p0262
  have p0264 :=
    @gWppfrecprefixeqvalndv (.cv y) k (synCwppstopstep F C)
      (synCwppstopstep F (synCtc C)) (synCif (.classEq I (synCtc I)) I (synC0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0265 :=
    @gBiimpd (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0089) p0264
  have p0266 :=
    @gN3imp (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0089 p0265
  have p0267 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0087 syntaxFormula0089 p0263
      p0266
  have p0268 := @gFveq2 syntaxClass0060 syntaxClass0088 (synCwppstopstep F C)
  have p0269 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0089 syntaxFormula0091 p0267
      p0268
  have p0270 := @gEqeq2 syntaxClass0061 syntaxClass0090 syntaxClass0059
  have p0271 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0091 syntaxFormula0093 p0269
      p0270
  have p0272 := @gBi1 syntaxFormula0062 syntaxFormula0092
  have p0273 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0093
      (.imp syntaxFormula0062 syntaxFormula0092) p0271 p0272
  have p0274 :=
    @gMpdi syntaxFormula0001 syntaxFormula0058 syntaxFormula0062 syntaxFormula0092 p0174
      p0273
  have p0279 := @gKqfinsucnle (.cv y)
  have p0280 :=
    @gSyl syntaxFormula0064 (.classMem (.cv y) (synCnnc))
      (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      p0182 p0279
  have p0281 := @gNotnot2 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0282 :=
    @gSimpr syntaxFormula0064 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0283 :=
    @gSimpl syntaxFormula0064 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0285 :=
    @gSyl syntaxFormula0094 syntaxFormula0064
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0283 p0181
  have p0286 :=
    @gA1d syntaxFormula0094
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)) p0285
  have p0287 :=
    @gAncom (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0295 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc)) syntaxFormula0094
      p0206
  have p0311 :=
    @gSyl syntaxFormula0094 (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      syntaxFormula0076 p0295 p0222
  have p0316 :=
    @gSyl syntaxFormula0094 syntaxFormula0064
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) p0283 p0227
  have p0318 :=
    @gSyl5 syntaxFormula0094 syntaxFormula0064 syntaxFormula0001
      (.classMem (.cv k) (synCnnc)) p0283 p0229
  have p0319 :=
    @g_pm3_2 (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (.classMem (.cv k) (synCnnc))
  have p0320 :=
    @gSyl9 syntaxFormula0001 syntaxFormula0094 (.classMem (.cv k) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) syntaxFormula0095 p0318 p0319
  have p0321 :=
    @gSyl5 syntaxFormula0094 (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      syntaxFormula0001 (.imp syntaxFormula0094 syntaxFormula0095) p0316 p0320
  have p0322 := @gPm243d syntaxFormula0001 syntaxFormula0094 syntaxFormula0095 p0321
  have p0325 :=
    @gSyl syntaxFormula0094 syntaxFormula0064 (.classMem (.cv y) (synCnnc)) p0283 p0182
  have p0326 := @g_pm3_2 syntaxFormula0095 (.classMem (.cv y) (synCnnc))
  have p0327 :=
    @gSyl5 syntaxFormula0094 (.classMem (.cv y) (synCnnc)) syntaxFormula0095
      syntaxFormula0096 p0325 p0326
  have p0328 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0094 syntaxFormula0095
      (.imp syntaxFormula0094 syntaxFormula0096) p0322 p0327
  have p0329 := @gPm243d syntaxFormula0001 syntaxFormula0094 syntaxFormula0096 p0328
  have p0330 := (Nominal.biimpRefl syntaxFormula0097)
  have p0331 :=
    @gSyl6ibr syntaxFormula0001 syntaxFormula0094 syntaxFormula0096 syntaxFormula0097
      p0329 p0330
  have p0332 :=
    @gBreq1 (.cv x) (synCplc (.cv y) (synC1c)) (.cv a) (synCkqrel (synClefin))
  have p0333 :=
    @gAnbi1d (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)) p0332
  have p0334 :=
    @gBreq1 (.cv x) (synCplc (.cv y) (synC1c)) (.cv z) (synCkqrel (synClefin))
  have p0335 :=
    @gImbi12d (.classEq (.cv x) (synCplc (.cv y) (synC1c))) syntaxFormula0066
      syntaxFormula0098 (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)) p0333 p0334
  have p0336 :=
    @gBreq2 (.cv a) (.cv k) (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin))
  have p0337 := @gBreq1 (.cv a) (.cv k) (.cv z) (synCkqrel (synClefin))
  have p0338 :=
    @gAnbi12d (.classEq (.cv a) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)) p0336 p0337
  have p0339 :=
    @gImbi1d (.classEq (.cv a) (.cv k)) syntaxFormula0098 syntaxFormula0099
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)) p0338
  have p0340 := @gBreq2 (.cv z) (.cv y) (.cv k) (synCkqrel (synClefin))
  have p0341 :=
    @gAnbi2d (.classEq (.cv z) (.cv y))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0340
  have p0342 :=
    @gBreq2 (.cv z) (.cv y) (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin))
  have p0343 :=
    @gImbi12d (.classEq (.cv z) (.cv y)) syntaxFormula0099 syntaxFormula0100
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0341 p0342
  have p0344 :=
    @gRspc3v syntaxFormula0068 syntaxFormula0101
      (.imp syntaxFormula0098
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
      (.imp syntaxFormula0099
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
      x a z (synCplc (.cv y) (synC1c)) (.cv k) (.cv y) (synCnnc) (synCnnc) (synCnnc)
      dv_cache_0055 dv_cache_0049 dv_cache_0050 dv_cache_0056 dv_cache_0051 dv_cache_0048
      dv_cache_0029 dv_cache_0029 dv_cache_0027 dv_cache_0029 dv_cache_0027 dv_cache_0025
      dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0037 dv_cache_0038 dv_cache_0039
      p0335 p0339 p0343
  have p0345 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0094 syntaxFormula0097
      (.imp syntaxFormula0076 syntaxFormula0101) p0331 p0344
  have p0346 :=
    @gMpdi syntaxFormula0001 syntaxFormula0094 syntaxFormula0076 syntaxFormula0101 p0311
      p0345
  have p0347 :=
    @gSyl7bi
      (synWa (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      syntaxFormula0100 syntaxFormula0001 syntaxFormula0094
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0287 p0346
  have p0348 :=
    @gExp4a syntaxFormula0001 syntaxFormula0094
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0347
  have p0349 :=
    Nominal.ax2 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))
  have p0350 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0094
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      (.imp (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      p0348 p0349
  have p0351 :=
    @gMpdi syntaxFormula0001 syntaxFormula0094
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      p0286 p0350
  have p0352 :=
    @gMpdi syntaxFormula0001 syntaxFormula0094
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0282 p0351
  have p0353 :=
    @gExp3a syntaxFormula0001 syntaxFormula0064
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0352
  have p0354 :=
    @gSyl7 (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)) syntaxFormula0001
      syntaxFormula0064
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0281 p0353
  have p0355 :=
    @gNotnot1 (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))
  have p0356 :=
    @gSyl8 syntaxFormula0001 syntaxFormula0064
      (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))
      (.neg (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      p0354 p0355
  have p0357 :=
    Nominal.ax3 (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
  have p0358 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0064
      (.imp (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))) (.neg (.neg
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))))
      (.imp (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
        (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      p0356 p0357
  have p0359 :=
    @gMpdi syntaxFormula0001 syntaxFormula0064
      (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))) p0280 p0358
  have p0360 := @gNotnot2 syntaxFormula0102
  have p0362 := @g_pm3_2 (.classMem (.cv y) (synCnnc)) syntaxFormula0102
  have p0364 :=
    @gElwpphitvndv (synCtc C) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv y)
  have p0365 := Nominal.mp p0121 p0364
  have p0366 := @gBiimpri syntaxFormula0103 syntaxFormula0104 p0365
  have p0367 :=
    @gSyl6 (.classMem (.cv y) (synCnnc)) syntaxFormula0102 syntaxFormula0104
      syntaxFormula0103 p0362 p0366
  have p0368 := @gSimprd syntaxFormula0001 syntaxFormula0022 syntaxFormula0023 p0057
  have p0369 := @gId (.classEq (.cv n) (.cv q))
  have p0370 := @gEleq1d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) syntaxClass0019 p0369
  have p0371 := @gId (.classEq (.cv n) (.cv q))
  have p0372 :=
    @gBreq2d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) (.cv k) (synCkqrel (synClefin))
      p0371
  have p0373 :=
    @gImbi12d (.classEq (.cv n) (.cv q)) syntaxFormula0020 syntaxFormula0105
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)) p0370 p0372
  have p0374_e00_recanon :
    Nominal.NPrf (.imp (.objEq n q) (synWb syntaxFormula0021 syntaxFormula0106)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWbr, synCop, synCun, synCnin,
          synWnan, synCcompl, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0373
  have p0374 :=
    @gCbvralv syntaxFormula0021 syntaxFormula0106 n q (synCnnc) dv_cache_0060
      dv_cache_0061 dv_cache_0062 dv_cache_0063 p0374_e00_recanon
  have p0375 := @gSylib syntaxFormula0001 syntaxFormula0023 syntaxFormula0107 p0368 p0374
  have p0386 := @gEleq2i syntaxClass0026 syntaxClass0019 (.cv q) p0082
  have p0387 :=
    @gImbi1i syntaxFormula0108 syntaxFormula0105
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)) p0386
  have p0388 := @gRalbii syntaxFormula0109 syntaxFormula0106 q (synCnnc) p0387
  have p0389 :=
    @gSylibr syntaxFormula0001 syntaxFormula0107 syntaxFormula0110 p0375 p0388
  have p0390 := @gId (.classEq (.cv q) (.cv y))
  have p0391 := @gEleq1d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) syntaxClass0026 p0390
  have p0393 :=
    @gBreq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (.cv k) (synCkqrel (synClefin))
      p0390
  have p0394 :=
    @gImbi12d (.classEq (.cv q) (.cv y)) syntaxFormula0108 syntaxFormula0103
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)) p0391 p0393
  have p0395 :=
    @gRspcv syntaxFormula0109 syntaxFormula0111 q (.cv y) (synCnnc) dv_cache_0064
      dv_cache_0061 dv_cache_0065 p0394
  have p0396 :=
    @gSyl5com syntaxFormula0001 syntaxFormula0110 (.classMem (.cv y) (synCnnc))
      syntaxFormula0111 p0389 p0395
  have p0397 :=
    @gA1dd syntaxFormula0001 (.classMem (.cv y) (synCnnc)) syntaxFormula0111
      syntaxFormula0102 p0396
  have p0398 :=
    Nominal.ax2 syntaxFormula0102 syntaxFormula0103
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0399 :=
    @gSyl6 syntaxFormula0001 (.classMem (.cv y) (synCnnc))
      (.imp syntaxFormula0102 syntaxFormula0111)
      (.imp syntaxFormula0112 syntaxFormula0113) p0397 p0398
  have p0400 :=
    @gMpdi syntaxFormula0001 (.classMem (.cv y) (synCnnc)) syntaxFormula0112
      syntaxFormula0113 p0367 p0399
  have p0401 :=
    @gSyl5 syntaxFormula0064 (.classMem (.cv y) (synCnnc)) syntaxFormula0001
      syntaxFormula0113 p0182 p0400
  have p0402 :=
    @gSyl7 syntaxFormula0115 syntaxFormula0102 syntaxFormula0001 syntaxFormula0064
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)) p0360 p0401
  have p0403 := @gNotnot1 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0404 :=
    @gSyl8 syntaxFormula0001 syntaxFormula0064 syntaxFormula0115
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))) p0402 p0403
  have p0405 :=
    Nominal.ax3 syntaxFormula0114
      (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
  have p0406 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0064
      (.imp syntaxFormula0115 (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))))
      (.imp (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))) syntaxFormula0114)
      p0404 p0405
  have p0407 :=
    @gMpdd syntaxFormula0001 syntaxFormula0064
      (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))) syntaxFormula0114 p0359
      p0406
  have p0416 :=
    @gWpporbithwcldmndv (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) q dv_cache_0066 dv_cache_0067 p0084
      p0119 p0120 p0116
  have p0417 := @gHwcardstcclndv C
  have p0418 := Nominal.mp hyp_wppstopfixedhitcontrgrowfixdndv_3 p0417
  have p0419 :=
    @gA1i (.classMem (synCtc C) (synChwcards (synCvv))) syntaxFormula0118 p0418
  have p0420 := @gSimpr (.classMem (.cv q) (synCnnc)) syntaxFormula0117
  have p0421 :=
    @gJca syntaxFormula0118 (.classMem (synCtc C) (synChwcards (synCvv)))
      syntaxFormula0117 p0419 p0420
  have p0422 := @gHwcardslecconnexndv (synCtc C) syntaxClass0116
  have p0423 :=
    @gSyl syntaxFormula0118
      (synWa (.classMem (synCtc C) (synChwcards (synCvv))) syntaxFormula0117)
      syntaxFormula0121 p0421 p0422
  have p0424 := @gNotnot syntaxFormula0119
  have p0425 := @gBiimpi syntaxFormula0119 (.neg syntaxFormula0122) p0424
  have p0426 := @gPm221 syntaxFormula0122 syntaxFormula0120
  have p0427 :=
    @gSyl syntaxFormula0119 (.neg syntaxFormula0122) syntaxFormula0123 p0425 p0426
  have p0428 := @gId syntaxFormula0120
  have p0429 := @gA1d syntaxFormula0120 syntaxFormula0120 syntaxFormula0122 p0428
  have p0430 := @gJaoi syntaxFormula0119 syntaxFormula0123 syntaxFormula0120 p0427 p0429
  have p0431 := @gSyl syntaxFormula0118 syntaxFormula0121 syntaxFormula0123 p0423 p0430
  have p0432 := @gRalimiaa syntaxFormula0117 syntaxFormula0123 q (synCnnc) p0431
  have p0433 := Nominal.mp p0416 p0432
  have p0435 := @gFveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) syntaxClass0028 p0390
  have p0436 :=
    @gBreq2d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088 (synCtc C)
      (synClec) p0435
  have p0437 :=
    @gNotbid (.classEq (.cv q) (.cv y)) syntaxFormula0119 syntaxFormula0102 p0436
  have p0440 :=
    @gBreq1d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088 (synCtc C)
      (synClec) p0435
  have p0441 :=
    @gImbi12d (.classEq (.cv q) (.cv y)) syntaxFormula0122 syntaxFormula0114
      syntaxFormula0120 syntaxFormula0124 p0437 p0440
  have p0442 :=
    @gRspcv syntaxFormula0123 syntaxFormula0125 q (.cv y) (synCnnc) dv_cache_0064
      dv_cache_0061 dv_cache_0068 p0441
  have p0443 :=
    @gMpi (.classMem (.cv y) (synCnnc)) (synWral q (synCnnc) syntaxFormula0123)
      syntaxFormula0125 p0433 p0442
  have p0444 :=
    @gSyl syntaxFormula0064 (.classMem (.cv y) (synCnnc)) syntaxFormula0125 p0182 p0443
  have p0445 :=
    @gSylcom syntaxFormula0001 syntaxFormula0064 syntaxFormula0114 syntaxFormula0124
      p0407 p0444
  have p0454 := @gA1i syntaxFormula0126 (.classMem (.cv q) (synCnnc)) p0121
  have p0455 := @gId (.classMem (.cv q) (synCnnc))
  have p0456 :=
    @gJca (.classMem (.cv q) (synCnnc)) syntaxFormula0126 (.classMem (.cv q) (synCnnc))
      p0454 p0455
  have p0457 :=
    @gFrecdomfv (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv q)
  have p0458 :=
    @gSyl (.classMem (.cv q) (synCnnc))
      (synWa syntaxFormula0126 (.classMem (.cv q) (synCnnc))) syntaxFormula0127 p0456
      p0457
  have p0460 :=
    @gEleq2i (synCdm (synCwppstopstep F (synCtc C))) (synChwcards (synCvv))
      syntaxClass0116 p0116
  have p0461 := @gBiimpi syntaxFormula0127 syntaxFormula0117 p0460
  have p0462 :=
    @gSyl (.classMem (.cv q) (synCnnc)) syntaxFormula0127 syntaxFormula0117 p0458 p0461
  have p0463 :=
    @gWppstopstepsamebelowdndv y C F p dv_cache_0069 dv_cache_0070 dv_cache_0071
      hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
      hyp_wppstopfixedhitcontrgrowfixdndv_3 hyp_wppstopfixedhitcontrgrowfixdndv_4
      hyp_wppstopfixedhitcontrgrowfixdndv_5
  have p0464 := @gRgen syntaxFormula0129 y (synChwcards (synCvv)) p0463
  have p0465 := @gId syntaxFormula0130
  have p0466 :=
    @gBreq1d syntaxFormula0130 (.cv y) syntaxClass0116 (synCtc C) (synClec) p0465
  have p0468 :=
    @gFveq2d syntaxFormula0130 (.cv y) syntaxClass0116 (synCwppstopstep F C) p0465
  have p0470 :=
    @gFveq2d syntaxFormula0130 (.cv y) syntaxClass0116 (synCwppstopstep F (synCtc C))
      p0465
  have p0471 :=
    @gEqeq12d syntaxFormula0130 (synCfv (synCwppstopstep F C) (.cv y)) syntaxClass0131
      (synCfv (synCwppstopstep F (synCtc C)) (.cv y)) syntaxClass0132 p0468 p0470
  have p0472 :=
    @gImbi12d syntaxFormula0130 (synWbr (.cv y) (synClec) (synCtc C))
      syntaxFormula0120 syntaxFormula0128 syntaxFormula0133 p0466 p0471
  have p0473 :=
    @gRspcv syntaxFormula0129 syntaxFormula0134 y syntaxClass0116
      (synChwcards (synCvv)) dv_cache_0072 dv_cache_0073 dv_cache_0074 p0472
  have p0474 :=
    @gMpi syntaxFormula0117 (synWral y (synChwcards (synCvv)) syntaxFormula0129)
      syntaxFormula0134 p0464 p0473
  have p0475 :=
    @gSyl (.classMem (.cv q) (synCnnc)) syntaxFormula0117 syntaxFormula0134 p0462 p0474
  have p0476 := @gRgen syntaxFormula0134 q (synCnnc) p0475
  have p0482 :=
    @gFveq2d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088
      (synCwppstopstep F C) p0435
  have p0485 :=
    @gFveq2d (.classEq (.cv q) (.cv y)) syntaxClass0116 syntaxClass0088
      (synCwppstopstep F (synCtc C)) p0435
  have p0486 :=
    @gEqeq12d (.classEq (.cv q) (.cv y)) syntaxClass0131 syntaxClass0090 syntaxClass0132
      syntaxClass0135 p0482 p0485
  have p0487 :=
    @gImbi12d (.classEq (.cv q) (.cv y)) syntaxFormula0120 syntaxFormula0124
      syntaxFormula0133 syntaxFormula0136 p0440 p0486
  have p0488 :=
    @gRspcv syntaxFormula0134 syntaxFormula0137 q (.cv y) (synCnnc) dv_cache_0064
      dv_cache_0061 dv_cache_0075 p0487
  have p0489 :=
    @gMpi (.classMem (.cv y) (synCnnc)) (synWral q (synCnnc) syntaxFormula0134)
      syntaxFormula0137 p0476 p0488
  have p0490 :=
    @gSyl syntaxFormula0064 (.classMem (.cv y) (synCnnc)) syntaxFormula0137 p0182 p0489
  have p0491 :=
    @gSylcom syntaxFormula0001 syntaxFormula0064 syntaxFormula0124 syntaxFormula0136
      p0445 p0490
  have p0492 :=
    @gSyl5 syntaxFormula0058 syntaxFormula0064 syntaxFormula0001 syntaxFormula0136 p0180
      p0491
  have p0493 := @gEqeq2 syntaxClass0090 syntaxClass0135 syntaxClass0059
  have p0494 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0136 syntaxFormula0139 p0492
      p0493
  have p0495 := @gBi1 syntaxFormula0092 syntaxFormula0138
  have p0496 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0058 syntaxFormula0139
      (.imp syntaxFormula0092 syntaxFormula0138) p0494 p0495
  have p0497 :=
    @gMpdd syntaxFormula0001 syntaxFormula0058 syntaxFormula0092 syntaxFormula0138 p0274
      p0496
  have p0499 := @gA1i syntaxFormula0126 syntaxFormula0058 p0121
  have p0501 :=
    @gJca syntaxFormula0058 syntaxFormula0126 (.classMem (.cv y) (synCnnc)) p0499 p0171
  have p0502 :=
    @gWpporbitsucndv (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv y)
  have p0503 :=
    @gSyl syntaxFormula0058 (synWa syntaxFormula0126 (.classMem (.cv y) (synCnnc)))
      (.classEq syntaxClass0140 syntaxClass0135) p0501 p0502
  have p0504 := @gEqcomd syntaxFormula0058 syntaxClass0140 syntaxClass0135 p0503
  have p0505 :=
    @gEqeq2d syntaxFormula0058 syntaxClass0135 syntaxClass0140 syntaxClass0059 p0504
  have p0506 :=
    @gMpbidi syntaxFormula0058 syntaxFormula0138 syntaxFormula0141 syntaxFormula0001
      p0497 p0505
  have p0507 :=
    @gN3expd syntaxFormula0001 (.classMem (.cv y) (synCnnc)) syntaxFormula0056
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      syntaxFormula0141 p0506
  have p0509 :=
    @gWppfrecprefixeqvalndv (synCplc (.cv y) (synC1c)) k (synCwppstopstep F C)
      (synCwppstopstep F (synCtc C)) (synCif (.classEq I (synCtc I)) I (synC0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0510 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (synWb syntaxFormula0142 syntaxFormula0143) p0226 p0509
  have p0511 :=
    @gBiimprd (.classMem (.cv y) (synCnnc)) syntaxFormula0142 syntaxFormula0143 p0510
  have p0512 :=
    @gA1d (.classMem (.cv y) (synCnnc)) (.imp syntaxFormula0143 syntaxFormula0142)
      syntaxFormula0056 p0511
  have p0513 :=
    @gA2d (.classMem (.cv y) (synCnnc)) syntaxFormula0056 syntaxFormula0143
      syntaxFormula0142 p0512
  have p0514 :=
    @gSylcom syntaxFormula0001 (.classMem (.cv y) (synCnnc))
      (.imp syntaxFormula0056 syntaxFormula0143) syntaxFormula0144 p0507 p0513
  have p0515 :=
    @gAdantrd syntaxFormula0001 (.classMem (.cv y) (synCnnc)) syntaxFormula0144 synWtru
      p0514
  have p0516 :=
    @gSyl7bi syntaxFormula0145 syntaxFormula0056 syntaxFormula0001
      (synWa (.classMem (.cv y) (synCnnc)) synWtru) syntaxFormula0142 p0168 p0515
  have p0517 := @gN1cex
  have p0518 := @gAddcex (.cv y) (synC1c) p0165 p0517
  have p0519 := @gId (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
  have p0520 :=
    @gEleq1d (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.cv x)
      (synCplc (.cv y) (synC1c)) syntaxClass0045 p0519
  have p0521 :=
    @gElab syntaxFormula0046 syntaxFormula0142 x (synCplc (.cv y) (synC1c))
      dv_cache_0055 dv_cache_0076 p0518 p0520
  have p0522 := @gBiimpri syntaxFormula0146 syntaxFormula0142 p0521
  have p0523 :=
    @gSyl8 syntaxFormula0001 (synWa (.classMem (.cv y) (synCnnc)) synWtru)
      syntaxFormula0145 syntaxFormula0142 syntaxFormula0146 p0516 p0522
  have p0524 :=
    @gAncomsd syntaxFormula0001 (.classMem (.cv y) (synCnnc)) synWtru syntaxFormula0147
      p0523
  have p0525 :=
    @gExp3a syntaxFormula0001 synWtru (.classMem (.cv y) (synCnnc)) syntaxFormula0147
      p0524
  have p0526 :=
    @gRalrimdv syntaxFormula0001 synWtru syntaxFormula0147 y (synCnnc) dv_cache_0077
      dv_cache_0078 p0525
  have p0527 := @g_pm3_2 syntaxFormula0148 syntaxFormula0149
  have p0528 :=
    @gSyl9 syntaxFormula0001 synWtru syntaxFormula0149 syntaxFormula0148
      syntaxFormula0150 p0526 p0527
  have p0529 :=
    @gSyl5 synWtru syntaxFormula0148 syntaxFormula0001 (.imp synWtru syntaxFormula0150)
      p0164 p0528
  have p0530 := @gPm243d syntaxFormula0001 synWtru syntaxFormula0150 p0529
  have p0531 := (Nominal.biimpRefl syntaxFormula0151)
  have p0532 :=
    @gSyl6ibr syntaxFormula0001 synWtru syntaxFormula0150 syntaxFormula0151 p0530 p0531
  have p0533 := @gPeano5 y syntaxClass0047 (synCvv) dv_cache_0079
  have p0534 :=
    @gSyl6 syntaxFormula0001 synWtru syntaxFormula0151 syntaxFormula0152 p0532 p0533
  have p0535 := @gSsel (synCnnc) syntaxClass0047 (.cv n)
  have p0536 :=
    @gSyl6 syntaxFormula0001 synWtru syntaxFormula0152
      (.imp (.classMem (.cv n) (synCnnc)) syntaxFormula0153) p0534 p0535
  have p0537 :=
    @gCom23 syntaxFormula0001 synWtru (.classMem (.cv n) (synCnnc)) syntaxFormula0153
      p0536
  have p0538 :=
    @gImp3a syntaxFormula0001 (.classMem (.cv n) (synCnnc)) synWtru syntaxFormula0153
      p0537
  have p0539 := @gId (.classEq (.cv x) (.cv n))
  have p0540 := @gEleq1d (.classEq (.cv x) (.cv n)) (.cv x) (.cv n) syntaxClass0045 p0539
  have p0541 :=
    @gElabg syntaxFormula0046 syntaxFormula0154 x (.cv n) (synCnnc) dv_cache_0080
      dv_cache_0081 p0540
  have p0542 :=
    @gAdantr (.classMem (.cv n) (synCnnc)) (synWb syntaxFormula0153 syntaxFormula0154)
      synWtru p0541
  have p0543 :=
    @gMpbidi (synWa (.classMem (.cv n) (synCnnc)) synWtru) syntaxFormula0153
      syntaxFormula0154 syntaxFormula0001 p0538 p0542
  have p0544 :=
    @gMpan2i syntaxFormula0001 (.classMem (.cv n) (synCnnc)) synWtru syntaxFormula0154
      p0133 p0543
  have p0545 :=
    @gWppfrecprefixeqvalndv (.cv n) k (synCwppstopstep F C)
      (synCwppstopstep F (synCtc C)) (synCif (.classEq I (synCtc I)) I (synC0c))
      p0134 p0143 p0144 p0084 p0119 p0120
  have p0546 :=
    @gMpbidi (.classMem (.cv n) (synCnnc)) syntaxFormula0154 syntaxFormula0158
      syntaxFormula0001 p0544 p0545
  have p0547 :=
    @gRalrimiv syntaxFormula0001 syntaxFormula0158 n (synCnnc) dv_cache_0082 p0546
  have p0548 := @gId (.classEq (.cv n) (.cv k))
  have p0549 :=
    @gBreq1d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (.cv k) (synCkqrel (synClefin))
      p0548
  have p0551 := @gFveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) syntaxClass0051 p0548
  have p0553 := @gFveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) syntaxClass0028 p0548
  have p0554 :=
    @gEqeq12d (.classEq (.cv n) (.cv k)) syntaxClass0155 syntaxClass0159 syntaxClass0156
      syntaxClass0043 p0551 p0553
  have p0555 :=
    @gImbi12d (.classEq (.cv n) (.cv k))
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0157
      syntaxFormula0160 p0549 p0554
  have p0556 :=
    @gRspcv syntaxFormula0158 syntaxFormula0161 n (.cv k) (synCnnc) dv_cache_0083
      dv_cache_0060 dv_cache_0084 p0555
  have p0557 :=
    @gSyl5com syntaxFormula0001 (synWral n (synCnnc) syntaxFormula0158)
      (.classMem (.cv k) (synCnnc)) syntaxFormula0161 p0547 p0556
  have p0558 :=
    @gMpd syntaxFormula0001 (.classMem (.cv k) (synCnnc)) syntaxFormula0161 p0053 p0557
  have p0559 :=
    @gMpd syntaxFormula0001 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
      syntaxFormula0160 p0132 p0558
  have p0560 := @gEqcomd syntaxFormula0001 syntaxClass0159 syntaxClass0043 p0559
  have p0561 :=
    @gBreq2d syntaxFormula0001 syntaxClass0043 syntaxClass0159 (synCtc C) (synClec)
      p0560
  have p0562 := @gMpbid syntaxFormula0001 syntaxFormula0044 syntaxFormula0162 p0125 p0561
  have p0563 :=
    @gJca syntaxFormula0001 (.classMem (.cv k) (synCnnc)) syntaxFormula0162 p0053 p0562
  have p0565 :=
    @gElwpphitvndv (synCtc C) (synCwppstopstep F C)
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv k)
  have p0566 := Nominal.mp p0145 p0565
  have p0567 :=
    @gSylibr syntaxFormula0001 (synWa (.classMem (.cv k) (synCnnc)) syntaxFormula0162)
      syntaxFormula0164 p0563 p0566
  have p0568 := @gJca syntaxFormula0001 syntaxFormula0164 syntaxFormula0165 p0567 p0560
  have p0569 := @gSimpl syntaxFormula0164 syntaxFormula0165
  have p0570 :=
    @gSyl syntaxFormula0001 (synWa syntaxFormula0164 syntaxFormula0165)
      syntaxFormula0164 p0568 p0569
  have p0572 := @gWppweconnex (synCnnc) (synCkqrel (synClefin))
  have p0573 := Nominal.mp p0126 p0572
  have p0574 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc)) syntaxFormula0167
      p0573
  have p0575 := @gBrex (synCkqrel (synClefin)) (synCnnc) (synCconnex)
  have p0576 := @gBreq (.cv x) (.cv y) (.cv r) (synCkqrel (synClefin))
  have p0577 := @gBreq (.cv y) (.cv x) (.cv r) (synCkqrel (synClefin))
  have p0578 :=
    @gOrbi12d (.classEq (.cv r) (synCkqrel (synClefin)))
      (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (.cv r) (.cv x))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)) p0576 p0577
  have p0579 :=
    @gN2ralbidv (.classEq (.cv r) (synCkqrel (synClefin)))
      (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      syntaxFormula0168 x y (.cv a) (.cv a) dv_cache_0022 dv_cache_0085 p0578
  have p0580 :=
    @gRaleq syntaxFormula0168 y (.cv a) (synCnnc) dv_cache_0086 dv_cache_0087
  have p0581 :=
    @gRaleqbi1dv (synWral y (.cv a) syntaxFormula0168) syntaxFormula0169 x (.cv a)
      (synCnnc) dv_cache_0088 dv_cache_0029 p0580
  have p0582 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfConnex x y r a
      dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0034 dv_cache_0092 dv_cache_0093
  have p0583 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      (synWral x (.cv a) (synWral y (.cv a) syntaxFormula0168)) syntaxFormula0170 r a
      (synCkqrel (synClefin)) (synCnnc) (synCvv) (synCvv) (synCconnex) dv_cache_0040
      dv_cache_0094 dv_cache_0042 dv_cache_0027 dv_cache_0095 dv_cache_0096 dv_cache_0035
      p0579 p0581 p0582
  have p0584 :=
    @gSyl (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc))
      (synWa (.classMem (synCkqrel (synClefin)) (synCvv)) (.classMem (synCnnc) (synCvv)))
      (synWb (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc)) syntaxFormula0170)
      p0575 p0583
  have p0585 :=
    @gIbi (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc)) syntaxFormula0170
      p0584
  have p0586 := @gSimpl (.classMem (.cv n) (synCnnc)) syntaxFormula0166
  have p0587 :=
    @gA1d syntaxFormula0001 (.classMem (.cv k) (synCnnc)) syntaxFormula0167 p0053
  have p0588 := @gBreq1 (.cv x) (.cv n) (.cv y) (synCkqrel (synClefin))
  have p0589 := @gBreq2 (.cv x) (.cv n) (.cv y) (synCkqrel (synClefin))
  have p0590 :=
    @gOrbi12d (.classEq (.cv x) (.cv n))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv n)) p0588 p0589
  have p0591 := @gBreq2 (.cv y) (.cv k) (.cv n) (synCkqrel (synClefin))
  have p0592 := @gBreq1 (.cv y) (.cv k) (.cv n) (synCkqrel (synClefin))
  have p0593 :=
    @gOrbi12d (.classEq (.cv y) (.cv k))
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0591 p0592
  have p0594 :=
    @gRspc2v syntaxFormula0168 syntaxFormula0171
      (synWo (synWbr (.cv n) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv n)))
      x y (.cv n) (.cv k) (synCnnc) (synCnnc) dv_cache_0080 dv_cache_0097 dv_cache_0098
      dv_cache_0029 dv_cache_0029 dv_cache_0087 dv_cache_0099 dv_cache_0100 dv_cache_0093
      p0590 p0593
  have p0595 :=
    @gEx (.classMem (.cv n) (synCnnc)) (.classMem (.cv k) (synCnnc)) syntaxFormula0172
      p0594
  have p0596 :=
    @gSyl9 syntaxFormula0001 syntaxFormula0167 (.classMem (.cv k) (synCnnc))
      (.classMem (.cv n) (synCnnc)) syntaxFormula0172 p0587 p0595
  have p0597 :=
    @gSyl5 syntaxFormula0167 (.classMem (.cv n) (synCnnc)) syntaxFormula0001
      (.imp syntaxFormula0167 syntaxFormula0172) p0586 p0596
  have p0598 := @gPm243d syntaxFormula0001 syntaxFormula0167 syntaxFormula0172 p0597
  have p0599 :=
    @gSyl7 (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc)) syntaxFormula0170
      syntaxFormula0001 syntaxFormula0167 syntaxFormula0171 p0585 p0598
  have p0600 :=
    @gMpdi syntaxFormula0001 syntaxFormula0167
      (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc)) syntaxFormula0171 p0574
      p0599
  have p0601 :=
    @gPm253 (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
  have p0602 := @gId (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
  have p0603 :=
    @gA1i
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
      syntaxFormula0167 p0602
  have p0604 :=
    @gCom12 syntaxFormula0167 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0603
  have p0605 :=
    @gSyl6 syntaxFormula0171 (.neg (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) syntaxFormula0173 p0601 p0604
  have p0606 :=
    @gCon1d syntaxFormula0171 (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      syntaxFormula0173 p0605
  have p0607 :=
    @gSimpl syntaxFormula0167 (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
  have p0609 :=
    @gSyl syntaxFormula0174 syntaxFormula0167 (.classMem (.cv n) (synCnnc)) p0607 p0586
  have p0611 := @gSimpr (.classMem (.cv n) (synCnnc)) syntaxFormula0166
  have p0612 := @gSyl syntaxFormula0174 syntaxFormula0167 syntaxFormula0166 p0607 p0611
  have p0620 :=
    @gElwpphitvndv (synCtc C) (synCwppstopstep F C)
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv n)
  have p0621 := Nominal.mp p0145 p0620
  have p0622 := @gBiimpi syntaxFormula0166 syntaxFormula0176 p0621
  have p0623 := @gSyl syntaxFormula0174 syntaxFormula0166 syntaxFormula0176 p0612 p0622
  have p0624 := @gSimpr (.classMem (.cv n) (synCnnc)) syntaxFormula0175
  have p0625 := @gSyl syntaxFormula0174 syntaxFormula0176 syntaxFormula0175 p0623 p0624
  have p0626 :=
    @gSimpr syntaxFormula0167 (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
  have p0630 :=
    @gSyl5 syntaxFormula0174 (.classMem (.cv n) (synCnnc)) syntaxFormula0001
      syntaxFormula0158 p0609 p0546
  have p0631 :=
    @gMpdi syntaxFormula0001 syntaxFormula0174
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0157 p0626 p0630
  have p0632 := @gBreq2 syntaxClass0155 syntaxClass0156 (synCtc C) (synClec)
  have p0633 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0174 syntaxFormula0157 syntaxFormula0178 p0631
      p0632
  have p0634 := @gBi1 syntaxFormula0175 syntaxFormula0177
  have p0635 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0174 syntaxFormula0178
      (.imp syntaxFormula0175 syntaxFormula0177) p0633 p0634
  have p0636 :=
    @gMpdi syntaxFormula0001 syntaxFormula0174 syntaxFormula0175 syntaxFormula0177 p0625
      p0635
  have p0637 := @g_pm3_2 (.classMem (.cv n) (synCnnc)) syntaxFormula0177
  have p0638 :=
    @gSyl9 syntaxFormula0001 syntaxFormula0174 syntaxFormula0177
      (.classMem (.cv n) (synCnnc)) syntaxFormula0179 p0636 p0637
  have p0639 :=
    @gSyl5 syntaxFormula0174 (.classMem (.cv n) (synCnnc)) syntaxFormula0001
      (.imp syntaxFormula0174 syntaxFormula0179) p0609 p0638
  have p0640 := @gPm243d syntaxFormula0001 syntaxFormula0174 syntaxFormula0179 p0639
  have p0648 :=
    @gElwpphitvndv (synCtc C) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv n)
  have p0649 := Nominal.mp p0121 p0648
  have p0650 := @gBiimpri syntaxFormula0180 syntaxFormula0179 p0649
  have p0651 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0174 syntaxFormula0179 syntaxFormula0180 p0640
      p0650
  have p0655 := @gId (.classEq (.cv q) (.cv n))
  have p0656 := @gEleq1d (.classEq (.cv q) (.cv n)) (.cv q) (.cv n) syntaxClass0026 p0655
  have p0658 :=
    @gBreq2d (.classEq (.cv q) (.cv n)) (.cv q) (.cv n) (.cv k) (synCkqrel (synClefin))
      p0655
  have p0659 :=
    @gImbi12d (.classEq (.cv q) (.cv n)) syntaxFormula0108 syntaxFormula0180
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0656 p0658
  have p0660 :=
    @gRspcv syntaxFormula0109 syntaxFormula0181 q (.cv n) (synCnnc) dv_cache_0101
      dv_cache_0061 dv_cache_0102 p0659
  have p0661 :=
    @gSyl5com syntaxFormula0001 syntaxFormula0110 (.classMem (.cv n) (synCnnc))
      syntaxFormula0181 p0389 p0660
  have p0662 :=
    @gSyl5 syntaxFormula0174 (.classMem (.cv n) (synCnnc)) syntaxFormula0001
      syntaxFormula0181 p0609 p0661
  have p0663 :=
    @gMpdd syntaxFormula0001 syntaxFormula0174 syntaxFormula0180
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0651 p0662
  have p0664 :=
    @gExp3a syntaxFormula0001 syntaxFormula0167
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0663
  have p0665 :=
    @gCom23 syntaxFormula0001 syntaxFormula0167
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0664
  have p0666 := @gA1d syntaxFormula0001 syntaxFormula0182 syntaxFormula0171 p0665
  have p0667 :=
    @gA1dd syntaxFormula0001 syntaxFormula0171 syntaxFormula0182 syntaxFormula0183 p0666
  have p0668 :=
    Nominal.ax2 syntaxFormula0183 (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      syntaxFormula0173
  have p0669 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0171 (.imp syntaxFormula0183 syntaxFormula0182)
      (.imp syntaxFormula0184 syntaxFormula0185) p0667 p0668
  have p0670 :=
    @gMpdi syntaxFormula0001 syntaxFormula0171 syntaxFormula0184 syntaxFormula0185 p0606
      p0669
  have p0671 := @gPm218 syntaxFormula0173
  have p0672 :=
    @gSyl6 syntaxFormula0001 syntaxFormula0171 syntaxFormula0185 syntaxFormula0173 p0670
      p0671
  have p0673 :=
    @gCom23 syntaxFormula0001 syntaxFormula0171 syntaxFormula0167
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0672
  have p0674 :=
    @gMpdd syntaxFormula0001 syntaxFormula0167 syntaxFormula0171
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0600 p0673
  have p0675 :=
    @gExp3a syntaxFormula0001 (.classMem (.cv n) (synCnnc)) syntaxFormula0166
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)) p0674
  have p0676 :=
    @gRalrimiv syntaxFormula0001 syntaxFormula0186 n (synCnnc) dv_cache_0082 p0675
  have p0681 := @gFveq1i (.cv k) syntaxClass0028 syntaxClass0029 p0077
  have p0682 := @gEqcomi syntaxClass0043 syntaxClass0187 p0681
  have p0683 :=
    @gSyl5eq syntaxFormula0001 syntaxClass0187 syntaxClass0043 syntaxClass0159 p0682
      p0560
  have p0684 :=
    @gN3jca syntaxFormula0001 syntaxFormula0164 syntaxFormula0188 syntaxFormula0189
      p0570 p0676 p0683
  have p0685 :=
    @gSimp1d syntaxFormula0001 syntaxFormula0164 syntaxFormula0188 syntaxFormula0189
      p0684
  have p0686 := @gJca syntaxFormula0001 syntaxFormula0009 syntaxFormula0164 p0056 p0685
  have p0687 :=
    @gJca syntaxFormula0001
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      syntaxFormula0190 p0054 p0686
  have p0688 := @gSimprd syntaxFormula0001 syntaxFormula0009 syntaxFormula0010 p0055
  have p0689 := @gJca syntaxFormula0001 syntaxFormula0010 syntaxFormula0188 p0688 p0676
  have p0690 := @gJca syntaxFormula0001 syntaxFormula0191 syntaxFormula0192 p0687 p0689
  have p0698 := @gHwcardssnc (synCvv)
  have p0699 :=
    @gSselii (synChwcards (synCvv)) (synCncs) C p0698
      hyp_wppstopfixedhitcontrgrowfixdndv_3
  have p0700 := @gTccl C
  have p0701 := Nominal.mp p0699 p0700
  have p0702 :=
    @gN3pm32i (.classMem (synCtc C) (synCncs)) (.classMem C (synCncs))
      (synWbr (synCtc C) (synClec) C) p0701 p0699 hyp_wppstopfixedhitcontrgrowfixdndv_4
  have p0703 := @gPm32i syntaxFormula0057 syntaxFormula0193 p0145 p0702
  have p0711 :=
    @gFrecdomfv (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c))
      (.cv n)
  have p0712 :=
    @gMpan syntaxFormula0057 (.classMem (.cv n) (synCnnc)) syntaxFormula0194 p0145 p0711
  have p0714 :=
    @gEleq2i (synCdm (synCwppstopstep F C)) (synChwcards (synCvv)) syntaxClass0155
      p0140
  have p0715 := @gBiimpi syntaxFormula0194 syntaxFormula0195 p0714
  have p0716 :=
    @gSyl (.classMem (.cv n) (synCnnc)) syntaxFormula0194 syntaxFormula0195 p0712 p0715
  have p0718 := @gSseli (synChwcards (synCvv)) (synCncs) syntaxClass0155 p0698
  have p0719 :=
    @gSyl (.classMem (.cv n) (synCnnc)) syntaxFormula0195 syntaxFormula0196 p0716 p0718
  have p0720 := @gRgen syntaxFormula0196 n (synCnnc) p0719
  have p0721 := @gId (.classEq (.cv n) (.cv q))
  have p0722 := @gFveq2d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) syntaxClass0051 p0721
  have p0723 :=
    @gEleq1d (.classEq (.cv n) (.cv q)) syntaxClass0155 syntaxClass0197 (synCncs) p0722
  have p0724_e00_recanon :
    Nominal.NPrf (.imp (.objEq n q) (synWb syntaxFormula0196 syntaxFormula0198)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa, synCsn, synCop, synCun, synCnin, synWnan,
          synCcompl, synWrex, synCphi, synCin, synCopab, synCvv, synCplc, synC1c,
          synCif, synWo, synC0c, synCncs, synCqs, synCen]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0723
  have p0724 :=
    @gCbvralv syntaxFormula0196 syntaxFormula0198 n q (synCnnc) dv_cache_0060
      dv_cache_0061 dv_cache_0103 dv_cache_0104 p0724_e00_recanon
  have p0725 :=
    @gMpbi (synWral n (synCnnc) syntaxFormula0196) syntaxFormula0199 p0720 p0724
  have p0726 := @gPm32i syntaxFormula0200 syntaxFormula0199 p0703 p0725
  have p0727 := @gJctir syntaxFormula0001 syntaxFormula0201 syntaxFormula0202 p0690 p0726
  have p0729 :=
    @gSimpr (synWa (.classEq I (synCtc I)) ps) (synWa (.classEq I (synCtc I)) ch)
  have p0730 :=
    @gSyl syntaxFormula0001 syntaxFormula0000 (synWa (.classEq I (synCtc I)) ch) p0035
      p0729
  have p0731 := @gSimpr (.classEq I (synCtc I)) ch
  have p0732 :=
    @gSyl (synWa (.classEq I (synCtc I)) ch) ch syntaxFormula0204 p0731
      hyp_wppstopfixedhitcontrgrowfixdndv_12
  have p0733 :=
    @gSyl syntaxFormula0001 (synWa (.classEq I (synCtc I)) ch) syntaxFormula0204 p0730
      p0732
  have p0741 :=
    @gFrecdomfv (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c))
      (.cv r)
  have p0742 :=
    @gMpan syntaxFormula0057 (.classMem (.cv r) (synCnnc))
      (.classMem syntaxClass0205 (synCdm (synCwppstopstep F C))) p0145 p0741
  have p0743 := @gSimpr (.classMem (.cv r) (synCnnc)) syntaxFormula0206
  have p0744 :=
    @gBreq2d syntaxFormula0207 (.cv y) syntaxClass0205 (synCtc C) (synClec) p0743
  have p0746 :=
    @gFveq2d syntaxFormula0207 (.cv y) syntaxClass0205 (synCwppstopstep F C) p0743
  have p0747 :=
    @gBreq2d syntaxFormula0207 (synCfv (synCwppstopstep F C) (.cv y)) syntaxClass0208 C
      (synClec) p0746
  have p0748 :=
    @gImbi12d syntaxFormula0207 (synWbr (synCtc C) (synClec) (.cv y))
      syntaxFormula0209 (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))
      syntaxFormula0210 p0744 p0747
  have p0749 :=
    @gRspcdv (.classMem (.cv r) (synCnnc)) syntaxFormula0203 syntaxFormula0211 y
      syntaxClass0205 (synCdm (synCwppstopstep F C)) dv_cache_0105 dv_cache_0106
      dv_cache_0107 dv_cache_0108 p0742 p0748
  have p0750 :=
    @gSyl5com syntaxFormula0001 syntaxFormula0204 (.classMem (.cv r) (synCnnc))
      syntaxFormula0211 p0733 p0749
  have p0751 :=
    @gRalrimiv syntaxFormula0001 syntaxFormula0211 r (synCnnc) dv_cache_0109 p0750
  have p0752 := (Nominal.biimpRefl syntaxFormula0213)
  have p0753 :=
    @gSylanbrc syntaxFormula0001 (synWa syntaxFormula0201 syntaxFormula0202)
      syntaxFormula0212 syntaxFormula0213 p0727 p0751 p0752
  have p0754 :=
    @gWpphitminadjndv k m n (synCwppstopstep F C) C
      (synCif (.classEq I (synCtc I)) I (synC0c)) (synCtc C) r q dv_cache_0110
      dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116
      dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122
      dv_cache_0067 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127
      dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133
  have p0755 :=
    @gSyl syntaxFormula0001 syntaxFormula0213
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0753 p0754
  have p0756 := @gA1i (.classMem C (synCncs)) syntaxFormula0214 p0699
  have p0757 := @gSimpl (.classMem (.cv n) (synCnnc)) syntaxFormula0196
  have p0758 :=
    @gJca syntaxFormula0214 (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc)) p0756
      p0757
  have p0759 := @gSimpr (.classMem (.cv n) (synCnnc)) syntaxFormula0196
  have p0760 :=
    @gJca syntaxFormula0214
      (synWa (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc))) syntaxFormula0196
      p0758 p0759
  have p0762 :=
    @gElwpphitvndv C (synCwppstopstep F C)
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv n)
  have p0763 := Nominal.mp p0145 p0762
  have p0764 :=
    @gA1i
      (synWb syntaxFormula0007 (synWa (.classMem (.cv n) (synCnnc)) syntaxFormula0215))
      syntaxFormula0216 p0763
  have p0765 :=
    @gSimpl (synWa (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc)))
      syntaxFormula0196
  have p0766 := @gSimpr (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc))
  have p0767 :=
    @gSyl syntaxFormula0216
      (synWa (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc)))
      (.classMem (.cv n) (synCnnc)) p0765 p0766
  have p0771 := @gNntccl (.cv n)
  have p0772 :=
    @gSyl syntaxFormula0216 (.classMem (.cv n) (synCnnc))
      (.classMem (synCtc (.cv n)) (synCnnc)) p0767 p0771
  have p0773 :=
    @gN2thd syntaxFormula0216 (.classMem (.cv n) (synCnnc))
      (.classMem (synCtc (.cv n)) (synCnnc)) p0767 p0772
  have p0775 := @gSimpl (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc))
  have p0776 :=
    @gSyl syntaxFormula0216
      (synWa (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc)))
      (.classMem C (synCncs)) p0765 p0775
  have p0777 :=
    @gSimpr (synWa (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc)))
      syntaxFormula0196
  have p0778 :=
    @gJca syntaxFormula0216 (.classMem C (synCncs)) syntaxFormula0196 p0776 p0777
  have p0779 := @gTlecg C syntaxClass0155
  have p0780 :=
    @gSyl syntaxFormula0216 (synWa (.classMem C (synCncs)) syntaxFormula0196)
      (synWb syntaxFormula0215 (synWbr (synCtc C) (synClec) syntaxClass0217)) p0778
      p0779
  have p0785 :=
    @gEqeltrri (synCif (.classEq I (synCtc I)) I (synC0c))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synChwcards (synCvv))
      p0074 p0115
  have p0787 :=
    @gEleq2i (synCdm (synCwppstopstep F (synCtc C))) (synChwcards (synCvv))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) p0116
  have p0788 :=
    @gBiimpri
      (.classMem (synCtc (synCif (.classEq I (synCtc I)) I (synC0c)))
        (synCdm (synCwppstopstep F (synCtc C))))
      (.classMem (synCtc (synCif (.classEq I (synCtc I)) I (synC0c)))
        (synChwcards (synCvv)))
      p0787
  have p0789 := Nominal.mp p0785 p0788
  have p0791 :=
    @gFrectchom0 x (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv n) dv_cache_0134 dv_cache_0135
      dv_cache_0136 p0134 p0143 p0144 p0084 p0789 p0120
      hyp_wppstopfixedhitcontrgrowfixdndv_6
  have p0792 :=
    @gSyl syntaxFormula0216 (.classMem (.cv n) (synCnnc))
      (.classEq syntaxClass0217 syntaxClass0218) p0767 p0791
  have p0793 :=
    @gBreq2d syntaxFormula0216 syntaxClass0217 syntaxClass0218 (synCtc C) (synClec)
      p0792
  have p0794 :=
    @gBitrd syntaxFormula0216 syntaxFormula0215
      (synWbr (synCtc C) (synClec) syntaxClass0217) syntaxFormula0219 p0780 p0793
  have p0795 :=
    @gAnbi12d syntaxFormula0216 (.classMem (.cv n) (synCnnc))
      (.classMem (synCtc (.cv n)) (synCnnc)) syntaxFormula0215 syntaxFormula0219 p0773
      p0794
  have p0796 :=
    @gBitrd syntaxFormula0216 syntaxFormula0007
      (synWa (.classMem (.cv n) (synCnnc)) syntaxFormula0215) syntaxFormula0220 p0764
      p0795
  have p0797 :=
    @gN3pm32i (.classMem (synCwppstopstep F (synCtc C)) (synCfuns))
      (.classMem (synCtc (synCif (.classEq I (synCtc I)) I (synC0c)))
        (synCdm (synCwppstopstep F (synCtc C))))
      syntaxFormula0042 p0084 p0789 p0120
  have p0798 :=
    @gElwpphitvndv (synCtc C) (synCwppstopstep F (synCtc C))
      (synCtc (synCif (.classEq I (synCtc I)) I (synC0c))) (synCtc (.cv n))
  have p0799 := Nominal.mp p0797 p0798
  have p0800 :=
    @gA1i (synWb syntaxFormula0221 syntaxFormula0220) syntaxFormula0216 p0799
  have p0801 := @gBicomd syntaxFormula0216 syntaxFormula0221 syntaxFormula0220 p0800
  have p0802 :=
    @gBitrd syntaxFormula0216 syntaxFormula0007 syntaxFormula0220 syntaxFormula0221 p0796
      p0801
  have p0803 := @gSyl syntaxFormula0214 syntaxFormula0216 syntaxFormula0222 p0760 p0802
  have p0804 := @gRalimiaa syntaxFormula0196 syntaxFormula0222 n (synCnnc) p0803
  have p0805 := Nominal.mp p0720 p0804
  have p0806 :=
    @gJctir syntaxFormula0001 (.classMem (.cv m) (synCnnc)) syntaxFormula0223 p0034
      p0805
  have p0807 := @gId (.classEq (.cv n) (.cv m))
  have p0808 := @gEleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) syntaxClass0006 p0807
  have p0809 := @gTceq (.cv n) (.cv m)
  have p0810 :=
    @gEleq1d (.classEq (.cv n) (.cv m)) (synCtc (.cv n)) (synCtc (.cv m))
      syntaxClass0019 p0809
  have p0811 :=
    @gBibi12d (.classEq (.cv n) (.cv m)) syntaxFormula0007 syntaxFormula0009
      syntaxFormula0221 syntaxFormula0224 p0808 p0810
  have p0812 :=
    @gRspcva syntaxFormula0222 syntaxFormula0225 n (.cv m) (synCnnc) dv_cache_0137
      dv_cache_0060 dv_cache_0138 p0811
  have p0813 :=
    @gSyl syntaxFormula0001 (synWa (.classMem (.cv m) (synCnnc)) syntaxFormula0223)
      syntaxFormula0225 p0806 p0812
  have p0814 := @gMpbid syntaxFormula0001 syntaxFormula0009 syntaxFormula0224 p0056 p0813
  have p0815 := @gNntccl (.cv m)
  have p0816 :=
    @gSyl syntaxFormula0001 (.classMem (.cv m) (synCnnc))
      (.classMem (synCtc (.cv m)) (synCnnc)) p0034 p0815
  have p0817 :=
    @gJca syntaxFormula0001 (.classMem (synCtc (.cv m)) (synCnnc)) syntaxFormula0023
      p0816 p0368
  have p0818 := @gId (.classEq (.cv n) (synCtc (.cv m)))
  have p0819 :=
    @gEleq1d (.classEq (.cv n) (synCtc (.cv m))) (.cv n) (synCtc (.cv m))
      syntaxClass0019 p0818
  have p0821 :=
    @gBreq2d (.classEq (.cv n) (synCtc (.cv m))) (.cv n) (synCtc (.cv m)) (.cv k)
      (synCkqrel (synClefin)) p0818
  have p0822 :=
    @gImbi12d (.classEq (.cv n) (synCtc (.cv m))) syntaxFormula0020 syntaxFormula0224
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv k) (synCkqrel (synClefin)) (synCtc (.cv m))) p0819 p0821
  have p0823 :=
    @gRspcva syntaxFormula0021 syntaxFormula0226 n (synCtc (.cv m)) (synCnnc)
      dv_cache_0139 dv_cache_0060 dv_cache_0140 p0822
  have p0824 :=
    @gSyl syntaxFormula0001
      (synWa (.classMem (synCtc (.cv m)) (synCnnc)) syntaxFormula0023)
      syntaxFormula0226 p0817 p0823
  have p0825 :=
    @gMpd syntaxFormula0001 syntaxFormula0224
      (synWbr (.cv k) (synCkqrel (synClefin)) (synCtc (.cv m))) p0814 p0824
  have p0826 := @gNntcpreim x (.cv k) dv_cache_0141
  have p0827 :=
    @gSyl syntaxFormula0001 (.classMem (.cv k) (synCnnc))
      (synWrex x (synCnnc) (.classEq (synCtc (.cv x)) (.cv k))) p0053 p0826
  have p0828 :=
    @gA1d syntaxFormula0001 syntaxFormula0022
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k))) p0058
  have p0829 :=
    @gSimpr (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k))
  have p0830 :=
    @gEleq1d (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synCtc (.cv x)) (.cv k) syntaxClass0019 p0829
  have p0831 :=
    @gBiimprd
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0227 syntaxFormula0022 p0830
  have p0832 :=
    @gSylcom syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0022 syntaxFormula0227 p0828 p0831
  have p0833 :=
    @gSimpl (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k))
  have p0834 :=
    @gA1i syntaxFormula0223
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k))) p0805
  have p0835 :=
    @gJca (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (.classMem (.cv x) (synCnnc)) syntaxFormula0223 p0833 p0834
  have p0836 := @gId (.classEq (.cv n) (.cv x))
  have p0837 := @gEleq1d (.classEq (.cv n) (.cv x)) (.cv n) (.cv x) syntaxClass0006 p0836
  have p0838 := @gTceq (.cv n) (.cv x)
  have p0839 :=
    @gEleq1d (.classEq (.cv n) (.cv x)) (synCtc (.cv n)) (synCtc (.cv x))
      syntaxClass0019 p0838
  have p0840 :=
    @gBibi12d (.classEq (.cv n) (.cv x)) syntaxFormula0007 syntaxFormula0228
      syntaxFormula0221 syntaxFormula0227 p0837 p0839
  have p0841 :=
    @gRspcva syntaxFormula0222 syntaxFormula0229 n (.cv x) (synCnnc) dv_cache_0142
      dv_cache_0060 dv_cache_0143 p0840
  have p0842 :=
    @gSyl (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synWa (.classMem (.cv x) (synCnnc)) syntaxFormula0223) syntaxFormula0229 p0835
      p0841
  have p0843 :=
    @gBiimprd
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0228 syntaxFormula0227 p0842
  have p0844 :=
    @gSylcom syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0227 syntaxFormula0228 p0832 p0843
  have p0846 :=
    @gA1d syntaxFormula0001 syntaxFormula0010
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k))) p0688
  have p0847 := @g_pm3_2 (.classMem (.cv x) (synCnnc)) syntaxFormula0010
  have p0848 :=
    @gSyl9 syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0010 (.classMem (.cv x) (synCnnc)) syntaxFormula0230 p0846 p0847
  have p0849 :=
    @gSyl5 (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (.classMem (.cv x) (synCnnc)) syntaxFormula0001
      (.imp (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
        syntaxFormula0230)
      p0833 p0848
  have p0850 :=
    @gPm243d syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0230 p0849
  have p0854 :=
    @gBreq2d (.classEq (.cv n) (.cv x)) (.cv n) (.cv x) (.cv m) (synCkqrel (synClefin))
      p0836
  have p0855 :=
    @gImbi12d (.classEq (.cv n) (.cv x)) syntaxFormula0007 syntaxFormula0228
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x)) p0837 p0854
  have p0856 :=
    @gRspcva syntaxFormula0008
      (.imp syntaxFormula0228 (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x))) n
      (.cv x) (synCnnc) dv_cache_0142 dv_cache_0060 dv_cache_0144 p0855
  have p0857 :=
    @gSyl6 syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0230
      (.imp syntaxFormula0228 (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x))) p0850
      p0856
  have p0858 :=
    @gMpdd syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      syntaxFormula0228 (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x)) p0844 p0857
  have p0859 :=
    @gA1d syntaxFormula0001 (.classMem (.cv m) (synCnnc))
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k))) p0034
  have p0861 := @g_pm3_2 (.classMem (.cv m) (synCnnc)) (.classMem (.cv x) (synCnnc))
  have p0862 :=
    @gSyl5 (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (.classMem (.cv x) (synCnnc)) (.classMem (.cv m) (synCnnc))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv x) (synCnnc))) p0833 p0861
  have p0863 :=
    @gSyl6 syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (.classMem (.cv m) (synCnnc))
      (.imp (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
        (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv x) (synCnnc))))
      p0859 p0862
  have p0864 :=
    @gPm243d syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv x) (synCnnc))) p0863
  have p0865 := @gKqlefintcb (.cv m) (.cv x)
  have p0866 :=
    @gSyl6 syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv x) (synCnnc)))
      (synWb (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x))
        (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (synCtc (.cv x))))
      p0864 p0865
  have p0867 :=
    @gBi1 (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (synCtc (.cv x)))
  have p0868 :=
    @gSyl6 syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synWb (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x))
        (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (synCtc (.cv x))))
      (.imp (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x))
        (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (synCtc (.cv x))))
      p0866 p0867
  have p0869 :=
    @gMpdd syntaxFormula0001
      (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv x))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (synCtc (.cv x))) p0858 p0868
  have p0871 :=
    @gBreq2d (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synCtc (.cv x)) (.cv k) (synCtc (.cv m)) (synCkqrel (synClefin)) p0829
  have p0872 :=
    @gMpbidi (synWa (.classMem (.cv x) (synCnnc)) (.classEq (synCtc (.cv x)) (.cv k)))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (synCtc (.cv x)))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k)) syntaxFormula0001
      p0869 p0871
  have p0873 :=
    @gExp3a syntaxFormula0001 (.classMem (.cv x) (synCnnc))
      (.classEq (synCtc (.cv x)) (.cv k))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k)) p0872
  have p0874 :=
    @gRexlimdv syntaxFormula0001 (.classEq (synCtc (.cv x)) (.cv k))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k)) x (synCnnc)
      dv_cache_0145 dv_cache_0146 p0873
  have p0875 :=
    @gMpd syntaxFormula0001 (synWrex x (synCnnc) (.classEq (synCtc (.cv x)) (.cv k)))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k)) p0827 p0874
  have p0876 :=
    @gJca syntaxFormula0001 (synWbr (.cv k) (synCkqrel (synClefin)) (synCtc (.cv m)))
      (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k)) p0825 p0875
  have p0877 :=
    @gJca syntaxFormula0001 (.classMem (.cv k) (synCnnc))
      (.classMem (synCtc (.cv m)) (synCnnc)) p0053 p0816
  have p0878 := @gKqfinantinn (.cv k) (synCtc (.cv m))
  have p0879 :=
    @gSyl syntaxFormula0001
      (synWa (.classMem (.cv k) (synCnnc)) (.classMem (synCtc (.cv m)) (synCnnc)))
      (.imp (synWa (synWbr (.cv k) (synCkqrel (synClefin)) (synCtc (.cv m)))
          (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k)))
        (.classEq (.cv k) (synCtc (.cv m))))
      p0877 p0878
  have p0880 :=
    @gMpd syntaxFormula0001
      (synWa (synWbr (.cv k) (synCkqrel (synClefin)) (synCtc (.cv m)))
        (synWbr (synCtc (.cv m)) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (.cv k) (synCtc (.cv m))) p0876 p0879
  have p0881 := @gEqeq2d syntaxFormula0001 (.cv k) (synCtc (.cv m)) (.cv m) p0880
  have p0882 := @gAddceq1d syntaxFormula0001 (.cv k) (synCtc (.cv m)) (synC1c) p0880
  have p0883 :=
    @gEqeq2d syntaxFormula0001 (synCplc (.cv k) (synC1c))
      (synCplc (synCtc (.cv m)) (synC1c)) (.cv m) p0882
  have p0884 :=
    @gOrbi12d syntaxFormula0001 (.classEq (.cv m) (.cv k))
      (.classEq (.cv m) (synCtc (.cv m))) (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (.classEq (.cv m) (synCplc (synCtc (.cv m)) (synC1c))) p0881 p0883
  have p0885 :=
    @gMpbid syntaxFormula0001
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      syntaxFormula0231 p0755 p0884
  have p0887 :=
    @gElwpphitvndv C (synCwppstopstep F C)
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv m)
  have p0888 := Nominal.mp p0145 p0887
  have p0889 :=
    @gSylib syntaxFormula0001 syntaxFormula0009
      (synWa (.classMem (.cv m) (synCnnc)) syntaxFormula0233) p0056 p0888
  have p0890 := @gSimpr (.classMem (.cv m) (synCnnc)) syntaxFormula0233
  have p0891 :=
    @gSyl syntaxFormula0001 (synWa (.classMem (.cv m) (synCnnc)) syntaxFormula0233)
      syntaxFormula0233 p0889 p0890
  have p0899 :=
    @gFrecdomfv (synCwppstopstep F C) (synCif (.classEq I (synCtc I)) I (synC0c))
      (.cv x)
  have p0900 :=
    @gMpan syntaxFormula0057 (.classMem (.cv x) (synCnnc)) syntaxFormula0235 p0145 p0899
  have p0902 :=
    @gEleq2i (synCdm (synCwppstopstep F C)) (synChwcards (synCvv)) syntaxClass0234
      p0140
  have p0903 :=
    @gBiimpi syntaxFormula0235 (.classMem syntaxClass0234 (synChwcards (synCvv))) p0902
  have p0904 :=
    @gSyl (.classMem (.cv x) (synCnnc)) syntaxFormula0235
      (.classMem syntaxClass0234 (synChwcards (synCvv))) p0900 p0903
  have p0905 := @gSimpr (.classMem (.cv x) (synCnnc)) syntaxFormula0236
  have p0906 := @gBreq2d syntaxFormula0237 (.cv y) syntaxClass0234 C (synClec) p0905
  have p0909 := @gTceq (.cv y) syntaxClass0234
  have p0910 :=
    @gSyl syntaxFormula0237 syntaxFormula0236
      (.classEq (synCtc (.cv y)) syntaxClass0238) p0905 p0909
  have p0911 :=
    @gNeeq12d syntaxFormula0237 (.cv y) syntaxClass0234 (synCtc (.cv y)) syntaxClass0238
      p0905 p0910
  have p0912 :=
    @gImbi12d syntaxFormula0237 (synWbr C (synClec) (.cv y)) syntaxFormula0239
      (synWne (.cv y) (synCtc (.cv y))) syntaxFormula0240 p0906 p0911
  have p0913 :=
    @gRspcdv (.classMem (.cv x) (synCnnc))
      (.imp (synWbr C (synClec) (.cv y)) (synWne (.cv y) (synCtc (.cv y))))
      syntaxFormula0241 y syntaxClass0234 (synChwcards (synCvv)) dv_cache_0147
      dv_cache_0073 dv_cache_0148 dv_cache_0149 p0904 p0912
  have p0914 :=
    @gMpi (.classMem (.cv x) (synCnnc))
      (synWral y (synChwcards (synCvv))
        (.imp (synWbr C (synClec) (.cv y)) (synWne (.cv y) (synCtc (.cv y)))))
      syntaxFormula0241 hyp_wppstopfixedhitcontrgrowfixdndv_9 p0913
  have p0915 := @gRgen syntaxFormula0241 x (synCnnc) p0914
  have p0916 := @gId (.classEq (.cv x) (.cv m))
  have p0917 := @gFveq2d (.classEq (.cv x) (.cv m)) (.cv x) (.cv m) syntaxClass0051 p0916
  have p0918 :=
    @gBreq2d (.classEq (.cv x) (.cv m)) syntaxClass0234 syntaxClass0232 C (synClec)
      p0917
  have p0923 := @gTceq syntaxClass0234 syntaxClass0232
  have p0924 :=
    @gSyl (.classEq (.cv x) (.cv m)) (.classEq syntaxClass0234 syntaxClass0232)
      (.classEq syntaxClass0238 syntaxClass0242) p0917 p0923
  have p0925 :=
    @gNeeq12d (.classEq (.cv x) (.cv m)) syntaxClass0234 syntaxClass0232 syntaxClass0238
      syntaxClass0242 p0917 p0924
  have p0926 :=
    @gImbi12d (.classEq (.cv x) (.cv m)) syntaxFormula0239 syntaxFormula0233
      syntaxFormula0240 syntaxFormula0243 p0918 p0925
  have p0927 :=
    @gRspcv syntaxFormula0241 syntaxFormula0244 x (.cv m) (synCnnc) dv_cache_0150
      dv_cache_0029 dv_cache_0151 p0926
  have p0928 :=
    @gMpi (.classMem (.cv m) (synCnnc)) (synWral x (synCnnc) syntaxFormula0241)
      syntaxFormula0244 p0915 p0927
  have p0929 :=
    @gSyl syntaxFormula0001 (.classMem (.cv m) (synCnnc)) syntaxFormula0244 p0034 p0928
  have p0930 := @gMpd syntaxFormula0001 syntaxFormula0233 syntaxFormula0243 p0891 p0929
  have p0931 := (Nominal.biimpRefl syntaxFormula0243)
  have p0932 := @gSylib syntaxFormula0001 syntaxFormula0243 syntaxFormula0246 p0930 p0931
  have p0933 :=
    @gFrectchom0 x (synCwppstopstep F C) (synCwppstopstep F (synCtc C))
      (synCif (.classEq I (synCtc I)) I (synC0c)) (.cv m) dv_cache_0134 dv_cache_0135
      dv_cache_0136 p0134 p0143 p0144 p0084 p0789 p0120
      hyp_wppstopfixedhitcontrgrowfixdndv_6
  have p0934 :=
    @gSyl syntaxFormula0001 (.classMem (.cv m) (synCnnc))
      (.classEq syntaxClass0242 (synCfv syntaxClass0029 (synCtc (.cv m)))) p0034 p0933
  have p0935 := @gEqcomd syntaxFormula0001 (.cv k) (synCtc (.cv m)) p0880
  have p0936 :=
    @gFveq2d syntaxFormula0001 (synCtc (.cv m)) (.cv k) syntaxClass0029 p0935
  have p0937 :=
    @gEqtrd syntaxFormula0001 syntaxClass0242 (synCfv syntaxClass0029 (synCtc (.cv m)))
      syntaxClass0187 p0934 p0936
  have p0938 :=
    @gEqtrd syntaxFormula0001 syntaxClass0242 syntaxClass0187 syntaxClass0159 p0937 p0683
  have p0939 :=
    @gA1d syntaxFormula0001 syntaxFormula0247 (.classEq (.cv m) (.cv k)) p0938
  have p0940 := @gId (.classEq (.cv m) (.cv k))
  have p0941 := @gEqcomd (.classEq (.cv m) (.cv k)) (.cv m) (.cv k) p0940
  have p0942 := @gFveq2d (.classEq (.cv m) (.cv k)) (.cv k) (.cv m) syntaxClass0051 p0941
  have p0943 :=
    @gEqeq2d (.classEq (.cv m) (.cv k)) syntaxClass0159 syntaxClass0232 syntaxClass0242
      p0942
  have p0944 :=
    @gMpbidi (.classEq (.cv m) (.cv k)) syntaxFormula0247 syntaxFormula0248
      syntaxFormula0001 p0939 p0943
  have p0945 := @gEqcom syntaxClass0242 syntaxClass0232
  have p0946 :=
    @gSyl6ib syntaxFormula0001 (.classEq (.cv m) (.cv k)) syntaxFormula0248
      syntaxFormula0245 p0944 p0945
  have p0947 := @gNecon3bd syntaxFormula0001 syntaxFormula0245 (.cv m) (.cv k) p0946
  have p0948 :=
    @gMpd syntaxFormula0001 syntaxFormula0246 (synWne (.cv m) (.cv k)) p0932 p0947
  have p0949 := @gNeeq2d syntaxFormula0001 (.cv k) (synCtc (.cv m)) (.cv m) p0880
  have p0950 :=
    @gMpbid syntaxFormula0001 (synWne (.cv m) (.cv k))
      (synWne (.cv m) (synCtc (.cv m))) p0948 p0949
  have p0951 := (Nominal.biimpRefl (synWne (.cv m) (synCtc (.cv m))))
  have p0952 :=
    @gSylib syntaxFormula0001 (synWne (.cv m) (synCtc (.cv m)))
      (.neg (.classEq (.cv m) (synCtc (.cv m)))) p0950 p0951
  have p0953 := @gNchoicelem1 (.cv m)
  have p0954 :=
    @gSyl syntaxFormula0001 (.classMem (.cv m) (synCnnc))
      (.neg (.classEq (.cv m) (synCplc (synCtc (.cv m)) (synC1c)))) p0034 p0953
  have p0955 :=
    @gJca syntaxFormula0001 (.neg (.classEq (.cv m) (synCtc (.cv m))))
      (.neg (.classEq (.cv m) (synCplc (synCtc (.cv m)) (synC1c)))) p0952 p0954
  have p0956 :=
    @gPm456 (.classEq (.cv m) (synCtc (.cv m)))
      (.classEq (.cv m) (synCplc (synCtc (.cv m)) (synC1c)))
  have p0957 :=
    @gSylib syntaxFormula0001
      (synWa (.neg (.classEq (.cv m) (synCtc (.cv m))))
        (.neg (.classEq (.cv m) (synCplc (synCtc (.cv m)) (synC1c)))))
      (.neg syntaxFormula0231) p0955 p0956
  have p0958 :=
    @gPm221dd syntaxFormula0001 syntaxFormula0231 (.neg (.classEq (.cv m) (.cv m)))
      p0885 p0957
  have p0959 :=
    @gA1d syntaxFormula0001 (.neg (.classEq (.cv m) (.cv m)))
      (.classEq (synC0c) (synC0c)) p0958
  have p0960 :=
    @gMt2d syntaxFormula0001 (.classEq (synC0c) (synC0c)) (.classEq (.cv m) (.cv m))
      p0017 p0959
  have p0961 :=
    @gSyl6 (.classEq I (synCtc I)) (synWa ph (synWa ps ch)) syntaxFormula0001
      (.neg (.classEq (synC0c) (synC0c))) p0015 p0960
  exact p0961


end NFChoice.DirectNominalPrf.WPPReplay
