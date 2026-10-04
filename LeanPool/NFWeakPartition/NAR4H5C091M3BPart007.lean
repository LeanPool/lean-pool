/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C091M3BPart007Stage1


/-! NF weak partition development: NAR4H5C091M3BPart007. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

/-- Checked nominal proof certificate identified upstream as `nb091_wpp_refl_0033`. -/
@[expose]
noncomputable def nb091WppRefl0033 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TReflOn
      [((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      ((synCcnv (synCdif R (synCid)))).fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0036 D R p dv_R_p)

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0011`. -/
@[expose]
noncomputable def nb091SplitAlpha0011 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
        (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R))) (synCsn (synC0c))))
      (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
        (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p))) (synCsn (synC0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                          (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
            ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
          (by decide)) (freshVar_injective (((synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy048 D R) ≠
                                    (nb091AlphaDummy155 D R) from (by
                                    unfold nb091AlphaDummy155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                            0)))) (show (nb091AlphaDummy050 D R p) ≠
                                    (nb091AlphaDummy157 D R p) from (by
                                    unfold nb091AlphaDummy157;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0155 D R p)
                                            0)))) (TAlphaVar.there (show
                                    (nb091AlphaDummy048 D R) ≠ (nb091AlphaDummy156 D R)
                                    from (by
                                      unfold nb091AlphaDummy156;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                              1)))) (show (nb091AlphaDummy050 D R p) ≠
                                      (nb091AlphaDummy158 D R p) from (by
                                      unfold nb091AlphaDummy158;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0155 D R p) 1))))
                                  (TAlphaVar.there (show (nb091AlphaDummy048 D R) ≠
                                        (nb091AlphaDummy181 D R) from (by
                                        unfold nb091AlphaDummy181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0180 D R) 0)))) (show
                                      (nb091AlphaDummy050 D R p) ≠
                                        (nb091AlphaDummy182 D R p) from (by
                                        unfold nb091AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0181 D R p) 0))))
                                    (TAlphaVar.there (show (nb091AlphaDummy048 D R) ≠
        (nb091AlphaDummy179 D R) from (by
                                          unfold nb091AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0178 D R) 0)))) (show
                                        (nb091AlphaDummy050 D R p) ≠
        (nb091AlphaDummy180 D R p) from (by
                                          unfold nb091AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0179 D R p) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb091AlphaDummy048 D R))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb091AlphaDummy050 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy155 D R) ≠ (nb091AlphaDummy162 D R) from (by
          unfold nb091AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D R)
                  1)))) (show (nb091AlphaDummy157 D R p) ≠ (nb091AlphaDummy165 D R p) from
        (by
          unfold nb091AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy155 D R) ≠
        (nb091AlphaDummy161 D R) from (by
          unfold nb091AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D
                    R)
                  0)))) (show (nb091AlphaDummy157 D R p) ≠ (nb091AlphaDummy164 D R p) from
        (by
          unfold nb091AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy155 D R) ≠
        (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156
                    D R)
                  0)))) (show (nb091AlphaDummy157 D R p) ≠ (nb091AlphaDummy160 D R p) from
        (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy163 D R), (nb091AlphaDummy166 D R p)),
        ((nb091AlphaDummy162 D R), (nb091AlphaDummy165 D R p)),
        ((nb091AlphaDummy161 D R), (nb091AlphaDummy164 D R p)),
        ((nb091AlphaDummy159 D R), (nb091AlphaDummy160 D R p)),
        ((nb091AlphaDummy155 D R), (nb091AlphaDummy157 D R p)),
        ((nb091AlphaDummy156 D R), (nb091AlphaDummy158 D R p)),
        ((nb091AlphaDummy181 D R), (nb091AlphaDummy182 D R p)),
        ((nb091AlphaDummy179 D R), (nb091AlphaDummy180 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy163 D R), (nb091AlphaDummy166 D R p)),
        ((nb091AlphaDummy162 D R), (nb091AlphaDummy165 D R p)),
        ((nb091AlphaDummy161 D R), (nb091AlphaDummy164 D R p)),
        ((nb091AlphaDummy159 D R), (nb091AlphaDummy160 D R p)),
        ((nb091AlphaDummy155 D R), (nb091AlphaDummy157 D R p)),
        ((nb091AlphaDummy156 D R), (nb091AlphaDummy158 D R p)),
        ((nb091AlphaDummy181 D R), (nb091AlphaDummy182 D R p)),
        ((nb091AlphaDummy179 D R), (nb091AlphaDummy180 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy157 D
        R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy173 D R) from
        (by
          unfold
            nb091AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy174 D R p) from
        (by
          unfold
            nb091AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy173 D R) from
        (by
          unfold
            nb091AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy174 D R p) from
        (by
          unfold
            nb091AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy175 D R) from (by
          unfold
            nb091AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy176 D R p) from
        (by
          unfold
            nb091AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy163
        D R) ≠ (nb091AlphaDummy175 D R) from (by
          unfold
            nb091AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy176 D R p) from
        (by
          unfold
            nb091AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy155 D R) ≠ (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091AlphaDummy157 D R p) ≠
        (nb091AlphaDummy160 D R p) from (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb091AlphaDummy159 D R),
        (nb091AlphaDummy160 D R p)), ((nb091AlphaDummy155 D R),
        (nb091AlphaDummy157 D R p)), ((nb091AlphaDummy156 D R),
        (nb091AlphaDummy158 D R p)), ((nb091AlphaDummy181 D R),
        (nb091AlphaDummy182 D R p)), ((nb091AlphaDummy179 D R),
        (nb091AlphaDummy180 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R),
        (nb091AlphaDummy178 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                        (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091AlphaDummy155 D R) ≠
        (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091AlphaDummy157 D R p) ≠
        (nb091AlphaDummy160 D R p) from (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy155 D R) ≠ (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091AlphaDummy157 D R p) ≠
        (nb091AlphaDummy160 D R p) from (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb091AlphaDummy159 D R),
        (nb091AlphaDummy160 D R p)), ((nb091AlphaDummy155 D R),
        (nb091AlphaDummy157 D R p)), ((nb091AlphaDummy156 D R),
        (nb091AlphaDummy158 D R p)), ((nb091AlphaDummy181 D R),
        (nb091AlphaDummy182 D R p)), ((nb091AlphaDummy179 D R),
        (nb091AlphaDummy180 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R),
        (nb091AlphaDummy178 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy048 D R) ≠
                                    (nb091AlphaDummy155 D R) from (by
                                    unfold nb091AlphaDummy155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                            0)))) (show (nb091AlphaDummy050 D R p) ≠
                                    (nb091AlphaDummy157 D R p) from (by
                                    unfold nb091AlphaDummy157;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0155 D R p)
                                            0)))) (TAlphaVar.there (show
                                    (nb091AlphaDummy048 D R) ≠ (nb091AlphaDummy156 D R)
                                    from (by
                                      unfold nb091AlphaDummy156;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                              1)))) (show (nb091AlphaDummy050 D R p) ≠
                                      (nb091AlphaDummy158 D R p) from (by
                                      unfold nb091AlphaDummy158;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0155 D R p) 1))))
                                  (TAlphaVar.there (show (nb091AlphaDummy048 D R) ≠
                                        (nb091AlphaDummy181 D R) from (by
                                        unfold nb091AlphaDummy181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0180 D R) 0)))) (show
                                      (nb091AlphaDummy050 D R p) ≠
                                        (nb091AlphaDummy182 D R p) from (by
                                        unfold nb091AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0181 D R p) 0))))
                                    (TAlphaVar.there (show (nb091AlphaDummy048 D R) ≠
        (nb091AlphaDummy179 D R) from (by
                                          unfold nb091AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0178 D R) 0)))) (show
                                        (nb091AlphaDummy050 D R p) ≠
        (nb091AlphaDummy180 D R p) from (by
                                          unfold nb091AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0179 D R p) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb091AlphaDummy048 D R))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb091AlphaDummy050 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy155 D R) ≠ (nb091AlphaDummy162 D R) from (by
          unfold nb091AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D R)
                  1)))) (show (nb091AlphaDummy157 D R p) ≠ (nb091AlphaDummy165 D R p) from
        (by
          unfold nb091AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy155 D R) ≠
        (nb091AlphaDummy161 D R) from (by
          unfold nb091AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D
                    R)
                  0)))) (show (nb091AlphaDummy157 D R p) ≠ (nb091AlphaDummy164 D R p) from
        (by
          unfold nb091AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy155 D R) ≠
        (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156
                    D R)
                  0)))) (show (nb091AlphaDummy157 D R p) ≠ (nb091AlphaDummy160 D R p) from
        (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy163 D R), (nb091AlphaDummy166 D R p)),
        ((nb091AlphaDummy162 D R), (nb091AlphaDummy165 D R p)),
        ((nb091AlphaDummy161 D R), (nb091AlphaDummy164 D R p)),
        ((nb091AlphaDummy159 D R), (nb091AlphaDummy160 D R p)),
        ((nb091AlphaDummy155 D R), (nb091AlphaDummy157 D R p)),
        ((nb091AlphaDummy156 D R), (nb091AlphaDummy158 D R p)),
        ((nb091AlphaDummy181 D R), (nb091AlphaDummy182 D R p)),
        ((nb091AlphaDummy179 D R), (nb091AlphaDummy180 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠ (nb091AlphaDummy169 D R) from
        (by
          unfold
            nb091AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy170 D R p) from
        (by
          unfold
            nb091AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy167 D R) from (by
          unfold
            nb091AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy168 D R p) from
        (by
          unfold
            nb091AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy163 D R), (nb091AlphaDummy166 D R p)),
        ((nb091AlphaDummy162 D R), (nb091AlphaDummy165 D R p)),
        ((nb091AlphaDummy161 D R), (nb091AlphaDummy164 D R p)),
        ((nb091AlphaDummy159 D R), (nb091AlphaDummy160 D R p)),
        ((nb091AlphaDummy155 D R), (nb091AlphaDummy157 D R p)),
        ((nb091AlphaDummy156 D R), (nb091AlphaDummy158 D R p)),
        ((nb091AlphaDummy181 D R), (nb091AlphaDummy182 D R p)),
        ((nb091AlphaDummy179 D R), (nb091AlphaDummy180 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy157 D
        R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy173 D R) from
        (by
          unfold
            nb091AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy174 D R p) from
        (by
          unfold
            nb091AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy173 D R) from
        (by
          unfold
            nb091AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy174 D R p) from
        (by
          unfold
            nb091AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy162 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy155
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy175 D R) from (by
          unfold
            nb091AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy176 D R p) from
        (by
          unfold
            nb091AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy163
        D R) ≠ (nb091AlphaDummy175 D R) from (by
          unfold
            nb091AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy176 D R p) from
        (by
          unfold
            nb091AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy163 D R) ≠
        (nb091AlphaDummy171 D R) from (by
          unfold
            nb091AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091AlphaDummy166 D R p) ≠ (nb091AlphaDummy172 D R p) from
        (by
          unfold
            nb091AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy155 D R) ≠ (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091AlphaDummy157 D R p) ≠
        (nb091AlphaDummy160 D R p) from (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb091AlphaDummy159 D R),
        (nb091AlphaDummy160 D R p)), ((nb091AlphaDummy155 D R),
        (nb091AlphaDummy157 D R p)), ((nb091AlphaDummy156 D R),
        (nb091AlphaDummy158 D R p)), ((nb091AlphaDummy181 D R),
        (nb091AlphaDummy182 D R p)), ((nb091AlphaDummy179 D R),
        (nb091AlphaDummy180 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R),
        (nb091AlphaDummy178 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                        (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091AlphaDummy155 D R) ≠
        (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091AlphaDummy157 D R p) ≠
        (nb091AlphaDummy160 D R p) from (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy155 D R) ≠ (nb091AlphaDummy159 D R) from (by
          unfold nb091AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091AlphaDummy157 D R p) ≠
        (nb091AlphaDummy160 D R p) from (by
          unfold nb091AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb091AlphaDummy159 D R),
        (nb091AlphaDummy160 D R p)), ((nb091AlphaDummy155 D R),
        (nb091AlphaDummy157 D R p)), ((nb091AlphaDummy156 D R),
        (nb091AlphaDummy158 D R p)), ((nb091AlphaDummy181 D R),
        (nb091AlphaDummy182 D R p)), ((nb091AlphaDummy179 D R),
        (nb091AlphaDummy180 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R),
        (nb091AlphaDummy178 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synCnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.reflOfClosed
              [((nb091AlphaDummy179 D R), (nb091AlphaDummy180 D R p)),
                ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
                ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
                ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
                ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
                ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
                ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                ((nb091AlphaDummy000 D R), p),
                ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
              (synCcompl (synCsn (synC0c)))
              (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))


open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0012`. -/
@[expose]
noncomputable def nb091SplitAlpha0012 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) (dv_R_p : p ∉ R.fv) :
    TAlphaWff
      [((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy177 D R))
          (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy177 D R))
            (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy178 D R p))
          (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy178 D R p))
            (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfReflOn [((nb091AlphaDummy103 D R),
                                    (nb091AlphaDummy104 D R p)),
                                  ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
                                  ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
                                  ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
                                  ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
                                  ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
                                  ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
                                  ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                                  ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                                  ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                                  ((nb091AlphaDummy000 D R), p),
                                  ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                D (nb091FocusedRefl0002 D R p dv_D_p)))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((synCuni (Class.cv
        (nb091AlphaDummy000 D R)))).fv) (by decide)) (freshVar_injective
        (((synCuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy116 D R) from (by
          unfold
            nb091AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy118 p) from (by
          unfold
            nb091AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy115 D R) from (by
          unfold
            nb091AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy117 p) from (by
          unfold
            nb091AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy112 D R) from (by
          unfold
            nb091AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy114 p) from (by
          unfold
            nb091AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy111 D R) from (by
          unfold
            nb091AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy113 p) from (by
          unfold
            nb091AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy109 D R) from (by
          unfold
            nb091AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy110 p) from (by
          unfold
            nb091AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy106 D R) from (by
          unfold
            nb091AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy108 R p) from (by
          unfold
            nb091AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy105 D R) from (by
          unfold
            nb091AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy107 R p) from (by
          unfold
            nb091AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy103 D R) from (by
          unfold
            nb091AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy104 D R p) from (by
          unfold
            nb091AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy101 D R) from (by
          unfold
            nb091AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy102 D R p) from (by
          unfold
            nb091AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy048 D R) from (by
          unfold
            nb091AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy050 D R p) from (by
          unfold
            nb091AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy047 D R) from (by
          unfold
            nb091AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy049 D R p) from (by
          unfold
            nb091AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy177 D R) from (by
          unfold
            nb091AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy178 D R p) from (by
          unfold
            nb091AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy051 D R) from (by
          unfold
            nb091AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy052 D R p) from (by
          unfold
            nb091AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy045 D R) from (by
          unfold
            nb091AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy046 D R p) from (by
          unfold
            nb091AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy042 D R) from (by
          unfold
            nb091AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy044 D R p) from (by
          unfold
            nb091AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy041 D R) from (by
          unfold
            nb091AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy043 D R p) from (by
          unfold
            nb091AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy001 D R) from (by
          unfold
            nb091AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy002 D R p) from (by
          unfold
            nb091AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                        [((nb091AlphaDummy106 D R),
        (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R),
        (nb091AlphaDummy107 R p)), ((nb091AlphaDummy103 D R),
        (nb091AlphaDummy104 D R p)), ((nb091AlphaDummy101 D R),
        (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R),
        (nb091AlphaDummy178 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                        (synCcnv (synCdif R (synCid)))
                                        (nb091WppRefl0033 D R p dv_R_p)))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfReflOn [((nb091AlphaDummy103 D R),
                                    (nb091AlphaDummy104 D R p)),
                                  ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
                                  ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
                                  ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
                                  ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
                                  ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
                                  ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
                                  ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                                  ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                                  ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                                  ((nb091AlphaDummy000 D R), p),
                                  ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                D (nb091FocusedRefl0002 D R p dv_D_p)))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((synCuni (Class.cv
        (nb091AlphaDummy000 D R)))).fv) (by decide)) (freshVar_injective
        (((synCuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy116 D R) from (by
          unfold
            nb091AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy118 p) from (by
          unfold
            nb091AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy115 D R) from (by
          unfold
            nb091AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy117 p) from (by
          unfold
            nb091AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy112 D R) from (by
          unfold
            nb091AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy114 p) from (by
          unfold
            nb091AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy111 D R) from (by
          unfold
            nb091AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy113 p) from (by
          unfold
            nb091AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy109 D R) from (by
          unfold
            nb091AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy110 p) from (by
          unfold
            nb091AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy106 D R) from (by
          unfold
            nb091AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy108 R p) from (by
          unfold
            nb091AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy105 D R) from (by
          unfold
            nb091AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy107 R p) from (by
          unfold
            nb091AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy103 D R) from (by
          unfold
            nb091AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy104 D R p) from (by
          unfold
            nb091AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy101 D R) from (by
          unfold
            nb091AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy102 D R p) from (by
          unfold
            nb091AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy048 D R) from (by
          unfold
            nb091AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy050 D R p) from (by
          unfold
            nb091AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy047 D R) from (by
          unfold
            nb091AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy049 D R p) from (by
          unfold
            nb091AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy177 D R) from (by
          unfold
            nb091AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy178 D R p) from (by
          unfold
            nb091AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy051 D R) from (by
          unfold
            nb091AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy052 D R p) from (by
          unfold
            nb091AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy045 D R) from (by
          unfold
            nb091AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy046 D R p) from (by
          unfold
            nb091AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy042 D R) from (by
          unfold
            nb091AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy044 D R p) from (by
          unfold
            nb091AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy041 D R) from (by
          unfold
            nb091AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy043 D R p) from (by
          unfold
            nb091AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy001 D R) from (by
          unfold
            nb091AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy002 D R p) from (by
          unfold
            nb091AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                        [((nb091AlphaDummy106 D R),
        (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R),
        (nb091AlphaDummy107 R p)), ((nb091AlphaDummy103 D R),
        (nb091AlphaDummy104 D R p)), ((nb091AlphaDummy101 D R),
        (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R),
        (nb091AlphaDummy178 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                        (synCcnv (synCdif R (synCid)))
                                        (nb091WppRefl0033 D R p dv_R_p)))))))))))))))
            (nb091SplitAlpha0011 D R p))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfReflOn [((nb091AlphaDummy103 D R),
                                      (nb091AlphaDummy104 D R p)),
                                    ((nb091AlphaDummy101 D R),
                                      (nb091AlphaDummy102 D R p)),
                                    ((nb091AlphaDummy048 D R),
                                      (nb091AlphaDummy050 D R p)),
                                    ((nb091AlphaDummy047 D R),
                                      (nb091AlphaDummy049 D R p)),
                                    ((nb091AlphaDummy177 D R),
                                      (nb091AlphaDummy178 D R p)),
                                    ((nb091AlphaDummy051 D R),
                                      (nb091AlphaDummy052 D R p)),
                                    ((nb091AlphaDummy045 D R),
                                      (nb091AlphaDummy046 D R p)),
                                    ((nb091AlphaDummy042 D R),
                                      (nb091AlphaDummy044 D R p)),
                                    ((nb091AlphaDummy041 D R),
                                      (nb091AlphaDummy043 D R p)),
                                    ((nb091AlphaDummy001 D R),
                                      (nb091AlphaDummy002 D R p)),
                                    ((nb091AlphaDummy000 D R), p),
                                    ((nb091AlphaDummy003 D R),
                                      (nb091AlphaDummy004 D R p))]
                                  D (nb091FocusedRefl0002 D R p dv_D_p)))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
        (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) (by decide))
        (freshVar_injective (((synCuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy116 D R) from (by
          unfold
            nb091AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy118 p) from (by
          unfold
            nb091AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy115 D R) from (by
          unfold
            nb091AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy117 p) from (by
          unfold
            nb091AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy112 D R) from (by
          unfold
            nb091AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy114 p) from (by
          unfold
            nb091AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy111 D R) from (by
          unfold
            nb091AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy113 p) from (by
          unfold
            nb091AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy109 D R) from (by
          unfold
            nb091AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy110 p) from (by
          unfold
            nb091AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy106 D R) from (by
          unfold
            nb091AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy108 R p) from (by
          unfold
            nb091AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy105 D R) from (by
          unfold
            nb091AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy107 R p) from (by
          unfold
            nb091AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy103 D R) from (by
          unfold
            nb091AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy104 D R p) from (by
          unfold
            nb091AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy101 D R) from (by
          unfold
            nb091AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy102 D R p) from (by
          unfold
            nb091AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy048 D R) from (by
          unfold
            nb091AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy050 D R p) from (by
          unfold
            nb091AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy047 D R) from (by
          unfold
            nb091AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy049 D R p) from (by
          unfold
            nb091AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy177 D R) from (by
          unfold
            nb091AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy178 D R p) from (by
          unfold
            nb091AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy051 D R) from (by
          unfold
            nb091AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy052 D R p) from (by
          unfold
            nb091AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy045 D R) from (by
          unfold
            nb091AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy046 D R p) from (by
          unfold
            nb091AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy042 D R) from (by
          unfold
            nb091AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy044 D R p) from (by
          unfold
            nb091AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy041 D R) from (by
          unfold
            nb091AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy043 D R p) from (by
          unfold
            nb091AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy001 D R) from (by
          unfold
            nb091AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy002 D R p) from (by
          unfold
            nb091AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
        [((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcnv (synCdif R (synCid)))
        (nb091WppRefl0033 D R p dv_R_p)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfReflOn [((nb091AlphaDummy103 D R),
                                      (nb091AlphaDummy104 D R p)),
                                    ((nb091AlphaDummy101 D R),
                                      (nb091AlphaDummy102 D R p)),
                                    ((nb091AlphaDummy048 D R),
                                      (nb091AlphaDummy050 D R p)),
                                    ((nb091AlphaDummy047 D R),
                                      (nb091AlphaDummy049 D R p)),
                                    ((nb091AlphaDummy177 D R),
                                      (nb091AlphaDummy178 D R p)),
                                    ((nb091AlphaDummy051 D R),
                                      (nb091AlphaDummy052 D R p)),
                                    ((nb091AlphaDummy045 D R),
                                      (nb091AlphaDummy046 D R p)),
                                    ((nb091AlphaDummy042 D R),
                                      (nb091AlphaDummy044 D R p)),
                                    ((nb091AlphaDummy041 D R),
                                      (nb091AlphaDummy043 D R p)),
                                    ((nb091AlphaDummy001 D R),
                                      (nb091AlphaDummy002 D R p)),
                                    ((nb091AlphaDummy000 D R), p),
                                    ((nb091AlphaDummy003 D R),
                                      (nb091AlphaDummy004 D R p))]
                                  D (nb091FocusedRefl0002 D R p dv_D_p)))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
        (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) (by decide))
        (freshVar_injective (((synCuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy116 D R) from (by
          unfold
            nb091AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy118 p) from (by
          unfold
            nb091AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy115 D R) from (by
          unfold
            nb091AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy117 p) from (by
          unfold
            nb091AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy112 D R) from (by
          unfold
            nb091AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091AlphaDummy114 p) from (by
          unfold
            nb091AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy111 D R) from (by
          unfold
            nb091AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy113 p) from (by
          unfold
            nb091AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy109 D R) from (by
          unfold
            nb091AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091AlphaDummy110 p) from (by
          unfold
            nb091AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy106 D R) from (by
          unfold
            nb091AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy108 R p) from (by
          unfold
            nb091AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy105 D R) from (by
          unfold
            nb091AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy107 R p) from (by
          unfold
            nb091AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy103 D R) from (by
          unfold
            nb091AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy104 D R p) from (by
          unfold
            nb091AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy101 D R) from (by
          unfold
            nb091AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy102 D R p) from (by
          unfold
            nb091AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy048 D R) from (by
          unfold
            nb091AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy050 D R p) from (by
          unfold
            nb091AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy047 D R) from (by
          unfold
            nb091AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy049 D R p) from (by
          unfold
            nb091AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy177 D R) from (by
          unfold
            nb091AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy178 D R p) from (by
          unfold
            nb091AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy051 D R) from (by
          unfold
            nb091AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy052 D R p) from (by
          unfold
            nb091AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy045 D R) from (by
          unfold
            nb091AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy046 D R p) from (by
          unfold
            nb091AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy042 D R) from (by
          unfold
            nb091AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091AlphaDummy044 D R p) from (by
          unfold
            nb091AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy041 D R) from (by
          unfold
            nb091AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy043 D R p) from (by
          unfold
            nb091AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy001 D R) from (by
          unfold
            nb091AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091AlphaDummy002 D R p) from (by
          unfold
            nb091AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy105
        D R) ≠ (nb091AlphaDummy120 D R) from (by
          unfold
            nb091AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
          unfold
            nb091AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy119 D R) from (by
          unfold
            nb091AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold
            nb091AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy149 D R) from (by
          unfold
            nb091AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy150 R p) from (by
          unfold
            nb091AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy105 D R) ≠
        (nb091AlphaDummy123 D R) from (by
          unfold
            nb091AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy124 R p) from (by
          unfold
            nb091AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D
        R)))))).fv) (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy106 D R))).fv ∪ ((Class.cv (nb091AlphaDummy105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy108
        R p))).fv ∪ ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy151 D R), (nb091AlphaDummy152 R p)), ((nb091AlphaDummy120
        D R), (nb091AlphaDummy122 R p)), ((nb091AlphaDummy119 D R), (nb091AlphaDummy121
        R p)), ((nb091AlphaDummy149 D R), (nb091AlphaDummy150 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)), ((nb091AlphaDummy106
        D R), (nb091AlphaDummy108 R p)), ((nb091AlphaDummy105 D R), (nb091AlphaDummy107
        R p)), ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)), ((nb091AlphaDummy048
        D R), (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy177 D R), (nb091AlphaDummy178
        D R p)), ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042
        D R), (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R), (nb091AlphaDummy002
        D R p)), ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
        [((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCcnv (synCdif R (synCid)))
        (nb091WppRefl0033 D R p dv_R_p))))))))))))))) (nb091SplitAlpha0011 D R p)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
