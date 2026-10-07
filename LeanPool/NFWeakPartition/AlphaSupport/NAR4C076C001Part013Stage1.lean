/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C076C001Block004

/-! NF weak partition development: NAR4C076C001Part013. -/


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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0007`. -/
@[expose]
noncomputable def nb076SplitAlpha0007 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
        ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
        ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
        ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.classEq (Class.cv (nb076AlphaDummy081))
        (synCun (synCphi (Class.cv (nb076AlphaDummy082))) (synCsn (synC0c))))
      (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
        (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b))) (synCsn (synC0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb076AlphaDummy000))).fv ∪
            ((synCxp (Class.cv (nb076AlphaDummy001))
                (Class.cv (nb076AlphaDummy002)))).fv) (by decide))
        (freshVar_injective (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv)
          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy089) from (by
                                    unfold nb076AlphaDummy089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                                  (nb076AlphaDummy084 g a b) ≠ (nb076AlphaDummy091 g a b)
                                  from (by
                                    unfold nb076AlphaDummy091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                            0)))) (TAlphaVar.there
                                  (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy090) from
                                    (by
                                      unfold nb076AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0098)
                                              1)))) (show (nb076AlphaDummy084 g a b) ≠
                                      (nb076AlphaDummy092 g a b) from (by
                                      unfold nb076AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0099 g a b) 1))))
                                  (TAlphaVar.there (show
                                      (nb076AlphaDummy082) ≠ (nb076AlphaDummy157) from (by
                                        unfold nb076AlphaDummy157;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0184)
                                                0)))) (show (nb076AlphaDummy084 g a b) ≠
                                        (nb076AlphaDummy158 g a b) from (by
                                        unfold nb076AlphaDummy158;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0185 g a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076AlphaDummy082) ≠ (nb076AlphaDummy155) from
                                        (by
                                          unfold nb076AlphaDummy155;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0182)
                                                  0)))) (show (nb076AlphaDummy084 g a b) ≠
        (nb076AlphaDummy156 g a b) from (by
                                          unfold nb076AlphaDummy156;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0183 g a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb076AlphaDummy082))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb076AlphaDummy084 g a b))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy089) ≠ (nb076AlphaDummy096) from (by
          unfold nb076AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102)
                  1)))) (show (nb076AlphaDummy091 g a b) ≠ (nb076AlphaDummy099 g a b) from
        (by
          unfold nb076AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy095)
        from (by
          unfold nb076AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102)
                  0)))) (show (nb076AlphaDummy091 g a b) ≠ (nb076AlphaDummy098 g a b) from
        (by
          unfold nb076AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g
                    a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy093)
        from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100)
                  0)))) (show (nb076AlphaDummy091 g a b) ≠ (nb076AlphaDummy094 g a b) from
        (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a
        b))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy103) from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy103)
        from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy103) from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy103)
        from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a
        b))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy089))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy091 g a
        b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy096) ≠
        (nb076AlphaDummy107) from (by
          unfold
            nb076AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy108 g a b) from
        (by
          unfold
            nb076AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy107)
        from (by
          unfold
            nb076AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy108 g a b) from
        (by
          unfold
            nb076AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy109) from (by
          unfold
            nb076AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy110 g a b) from
        (by
          unfold
            nb076AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy097) ≠
        (nb076AlphaDummy109) from (by
          unfold
            nb076AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy110 g a b) from
        (by
          unfold
            nb076AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb076AlphaDummy089) ≠
        (nb076AlphaDummy093) from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy089) from (by
                                    unfold nb076AlphaDummy089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                                  (nb076AlphaDummy084 g a b) ≠ (nb076AlphaDummy091 g a b)
                                  from (by
                                    unfold nb076AlphaDummy091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                            0)))) (TAlphaVar.there
                                  (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy090) from
                                    (by
                                      unfold nb076AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0098)
                                              1)))) (show (nb076AlphaDummy084 g a b) ≠
                                      (nb076AlphaDummy092 g a b) from (by
                                      unfold nb076AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0099 g a b) 1))))
                                  (TAlphaVar.there (show
                                      (nb076AlphaDummy082) ≠ (nb076AlphaDummy157) from (by
                                        unfold nb076AlphaDummy157;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0184)
                                                0)))) (show (nb076AlphaDummy084 g a b) ≠
                                        (nb076AlphaDummy158 g a b) from (by
                                        unfold nb076AlphaDummy158;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0185 g a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076AlphaDummy082) ≠ (nb076AlphaDummy155) from
                                        (by
                                          unfold nb076AlphaDummy155;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0182)
                                                  0)))) (show (nb076AlphaDummy084 g a b) ≠
        (nb076AlphaDummy156 g a b) from (by
                                          unfold nb076AlphaDummy156;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0183 g a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb076AlphaDummy082))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb076AlphaDummy084 g a b))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy089) ≠ (nb076AlphaDummy096) from (by
          unfold nb076AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102)
                  1)))) (show (nb076AlphaDummy091 g a b) ≠ (nb076AlphaDummy099 g a b) from
        (by
          unfold nb076AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy095)
        from (by
          unfold nb076AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102)
                  0)))) (show (nb076AlphaDummy091 g a b) ≠ (nb076AlphaDummy098 g a b) from
        (by
          unfold nb076AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g
                    a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy093)
        from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100)
                  0)))) (show (nb076AlphaDummy091 g a b) ≠ (nb076AlphaDummy094 g a b) from
        (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a
        b))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy103) from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy103)
        from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy103) from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy103)
        from (by
          unfold
            nb076AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy104 g a b) from
        (by
          unfold
            nb076AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy101)
        from (by
          unfold
            nb076AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy102 g a b) from
        (by
          unfold
            nb076AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a
        b))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy089))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy091 g a
        b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy096) ≠
        (nb076AlphaDummy107) from (by
          unfold
            nb076AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy108 g a b) from
        (by
          unfold
            nb076AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy107)
        from (by
          unfold
            nb076AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy108 g a b) from
        (by
          unfold
            nb076AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy109) from (by
          unfold
            nb076AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy110 g a b) from
        (by
          unfold
            nb076AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy097) ≠
        (nb076AlphaDummy109) from (by
          unfold
            nb076AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy110 g a b) from
        (by
          unfold
            nb076AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy097) ≠ (nb076AlphaDummy105)
        from (by
          unfold
            nb076AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076AlphaDummy100 g a b) ≠ (nb076AlphaDummy106 g a b) from
        (by
          unfold
            nb076AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb076AlphaDummy089) ≠
        (nb076AlphaDummy093) from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from (by
          unfold nb076AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
          unfold nb076AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy157),
        (nb076AlphaDummy158 g a b)), ((nb076AlphaDummy155),
        (nb076AlphaDummy156 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.reflOfClosed
              [((nb076AlphaDummy155), (nb076AlphaDummy156 g a b)),
                ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                ((nb076AlphaDummy000), a),
                ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
                ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
              (synCcompl (synCsn (synC0c)))
              (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))

theorem nb076_wpp_notmem_0418 : (nb076AlphaDummy002) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy002, fv_syn_cen] using (nb076_compact_fv_empty_0080)

theorem nb076_wpp_notmem_0419 (g : Var) : g ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0081 g)

theorem nb076_wpp_notmem_0420 : (nb076AlphaDummy001) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy001, fv_syn_cen] using (nb076_compact_fv_empty_0082)

theorem nb076_wpp_notmem_0421 (b : Var) : b ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0083 b)

theorem nb076_wpp_notmem_0422 : (nb076AlphaDummy000) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy000, fv_syn_cen] using (nb076_compact_fv_empty_0084)

theorem nb076_wpp_notmem_0423 (a : Var) : a ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0085 a)

theorem nb076_wpp_notmem_0424 : (nb076AlphaDummy005) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy005, fv_syn_cen] using (nb076_compact_fv_empty_0028)

theorem nb076_wpp_notmem_0425 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy006, fv_syn_cen] using
    (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_wpp_notmem_0426 : (nb076AlphaDummy004) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy004, fv_syn_cen] using (nb076_compact_fv_empty_0030)

theorem nb076_wpp_notmem_0427 (n : Var) : n ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0031 n)

theorem nb076_wpp_notmem_0428 : (nb076AlphaDummy003) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy003, fv_syn_cen] using (nb076_compact_fv_empty_0032)

theorem nb076_wpp_notmem_0429 (m : Var) : m ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0033 m)

theorem nb076_wpp_notmem_0430 : (nb076AlphaDummy007) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy007, fv_syn_cen] using (nb076_compact_fv_empty_0034)

theorem nb076_wpp_notmem_0431 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy008 g m n a b) ∉ ((synCen)).fv := by
  simpa only [nb076AlphaDummy008, fv_syn_cen] using
    (nb076_compact_fv_empty_0035 g m n a b)

theorem nb076_compact_envfresh_0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TEnvFresh
      [((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      ((synCen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb076AlphaDummy002) g (nb076_wpp_notmem_0418)
      (nb076_wpp_notmem_0419 g)
      (TEnvFresh.consFresh (nb076AlphaDummy001) b (nb076_wpp_notmem_0420)
        (nb076_wpp_notmem_0421 b)
        (TEnvFresh.consFresh (nb076AlphaDummy000) a (nb076_wpp_notmem_0422)
          (nb076_wpp_notmem_0423 a)
          (TEnvFresh.consFresh (nb076AlphaDummy005) (nb076AlphaDummy006 g m n a b)
            (nb076_wpp_notmem_0424) (nb076_wpp_notmem_0425 g m n a b)
            (TEnvFresh.consFresh (nb076AlphaDummy004) n (nb076_wpp_notmem_0426)
              (nb076_wpp_notmem_0427 n)
              (TEnvFresh.consFresh (nb076AlphaDummy003) m (nb076_wpp_notmem_0428)
                (nb076_wpp_notmem_0429 m) (TEnvFresh.consFresh (nb076AlphaDummy007)
                  (nb076AlphaDummy008 g m n a b) (nb076_wpp_notmem_0430)
                  (nb076_wpp_notmem_0431 g m n a b) (TEnvFresh.nil ((synCen)).fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
