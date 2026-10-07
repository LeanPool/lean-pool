/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C076C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C076C001Part010`. -/


section

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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0004`. -/
@[expose]
noncomputable def nb076SplitAlpha0004 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) :
    TAlphaWff
      [((nb076AlphaDummy087), (nb076AlphaDummy088 g a b)),
        ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
        ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy087))
          (Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy087)) (Class.cab (nb076AlphaDummy081)
              (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCphi (Class.cv (nb076AlphaDummy082)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy088 g a b))
          (Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy088 g a b))
            (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy082) from
                    (by
                      unfold nb076AlphaDummy082;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
                  (show a ≠ (nb076AlphaDummy084 g a b) from (by
                      unfold nb076AlphaDummy084;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
                  (TAlphaVar.there (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy081) from
                      (by
                        unfold nb076AlphaDummy081;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))))
                    (show a ≠ (nb076AlphaDummy083 g a b) from (by
                        unfold nb076AlphaDummy083;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy087) from (by
                          unfold nb076AlphaDummy087;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0096) 0))))
                      (show a ≠ (nb076AlphaDummy088 g a b) from (by
                          unfold nb076AlphaDummy088;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0097 g a b) 0))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy085) from (by
                            unfold nb076AlphaDummy085;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0093) 0))))
                        (show a ≠ (nb076AlphaDummy086 g a b) from (by
                            unfold nb076AlphaDummy086;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0095 g a b) 0))))
                        (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_g
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy000))).fv ∪
                      ((synCxp (Class.cv (nb076AlphaDummy001))
                          (Class.cv (nb076AlphaDummy002)))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy089) from (by
                              unfold nb076AlphaDummy089;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                            (nb076AlphaDummy084 g a b) ≠ (nb076AlphaDummy091 g a b) from
                            (by
                              unfold nb076AlphaDummy091;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0099 g a b) 0))))
                          (TAlphaVar.there
                            (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy090) from (by
                                unfold nb076AlphaDummy090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0098) 1)))) (show
                              (nb076AlphaDummy084 g a b) ≠ (nb076AlphaDummy092 g a b) from
                              (by
                                unfold nb076AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076AlphaDummy082))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076AlphaDummy084 g a b))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy096) from (by
          unfold nb076AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102) 1)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy099 g a b) from (by
          unfold nb076AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy095)
        from (by
          unfold nb076AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy098 g a b) from (by
          unfold nb076AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy093)
        from (by
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
                  (nb076_support_mem_0101 g a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy087),
        (nb076AlphaDummy088 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy096) ≠
        (nb076AlphaDummy103) from (by
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy087),
        (nb076AlphaDummy088 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy089))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy091 g a
        b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy107) from (by
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from (by
                                        unfold nb076AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0100)
                                                0)))) (show (nb076AlphaDummy091 g a b) ≠
                                        (nb076AlphaDummy094 g a b) from (by
                                        unfold nb076AlphaDummy094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0101 g a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy093), (nb076AlphaDummy094 g a b)),
                                    ((nb076AlphaDummy089), (nb076AlphaDummy091 g a b)),
                                    ((nb076AlphaDummy090), (nb076AlphaDummy092 g a b)),
                                    ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                    ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                    ((nb076AlphaDummy087), (nb076AlphaDummy088 g a b)),
                                    ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                    ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                                    ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from
                                    (by
                                      unfold nb076AlphaDummy093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0100)
                                              0)))) (show (nb076AlphaDummy091 g a b) ≠
                                      (nb076AlphaDummy094 g a b) from (by
                                      unfold nb076AlphaDummy094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0101 g a b) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from (by
                                        unfold nb076AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0100)
                                                0)))) (show (nb076AlphaDummy091 g a b) ≠
                                        (nb076AlphaDummy094 g a b) from (by
                                        unfold nb076AlphaDummy094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0101 g a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy093), (nb076AlphaDummy094 g a b)),
                                    ((nb076AlphaDummy089), (nb076AlphaDummy091 g a b)),
                                    ((nb076AlphaDummy090), (nb076AlphaDummy092 g a b)),
                                    ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                    ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                    ((nb076AlphaDummy087), (nb076AlphaDummy088 g a b)),
                                    ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                    ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                                    ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy082) from
                      (by
                        unfold nb076AlphaDummy082;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
                    (show a ≠ (nb076AlphaDummy084 g a b) from (by
                        unfold nb076AlphaDummy084;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy081) from (by
                          unfold nb076AlphaDummy081;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0092) 0))))
                      (show a ≠ (nb076AlphaDummy083 g a b) from (by
                          unfold nb076AlphaDummy083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy087) from (by
                            unfold nb076AlphaDummy087;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0096) 0))))
                        (show a ≠ (nb076AlphaDummy088 g a b) from (by
                            unfold nb076AlphaDummy088;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0097 g a b) 0))))
                        (TAlphaVar.there
                          (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy085) from (by
                              unfold nb076AlphaDummy085;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0093) 0))))
                          (show a ≠ (nb076AlphaDummy086 g a b) from (by
                              unfold nb076AlphaDummy086;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0095 g a b) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_g
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb076AlphaDummy000))).fv ∪
                        ((synCxp (Class.cv (nb076AlphaDummy001))
                            (Class.cv (nb076AlphaDummy002)))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy089) from (by
                                unfold nb076AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                              (nb076AlphaDummy084 g a b) ≠ (nb076AlphaDummy091 g a b) from
                              (by
                                unfold nb076AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                        0)))) (TAlphaVar.there
                              (show (nb076AlphaDummy082) ≠ (nb076AlphaDummy090) from (by
                                  unfold nb076AlphaDummy090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0098) 1)))) (show
                                (nb076AlphaDummy084 g a b) ≠ (nb076AlphaDummy092 g a b)
                                from (by
                                  unfold nb076AlphaDummy092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076AlphaDummy082))).fv)
                              (by decide)) (freshVar_injective
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
                  (nb076_support_mem_0102) 1)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy099 g a b) from (by
          unfold nb076AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy089) ≠ (nb076AlphaDummy095)
        from (by
          unfold nb076AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102) 0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy098 g a b) from (by
          unfold nb076AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
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
                  (nb076_support_mem_0101 g a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy087),
        (nb076AlphaDummy088 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy096) ≠
        (nb076AlphaDummy103) from (by
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy097), (nb076AlphaDummy100 g a b)), ((nb076AlphaDummy096),
        (nb076AlphaDummy099 g a b)), ((nb076AlphaDummy095),
        (nb076AlphaDummy098 g a b)), ((nb076AlphaDummy093),
        (nb076AlphaDummy094 g a b)), ((nb076AlphaDummy089),
        (nb076AlphaDummy091 g a b)), ((nb076AlphaDummy090),
        (nb076AlphaDummy092 g a b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy087),
        (nb076AlphaDummy088 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy089))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy091 g a
        b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy096) ≠ (nb076AlphaDummy107) from (by
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
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
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from
                                        (by
                                          unfold nb076AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0100)
                                                  0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
                                          unfold nb076AlphaDummy094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0101 g a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy093), (nb076AlphaDummy094 g a b)),
                                      ((nb076AlphaDummy089), (nb076AlphaDummy091 g a b)),
                                      ((nb076AlphaDummy090), (nb076AlphaDummy092 g a b)),
                                      ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                      ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                      ((nb076AlphaDummy087), (nb076AlphaDummy088 g a b)),
                                      ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                      ((nb076AlphaDummy002), g),
                                      ((nb076AlphaDummy001), b),
                                      ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from (by
                                        unfold nb076AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0100)
                                                0)))) (show (nb076AlphaDummy091 g a b) ≠
                                        (nb076AlphaDummy094 g a b) from (by
                                        unfold nb076AlphaDummy094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0101 g a b) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy089) ≠ (nb076AlphaDummy093) from
                                        (by
                                          unfold nb076AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0100)
                                                  0)))) (show (nb076AlphaDummy091 g a b) ≠
        (nb076AlphaDummy094 g a b) from (by
                                          unfold nb076AlphaDummy094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0101 g a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy093), (nb076AlphaDummy094 g a b)),
                                      ((nb076AlphaDummy089), (nb076AlphaDummy091 g a b)),
                                      ((nb076AlphaDummy090), (nb076AlphaDummy092 g a b)),
                                      ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                      ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                      ((nb076AlphaDummy087), (nb076AlphaDummy088 g a b)),
                                      ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                      ((nb076AlphaDummy002), g),
                                      ((nb076AlphaDummy001), b),
                                      ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part011`. -/


section

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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0005`. -/
@[expose]
noncomputable def nb076SplitAlpha0005 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
        ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
        ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
        ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
        ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
        ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy125))
          (Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy125)) (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCphi (Class.cv (nb076AlphaDummy120)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy126 g b))
          (Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy126 g b))
            (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCphi (Class.cv (nb076AlphaDummy122 g b))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy120) from
                    (by
                      unfold nb076AlphaDummy120;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
                  (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy122 g b) from (by
                      unfold nb076AlphaDummy122;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0126 g b) 1)))) (TAlphaVar.there
                    (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy119) from (by
                        unfold nb076AlphaDummy119;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))))
                    (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy121 g b) from (by
                        unfold nb076AlphaDummy121;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy125) from (by
                          unfold nb076AlphaDummy125;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0128) 0))))
                      (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy126 g b) from (by
                          unfold nb076AlphaDummy126;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0129 g b) 0))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy123) from (by
                            unfold nb076AlphaDummy123;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0125) 0))))
                        (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy124 g b) from (by
                            unfold nb076AlphaDummy124;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0127 g b) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb076AlphaDummy001))).fv ∪
                              ((Class.cv (nb076AlphaDummy002))).fv) (by decide))
                          (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv g)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb076AlphaDummy113))).fv ∪
                      ((Class.cv (nb076AlphaDummy114))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
                      ((Class.cv (nb076AlphaDummy116 g b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy127) from (by
                              unfold nb076AlphaDummy127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0130) 0))))
                          (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy129 g b) from
                            (by
                              unfold nb076AlphaDummy129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0131 g b) 0))))
                          (TAlphaVar.there
                            (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy128) from (by
                                unfold nb076AlphaDummy128;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0130) 1)))) (show
                              (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy130 g b) from (by
                                unfold nb076AlphaDummy130;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0131 g b) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076AlphaDummy120))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076AlphaDummy122 g b))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy134) from (by
          unfold nb076AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 1)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy137 g b) from (by
          unfold nb076AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy127) ≠ (nb076AlphaDummy133) from (by
          unfold nb076AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy136 g b) from (by
          unfold nb076AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131)
        from (by
          unfold nb076AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132) 0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy132 g b) from (by
          unfold nb076AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy135), (nb076AlphaDummy138 g b)), ((nb076AlphaDummy134),
        (nb076AlphaDummy137 g b)), ((nb076AlphaDummy133), (nb076AlphaDummy136 g b)),
        ((nb076AlphaDummy131), (nb076AlphaDummy132 g b)), ((nb076AlphaDummy127),
        (nb076AlphaDummy129 g b)), ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
        ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119),
        (nb076AlphaDummy121 g b)), ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114),
        (nb076AlphaDummy116 g b)), ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠
        (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy135), (nb076AlphaDummy138 g b)), ((nb076AlphaDummy134),
        (nb076AlphaDummy137 g b)), ((nb076AlphaDummy133), (nb076AlphaDummy136 g b)),
        ((nb076AlphaDummy131), (nb076AlphaDummy132 g b)), ((nb076AlphaDummy127),
        (nb076AlphaDummy129 g b)), ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
        ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119),
        (nb076AlphaDummy121 g b)), ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114),
        (nb076AlphaDummy116 g b)), ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy127))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy129 g
        b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy145) from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy145)
        from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠
        (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                        unfold nb076AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0132)
                                                0)))) (show (nb076AlphaDummy129 g b) ≠
                                        (nb076AlphaDummy132 g b) from (by
                                        unfold nb076AlphaDummy132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0133 g b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                                    ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                                    ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                                    ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                                    ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                                    ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
                                    ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                                    ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                                    ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                                    ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                                    ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                    ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                    ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                                    ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                    ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                                    ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from
                                    (by
                                      unfold nb076AlphaDummy131;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0132)
                                              0)))) (show (nb076AlphaDummy129 g b) ≠
                                      (nb076AlphaDummy132 g b) from (by
                                      unfold nb076AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0133 g b)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                        unfold nb076AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0132)
                                                0)))) (show (nb076AlphaDummy129 g b) ≠
                                        (nb076AlphaDummy132 g b) from (by
                                        unfold nb076AlphaDummy132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0133 g b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                                    ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                                    ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                                    ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                                    ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                                    ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
                                    ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                                    ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                                    ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                                    ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                                    ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                    ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                    ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                                    ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                    ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                                    ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy120) from
                      (by
                        unfold nb076AlphaDummy120;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
                    (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy122 g b) from (by
                        unfold nb076AlphaDummy122;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy119) from (by
                          unfold nb076AlphaDummy119;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0124) 0))))
                      (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy121 g b) from (by
                          unfold nb076AlphaDummy121;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy125) from (by
                            unfold nb076AlphaDummy125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0128) 0))))
                        (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy126 g b) from (by
                            unfold nb076AlphaDummy126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0129 g b) 0))))
                        (TAlphaVar.there
                          (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy123) from (by
                              unfold nb076AlphaDummy123;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0125) 0))))
                          (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy124 g b) from
                            (by
                              unfold nb076AlphaDummy124;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0127 g b) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb076AlphaDummy001))).fv ∪
                                ((Class.cv (nb076AlphaDummy002))).fv) (by decide))
                            (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv g)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb076AlphaDummy113))).fv ∪
                        ((Class.cv (nb076AlphaDummy114))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
                        ((Class.cv (nb076AlphaDummy116 g b))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy127) from (by
                                unfold nb076AlphaDummy127;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0130) 0)))) (show
                              (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy129 g b) from (by
                                unfold nb076AlphaDummy129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0131 g b) 0))))
                            (TAlphaVar.there
                              (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy128) from (by
                                  unfold nb076AlphaDummy128;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0130) 1)))) (show
                                (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy130 g b) from
                                (by
                                  unfold nb076AlphaDummy130;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0131 g b)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076AlphaDummy120))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb076AlphaDummy122 g b))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy127) ≠ (nb076AlphaDummy134) from (by
          unfold nb076AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 1)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy137 g b) from (by
          unfold nb076AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy133)
        from (by
          unfold nb076AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy136 g b) from (by
          unfold nb076AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131)
        from (by
          unfold nb076AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132)
                  0)))) (show (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy132 g b) from (by
          unfold nb076AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy135), (nb076AlphaDummy138 g b)), ((nb076AlphaDummy134),
        (nb076AlphaDummy137 g b)), ((nb076AlphaDummy133), (nb076AlphaDummy136 g b)),
        ((nb076AlphaDummy131), (nb076AlphaDummy132 g b)), ((nb076AlphaDummy127),
        (nb076AlphaDummy129 g b)), ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
        ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119),
        (nb076AlphaDummy121 g b)), ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114),
        (nb076AlphaDummy116 g b)), ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠
        (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy135), (nb076AlphaDummy138 g b)), ((nb076AlphaDummy134),
        (nb076AlphaDummy137 g b)), ((nb076AlphaDummy133), (nb076AlphaDummy136 g b)),
        ((nb076AlphaDummy131), (nb076AlphaDummy132 g b)), ((nb076AlphaDummy127),
        (nb076AlphaDummy129 g b)), ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
        ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119),
        (nb076AlphaDummy121 g b)), ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114),
        (nb076AlphaDummy116 g b)), ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy127))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy129 g
        b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy145) from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy145)
        from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠
        (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from
                                        (by
                                          unfold nb076AlphaDummy131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0132)
                                                  0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy132 g b) from (by
                                          unfold nb076AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0133 g b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                                      ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                                      ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                                      ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                                      ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                                      ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
                                      ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                                      ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                                      ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                                      ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                                      ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                      ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                      ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                                      ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                      ((nb076AlphaDummy002), g),
                                      ((nb076AlphaDummy001), b),
                                      ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                        unfold nb076AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0132)
                                                0)))) (show (nb076AlphaDummy129 g b) ≠
                                        (nb076AlphaDummy132 g b) from (by
                                        unfold nb076AlphaDummy132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0133 g b) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from
                                        (by
                                          unfold nb076AlphaDummy131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0132)
                                                  0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy132 g b) from (by
                                          unfold nb076AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0133 g b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                                      ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                                      ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                                      ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                                      ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                                      ((nb076AlphaDummy125), (nb076AlphaDummy126 g b)),
                                      ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                                      ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                                      ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                                      ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                                      ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                                      ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                                      ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                                      ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                                      ((nb076AlphaDummy002), g),
                                      ((nb076AlphaDummy001), b),
                                      ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part012`. -/


section

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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0006`. -/
@[expose]
noncomputable def nb076SplitAlpha0006 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076AlphaDummy153), (nb076AlphaDummy154 g b)),
        ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)),
        ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
        ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
        ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)),
        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
        ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
        ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
        ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
        ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
        ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy153))
          (synCphi (Class.cv (nb076AlphaDummy120)))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy153))
            (synCphi (Class.cv (nb076AlphaDummy120))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy154 g b))
          (synCphi (Class.cv (nb076AlphaDummy122 g b)))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy154 g b))
            (synCphi (Class.cv (nb076AlphaDummy122 g b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy127) from
                    (by
                      unfold nb076AlphaDummy127;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0130) 0))))
                  (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy129 g b) from (by
                      unfold nb076AlphaDummy129;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0131 g b) 0)))) (TAlphaVar.there
                    (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy128) from (by
                        unfold nb076AlphaDummy128;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0130) 1))))
                    (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy130 g b) from (by
                        unfold nb076AlphaDummy130;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0131 g b) 1))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy153) from (by
                          unfold nb076AlphaDummy153;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0160) 0))))
                      (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy154 g b) from (by
                          unfold nb076AlphaDummy154;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0161 g b) 0))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy151) from (by
                            unfold nb076AlphaDummy151;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0158) 0))))
                        (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy152 g b) from (by
                            unfold nb076AlphaDummy152;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0159 g b) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy120))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb076AlphaDummy122 g b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy127) ≠ (nb076AlphaDummy134) from (by
                                        unfold nb076AlphaDummy134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0134)
                                                1)))) (show (nb076AlphaDummy129 g b) ≠
                                        (nb076AlphaDummy137 g b) from (by
                                        unfold nb076AlphaDummy137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0135 g b) 1))))
                                    (TAlphaVar.there (show
                                        (nb076AlphaDummy127) ≠ (nb076AlphaDummy133) from
                                        (by
                                          unfold nb076AlphaDummy133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0134)
                                                  0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy136 g b) from (by
                                          unfold nb076AlphaDummy136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0135 g b) 0))))
                                      (TAlphaVar.there (show (nb076AlphaDummy127) ≠
        (nb076AlphaDummy131) from (by
          unfold nb076AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132) 0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy132 g b) from (by
          unfold nb076AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb076AlphaDummy135),
        (nb076AlphaDummy138 g b)), ((nb076AlphaDummy134), (nb076AlphaDummy137 g b)),
                                        ((nb076AlphaDummy133), (nb076AlphaDummy136 g b)),
                                        ((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                                        ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                                        ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                                        ((nb076AlphaDummy153), (nb076AlphaDummy154 g b)),
                                        ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)),
                                        ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                                        ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                                        ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)),
                                        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                                        ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                                        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                                        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                                        ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
                                        ((nb076AlphaDummy001), b),
                                        ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
                                        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb076AlphaDummy135), (nb076AlphaDummy138 g b)),
        ((nb076AlphaDummy134), (nb076AlphaDummy137 g b)), ((nb076AlphaDummy133),
        (nb076AlphaDummy136 g b)), ((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
        ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)), ((nb076AlphaDummy128),
        (nb076AlphaDummy130 g b)), ((nb076AlphaDummy153), (nb076AlphaDummy154 g b)),
        ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)), ((nb076AlphaDummy120),
        (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
        ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)), ((nb076AlphaDummy123),
        (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)), ((nb076AlphaDummy117),
        (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy129 g b))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠
        (nb076AlphaDummy145) from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy145)
        from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠
        (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                unfold nb076AlphaDummy131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                              (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy132 g b) from (by
                                unfold nb076AlphaDummy132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                            ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                            ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                            ((nb076AlphaDummy153), (nb076AlphaDummy154 g b)),
                            ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)),
                            ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                            ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                            ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)),
                            ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                            ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                            ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                            ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                            ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                            ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                            ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                            ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                            ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                            ((nb076AlphaDummy000), a),
                            ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
                            ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                            ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                              unfold nb076AlphaDummy131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0132) 0))))
                          (show (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy132 g b) from
                            (by
                              unfold nb076AlphaDummy132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                unfold nb076AlphaDummy131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                              (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy132 g b) from (by
                                unfold nb076AlphaDummy132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                            ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                            ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                            ((nb076AlphaDummy153), (nb076AlphaDummy154 g b)),
                            ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)),
                            ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                            ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                            ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)),
                            ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                            ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                            ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                            ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                            ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                            ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                            ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                            ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                            ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                            ((nb076AlphaDummy000), a),
                            ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
                            ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                            ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy127) from (by
                        unfold nb076AlphaDummy127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0130) 0))))
                    (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy129 g b) from (by
                        unfold nb076AlphaDummy129;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0131 g b) 0))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy128) from (by
                          unfold nb076AlphaDummy128;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0130) 1))))
                      (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy130 g b) from (by
                          unfold nb076AlphaDummy130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0131 g b) 1))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy153) from (by
                            unfold nb076AlphaDummy153;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0160) 0))))
                        (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy154 g b) from (by
                            unfold nb076AlphaDummy154;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0161 g b) 0))))
                        (TAlphaVar.there
                          (show (nb076AlphaDummy120) ≠ (nb076AlphaDummy151) from (by
                              unfold nb076AlphaDummy151;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0158) 0))))
                          (show (nb076AlphaDummy122 g b) ≠ (nb076AlphaDummy152 g b) from
                            (by
                              unfold nb076AlphaDummy152;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0159 g b) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy120))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb076AlphaDummy122 g b))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb076AlphaDummy127) ≠ (nb076AlphaDummy134) from
                                        (by
                                          unfold nb076AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0134)
                                                  1)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy137 g b) from (by
                                          unfold nb076AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0135 g b) 1))))
                                      (TAlphaVar.there (show (nb076AlphaDummy127) ≠
        (nb076AlphaDummy133) from (by
          unfold nb076AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy136 g b) from (by
          unfold nb076AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b) 0)))) (TAlphaVar.there (show
        (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
          unfold nb076AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132) 0)))) (show (nb076AlphaDummy129 g b) ≠
        (nb076AlphaDummy132 g b) from (by
          unfold nb076AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb076AlphaDummy135),
        (nb076AlphaDummy138 g b)), ((nb076AlphaDummy134), (nb076AlphaDummy137 g b)),
        ((nb076AlphaDummy133), (nb076AlphaDummy136 g b)), ((nb076AlphaDummy131),
        (nb076AlphaDummy132 g b)), ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
        ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)), ((nb076AlphaDummy153),
        (nb076AlphaDummy154 g b)), ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)),
        ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119),
        (nb076AlphaDummy121 g b)), ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)),
        ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114),
        (nb076AlphaDummy116 g b)), ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
        ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082),
        (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy141) from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy141)
        from (by
          unfold
            nb076AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy142 g b) from (by
          unfold
            nb076AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy139)
        from (by
          unfold
            nb076AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy140 g b) from (by
          unfold
            nb076AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy135), (nb076AlphaDummy138 g b)), ((nb076AlphaDummy134),
        (nb076AlphaDummy137 g b)), ((nb076AlphaDummy133), (nb076AlphaDummy136 g b)),
        ((nb076AlphaDummy131), (nb076AlphaDummy132 g b)), ((nb076AlphaDummy127),
        (nb076AlphaDummy129 g b)), ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
        ((nb076AlphaDummy153), (nb076AlphaDummy154 g b)), ((nb076AlphaDummy151),
        (nb076AlphaDummy152 g b)), ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
        ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)), ((nb076AlphaDummy149),
        (nb076AlphaDummy150 g b)), ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
        ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)), ((nb076AlphaDummy113),
        (nb076AlphaDummy115 g b)), ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
        ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)), ((nb076AlphaDummy081),
        (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085),
        (nb076AlphaDummy086 g a b)), ((nb076AlphaDummy002), g),
        ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy129 g b))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠
        (nb076AlphaDummy145) from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy145)
        from (by
          unfold
            nb076AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy146 g b) from (by
          unfold
            nb076AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy134) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy135) ≠
        (nb076AlphaDummy147) from (by
          unfold
            nb076AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy148 g b) from (by
          unfold
            nb076AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy135) ≠ (nb076AlphaDummy143)
        from (by
          unfold
            nb076AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076AlphaDummy138 g b) ≠ (nb076AlphaDummy144 g b) from (by
          unfold
            nb076AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                  unfold nb076AlphaDummy131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                                (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy132 g b) from
                                (by
                                  unfold nb076AlphaDummy132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0133 g b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                              ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                              ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                              ((nb076AlphaDummy153), (nb076AlphaDummy154 g b)),
                              ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)),
                              ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                              ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                              ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)),
                              ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                              ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                              ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                              ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                              ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                              ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                              ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                              ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                              ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                              ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                (nb076AlphaDummy006 g m n a b)),
                              ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                              ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                unfold nb076AlphaDummy131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                              (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy132 g b) from (by
                                unfold nb076AlphaDummy132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb076AlphaDummy127) ≠ (nb076AlphaDummy131) from (by
                                  unfold nb076AlphaDummy131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                                (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy132 g b) from
                                (by
                                  unfold nb076AlphaDummy132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0133 g b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb076AlphaDummy131), (nb076AlphaDummy132 g b)),
                              ((nb076AlphaDummy127), (nb076AlphaDummy129 g b)),
                              ((nb076AlphaDummy128), (nb076AlphaDummy130 g b)),
                              ((nb076AlphaDummy153), (nb076AlphaDummy154 g b)),
                              ((nb076AlphaDummy151), (nb076AlphaDummy152 g b)),
                              ((nb076AlphaDummy120), (nb076AlphaDummy122 g b)),
                              ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
                              ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)),
                              ((nb076AlphaDummy123), (nb076AlphaDummy124 g b)),
                              ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
                              ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)),
                              ((nb076AlphaDummy117), (nb076AlphaDummy118 g b)),
                              ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
                              ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)),
                              ((nb076AlphaDummy111), (nb076AlphaDummy112 g a b)),
                              ((nb076AlphaDummy085), (nb076AlphaDummy086 g a b)),
                              ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
                              ((nb076AlphaDummy000), a), ((nb076AlphaDummy005),
                                (nb076AlphaDummy006 g m n a b)),
                              ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                              ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
