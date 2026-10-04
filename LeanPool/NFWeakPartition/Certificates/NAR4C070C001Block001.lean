/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C070C001Part002Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C070C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb070_power_variable_occurrence`. -/
@[expose]
noncomputable def nb070PowerVariableOccurrence (x : Var) (A : Class) (b : Var) :
    TAlphaClass
      [((nb070AlphaDummy022 A), (nb070AlphaDummy023 x)),
        ((nb070AlphaDummy020 A), (nb070AlphaDummy021 x)),
        ((nb070AlphaDummy018 A), (nb070AlphaDummy019 x)),
        ((nb070AlphaDummy016 A), (nb070AlphaDummy017 x)),
        ((nb070AlphaDummy014 A), (nb070AlphaDummy015 x)),
        ((nb070AlphaDummy012 A), (nb070AlphaDummy013 x)),
        ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Class.cv (nb070AlphaDummy001 A)) (Class.cv x) :=
  by
  have freshness0 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy022 A) :=
    by
    unfold nb070AlphaDummy022
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0016 A) 0))
  have freshness1 : x ≠ (nb070AlphaDummy023 x) :=
    by
    unfold nb070AlphaDummy023
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0017 x) 0))
  have freshness2 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy020 A) :=
    by
    unfold nb070AlphaDummy020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0014 A) 0))
  have freshness3 : x ≠ (nb070AlphaDummy021 x) :=
    by
    unfold nb070AlphaDummy021
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0015 x) 0))
  have freshness4 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy018 A) :=
    by
    unfold nb070AlphaDummy018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0012 A) 0))
  have freshness5 : x ≠ (nb070AlphaDummy019 x) :=
    by
    unfold nb070AlphaDummy019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0013 x) 0))
  have freshness6 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy016 A) :=
    by
    unfold nb070AlphaDummy016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0010 A) 0))
  have freshness7 : x ≠ (nb070AlphaDummy017 x) :=
    by
    unfold nb070AlphaDummy017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0011 x) 0))
  have freshness8 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy014 A) :=
    by
    unfold nb070AlphaDummy014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0008 A) 0))
  have freshness9 : x ≠ (nb070AlphaDummy015 x) :=
    by
    unfold nb070AlphaDummy015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0009 x) 0))
  have freshness10 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy012 A) :=
    by
    unfold nb070AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0006 A) 0))
  have freshness11 : x ≠ (nb070AlphaDummy013 x) :=
    by
    unfold nb070AlphaDummy013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0007 x) 0))
  have freshness12 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy009 A) :=
    by
    unfold nb070AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 1))
  have freshness13 : x ≠ (nb070AlphaDummy011 x) :=
    by
    unfold nb070AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 1))
  have freshness14 : (nb070AlphaDummy001 A) ≠ (nb070AlphaDummy008 A) :=
    by
    unfold nb070AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 0))
  have freshness15 : x ≠ (nb070AlphaDummy010 x) :=
    by
    unfold nb070AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13
                      (TAlphaVar.there freshness14 freshness15 (TAlphaVar.here _ _ _))))))))))

/-- Checked nominal proof certificate identified upstream as `nb070_split_alpha_0000`. -/
@[expose]
noncomputable def nb070SplitAlpha0000 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070AlphaDummy014 A), (nb070AlphaDummy015 x)),
        ((nb070AlphaDummy012 A), (nb070AlphaDummy013 x)),
        ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Wff.imp (Wff.classMem (Class.cv (nb070AlphaDummy014 A))
          (synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb070AlphaDummy014 A))
            (synCnin (synCpw (Class.cv (nb070AlphaDummy001 A))) (synC1c)))))
      (Wff.imp (Wff.classMem (Class.cv (nb070AlphaDummy015 x))
          (synCnin (synCpw (Class.cv x)) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb070AlphaDummy015 x))
            (synCnin (synCpw (Class.cv x)) (synC1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0002 A) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0003 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (nb070PowerVariableOccurrence x A b))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0002 A) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0003 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (nb070PowerVariableOccurrence x A b)))))))))
                  (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfClosed
                [((nb070AlphaDummy016 A), (nb070AlphaDummy017 x)),
                  ((nb070AlphaDummy014 A), (nb070AlphaDummy015 x)),
                  ((nb070AlphaDummy012 A), (nb070AlphaDummy013 x)),
                  ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                  ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                  ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                  ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                  ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                  ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                (synC1c) (by simp only [fv_syn_c1c]))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (nb070PowerVariableOccurrence x A b))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (nb070PowerVariableOccurrence x A b)))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb070AlphaDummy016 A), (nb070AlphaDummy017 x)),
                    ((nb070AlphaDummy014 A), (nb070AlphaDummy015 x)),
                    ((nb070AlphaDummy012 A), (nb070AlphaDummy013 x)),
                    ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                    ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                    ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                    ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                    ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                    ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                  (synC1c) (by simp only [fv_syn_c1c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C070C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb070_split_alpha_0001`. -/
@[expose]
noncomputable def nb070SplitAlpha0001 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070AlphaDummy040 A), (nb070AlphaDummy043 x)),
        ((nb070AlphaDummy039 A), (nb070AlphaDummy042 x)),
        ((nb070AlphaDummy038 A), (nb070AlphaDummy041 x)),
        ((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
        ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
        ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
        ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
        ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
        ((nb070AlphaDummy030 A), (nb070AlphaDummy031 x)),
        ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
        ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070AlphaDummy038 A))
            (synCun (Class.cv (nb070AlphaDummy039 A))
              (Class.cv (nb070AlphaDummy040 A))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070AlphaDummy041 x))
            (synCun (Class.cv (nb070AlphaDummy042 x))
              (Class.cv (nb070AlphaDummy043 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb070AlphaDummy040 A), (nb070AlphaDummy043 x)),
          ((nb070AlphaDummy039 A), (nb070AlphaDummy042 x)),
          ((nb070AlphaDummy038 A), (nb070AlphaDummy041 x)),
          ((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
          ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
          ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
          ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
          ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
          ((nb070AlphaDummy030 A), (nb070AlphaDummy031 x)),
          ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
          ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
          ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
          ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
          ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
          ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
          ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy050 A) from (by
                                unfold nb070AlphaDummy050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy051 x) from (by
                                unfold nb070AlphaDummy051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy050 A) from (by
                                unfold nb070AlphaDummy050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy051 x) from (by
                                unfold nb070AlphaDummy051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy052 A) from (by
                                unfold nb070AlphaDummy052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy053 x) from (by
                                unfold nb070AlphaDummy053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy052 A) from (by
                                unfold nb070AlphaDummy052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy053 x) from (by
                                unfold nb070AlphaDummy053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb070_split_alpha_0002`. -/
@[expose]
noncomputable def nb070SplitAlpha0002 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
        ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
        ((nb070AlphaDummy030 A), (nb070AlphaDummy031 x)),
        ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
        ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
        (synCphi (Class.cv (nb070AlphaDummy025 A))))
      (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
        (synCphi (Class.cv (nb070AlphaDummy027 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb070AlphaDummy009 A))).fv ∪
            ((Class.cv (nb070AlphaDummy008 A))).fv) (by decide)) (freshVar_injective
          (((Class.cv (nb070AlphaDummy011 x))).fv ∪
            ((Class.cv (nb070AlphaDummy010 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb070AlphaDummy025 A) ≠ (nb070AlphaDummy032 A) from
                  (by
                    unfold nb070AlphaDummy032;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 0))))
                (show (nb070AlphaDummy027 x) ≠ (nb070AlphaDummy034 x) from (by
                    unfold nb070AlphaDummy034;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 0))))
                (TAlphaVar.there
                  (show (nb070AlphaDummy025 A) ≠ (nb070AlphaDummy033 A) from (by
                      unfold nb070AlphaDummy033;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 1))))
                  (show (nb070AlphaDummy027 x) ≠ (nb070AlphaDummy035 x) from (by
                      unfold nb070AlphaDummy035;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb070AlphaDummy025 A))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb070AlphaDummy027 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy039 A) from
                                    (by
                                      unfold nb070AlphaDummy039;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0028 A)
                                              1)))) (show
                                    (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy042 x) from
                                    (by
                                      unfold nb070AlphaDummy042;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0029 x)
                                              1)))) (TAlphaVar.there (show
                                      (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy038 A) from
                                      (by
                                        unfold nb070AlphaDummy038;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb070_support_mem_0028 A)
                                                0)))) (show (nb070AlphaDummy034 x) ≠
                                        (nb070AlphaDummy041 x) from (by
                                        unfold nb070AlphaDummy041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb070_support_mem_0029 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A)
                                        from (by
                                          unfold nb070AlphaDummy036;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb070_support_mem_0026 A) 0)))) (show
                                        (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x)
                                        from (by
                                          unfold nb070AlphaDummy037;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb070_support_mem_0027 x) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed [((nb070AlphaDummy040 A),
                                        (nb070AlphaDummy043 x)), ((nb070AlphaDummy039 A),
                                        (nb070AlphaDummy042 x)), ((nb070AlphaDummy038 A),
                                        (nb070AlphaDummy041 x)), ((nb070AlphaDummy036 A),
                                        (nb070AlphaDummy037 x)), ((nb070AlphaDummy032 A),
                                        (nb070AlphaDummy034 x)), ((nb070AlphaDummy033 A),
                                        (nb070AlphaDummy035 x)), ((nb070AlphaDummy025 A),
                                        (nb070AlphaDummy027 x)), ((nb070AlphaDummy024 A),
                                        (nb070AlphaDummy026 x)), ((nb070AlphaDummy030 A),
                                        (nb070AlphaDummy031 x)), ((nb070AlphaDummy028 A),
                                        (nb070AlphaDummy029 x)), ((nb070AlphaDummy009 A),
                                        (nb070AlphaDummy011 x)), ((nb070AlphaDummy008 A),
                                        (nb070AlphaDummy010 x)),
                                      ((nb070AlphaDummy001 A), x),
                                      ((nb070AlphaDummy000 A), b),
                                      ((nb070AlphaDummy002 A),
                                        (nb070AlphaDummy003 x A b)),
                                      ((nb070AlphaDummy005 A),
                                        (nb070AlphaDummy007 x A b)),
                                      ((nb070AlphaDummy004 A),
                                        (nb070AlphaDummy006 x A b))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb070SplitAlpha0001 x A b))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A) from (by
                              unfold nb070AlphaDummy036;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                          (show (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x) from (by
                              unfold nb070AlphaDummy037;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
                          ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
                          ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
                          ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
                          ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
                          ((nb070AlphaDummy030 A), (nb070AlphaDummy031 x)),
                          ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
                          ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                          ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                          ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                          ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                          ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                          ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A) from (by
                            unfold nb070AlphaDummy036;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                        (show (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x) from (by
                            unfold nb070AlphaDummy037;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A) from (by
                              unfold nb070AlphaDummy036;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                          (show (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x) from (by
                              unfold nb070AlphaDummy037;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
                          ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
                          ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
                          ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
                          ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
                          ((nb070AlphaDummy030 A), (nb070AlphaDummy031 x)),
                          ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
                          ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                          ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                          ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                          ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                          ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                          ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb070_split_alpha_0003`. -/
@[expose]
noncomputable def nb070SplitAlpha0003 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070AlphaDummy040 A), (nb070AlphaDummy043 x)),
        ((nb070AlphaDummy039 A), (nb070AlphaDummy042 x)),
        ((nb070AlphaDummy038 A), (nb070AlphaDummy041 x)),
        ((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
        ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
        ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
        ((nb070AlphaDummy058 A), (nb070AlphaDummy059 x)),
        ((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
        ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
        ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
        ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
        ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
        ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb070AlphaDummy039 A))
            (Class.cv (nb070AlphaDummy040 A))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070AlphaDummy038 A))
            (synCun (Class.cv (nb070AlphaDummy039 A))
              (Class.cv (nb070AlphaDummy040 A))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb070AlphaDummy042 x))
            (Class.cv (nb070AlphaDummy043 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070AlphaDummy041 x))
            (synCun (Class.cv (nb070AlphaDummy042 x))
              (Class.cv (nb070AlphaDummy043 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy046 A) from (by
                              unfold nb070AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy047 x) from (by
                              unfold nb070AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy044 A) from (by
                                unfold nb070AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy045 x) from (by
                                unfold nb070AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb070AlphaDummy040 A), (nb070AlphaDummy043 x)),
          ((nb070AlphaDummy039 A), (nb070AlphaDummy042 x)),
          ((nb070AlphaDummy038 A), (nb070AlphaDummy041 x)),
          ((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
          ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
          ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
          ((nb070AlphaDummy058 A), (nb070AlphaDummy059 x)),
          ((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
          ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
          ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
          ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
          ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
          ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
          ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
          ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
          ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
          ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
          ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy050 A) from (by
                                unfold nb070AlphaDummy050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy051 x) from (by
                                unfold nb070AlphaDummy051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy050 A) from (by
                                unfold nb070AlphaDummy050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy051 x) from (by
                                unfold nb070AlphaDummy051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy039 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070AlphaDummy042 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy032 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070AlphaDummy034 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy052 A) from (by
                                unfold nb070AlphaDummy052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy053 x) from (by
                                unfold nb070AlphaDummy053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy052 A) from (by
                                unfold nb070AlphaDummy052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy053 x) from (by
                                unfold nb070AlphaDummy053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070AlphaDummy040 A) ≠ (nb070AlphaDummy048 A) from
                                (by
                                  unfold nb070AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070AlphaDummy043 x) ≠ (nb070AlphaDummy049 x) from
                                (by
                                  unfold nb070AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
