/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C071C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C071C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0005`. -/
@[expose]
noncomputable def nb071SplitAlpha0005 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy061), (nb071AlphaDummy062 x)),
        ((nb071AlphaDummy059), (nb071AlphaDummy060 x)),
        ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy061))
          (synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb071AlphaDummy061))
            (synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c)))))
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy062 x))
          (synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb071AlphaDummy062 x))
            (synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb071AlphaDummy065) ≠ (nb071AlphaDummy069) from
                                        (by
                                          unfold nb071AlphaDummy069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0054)
                                                  0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy070 x) from (by
                                          unfold nb071AlphaDummy070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0055 x) 0))))
                                      (TAlphaVar.there (show (nb071AlphaDummy065) ≠
        (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb071AlphaDummy042) ≠ (nb071AlphaDummy069) from
                                        (by
                                          unfold nb071AlphaDummy069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0068)
                                                  0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy070 x) from (by
                                          unfold nb071AlphaDummy070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0069 x) 0))))
                                      (TAlphaVar.there (show (nb071AlphaDummy042) ≠
        (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy065) from (by
          unfold nb071AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy066 x) from (by
          unfold nb071AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy063) from (by
          unfold nb071AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy064 x) from (by
          unfold nb071AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy061) from (by
          unfold nb071AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy062 x) from (by
          unfold nb071AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy059) from (by
          unfold nb071AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy060 x) from (by
          unfold nb071AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy056)
        from (by
          unfold nb071AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy058 x) from (by
          unfold nb071AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy055)
        from (by
          unfold nb071AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy057 x) from (by
          unfold nb071AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb071AlphaDummy065) ≠ (nb071AlphaDummy069) from
                                        (by
                                          unfold nb071AlphaDummy069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0054)
                                                  0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy070 x) from (by
                                          unfold nb071AlphaDummy070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0055 x) 0))))
                                      (TAlphaVar.there (show (nb071AlphaDummy065) ≠
        (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb071AlphaDummy042) ≠ (nb071AlphaDummy069) from
                                        (by
                                          unfold nb071AlphaDummy069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0068)
                                                  0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy070 x) from (by
                                          unfold nb071AlphaDummy070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0069 x) 0))))
                                      (TAlphaVar.there (show (nb071AlphaDummy042) ≠
        (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy065) from (by
          unfold nb071AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy066 x) from (by
          unfold nb071AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy063) from (by
          unfold nb071AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy064 x) from (by
          unfold nb071AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy061) from (by
          unfold nb071AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy062 x) from (by
          unfold nb071AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy059) from (by
          unfold nb071AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy060 x) from (by
          unfold nb071AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy056)
        from (by
          unfold nb071AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy058 x) from (by
          unfold nb071AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy055)
        from (by
          unfold nb071AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy057 x) from (by
          unfold nb071AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))
                  (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfClosed [((nb071AlphaDummy063), (nb071AlphaDummy064 x)),
                  ((nb071AlphaDummy061), (nb071AlphaDummy062 x)),
                  ((nb071AlphaDummy059), (nb071AlphaDummy060 x)),
                  ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                  ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                  ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                  ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                  ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                  ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                  ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                  ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                  ((nb071AlphaDummy000), x),
                  ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                (synC1c) (by simp only [fv_syn_c1c]))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb071AlphaDummy065) ≠
        (nb071AlphaDummy069) from (by
          unfold nb071AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0054) 0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy070 x) from (by
          unfold nb071AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0055 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy065) ≠ (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cv (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy069) from (by
          unfold nb071AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0068) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy070 x) from (by
          unfold nb071AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0069 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy065) from (by
          unfold nb071AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy066 x) from (by
          unfold nb071AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy063) from (by
          unfold nb071AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy064 x) from (by
          unfold nb071AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy061) from (by
          unfold nb071AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy062 x) from (by
          unfold nb071AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy059)
        from (by
          unfold nb071AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058)
                  0)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy060 x) from (by
          unfold nb071AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy056)
        from (by
          unfold nb071AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy058 x) from (by
          unfold nb071AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy055)
        from (by
          unfold nb071AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy057 x) from (by
          unfold nb071AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb071AlphaDummy065) ≠
        (nb071AlphaDummy069) from (by
          unfold nb071AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0054) 0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy070 x) from (by
          unfold nb071AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0055 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy065) ≠ (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071AlphaDummy066 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cv (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy069) from (by
          unfold nb071AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0068) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy070 x) from (by
          unfold nb071AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0069 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy067) from (by
          unfold nb071AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy068 x) from (by
          unfold nb071AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy065) from (by
          unfold nb071AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy066 x) from (by
          unfold nb071AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy063) from (by
          unfold nb071AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy064 x) from (by
          unfold nb071AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy042) ≠ (nb071AlphaDummy061) from (by
          unfold nb071AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071AlphaDummy044 x) ≠
        (nb071AlphaDummy062 x) from (by
          unfold nb071AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy059)
        from (by
          unfold nb071AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058)
                  0)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy060 x) from (by
          unfold nb071AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy056)
        from (by
          unfold nb071AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy058 x) from (by
          unfold nb071AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071AlphaDummy042) ≠ (nb071AlphaDummy055)
        from (by
          unfold nb071AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071AlphaDummy044 x) ≠ (nb071AlphaDummy057 x) from (by
          unfold nb071AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb071AlphaDummy063), (nb071AlphaDummy064 x)),
                    ((nb071AlphaDummy061), (nb071AlphaDummy062 x)),
                    ((nb071AlphaDummy059), (nb071AlphaDummy060 x)),
                    ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                    ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                    ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                    ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                    ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                    ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                    ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                    ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                    ((nb071AlphaDummy000), x),
                    ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                  (synC1c) (by simp only [fv_syn_c1c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0006`. -/
@[expose]
noncomputable def nb071SplitAlpha0006 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy087), (nb071AlphaDummy090 x)),
        ((nb071AlphaDummy086), (nb071AlphaDummy089 x)),
        ((nb071AlphaDummy085), (nb071AlphaDummy088 x)),
        ((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
        ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
        ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
        ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
        ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
        ((nb071AlphaDummy077), (nb071AlphaDummy078 x)),
        ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
        ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb071AlphaDummy085))
            (synCun (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy088 x))
            (synCun (Class.cv (nb071AlphaDummy089 x))
              (Class.cv (nb071AlphaDummy090 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb071AlphaDummy087), (nb071AlphaDummy090 x)),
          ((nb071AlphaDummy086), (nb071AlphaDummy089 x)),
          ((nb071AlphaDummy085), (nb071AlphaDummy088 x)),
          ((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
          ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
          ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
          ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
          ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
          ((nb071AlphaDummy077), (nb071AlphaDummy078 x)),
          ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
          ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
          ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
          ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
          ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
          ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
          ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
          ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
          ((nb071AlphaDummy001), (nb071AlphaDummy002 x)), ((nb071AlphaDummy000), x),
          ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy097) from (by
                                unfold nb071AlphaDummy097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy098 x) from (by
                                unfold nb071AlphaDummy098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy097) from (by
                                unfold nb071AlphaDummy097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy098 x) from (by
                                unfold nb071AlphaDummy098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy099) from (by
                                unfold nb071AlphaDummy099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy100 x) from (by
                                unfold nb071AlphaDummy100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy099) from (by
                                unfold nb071AlphaDummy099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy100 x) from (by
                                unfold nb071AlphaDummy100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0007`. -/
@[expose]
noncomputable def nb071SplitAlpha0007 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
        ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
        ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
        ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
        ((nb071AlphaDummy077), (nb071AlphaDummy078 x)),
        ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
        ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy079))
          (Class.cv (nb071AlphaDummy072))) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy080))
            (synCif (Wff.classMem (Class.cv (nb071AlphaDummy079)) (synCnnc))
              (synCplc (Class.cv (nb071AlphaDummy079)) (synC1c))
              (Class.cv (nb071AlphaDummy079))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy081 x))
          (Class.cv (nb071AlphaDummy074 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy082 x))
            (synCif (Wff.classMem (Class.cv (nb071AlphaDummy081 x)) (synCnnc))
              (synCplc (Class.cv (nb071AlphaDummy081 x)) (synC1c))
              (Class.cv (nb071AlphaDummy081 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071AlphaDummy072) ≠ (nb071AlphaDummy079) from (by
              unfold nb071AlphaDummy079;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0076) 0))))
          (show (nb071AlphaDummy074 x) ≠ (nb071AlphaDummy081 x) from (by
              unfold nb071AlphaDummy081;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0077 x) 0))))
          (TAlphaVar.there (show (nb071AlphaDummy072) ≠ (nb071AlphaDummy080) from (by
                unfold nb071AlphaDummy080;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0076) 1))))
            (show (nb071AlphaDummy074 x) ≠ (nb071AlphaDummy082 x) from (by
                unfold nb071AlphaDummy082;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0077 x) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071AlphaDummy072))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb071AlphaDummy074 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy086) from (by
                                  unfold nb071AlphaDummy086;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0080) 1))))
                              (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy089 x) from
                                (by
                                  unfold nb071AlphaDummy089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0081 x) 1))))
                              (TAlphaVar.there
                                (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy085) from (by
                                    unfold nb071AlphaDummy085;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0080) 0)))) (show
                                  (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy088 x) from (by
                                    unfold nb071AlphaDummy088;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0081 x)
                                            0)))) (TAlphaVar.there
                                  (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from
                                    (by
                                      unfold nb071AlphaDummy083;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0078)
                                              0)))) (show
                                    (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from
                                    (by
                                      unfold nb071AlphaDummy084;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0079 x)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb071AlphaDummy087), (nb071AlphaDummy090 x)),
                                  ((nb071AlphaDummy086), (nb071AlphaDummy089 x)),
                                  ((nb071AlphaDummy085), (nb071AlphaDummy088 x)),
                                  ((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
                                  ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
                                  ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
                                  ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                                  ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                                  ((nb071AlphaDummy077), (nb071AlphaDummy078 x)),
                                  ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                                  ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                                  ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                                  ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                                  ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                                  ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                                  ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                                  ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                                  ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                                  ((nb071AlphaDummy000), x),
                                  ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb071SplitAlpha0006 x)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from (by
                          unfold nb071AlphaDummy083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                      (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from (by
                          unfold nb071AlphaDummy084;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
                      ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
                      ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
                      ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                      ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                      ((nb071AlphaDummy077), (nb071AlphaDummy078 x)),
                      ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                      ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                      ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                      ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                      ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                      ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                      ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                      ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                      ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                      ((nb071AlphaDummy000), x),
                      ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from
                      (by
                        unfold nb071AlphaDummy083;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                    (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from (by
                        unfold nb071AlphaDummy084;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from (by
                          unfold nb071AlphaDummy083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                      (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from (by
                          unfold nb071AlphaDummy084;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
                      ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
                      ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
                      ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                      ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                      ((nb071AlphaDummy077), (nb071AlphaDummy078 x)),
                      ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                      ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                      ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                      ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                      ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                      ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                      ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                      ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                      ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                      ((nb071AlphaDummy000), x),
                      ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C071C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0008`. -/
@[expose]
noncomputable def nb071SplitAlpha0008 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy087), (nb071AlphaDummy090 x)),
        ((nb071AlphaDummy086), (nb071AlphaDummy089 x)),
        ((nb071AlphaDummy085), (nb071AlphaDummy088 x)),
        ((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
        ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
        ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
        ((nb071AlphaDummy105), (nb071AlphaDummy106 x)),
        ((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
        ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
        ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
        ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
        ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
        ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb071AlphaDummy085))
            (synCun (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy088 x))
            (synCun (Class.cv (nb071AlphaDummy089 x))
              (Class.cv (nb071AlphaDummy090 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy093) from (by
                              unfold nb071AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy094 x) from (by
                              unfold nb071AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy091) from (by
                                unfold nb071AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy092 x) from (by
                                unfold nb071AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb071AlphaDummy087), (nb071AlphaDummy090 x)),
          ((nb071AlphaDummy086), (nb071AlphaDummy089 x)),
          ((nb071AlphaDummy085), (nb071AlphaDummy088 x)),
          ((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
          ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
          ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
          ((nb071AlphaDummy105), (nb071AlphaDummy106 x)),
          ((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
          ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
          ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
          ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
          ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
          ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
          ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
          ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
          ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
          ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
          ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
          ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
          ((nb071AlphaDummy001), (nb071AlphaDummy002 x)), ((nb071AlphaDummy000), x),
          ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy097) from (by
                                unfold nb071AlphaDummy097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy098 x) from (by
                                unfold nb071AlphaDummy098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy097) from (by
                                unfold nb071AlphaDummy097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy098 x) from (by
                                unfold nb071AlphaDummy098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy086) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy099) from (by
                                unfold nb071AlphaDummy099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy100 x) from (by
                                unfold nb071AlphaDummy100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy099) from (by
                                unfold nb071AlphaDummy099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy100 x) from (by
                                unfold nb071AlphaDummy100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy087) ≠ (nb071AlphaDummy095) from (by
                                  unfold nb071AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071AlphaDummy090 x) ≠ (nb071AlphaDummy096 x) from
                                (by
                                  unfold nb071AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0009`. -/
@[expose]
noncomputable def nb071SplitAlpha0009 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
        ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
        ((nb071AlphaDummy105), (nb071AlphaDummy106 x)),
        ((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
        ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
        ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
        ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
        ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
        ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.classEq (Class.cv (nb071AlphaDummy080))
        (synCif (Wff.classMem (Class.cv (nb071AlphaDummy079)) (synCnnc))
          (synCplc (Class.cv (nb071AlphaDummy079)) (synC1c))
          (Class.cv (nb071AlphaDummy079))))
      (Wff.classEq (Class.cv (nb071AlphaDummy082 x))
        (synCif (Wff.classMem (Class.cv (nb071AlphaDummy081 x)) (synCnnc))
          (synCplc (Class.cv (nb071AlphaDummy081 x)) (synC1c))
          (Class.cv (nb071AlphaDummy081 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb071AlphaDummy072))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb071AlphaDummy074 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy086) from (by
                              unfold nb071AlphaDummy086;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0080) 1))))
                          (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy089 x) from (by
                              unfold nb071AlphaDummy089;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0081 x) 1))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy085) from (by
                                unfold nb071AlphaDummy085;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0080) 0))))
                            (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy088 x) from (by
                                unfold nb071AlphaDummy088;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0081 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from (by
                                  unfold nb071AlphaDummy083;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                              (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from
                                (by
                                  unfold nb071AlphaDummy084;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb071AlphaDummy087), (nb071AlphaDummy090 x)),
                              ((nb071AlphaDummy086), (nb071AlphaDummy089 x)),
                              ((nb071AlphaDummy085), (nb071AlphaDummy088 x)),
                              ((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
                              ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
                              ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
                              ((nb071AlphaDummy105), (nb071AlphaDummy106 x)),
                              ((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
                              ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                              ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                              ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
                              ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                              ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                              ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                              ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                              ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                              ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                              ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                              ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                              ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                              ((nb071AlphaDummy000), x),
                              ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb071SplitAlpha0008 x)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from (by
                      unfold nb071AlphaDummy083;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                  (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from (by
                      unfold nb071AlphaDummy084;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
                  ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
                  ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
                  ((nb071AlphaDummy105), (nb071AlphaDummy106 x)),
                  ((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
                  ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                  ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                  ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
                  ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                  ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                  ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                  ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                  ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                  ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                  ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                  ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                  ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                  ((nb071AlphaDummy000), x),
                  ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from (by
                    unfold nb071AlphaDummy083;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from (by
                    unfold nb071AlphaDummy084;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb071AlphaDummy079) ≠ (nb071AlphaDummy083) from
                    (by
                      unfold nb071AlphaDummy083;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                  (show (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy084 x) from (by
                      unfold nb071AlphaDummy084;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb071AlphaDummy083), (nb071AlphaDummy084 x)),
                  ((nb071AlphaDummy079), (nb071AlphaDummy081 x)),
                  ((nb071AlphaDummy080), (nb071AlphaDummy082 x)),
                  ((nb071AlphaDummy105), (nb071AlphaDummy106 x)),
                  ((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
                  ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                  ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                  ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
                  ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                  ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                  ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                  ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                  ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                  ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                  ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                  ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                  ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                  ((nb071AlphaDummy000), x),
                  ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0010`. -/
@[expose]
noncomputable def nb071SplitAlpha0010 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
        ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
        ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy101))
          (Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb071AlphaDummy101))
            (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy102 x))
          (Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb071AlphaDummy102 x))
            (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy072) from
                    (by
                      unfold nb071AlphaDummy072;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
                  (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy074 x) from (by
                      unfold nb071AlphaDummy074;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))))
                  (TAlphaVar.there (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy071) from
                      (by
                        unfold nb071AlphaDummy071;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))))
                    (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy073 x) from (by
                        unfold nb071AlphaDummy073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0100 x) 0)))) (TAlphaVar.there
                      (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy101) from (by
                          unfold nb071AlphaDummy101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0102) 0))))
                      (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy102 x) from (by
                          unfold nb071AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0103 x) 0))))
                      (TAlphaVar.there
                        (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy075) from (by
                            unfold nb071AlphaDummy075;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0099) 0))))
                        (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy076 x) from (by
                            unfold nb071AlphaDummy076;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0101 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCen)).fv ∪ ((synCsn
                                  (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv)
                            (by decide)) (freshVar_injective (((synCen)).fv ∪ ((synCsn
                                  (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb071AlphaDummy056))).fv ∪
                      ((Class.cv (nb071AlphaDummy055))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb071AlphaDummy058 x))).fv ∪
                      ((Class.cv (nb071AlphaDummy057 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb071AlphaDummy072) ≠
        (nb071AlphaDummy079) from (by
          unfold nb071AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy081 x) from (by
          unfold nb071AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy080) from (by
          unfold nb071AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy082 x) from (by
          unfold nb071AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy105) from (by
          unfold nb071AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy106 x) from (by
          unfold nb071AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy103) from (by
          unfold nb071AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy104 x) from (by
          unfold nb071AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071SplitAlpha0009 x)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb071AlphaDummy072) ≠
        (nb071AlphaDummy079) from (by
          unfold nb071AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy081 x) from (by
          unfold nb071AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy080) from (by
          unfold nb071AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy082 x) from (by
          unfold nb071AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy105) from (by
          unfold nb071AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy106 x) from (by
          unfold nb071AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy103) from (by
          unfold nb071AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy104 x) from (by
          unfold nb071AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071SplitAlpha0009 x)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
                          ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                          ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                          ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
                          ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                          ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                          ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                          ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                          ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                          ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                          ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                          ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                          ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                          ((nb071AlphaDummy000), x),
                          ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy072) from
                      (by
                        unfold nb071AlphaDummy072;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
                    (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy074 x) from (by
                        unfold nb071AlphaDummy074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0100 x) 1)))) (TAlphaVar.there
                      (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy071) from (by
                          unfold nb071AlphaDummy071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0098) 0))))
                      (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy073 x) from (by
                          unfold nb071AlphaDummy073;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0100 x) 0))))
                      (TAlphaVar.there
                        (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy101) from (by
                            unfold nb071AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0102) 0))))
                        (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy102 x) from (by
                            unfold nb071AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0103 x) 0))))
                        (TAlphaVar.there
                          (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy075) from (by
                              unfold nb071AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0099) 0))))
                          (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy076 x) from (by
                              unfold nb071AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0101 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCen)).fv ∪ ((synCsn
                                    (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv)
                              (by decide)) (freshVar_injective (((synCen)).fv ∪ ((synCsn
                                    (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb071AlphaDummy056))).fv ∪
                        ((Class.cv (nb071AlphaDummy055))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb071AlphaDummy058 x))).fv ∪
                        ((Class.cv (nb071AlphaDummy057 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071AlphaDummy072) ≠ (nb071AlphaDummy079) from (by
          unfold nb071AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy081 x) from (by
          unfold nb071AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy080) from (by
          unfold nb071AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy082 x) from (by
          unfold nb071AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy105) from (by
          unfold nb071AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy106 x) from (by
          unfold nb071AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy072) ≠ (nb071AlphaDummy103)
        from (by
          unfold nb071AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104)
                  0)))) (show (nb071AlphaDummy074 x) ≠ (nb071AlphaDummy104 x) from (by
          unfold nb071AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071SplitAlpha0009 x)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071AlphaDummy072) ≠ (nb071AlphaDummy079) from (by
          unfold nb071AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy081 x) from (by
          unfold nb071AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy080) from (by
          unfold nb071AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy082 x) from (by
          unfold nb071AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071AlphaDummy072) ≠ (nb071AlphaDummy105) from (by
          unfold nb071AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071AlphaDummy074 x) ≠
        (nb071AlphaDummy106 x) from (by
          unfold nb071AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy072) ≠ (nb071AlphaDummy103)
        from (by
          unfold nb071AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104)
                  0)))) (show (nb071AlphaDummy074 x) ≠ (nb071AlphaDummy104 x) from (by
          unfold nb071AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071SplitAlpha0009 x)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb071AlphaDummy103), (nb071AlphaDummy104 x)),
                            ((nb071AlphaDummy072), (nb071AlphaDummy074 x)),
                            ((nb071AlphaDummy071), (nb071AlphaDummy073 x)),
                            ((nb071AlphaDummy101), (nb071AlphaDummy102 x)),
                            ((nb071AlphaDummy075), (nb071AlphaDummy076 x)),
                            ((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                            ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                            ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                            ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                            ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                            ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                            ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                            ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                            ((nb071AlphaDummy000), x),
                            ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb071_wpp_notmem_0264 : (nb071AlphaDummy056) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy056, fv_syn_cen] using (nb071_compact_fv_empty_0046)

theorem nb071_wpp_notmem_0265 (x : Var) : (nb071AlphaDummy058 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy058, fv_syn_cen] using (nb071_compact_fv_empty_0047 x)

theorem nb071_wpp_notmem_0266 : (nb071AlphaDummy055) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy055, fv_syn_cen] using (nb071_compact_fv_empty_0048)

theorem nb071_wpp_notmem_0267 (x : Var) : (nb071AlphaDummy057 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy057, fv_syn_cen] using (nb071_compact_fv_empty_0049 x)

theorem nb071_wpp_notmem_0268 : (nb071AlphaDummy042) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy042, fv_syn_cen] using (nb071_compact_fv_empty_0050)

theorem nb071_wpp_notmem_0269 (x : Var) : (nb071AlphaDummy044 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy044, fv_syn_cen] using (nb071_compact_fv_empty_0051 x)

theorem nb071_wpp_notmem_0270 : (nb071AlphaDummy041) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy041, fv_syn_cen] using (nb071_compact_fv_empty_0032)

theorem nb071_wpp_notmem_0271 (x : Var) : (nb071AlphaDummy043 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy043, fv_syn_cen] using (nb071_compact_fv_empty_0033 x)

theorem nb071_wpp_notmem_0272 : (nb071AlphaDummy045) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy045, fv_syn_cen] using (nb071_compact_fv_empty_0034)

theorem nb071_wpp_notmem_0273 (x : Var) : (nb071AlphaDummy046 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy046, fv_syn_cen] using (nb071_compact_fv_empty_0035 x)

theorem nb071_wpp_notmem_0274 : (nb071AlphaDummy048) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy048, fv_syn_cen] using (nb071_compact_fv_empty_0036)

theorem nb071_wpp_notmem_0275 (x : Var) : (nb071AlphaDummy050 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy050, fv_syn_cen] using (nb071_compact_fv_empty_0037 x)

theorem nb071_wpp_notmem_0276 : (nb071AlphaDummy047) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy047, fv_syn_cen] using (nb071_compact_fv_empty_0038)

theorem nb071_wpp_notmem_0277 (x : Var) : (nb071AlphaDummy049 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy049, fv_syn_cen] using (nb071_compact_fv_empty_0039 x)

theorem nb071_wpp_notmem_0278 : (nb071AlphaDummy001) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy001, fv_syn_cen] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0279 (x : Var) : (nb071AlphaDummy002 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy002, fv_syn_cen] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0280 : (nb071AlphaDummy000) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy000, fv_syn_cen] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0281 (x : Var) : x ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0282 : (nb071AlphaDummy003) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy003, fv_syn_cen] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0283 (x : Var) : (nb071AlphaDummy004 x) ∉ ((synCen)).fv := by
  simpa only [nb071AlphaDummy004, fv_syn_cen] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0017 (x : Var) :
    TEnvFresh
      [((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      ((synCen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb071AlphaDummy056) (nb071AlphaDummy058 x)
      (nb071_wpp_notmem_0264) (nb071_wpp_notmem_0265 x)
      (TEnvFresh.consFresh (nb071AlphaDummy055) (nb071AlphaDummy057 x)
        (nb071_wpp_notmem_0266) (nb071_wpp_notmem_0267 x)
        (TEnvFresh.consFresh (nb071AlphaDummy042) (nb071AlphaDummy044 x)
          (nb071_wpp_notmem_0268) (nb071_wpp_notmem_0269 x)
          (TEnvFresh.consFresh (nb071AlphaDummy041) (nb071AlphaDummy043 x)
            (nb071_wpp_notmem_0270) (nb071_wpp_notmem_0271 x)
            (TEnvFresh.consFresh (nb071AlphaDummy045) (nb071AlphaDummy046 x)
              (nb071_wpp_notmem_0272) (nb071_wpp_notmem_0273 x)
              (TEnvFresh.consFresh (nb071AlphaDummy048) (nb071AlphaDummy050 x)
                (nb071_wpp_notmem_0274) (nb071_wpp_notmem_0275 x)
                (TEnvFresh.consFresh (nb071AlphaDummy047) (nb071AlphaDummy049 x)
                  (nb071_wpp_notmem_0276) (nb071_wpp_notmem_0277 x)
                  (TEnvFresh.consFresh (nb071AlphaDummy001) (nb071AlphaDummy002 x)
                    (nb071_wpp_notmem_0278) (nb071_wpp_notmem_0279 x)
                    (TEnvFresh.consFresh (nb071AlphaDummy000) x (nb071_wpp_notmem_0280)
                      (nb071_wpp_notmem_0281 x) (TEnvFresh.consFresh (nb071AlphaDummy003)
                        (nb071AlphaDummy004 x) (nb071_wpp_notmem_0282)
                        (nb071_wpp_notmem_0283 x) (TEnvFresh.nil ((synCen)).fv)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_wpp_refl_0017`. -/
@[expose]
noncomputable def nb071WppRefl0017 (x : Var) :
    TReflOn
      [((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
        ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
        ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      ((synCen)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0017 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
