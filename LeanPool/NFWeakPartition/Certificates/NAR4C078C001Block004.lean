/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part018`. -/


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

theorem nb078_fresh_1154 :
    (nb078_alpha_dummy_343) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_339))).fv) :=
  by
  simpa only [nb078_alpha_dummy_343] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_339))).fv)
      0

theorem nb078_fresh_1155 (g : Var) :
    (nb078_alpha_dummy_344 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_341 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_344] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_341 g))).fv)
      0

theorem nb078_fresh_1156 :
    (nb078_alpha_dummy_385) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_381))).fv) :=
  by
  simpa only [nb078_alpha_dummy_385] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_381))).fv)
      0

theorem nb078_fresh_1157 (g : Var) :
    (nb078_alpha_dummy_386 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_383 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_386] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_383 g))).fv)
      0

theorem nb078_fresh_1158 :
    (nb078_alpha_dummy_421) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_417))).fv) :=
  by
  simpa only [nb078_alpha_dummy_421] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_417))).fv)
      0

theorem nb078_fresh_1159 (g : Var) :
    (nb078_alpha_dummy_422 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_419 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_422] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_419 g))).fv)
      0

theorem nb078_fresh_1160 :
    (nb078_alpha_dummy_457) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_453))).fv) :=
  by
  simpa only [nb078_alpha_dummy_457] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_453))).fv)
      0

theorem nb078_fresh_1161 (g : Var) :
    (nb078_alpha_dummy_458 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_455 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_458] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_455 g))).fv)
      0

theorem nb078_fresh_1162 :
    (nb078_alpha_dummy_497) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_493))).fv) :=
  by
  simpa only [nb078_alpha_dummy_497] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_493))).fv)
      0

theorem nb078_fresh_1163 (g : Var) :
    (nb078_alpha_dummy_498 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_495 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_498] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_495 g))).fv)
      0

theorem nb078_fresh_1164 :
    (nb078_alpha_dummy_541) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_537))).fv) :=
  by
  simpa only [nb078_alpha_dummy_541] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_537))).fv)
      0

theorem nb078_fresh_1165 (g : Var) :
    (nb078_alpha_dummy_542 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_539 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_542] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_539 g))).fv)
      0

theorem nb078_fresh_1166 :
    (nb078_alpha_dummy_589) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_585))).fv) :=
  by
  simpa only [nb078_alpha_dummy_589] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_585))).fv)
      0

theorem nb078_fresh_1167 (g : Var) :
    (nb078_alpha_dummy_590 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_587 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_590] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_587 g))).fv)
      0

theorem nb078_fresh_1168 :
    (nb078_alpha_dummy_625) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_621))).fv) :=
  by
  simpa only [nb078_alpha_dummy_625] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_621))).fv)
      0

theorem nb078_fresh_1169 (g : Var) :
    (nb078_alpha_dummy_626 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_623 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_626] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_623 g))).fv)
      0

theorem nb078_fresh_1170 :
    (nb078_alpha_dummy_667) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_663))).fv) :=
  by
  simpa only [nb078_alpha_dummy_667] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_663))).fv)
      0

theorem nb078_fresh_1171 (g : Var) :
    (nb078_alpha_dummy_668 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_665 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_668] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_665 g))).fv)
      0

theorem nb078_fresh_1172 :
    (nb078_alpha_dummy_703) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_699))).fv) :=
  by
  simpa only [nb078_alpha_dummy_703] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_699))).fv)
      0

theorem nb078_fresh_1173 (g : Var) :
    (nb078_alpha_dummy_704 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_701 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_704] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_701 g))).fv)
      0

theorem nb078_fresh_1174 :
    (nb078_alpha_dummy_739) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_735))).fv) :=
  by
  simpa only [nb078_alpha_dummy_739] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_735))).fv)
      0

theorem nb078_fresh_1175 (g : Var) :
    (nb078_alpha_dummy_740 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_737 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_740] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_737 g))).fv)
      0

theorem nb078_fresh_1176 :
    (nb078_alpha_dummy_787) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_783))).fv) :=
  by
  simpa only [nb078_alpha_dummy_787] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_783))).fv)
      0

theorem nb078_fresh_1177 (h : Var) :
    (nb078_alpha_dummy_788 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_785 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_788] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_785 h))).fv)
      0

theorem nb078_fresh_1178 :
    (nb078_alpha_dummy_823) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_819))).fv) :=
  by
  simpa only [nb078_alpha_dummy_823] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_819))).fv)
      0

theorem nb078_fresh_1179 (h : Var) :
    (nb078_alpha_dummy_824 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_821 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_824] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_821 h))).fv)
      0

theorem nb078_fresh_1180 :
    (nb078_alpha_dummy_865) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_861))).fv) :=
  by
  simpa only [nb078_alpha_dummy_865] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_861))).fv)
      0

theorem nb078_fresh_1181 (h : Var) :
    (nb078_alpha_dummy_866 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_863 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_866] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_863 h))).fv)
      0

theorem nb078_fresh_1182 :
    (nb078_alpha_dummy_901) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_897))).fv) :=
  by
  simpa only [nb078_alpha_dummy_901] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_897))).fv)
      0

theorem nb078_fresh_1183 (h : Var) :
    (nb078_alpha_dummy_902 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_899 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_902] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_899 h))).fv)
      0

theorem nb078_fresh_1184 :
    (nb078_alpha_dummy_937) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_933))).fv) :=
  by
  simpa only [nb078_alpha_dummy_937] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_933))).fv)
      0

theorem nb078_fresh_1185 (h : Var) :
    (nb078_alpha_dummy_938 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_935 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_938] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_935 h))).fv)
      0

theorem nb078_fresh_1186 :
    (nb078_alpha_dummy_977) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_973))).fv) :=
  by
  simpa only [nb078_alpha_dummy_977] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_973))).fv)
      0

theorem nb078_fresh_1187 (h : Var) :
    (nb078_alpha_dummy_978 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_975 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_978] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_975 h))).fv)
      0

theorem nb078_fresh_1188 :
    (nb078_alpha_dummy_203) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_203] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      0

theorem nb078_fresh_1189 :
    (nb078_alpha_dummy_204) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_204] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      1

theorem nb078_distinct_1190 : (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_204) := by
  simpa only [nb078_alpha_dummy_203, nb078_alpha_dummy_204] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_fresh_1191 :
    (nb078_alpha_dummy_649) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  simpa only [nb078_alpha_dummy_649] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 0

theorem nb078_fresh_1192 :
    (nb078_alpha_dummy_650) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  simpa only [nb078_alpha_dummy_650] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 1

theorem nb078_distinct_1193 : (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_650) := by
  simpa only [nb078_alpha_dummy_649, nb078_alpha_dummy_650] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_fresh_1194 :
    (nb078_alpha_dummy_569) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_569] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
      0

theorem nb078_fresh_1195 :
    (nb078_alpha_dummy_570) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_570] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
      1

theorem nb078_fresh_1196 :
    (nb078_alpha_dummy_571) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_571] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
      2

theorem nb078_distinct_1197 : (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_570) := by
  simpa only [nb078_alpha_dummy_569, nb078_alpha_dummy_570] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1198 : (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_571) := by
  simpa only [nb078_alpha_dummy_569, nb078_alpha_dummy_571] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1199 : (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_571) := by
  simpa only [nb078_alpha_dummy_570, nb078_alpha_dummy_571] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1200 :
    (nb078_alpha_dummy_481) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_481] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv)
      0

theorem nb078_fresh_1201 :
    (nb078_alpha_dummy_482) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_482] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv)
      1

theorem nb078_distinct_1202 : (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_482) := by
  simpa only [nb078_alpha_dummy_481, nb078_alpha_dummy_482] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_fresh_1203 :
    (nb078_alpha_dummy_1129) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  simpa only [nb078_alpha_dummy_1129] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 0

theorem nb078_fresh_1204 :
    (nb078_alpha_dummy_1130) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  simpa only [nb078_alpha_dummy_1130] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 1

theorem nb078_distinct_1205 : (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1130) := by
  simpa only [nb078_alpha_dummy_1129, nb078_alpha_dummy_1130] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_fresh_1206 :
    (nb078_alpha_dummy_1049) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1049] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
      0

theorem nb078_fresh_1207 :
    (nb078_alpha_dummy_1050) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1050] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
      1

theorem nb078_fresh_1208 :
    (nb078_alpha_dummy_1051) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1051] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
      2

theorem nb078_distinct_1209 : (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1050) := by
  simpa only [nb078_alpha_dummy_1049, nb078_alpha_dummy_1050] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1210 : (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1051) := by
  simpa only [nb078_alpha_dummy_1049, nb078_alpha_dummy_1051] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1211 : (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1051) := by
  simpa only [nb078_alpha_dummy_1050, nb078_alpha_dummy_1051] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1212 :
    (nb078_alpha_dummy_961) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_961] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv)
      0

theorem nb078_fresh_1213 :
    (nb078_alpha_dummy_962) ∉
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_962] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv)
      1

theorem nb078_distinct_1214 : (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_962) := by
  simpa only [nb078_alpha_dummy_961, nb078_alpha_dummy_962] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_fresh_1215 (f : Var) :
    (nb078_alpha_dummy_205 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_205] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1216 (f : Var) :
    (nb078_alpha_dummy_206 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_206] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1217 (f : Var) :
    (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_206 f) := by
  simpa only [nb078_alpha_dummy_205, nb078_alpha_dummy_206] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1218 (g : Var) :
    (nb078_alpha_dummy_651 g) ∉ (((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_651] using
    freshVar_not_mem (((syn_ccnv (Class.cv g))).fv) 0

theorem nb078_fresh_1219 (g : Var) :
    (nb078_alpha_dummy_652 g) ∉ (((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_652] using
    freshVar_not_mem (((syn_ccnv (Class.cv g))).fv) 1

theorem nb078_distinct_1220 (g : Var) :
    (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_652 g) := by
  simpa only [nb078_alpha_dummy_651, nb078_alpha_dummy_652] using
    (freshVar_injective (((syn_ccnv (Class.cv g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1221 (g : Var) :
    (nb078_alpha_dummy_572 g) ∉
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_572] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 0

theorem nb078_fresh_1222 (g : Var) :
    (nb078_alpha_dummy_573 g) ∉
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_573] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 1

theorem nb078_fresh_1223 (g : Var) :
    (nb078_alpha_dummy_574 g) ∉
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_574] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 2

theorem nb078_distinct_1224 (g : Var) :
    (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_573 g) := by
  simpa only [nb078_alpha_dummy_572, nb078_alpha_dummy_573] using
    (freshVar_injective
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_distinct_1225 (g : Var) :
    (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_574 g) := by
  simpa only [nb078_alpha_dummy_572, nb078_alpha_dummy_574] using
    (freshVar_injective
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb078_distinct_1226 (g : Var) :
    (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_574 g) := by
  simpa only [nb078_alpha_dummy_573, nb078_alpha_dummy_574] using
    (freshVar_injective
      (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb078_fresh_1227 (g : Var) :
    (nb078_alpha_dummy_483 g) ∉ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_483] using
    freshVar_not_mem (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1228 (g : Var) :
    (nb078_alpha_dummy_484 g) ∉ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_484] using
    freshVar_not_mem (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1229 (g : Var) :
    (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_484 g) := by
  simpa only [nb078_alpha_dummy_483, nb078_alpha_dummy_484] using
    (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1230 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∉ (((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_1131] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv) 0

theorem nb078_fresh_1231 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∉ (((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_1132] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv) 1

theorem nb078_distinct_1232 (h : Var) :
    (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1132 h) := by
  simpa only [nb078_alpha_dummy_1131, nb078_alpha_dummy_1132] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1233 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∉
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1052] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 0

theorem nb078_fresh_1234 (h : Var) :
    (nb078_alpha_dummy_1053 h) ∉
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1053] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 1

theorem nb078_fresh_1235 (h : Var) :
    (nb078_alpha_dummy_1054 h) ∉
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1054] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 2

theorem nb078_distinct_1236 (h : Var) :
    (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1053 h) := by
  simpa only [nb078_alpha_dummy_1052, nb078_alpha_dummy_1053] using
    (freshVar_injective
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_distinct_1237 (h : Var) :
    (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1054 h) := by
  simpa only [nb078_alpha_dummy_1052, nb078_alpha_dummy_1054] using
    (freshVar_injective
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb078_distinct_1238 (h : Var) :
    (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1054 h) := by
  simpa only [nb078_alpha_dummy_1053, nb078_alpha_dummy_1054] using
    (freshVar_injective
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb078_fresh_1239 (h : Var) :
    (nb078_alpha_dummy_963 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_963] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1240 (h : Var) :
    (nb078_alpha_dummy_964 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_964] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1241 (h : Var) :
    (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_964 h) := by
  simpa only [nb078_alpha_dummy_963, nb078_alpha_dummy_964] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1242 :
    (nb078_alpha_dummy_007) ∉
      (((syn_ccom (Class.cv (nb078_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb078_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb078_fresh_1243 :
    (nb078_alpha_dummy_285) ∉
      (((syn_ccom (Class.cv (nb078_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_285] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb078_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb078_fresh_1244 :
    (nb078_alpha_dummy_765) ∉
      (((syn_ccom (Class.cv (nb078_alpha_dummy_002))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_765] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb078_alpha_dummy_002))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb078_fresh_1245 (f : Var) :
    (nb078_alpha_dummy_008 f) ∉
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1246 (g : Var) :
    (nb078_alpha_dummy_286 g) ∉
      (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_286] using
    freshVar_not_mem
      (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1247 (h : Var) :
    (nb078_alpha_dummy_766 h) ∉
      (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_766] using
    freshVar_not_mem
      (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1248 :
    (nb078_alpha_dummy_567) ∉
      (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_567] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb078_fresh_1249 :
    (nb078_alpha_dummy_1047) ∉
      (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1047] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb078_fresh_1250 (g : Var) :
    (nb078_alpha_dummy_568 g) ∉
      (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪
        ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_568] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪
        ((syn_cid)).fv)
      0

theorem nb078_fresh_1251 (h : Var) :
    (nb078_alpha_dummy_1048 h) ∉
      (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
        ((syn_cid)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1048] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
        ((syn_cid)).fv)
      0

theorem nb078_fresh_1252 :
    (nb078_alpha_dummy_021) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_021] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1253 (f : Var) :
    (nb078_alpha_dummy_022 f) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_022] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1254 :
    (nb078_alpha_dummy_057) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_057] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1255 (f : Var) :
    (nb078_alpha_dummy_058 f) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_058] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1256 :
    (nb078_alpha_dummy_099) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_099] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1257 (f : Var) :
    (nb078_alpha_dummy_100 f) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_100] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1258 :
    (nb078_alpha_dummy_1013) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1013] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1259 (h : Var) :
    (nb078_alpha_dummy_1014 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1014] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1260 :
    (nb078_alpha_dummy_1061) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1061] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1261 (h : Var) :
    (nb078_alpha_dummy_1062 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1062] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1262 :
    (nb078_alpha_dummy_1097) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1097] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1263 (h : Var) :
    (nb078_alpha_dummy_1098 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1098] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1264 :
    (nb078_alpha_dummy_1139) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1139] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1265 (h : Var) :
    (nb078_alpha_dummy_1140 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1140] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1266 :
    (nb078_alpha_dummy_1175) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1175] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1267 (h : Var) :
    (nb078_alpha_dummy_1176 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1176] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1268 :
    (nb078_alpha_dummy_1211) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1211] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1269 (h : Var) :
    (nb078_alpha_dummy_1212 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1212] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1270 :
    (nb078_alpha_dummy_135) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_135] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1271 (f : Var) :
    (nb078_alpha_dummy_136 f) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_136] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1272 :
    (nb078_alpha_dummy_171) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_171] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1273 (f : Var) :
    (nb078_alpha_dummy_172 f) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_172] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part019`. -/


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

theorem nb078_fresh_1274 :
    (nb078_alpha_dummy_211) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_211] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1275 (f : Var) :
    (nb078_alpha_dummy_212 f) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_212] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1276 :
    (nb078_alpha_dummy_251) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_251] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1277 (f : Var) :
    (nb078_alpha_dummy_252 f) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_252] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1278 :
    (nb078_alpha_dummy_299) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_299] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1279 (g : Var) :
    (nb078_alpha_dummy_300 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_300] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1280 :
    (nb078_alpha_dummy_335) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_335] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1281 (g : Var) :
    (nb078_alpha_dummy_336 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_336] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1282 :
    (nb078_alpha_dummy_377) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_377] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1283 (g : Var) :
    (nb078_alpha_dummy_378 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_378] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1284 :
    (nb078_alpha_dummy_413) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_413] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1285 (g : Var) :
    (nb078_alpha_dummy_414 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_414] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1286 :
    (nb078_alpha_dummy_449) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_449] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1287 (g : Var) :
    (nb078_alpha_dummy_450 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_450] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1288 :
    (nb078_alpha_dummy_489) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_489] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1289 (g : Var) :
    (nb078_alpha_dummy_490 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_490] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1290 :
    (nb078_alpha_dummy_533) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_533] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1291 (g : Var) :
    (nb078_alpha_dummy_534 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_534] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1292 :
    (nb078_alpha_dummy_581) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_581] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1293 (g : Var) :
    (nb078_alpha_dummy_582 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_582] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1294 :
    (nb078_alpha_dummy_617) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_617] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1295 (g : Var) :
    (nb078_alpha_dummy_618 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_618] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1296 :
    (nb078_alpha_dummy_659) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_659] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1297 (g : Var) :
    (nb078_alpha_dummy_660 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_660] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1298 :
    (nb078_alpha_dummy_695) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_695] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1299 (g : Var) :
    (nb078_alpha_dummy_696 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_696] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1300 :
    (nb078_alpha_dummy_731) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_731] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1301 (g : Var) :
    (nb078_alpha_dummy_732 g) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_732] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1302 :
    (nb078_alpha_dummy_779) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_779] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1303 (h : Var) :
    (nb078_alpha_dummy_780 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_780] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1304 :
    (nb078_alpha_dummy_815) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_815] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1305 (h : Var) :
    (nb078_alpha_dummy_816 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_816] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1306 :
    (nb078_alpha_dummy_857) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_857] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1307 (h : Var) :
    (nb078_alpha_dummy_858 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_858] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1308 :
    (nb078_alpha_dummy_893) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_893] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1309 (h : Var) :
    (nb078_alpha_dummy_894 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_894] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1310 :
    (nb078_alpha_dummy_929) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_929] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1311 (h : Var) :
    (nb078_alpha_dummy_930 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_930] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1312 :
    (nb078_alpha_dummy_969) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_969] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1313 (h : Var) :
    (nb078_alpha_dummy_970 h) ∉
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_970] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb078_fresh_1314 :
    (nb078_alpha_dummy_041) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv)
      0

theorem nb078_fresh_1315 (f : Var) :
    (nb078_alpha_dummy_042 f) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv)
      0

theorem nb078_fresh_1316 :
    (nb078_alpha_dummy_077) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv)
      0

theorem nb078_fresh_1317 (f : Var) :
    (nb078_alpha_dummy_078 f) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv)
      0

theorem nb078_fresh_1318 :
    (nb078_alpha_dummy_1033) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1033] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv)
      0

theorem nb078_fresh_1319 (h : Var) :
    (nb078_alpha_dummy_1034 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1034] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv)
      0

theorem nb078_fresh_1320 :
    (nb078_alpha_dummy_1081) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1081] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv)
      0

theorem nb078_fresh_1321 (h : Var) :
    (nb078_alpha_dummy_1082 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1082] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv)
      0

theorem nb078_fresh_1322 :
    (nb078_alpha_dummy_119) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_119] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv)
      0

theorem nb078_fresh_1323 :
    (nb078_alpha_dummy_1117) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1117] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv)
      0

theorem nb078_fresh_1324 (h : Var) :
    (nb078_alpha_dummy_1118 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1118] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv)
      0

theorem nb078_fresh_1325 (f : Var) :
    (nb078_alpha_dummy_120 f) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_120] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv)
      0

theorem nb078_fresh_1326 :
    (nb078_alpha_dummy_1159) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1150)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1151)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1159] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1150)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1151)))).fv)
      0

theorem nb078_fresh_1327 (h : Var) :
    (nb078_alpha_dummy_1160 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1154 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1160] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1154 h)))).fv)
      0

theorem nb078_fresh_1328 :
    (nb078_alpha_dummy_1195) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1186)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1187)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1195] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1186)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1187)))).fv)
      0

theorem nb078_fresh_1329 (h : Var) :
    (nb078_alpha_dummy_1196 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1190 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1196] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1190 h)))).fv)
      0

theorem nb078_fresh_1330 :
    (nb078_alpha_dummy_1231) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1223)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1231] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1223)))).fv)
      0

theorem nb078_fresh_1331 (h : Var) :
    (nb078_alpha_dummy_1232 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1226 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1232] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1226 h)))).fv)
      0

theorem nb078_fresh_1332 :
    (nb078_alpha_dummy_155) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_155] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv)
      0

theorem nb078_fresh_1333 (f : Var) :
    (nb078_alpha_dummy_156 f) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_156] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv)
      0

theorem nb078_fresh_1334 :
    (nb078_alpha_dummy_191) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_191] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv)
      0

theorem nb078_fresh_1335 (f : Var) :
    (nb078_alpha_dummy_192 f) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_192] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv)
      0

theorem nb078_fresh_1336 :
    (nb078_alpha_dummy_231) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_231] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv)
      0

theorem nb078_fresh_1337 (f : Var) :
    (nb078_alpha_dummy_232 f) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_232] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv)
      0

theorem nb078_fresh_1338 :
    (nb078_alpha_dummy_271) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_271] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv)
      0

theorem nb078_fresh_1339 (f : Var) :
    (nb078_alpha_dummy_272 f) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_272] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv)
      0

theorem nb078_fresh_1340 :
    (nb078_alpha_dummy_319) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_319] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv)
      0

theorem nb078_fresh_1341 (g : Var) :
    (nb078_alpha_dummy_320 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_320] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv)
      0

theorem nb078_fresh_1342 :
    (nb078_alpha_dummy_355) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_355] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv)
      0

theorem nb078_fresh_1343 (g : Var) :
    (nb078_alpha_dummy_356 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_356] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv)
      0

theorem nb078_fresh_1344 :
    (nb078_alpha_dummy_397) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_397] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv)
      0

theorem nb078_fresh_1345 (g : Var) :
    (nb078_alpha_dummy_398 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_398] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv)
      0

theorem nb078_fresh_1346 :
    (nb078_alpha_dummy_433) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_433] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv)
      0

theorem nb078_fresh_1347 (g : Var) :
    (nb078_alpha_dummy_434 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_434] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv)
      0

theorem nb078_fresh_1348 :
    (nb078_alpha_dummy_469) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_469] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv)
      0

theorem nb078_fresh_1349 (g : Var) :
    (nb078_alpha_dummy_470 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_470] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv)
      0

theorem nb078_fresh_1350 :
    (nb078_alpha_dummy_509) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_509] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv)
      0

theorem nb078_fresh_1351 (g : Var) :
    (nb078_alpha_dummy_510 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_510] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv)
      0

theorem nb078_fresh_1352 :
    (nb078_alpha_dummy_553) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_553] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv)
      0

theorem nb078_fresh_1353 (g : Var) :
    (nb078_alpha_dummy_554 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_554] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv)
      0

theorem nb078_fresh_1354 :
    (nb078_alpha_dummy_601) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_601] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv)
      0

theorem nb078_fresh_1355 (g : Var) :
    (nb078_alpha_dummy_602 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_602] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv)
      0

theorem nb078_fresh_1356 :
    (nb078_alpha_dummy_637) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_637] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv)
      0

theorem nb078_fresh_1357 (g : Var) :
    (nb078_alpha_dummy_638 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_638] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv)
      0

theorem nb078_fresh_1358 :
    (nb078_alpha_dummy_679) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_679] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part020`. -/


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

theorem nb078_fresh_1359 (g : Var) :
    (nb078_alpha_dummy_680 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_680] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv)
      0

theorem nb078_fresh_1360 :
    (nb078_alpha_dummy_715) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_715] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv)
      0

theorem nb078_fresh_1361 (g : Var) :
    (nb078_alpha_dummy_716 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_716] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv)
      0

theorem nb078_fresh_1362 :
    (nb078_alpha_dummy_751) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_751] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv)
      0

theorem nb078_fresh_1363 (g : Var) :
    (nb078_alpha_dummy_752 g) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_752] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv)
      0

theorem nb078_fresh_1364 :
    (nb078_alpha_dummy_799) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_799] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv)
      0

theorem nb078_fresh_1365 (h : Var) :
    (nb078_alpha_dummy_800 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_800] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv)
      0

theorem nb078_fresh_1366 :
    (nb078_alpha_dummy_835) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_835] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv)
      0

theorem nb078_fresh_1367 (h : Var) :
    (nb078_alpha_dummy_836 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_836] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv)
      0

theorem nb078_fresh_1368 :
    (nb078_alpha_dummy_877) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_877] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv)
      0

theorem nb078_fresh_1369 (h : Var) :
    (nb078_alpha_dummy_878 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_878] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv)
      0

theorem nb078_fresh_1370 :
    (nb078_alpha_dummy_913) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_913] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv)
      0

theorem nb078_fresh_1371 (h : Var) :
    (nb078_alpha_dummy_914 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_914] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv)
      0

theorem nb078_fresh_1372 :
    (nb078_alpha_dummy_949) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_949] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv)
      0

theorem nb078_fresh_1373 (h : Var) :
    (nb078_alpha_dummy_950 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_950] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv)
      0

theorem nb078_fresh_1374 :
    (nb078_alpha_dummy_989) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_989] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv)
      0

theorem nb078_fresh_1375 (h : Var) :
    (nb078_alpha_dummy_990 h) ∉
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_990] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv)
      0

theorem nb078_fresh_1376 :
    (nb078_alpha_dummy_049) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1377 (f : Var) :
    (nb078_alpha_dummy_050 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1378 :
    (nb078_alpha_dummy_085) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1379 (f : Var) :
    (nb078_alpha_dummy_086 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1380 :
    (nb078_alpha_dummy_127) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_127] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1381 (f : Var) :
    (nb078_alpha_dummy_128 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_128] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1382 :
    (nb078_alpha_dummy_1041) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1041] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1383 (h : Var) :
    (nb078_alpha_dummy_1042 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1042] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1384 :
    (nb078_alpha_dummy_1089) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1089] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1385 (h : Var) :
    (nb078_alpha_dummy_1090 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1090] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1386 :
    (nb078_alpha_dummy_1125) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1125] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1387 (h : Var) :
    (nb078_alpha_dummy_1126 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1126] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1388 :
    (nb078_alpha_dummy_1167) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1167] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1389 (h : Var) :
    (nb078_alpha_dummy_1168 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1168] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1390 :
    (nb078_alpha_dummy_1203) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1203] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1391 (h : Var) :
    (nb078_alpha_dummy_1204 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1204] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1392 :
    (nb078_alpha_dummy_1239) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1239] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1393 (h : Var) :
    (nb078_alpha_dummy_1240 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1240] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1394 :
    (nb078_alpha_dummy_163) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_163] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1395 (f : Var) :
    (nb078_alpha_dummy_164 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_164] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1396 :
    (nb078_alpha_dummy_199) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_199] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1397 (f : Var) :
    (nb078_alpha_dummy_200 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_200] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1398 :
    (nb078_alpha_dummy_239) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_239] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1399 (f : Var) :
    (nb078_alpha_dummy_240 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_240] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1400 :
    (nb078_alpha_dummy_279) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_279] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1401 (f : Var) :
    (nb078_alpha_dummy_280 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_280] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1402 :
    (nb078_alpha_dummy_327) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_327] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1403 (g : Var) :
    (nb078_alpha_dummy_328 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_328] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1404 :
    (nb078_alpha_dummy_363) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_363] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1405 (g : Var) :
    (nb078_alpha_dummy_364 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_364] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1406 :
    (nb078_alpha_dummy_405) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_405] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1407 (g : Var) :
    (nb078_alpha_dummy_406 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_406] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1408 :
    (nb078_alpha_dummy_441) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_441] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1409 (g : Var) :
    (nb078_alpha_dummy_442 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_442] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1410 :
    (nb078_alpha_dummy_477) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_477] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1411 (g : Var) :
    (nb078_alpha_dummy_478 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_478] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1412 :
    (nb078_alpha_dummy_517) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_517] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1413 (g : Var) :
    (nb078_alpha_dummy_518 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_518] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1414 :
    (nb078_alpha_dummy_561) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_561] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1415 (g : Var) :
    (nb078_alpha_dummy_562 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_562] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1416 :
    (nb078_alpha_dummy_609) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_609] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1417 (g : Var) :
    (nb078_alpha_dummy_610 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_610] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1418 :
    (nb078_alpha_dummy_645) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_645] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1419 (g : Var) :
    (nb078_alpha_dummy_646 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_646] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1420 :
    (nb078_alpha_dummy_687) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_687] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1421 (g : Var) :
    (nb078_alpha_dummy_688 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_688] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1422 :
    (nb078_alpha_dummy_723) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_723] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1423 (g : Var) :
    (nb078_alpha_dummy_724 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_724] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1424 :
    (nb078_alpha_dummy_759) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_759] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1425 (g : Var) :
    (nb078_alpha_dummy_760 g) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_760] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1426 :
    (nb078_alpha_dummy_807) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_807] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1427 (h : Var) :
    (nb078_alpha_dummy_808 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_808] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1428 :
    (nb078_alpha_dummy_843) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_843] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1429 (h : Var) :
    (nb078_alpha_dummy_844 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_844] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1430 :
    (nb078_alpha_dummy_885) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_885] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1431 (h : Var) :
    (nb078_alpha_dummy_886 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_886] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1432 :
    (nb078_alpha_dummy_921) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_921] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1433 (h : Var) :
    (nb078_alpha_dummy_922 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_922] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1434 :
    (nb078_alpha_dummy_957) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_957] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1435 (h : Var) :
    (nb078_alpha_dummy_958 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_958] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1436 :
    (nb078_alpha_dummy_997) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_997] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1437 (h : Var) :
    (nb078_alpha_dummy_998 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_998] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb078_fresh_1438 :
    (nb078_alpha_dummy_037) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_032))
            (Class.cv (nb078_alpha_dummy_033)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv)
      0

theorem nb078_fresh_1439 (f : Var) :
    (nb078_alpha_dummy_038 f) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv)
      0

theorem nb078_fresh_1440 :
    (nb078_alpha_dummy_073) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_068))
            (Class.cv (nb078_alpha_dummy_069)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_073] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv)
      0

theorem nb078_fresh_1441 (f : Var) :
    (nb078_alpha_dummy_074 f) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv)
      0

theorem nb078_fresh_1442 :
    (nb078_alpha_dummy_1029) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1024))
            (Class.cv (nb078_alpha_dummy_1025)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1029] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv)
      0

theorem nb078_fresh_1443 (h : Var) :
    (nb078_alpha_dummy_1030 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1030] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv)
      0

theorem nb078_fresh_1444 :
    (nb078_alpha_dummy_1077) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1072))
            (Class.cv (nb078_alpha_dummy_1073)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1077] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv)
      0

theorem nb078_fresh_1445 (h : Var) :
    (nb078_alpha_dummy_1078 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1078] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv)
      0

theorem nb078_fresh_1446 :
    (nb078_alpha_dummy_115) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_110))
            (Class.cv (nb078_alpha_dummy_111)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_115] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv)
      0

theorem nb078_fresh_1447 :
    (nb078_alpha_dummy_1113) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1108))
            (Class.cv (nb078_alpha_dummy_1109)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1113] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv)
      0

theorem nb078_fresh_1448 (h : Var) :
    (nb078_alpha_dummy_1114 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1114] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv)
      0

theorem nb078_fresh_1449 (f : Var) :
    (nb078_alpha_dummy_116 f) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_116] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv)
      0

theorem nb078_fresh_1450 :
    (nb078_alpha_dummy_1155) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1150))
            (Class.cv (nb078_alpha_dummy_1151)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1155] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv)
      0

theorem nb078_fresh_1451 (h : Var) :
    (nb078_alpha_dummy_1156 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1156] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv)
      0

theorem nb078_fresh_1452 :
    (nb078_alpha_dummy_1191) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1186))
            (Class.cv (nb078_alpha_dummy_1187)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1191] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv)
      0

theorem nb078_fresh_1453 (h : Var) :
    (nb078_alpha_dummy_1192 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1192] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv)
      0

theorem nb078_fresh_1454 :
    (nb078_alpha_dummy_1227) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1222))
            (Class.cv (nb078_alpha_dummy_1223)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1227] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv)
      0

theorem nb078_fresh_1455 (h : Var) :
    (nb078_alpha_dummy_1228 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1228] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv)
      0

theorem nb078_fresh_1456 :
    (nb078_alpha_dummy_151) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_146))
            (Class.cv (nb078_alpha_dummy_147)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv)
      0

theorem nb078_fresh_1457 (f : Var) :
    (nb078_alpha_dummy_152 f) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv)
      0

theorem nb078_fresh_1458 :
    (nb078_alpha_dummy_187) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_182))
            (Class.cv (nb078_alpha_dummy_183)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_187] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv)
      0

theorem nb078_fresh_1459 (f : Var) :
    (nb078_alpha_dummy_188 f) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_188] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv)
      0

theorem nb078_fresh_1460 :
    (nb078_alpha_dummy_227) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_222))
            (Class.cv (nb078_alpha_dummy_223)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_227] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv)
      0

theorem nb078_fresh_1461 (f : Var) :
    (nb078_alpha_dummy_228 f) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_228] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv)
      0

theorem nb078_fresh_1462 :
    (nb078_alpha_dummy_267) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_262))
            (Class.cv (nb078_alpha_dummy_263)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_267] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv)
      0

theorem nb078_fresh_1463 (f : Var) :
    (nb078_alpha_dummy_268 f) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_268] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv)
      0

theorem nb078_fresh_1464 :
    (nb078_alpha_dummy_315) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_310))
            (Class.cv (nb078_alpha_dummy_311)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_315] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv)
      0

theorem nb078_fresh_1465 (g : Var) :
    (nb078_alpha_dummy_316 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_316] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv)
      0

theorem nb078_fresh_1466 :
    (nb078_alpha_dummy_351) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_346))
            (Class.cv (nb078_alpha_dummy_347)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_351] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv)
      0

theorem nb078_fresh_1467 (g : Var) :
    (nb078_alpha_dummy_352 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_352] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv)
      0

theorem nb078_fresh_1468 :
    (nb078_alpha_dummy_393) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_388))
            (Class.cv (nb078_alpha_dummy_389)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_393] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv)
      0

theorem nb078_fresh_1469 (g : Var) :
    (nb078_alpha_dummy_394 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_394] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv)
      0

theorem nb078_fresh_1470 :
    (nb078_alpha_dummy_429) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_424))
            (Class.cv (nb078_alpha_dummy_425)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_429] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv)
      0

theorem nb078_fresh_1471 (g : Var) :
    (nb078_alpha_dummy_430 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_430] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv)
      0

theorem nb078_fresh_1472 :
    (nb078_alpha_dummy_465) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_460))
            (Class.cv (nb078_alpha_dummy_461)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_465] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv)
      0

theorem nb078_fresh_1473 (g : Var) :
    (nb078_alpha_dummy_466 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_466] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv)
      0

theorem nb078_fresh_1474 :
    (nb078_alpha_dummy_505) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_500))
            (Class.cv (nb078_alpha_dummy_501)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_505] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv)
      0

theorem nb078_fresh_1475 (g : Var) :
    (nb078_alpha_dummy_506 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_506] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv)
      0

theorem nb078_fresh_1476 :
    (nb078_alpha_dummy_549) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_544))
            (Class.cv (nb078_alpha_dummy_545)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_549] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv)
      0

theorem nb078_fresh_1477 (g : Var) :
    (nb078_alpha_dummy_550 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_550] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv)
      0

theorem nb078_fresh_1478 :
    (nb078_alpha_dummy_597) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_592))
            (Class.cv (nb078_alpha_dummy_593)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_597] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv)
      0

theorem nb078_fresh_1479 (g : Var) :
    (nb078_alpha_dummy_598 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_598] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv)
      0

theorem nb078_fresh_1480 :
    (nb078_alpha_dummy_633) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_628))
            (Class.cv (nb078_alpha_dummy_629)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_633] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv)
      0

theorem nb078_fresh_1481 (g : Var) :
    (nb078_alpha_dummy_634 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_634] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv)
      0

theorem nb078_fresh_1482 :
    (nb078_alpha_dummy_675) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_670))
            (Class.cv (nb078_alpha_dummy_671)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_675] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv)
      0

theorem nb078_fresh_1483 (g : Var) :
    (nb078_alpha_dummy_676 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_676] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv)
      0

theorem nb078_fresh_1484 :
    (nb078_alpha_dummy_711) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_706))
            (Class.cv (nb078_alpha_dummy_707)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_711] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv)
      0

theorem nb078_fresh_1485 (g : Var) :
    (nb078_alpha_dummy_712 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_712] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv)
      0

theorem nb078_fresh_1486 :
    (nb078_alpha_dummy_747) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_742))
            (Class.cv (nb078_alpha_dummy_743)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_747] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv)
      0

theorem nb078_fresh_1487 (g : Var) :
    (nb078_alpha_dummy_748 g) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_748] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv)
      0

theorem nb078_fresh_1488 :
    (nb078_alpha_dummy_795) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_790))
            (Class.cv (nb078_alpha_dummy_791)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_795] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv)
      0

theorem nb078_fresh_1489 (h : Var) :
    (nb078_alpha_dummy_796 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_796] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv)
      0

theorem nb078_fresh_1490 :
    (nb078_alpha_dummy_831) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_826))
            (Class.cv (nb078_alpha_dummy_827)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_831] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv)
      0

theorem nb078_fresh_1491 (h : Var) :
    (nb078_alpha_dummy_832 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_832] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv)
      0

theorem nb078_fresh_1492 :
    (nb078_alpha_dummy_873) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_868))
            (Class.cv (nb078_alpha_dummy_869)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_873] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv)
      0

theorem nb078_fresh_1493 (h : Var) :
    (nb078_alpha_dummy_874 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_874] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv)
      0

theorem nb078_fresh_1494 :
    (nb078_alpha_dummy_909) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_904))
            (Class.cv (nb078_alpha_dummy_905)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_909] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv)
      0

theorem nb078_fresh_1495 (h : Var) :
    (nb078_alpha_dummy_910 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_910] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv)
      0

theorem nb078_fresh_1496 :
    (nb078_alpha_dummy_945) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_940))
            (Class.cv (nb078_alpha_dummy_941)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_945] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv)
      0

theorem nb078_fresh_1497 (h : Var) :
    (nb078_alpha_dummy_946 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_946] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv)
      0

theorem nb078_fresh_1498 :
    (nb078_alpha_dummy_985) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_980))
            (Class.cv (nb078_alpha_dummy_981)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_985] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv)
      0

theorem nb078_fresh_1499 (h : Var) :
    (nb078_alpha_dummy_986 h) ∉
      (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_986] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv)
      0

theorem nb078_fresh_1500 :
    (nb078_alpha_dummy_005) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_005] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv)
      0

theorem nb078_fresh_1501 :
    (nb078_alpha_dummy_283) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_283] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part021`. -/


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

theorem nb078_fresh_1502 :
    (nb078_alpha_dummy_763) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_002))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_763] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_002))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv)
      0

theorem nb078_fresh_1503 (f : Var) :
    (nb078_alpha_dummy_006 f) ∉
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv)
      0

theorem nb078_fresh_1504 (g : Var) :
    (nb078_alpha_dummy_284 g) ∉
      (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_284] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv)
      0

theorem nb078_fresh_1505 (h : Var) :
    (nb078_alpha_dummy_764 h) ∉
      (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_764] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv)
      0

theorem nb078_fresh_1506 :
    (nb078_alpha_dummy_565) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_565] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv)
      0

theorem nb078_fresh_1507 :
    (nb078_alpha_dummy_1045) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1045] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv)
      0

theorem nb078_fresh_1508 (g : Var) :
    (nb078_alpha_dummy_566 g) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
            (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_566] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
            (syn_cid))).fv)
      0

theorem nb078_fresh_1509 (h : Var) :
    (nb078_alpha_dummy_1046 h) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1046] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv)
      0

theorem nb078_fresh_1510 :
    (nb078_alpha_dummy_521) ∉
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_521] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv)
      0

theorem nb078_fresh_1511 :
    (nb078_alpha_dummy_1001) ∉
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1001] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv)
      0

theorem nb078_fresh_1512 (x : Var) (g : Var) :
    (nb078_alpha_dummy_522 x g) ∉
      (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) :=
  by
  simpa only [nb078_alpha_dummy_522] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv)
      0

theorem nb078_fresh_1513 (y : Var) (h : Var) :
    (nb078_alpha_dummy_1002 y h) ∉
      (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1002] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv)
      0

theorem nb078_fresh_1514 :
    (nb078_alpha_dummy_051) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_051] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv)
      0

theorem nb078_fresh_1515 (f : Var) :
    (nb078_alpha_dummy_052 f) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv)
      0

theorem nb078_fresh_1516 :
    (nb078_alpha_dummy_087) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_087] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv)
      0

theorem nb078_fresh_1517 (f : Var) :
    (nb078_alpha_dummy_088 f) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_088] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv)
      0

theorem nb078_fresh_1518 :
    (nb078_alpha_dummy_129) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_129] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv)
      0

theorem nb078_fresh_1519 (f : Var) :
    (nb078_alpha_dummy_130 f) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_130] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv)
      0

theorem nb078_fresh_1520 :
    (nb078_alpha_dummy_1043) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1043] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv)
      0

theorem nb078_fresh_1521 (h : Var) :
    (nb078_alpha_dummy_1044 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1044] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv)
      0

theorem nb078_fresh_1522 :
    (nb078_alpha_dummy_1091) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1091] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv)
      0

theorem nb078_fresh_1523 (h : Var) :
    (nb078_alpha_dummy_1092 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1092] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv)
      0

theorem nb078_fresh_1524 :
    (nb078_alpha_dummy_1127) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1127] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv)
      0

theorem nb078_fresh_1525 (h : Var) :
    (nb078_alpha_dummy_1128 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1128] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv)
      0

theorem nb078_fresh_1526 :
    (nb078_alpha_dummy_1169) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1169] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv)
      0

theorem nb078_fresh_1527 (h : Var) :
    (nb078_alpha_dummy_1170 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1170] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv)
      0

theorem nb078_fresh_1528 :
    (nb078_alpha_dummy_1205) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1205] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv)
      0

theorem nb078_fresh_1529 (h : Var) :
    (nb078_alpha_dummy_1206 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1206] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv)
      0

theorem nb078_fresh_1530 :
    (nb078_alpha_dummy_1241) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1241] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv)
      0

theorem nb078_fresh_1531 (h : Var) :
    (nb078_alpha_dummy_1242 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1242] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv)
      0

theorem nb078_fresh_1532 :
    (nb078_alpha_dummy_165) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_165] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv)
      0

theorem nb078_fresh_1533 (f : Var) :
    (nb078_alpha_dummy_166 f) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_166] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv)
      0

theorem nb078_fresh_1534 :
    (nb078_alpha_dummy_201) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_201] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv)
      0

theorem nb078_fresh_1535 (f : Var) :
    (nb078_alpha_dummy_202 f) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_202] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv)
      0

theorem nb078_fresh_1536 :
    (nb078_alpha_dummy_241) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_241] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv)
      0

theorem nb078_fresh_1537 (f : Var) :
    (nb078_alpha_dummy_242 f) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_242] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv)
      0

theorem nb078_fresh_1538 :
    (nb078_alpha_dummy_281) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_281] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv)
      0

theorem nb078_fresh_1539 (f : Var) :
    (nb078_alpha_dummy_282 f) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_282] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv)
      0

theorem nb078_fresh_1540 :
    (nb078_alpha_dummy_329) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_329] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv)
      0

theorem nb078_fresh_1541 (g : Var) :
    (nb078_alpha_dummy_330 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_330] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv)
      0

theorem nb078_fresh_1542 :
    (nb078_alpha_dummy_365) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_365] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv)
      0

theorem nb078_fresh_1543 (g : Var) :
    (nb078_alpha_dummy_366 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_366] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv)
      0

theorem nb078_fresh_1544 :
    (nb078_alpha_dummy_407) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_407] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv)
      0

theorem nb078_fresh_1545 (g : Var) :
    (nb078_alpha_dummy_408 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_408] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv)
      0

theorem nb078_fresh_1546 :
    (nb078_alpha_dummy_443) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_443] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv)
      0

theorem nb078_fresh_1547 (g : Var) :
    (nb078_alpha_dummy_444 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_444] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv)
      0

theorem nb078_fresh_1548 :
    (nb078_alpha_dummy_479) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_479] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv)
      0

theorem nb078_fresh_1549 (g : Var) :
    (nb078_alpha_dummy_480 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_480] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv)
      0

theorem nb078_fresh_1550 :
    (nb078_alpha_dummy_519) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_519] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv)
      0

theorem nb078_fresh_1551 (g : Var) :
    (nb078_alpha_dummy_520 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_520] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv)
      0

theorem nb078_fresh_1552 :
    (nb078_alpha_dummy_563) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_563] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv)
      0

theorem nb078_fresh_1553 (g : Var) :
    (nb078_alpha_dummy_564 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_564] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv)
      0

theorem nb078_fresh_1554 :
    (nb078_alpha_dummy_611) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_611] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv)
      0

theorem nb078_fresh_1555 (g : Var) :
    (nb078_alpha_dummy_612 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_612] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv)
      0

theorem nb078_fresh_1556 :
    (nb078_alpha_dummy_647) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_647] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv)
      0

theorem nb078_fresh_1557 (g : Var) :
    (nb078_alpha_dummy_648 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_648] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv)
      0

theorem nb078_fresh_1558 :
    (nb078_alpha_dummy_689) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_689] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv)
      0

theorem nb078_fresh_1559 (g : Var) :
    (nb078_alpha_dummy_690 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_690] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv)
      0

theorem nb078_fresh_1560 :
    (nb078_alpha_dummy_725) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_725] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv)
      0

theorem nb078_fresh_1561 (g : Var) :
    (nb078_alpha_dummy_726 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_726] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv)
      0

theorem nb078_fresh_1562 :
    (nb078_alpha_dummy_761) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_761] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv)
      0

theorem nb078_fresh_1563 (g : Var) :
    (nb078_alpha_dummy_762 g) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_762] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv)
      0

theorem nb078_fresh_1564 :
    (nb078_alpha_dummy_809) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_809] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv)
      0

theorem nb078_fresh_1565 (h : Var) :
    (nb078_alpha_dummy_810 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_810] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv)
      0

theorem nb078_fresh_1566 :
    (nb078_alpha_dummy_845) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_845] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv)
      0

theorem nb078_fresh_1567 (h : Var) :
    (nb078_alpha_dummy_846 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_846] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv)
      0

theorem nb078_fresh_1568 :
    (nb078_alpha_dummy_887) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_887] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv)
      0

theorem nb078_fresh_1569 (h : Var) :
    (nb078_alpha_dummy_888 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_888] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv)
      0

theorem nb078_fresh_1570 :
    (nb078_alpha_dummy_923) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_923] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv)
      0

theorem nb078_fresh_1571 (h : Var) :
    (nb078_alpha_dummy_924 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_924] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv)
      0

theorem nb078_fresh_1572 :
    (nb078_alpha_dummy_959) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_959] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv)
      0

theorem nb078_fresh_1573 (h : Var) :
    (nb078_alpha_dummy_960 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_960] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv)
      0

theorem nb078_fresh_1574 :
    (nb078_alpha_dummy_999) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_999] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv)
      0

theorem nb078_fresh_1575 (h : Var) :
    (nb078_alpha_dummy_1000 h) ∉
      (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1000] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv)
      0

theorem nb078_fresh_1576 :
    (nb078_alpha_dummy_523) ∉
      (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_003))).fv) :=
  by
  simpa only [nb078_alpha_dummy_523] using
    freshVar_not_mem
      (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_003))).fv)
      0

theorem nb078_fresh_1577 :
    (nb078_alpha_dummy_1003) ∉
      (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_004))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1003] using
    freshVar_not_mem
      (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_004))).fv)
      0

theorem nb078_fresh_1578 (x : Var) (g : Var) :
    (nb078_alpha_dummy_524 x g) ∉ (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb078_alpha_dummy_524] using
    freshVar_not_mem (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) 0

theorem nb078_fresh_1579 (y : Var) (h : Var) :
    (nb078_alpha_dummy_1004 y h) ∉ (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb078_alpha_dummy_1004] using
    freshVar_not_mem (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) 0

theorem nb078_fresh_1580 :
    (nb078_alpha_dummy_015) ∉
      (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))
                (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011))
                (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_015] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))
                (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011))
                (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv)
      0

theorem nb078_fresh_1581 (f : Var) :
    (nb078_alpha_dummy_016 f) ∉
      (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb078_alpha_dummy_014 f)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f)
                (Class.cv (nb078_alpha_dummy_013 f)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_016] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb078_alpha_dummy_014 f)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f)
                (Class.cv (nb078_alpha_dummy_013 f)))))).fv)
      0

theorem nb078_fresh_1582 :
    (nb078_alpha_dummy_093) ∉
      (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000))
            (Class.cv (nb078_alpha_dummy_089)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_093] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000))
            (Class.cv (nb078_alpha_dummy_089)))).fv)
      0

theorem nb078_fresh_1583 (f : Var) :
    (nb078_alpha_dummy_094 f) ∉
      (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f)
            (Class.cv (nb078_alpha_dummy_091 f)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_094] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f)
            (Class.cv (nb078_alpha_dummy_091 f)))).fv)
      0

theorem nb078_fresh_1584 :
    (nb078_alpha_dummy_1055) ∉
      (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))
                (Class.cv (nb078_alpha_dummy_1051)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1051))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_1050)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1055] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))
                (Class.cv (nb078_alpha_dummy_1051)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1051))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_1050)))))).fv)
      0

theorem nb078_fresh_1585 (h : Var) :
    (nb078_alpha_dummy_1056 h) ∉
      (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h)
            (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1056] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h)
            (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_1053 h)))))).fv)
      0

theorem nb078_fresh_1586 :
    (nb078_alpha_dummy_1133) ∉
      (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1130))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_1129)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1133] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1130))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_1129)))).fv)
      0

theorem nb078_fresh_1587 (h : Var) :
    (nb078_alpha_dummy_1134 h) ∉
      (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb078_alpha_dummy_1131 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1134] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb078_alpha_dummy_1131 h)))).fv)
      0

theorem nb078_fresh_1588 :
    (nb078_alpha_dummy_293) ∉
      (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289))
                (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_293] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289))
                (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv)
      0

theorem nb078_fresh_1589 (g : Var) :
    (nb078_alpha_dummy_294 g) ∉
      (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_292 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g)
                (Class.cv (nb078_alpha_dummy_291 g)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_294] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_292 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g)
                (Class.cv (nb078_alpha_dummy_291 g)))))).fv)
      0

theorem nb078_fresh_1590 :
    (nb078_alpha_dummy_371) ∉
      (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001))
            (Class.cv (nb078_alpha_dummy_367)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_371] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001))
            (Class.cv (nb078_alpha_dummy_367)))).fv)
      0

theorem nb078_fresh_1591 (g : Var) :
    (nb078_alpha_dummy_372 g) ∉
      (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g)
            (Class.cv (nb078_alpha_dummy_369 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_372] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g)
            (Class.cv (nb078_alpha_dummy_369 g)))).fv)
      0

theorem nb078_fresh_1592 :
    (nb078_alpha_dummy_575) ∉
      (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))
                (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_570)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_575] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))
                (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_570)))))).fv)
      0

theorem nb078_fresh_1593 (g : Var) :
    (nb078_alpha_dummy_576 g) ∉
      (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_572 g))
                (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_573 g)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_576] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_572 g))
                (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_573 g)))))).fv)
      0

theorem nb078_fresh_1594 :
    (nb078_alpha_dummy_653) ∉
      (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_650))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_649)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_653] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_650))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_649)))).fv)
      0

theorem nb078_fresh_1595 (g : Var) :
    (nb078_alpha_dummy_654 g) ∉
      (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g))
            (Class.cv (nb078_alpha_dummy_651 g)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_654] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g))
            (Class.cv (nb078_alpha_dummy_651 g)))).fv)
      0

theorem nb078_fresh_1596 :
    (nb078_alpha_dummy_773) ∉
      (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769))
                (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_773] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769))
                (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv)
      0

theorem nb078_fresh_1597 (h : Var) :
    (nb078_alpha_dummy_774 h) ∉
      (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_772 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h)
                (Class.cv (nb078_alpha_dummy_771 h)))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_774] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_772 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h)
                (Class.cv (nb078_alpha_dummy_771 h)))))).fv)
      0

theorem nb078_fresh_1598 :
    (nb078_alpha_dummy_851) ∉
      (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002))
            (Class.cv (nb078_alpha_dummy_847)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_851] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002))
            (Class.cv (nb078_alpha_dummy_847)))).fv)
      0

theorem nb078_fresh_1599 (h : Var) :
    (nb078_alpha_dummy_852 h) ∉
      (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h)
            (Class.cv (nb078_alpha_dummy_849 h)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_852] using
    freshVar_not_mem
      (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h)
            (Class.cv (nb078_alpha_dummy_849 h)))).fv)
      0

theorem nb078_fresh_1600 : (nb078_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb078_fresh_1601 : (nb078_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb078_fresh_1602 : (nb078_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb078_fresh_1603 : (nb078_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb078_fresh_1604 : (nb078_alpha_dummy_004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb078_distinct_1605 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_001) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1606 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_002) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1607 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_003) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb078_distinct_1608 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb078_distinct_1609 : (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_002) := by
  simpa only [nb078_alpha_dummy_001, nb078_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb078_distinct_1610 : (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_003) := by
  simpa only [nb078_alpha_dummy_001, nb078_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb078_distinct_1611 : (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_001, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb078_distinct_1612 : (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_003) := by
  simpa only [nb078_alpha_dummy_002, nb078_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb078_distinct_1613 : (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_002, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb078_distinct_1614 : (nb078_alpha_dummy_003) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_003, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb078_support_mem_0000 :
    (nb078_alpha_dummy_009) ∈
      (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))
                (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011))
                (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0001 (f : Var) :
    (nb078_alpha_dummy_012 f) ∈
      (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb078_alpha_dummy_014 f)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f)
                (Class.cv (nb078_alpha_dummy_013 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0002 :
    (nb078_alpha_dummy_010) ∈
      (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))
                (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011))
                (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0003 (f : Var) :
    (nb078_alpha_dummy_013 f) ∈
      (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb078_alpha_dummy_014 f)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f)
                (Class.cv (nb078_alpha_dummy_013 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0004 :
    (nb078_alpha_dummy_009) ∈
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0005 :
    (nb078_alpha_dummy_009) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_017) from (by
          unfold nb078_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_018) from (by
            unfold nb078_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0006 (f : Var) :
    (nb078_alpha_dummy_012 f) ∈
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0007 (f : Var) :
    (nb078_alpha_dummy_012 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_019 f) from (by
          unfold nb078_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_020 f) from (by
            unfold nb078_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0008 :
    (nb078_alpha_dummy_009) ∈
      (((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_017) from (by
          unfold nb078_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_018) from (by
            unfold nb078_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0009 (f : Var) :
    (nb078_alpha_dummy_012 f) ∈
      (((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_019 f) from (by
          unfold nb078_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_020 f) from (by
            unfold nb078_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0010 :
    (nb078_alpha_dummy_018) ∈ (((Class.cv (nb078_alpha_dummy_018))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0011 (f : Var) :
    (nb078_alpha_dummy_020 f) ∈ (((Class.cv (nb078_alpha_dummy_020 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0012 :
    (nb078_alpha_dummy_025) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_025))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0013 (f : Var) :
    (nb078_alpha_dummy_027 f) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_027 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0014 :
    (nb078_alpha_dummy_025) ∈
      (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0015 (f : Var) :
    (nb078_alpha_dummy_027 f) ∈
      (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0016 :
    (nb078_alpha_dummy_032) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_032))
            (Class.cv (nb078_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0017 (f : Var) :
    (nb078_alpha_dummy_035 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0018 :
    (nb078_alpha_dummy_032) ∈
      (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0019 (f : Var) :
    (nb078_alpha_dummy_035 f) ∈
      (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0020 :
    (nb078_alpha_dummy_033) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_032))
            (Class.cv (nb078_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0021 (f : Var) :
    (nb078_alpha_dummy_036 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
            (Class.cv (nb078_alpha_dummy_036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0022 :
    (nb078_alpha_dummy_033) ∈
      (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0023 (f : Var) :
    (nb078_alpha_dummy_036 f) ∈
      (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0024 :
    (nb078_alpha_dummy_032) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0025 (f : Var) :
    (nb078_alpha_dummy_035 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0026 :
    (nb078_alpha_dummy_032) ∈
      (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0027 (f : Var) :
    (nb078_alpha_dummy_035 f) ∈
      (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_035 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0028 :
    (nb078_alpha_dummy_033) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0029 (f : Var) :
    (nb078_alpha_dummy_036 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0030 :
    (nb078_alpha_dummy_033) ∈
      (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0031 (f : Var) :
    (nb078_alpha_dummy_036 f) ∈
      (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0032 :
    (nb078_alpha_dummy_010) ∈
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
