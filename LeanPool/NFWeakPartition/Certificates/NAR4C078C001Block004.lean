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
    (nb078AlphaDummy343) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy339)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy339)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy339))).fv) :=
  by
  simpa only [nb078AlphaDummy343] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy339)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy339)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy339))).fv)
      0

theorem nb078_fresh_1155 (g : Var) :
    (nb078AlphaDummy344 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy341 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy341 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy341 g))).fv) :=
  by
  simpa only [nb078AlphaDummy344] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy341 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy341 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy341 g))).fv)
      0

theorem nb078_fresh_1156 :
    (nb078AlphaDummy385) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy381)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy381)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy381))).fv) :=
  by
  simpa only [nb078AlphaDummy385] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy381)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy381)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy381))).fv)
      0

theorem nb078_fresh_1157 (g : Var) :
    (nb078AlphaDummy386 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy383 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy383 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy383 g))).fv) :=
  by
  simpa only [nb078AlphaDummy386] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy383 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy383 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy383 g))).fv)
      0

theorem nb078_fresh_1158 :
    (nb078AlphaDummy421) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy417)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy417)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy417))).fv) :=
  by
  simpa only [nb078AlphaDummy421] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy417)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy417)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy417))).fv)
      0

theorem nb078_fresh_1159 (g : Var) :
    (nb078AlphaDummy422 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy419 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy419 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy419 g))).fv) :=
  by
  simpa only [nb078AlphaDummy422] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy419 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy419 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy419 g))).fv)
      0

theorem nb078_fresh_1160 :
    (nb078AlphaDummy457) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy453)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy453)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy453))).fv) :=
  by
  simpa only [nb078AlphaDummy457] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy453)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy453)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy453))).fv)
      0

theorem nb078_fresh_1161 (g : Var) :
    (nb078AlphaDummy458 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy455 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy455 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy455 g))).fv) :=
  by
  simpa only [nb078AlphaDummy458] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy455 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy455 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy455 g))).fv)
      0

theorem nb078_fresh_1162 :
    (nb078AlphaDummy497) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy493)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy493)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy493))).fv) :=
  by
  simpa only [nb078AlphaDummy497] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy493)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy493)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy493))).fv)
      0

theorem nb078_fresh_1163 (g : Var) :
    (nb078AlphaDummy498 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy495 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy495 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy495 g))).fv) :=
  by
  simpa only [nb078AlphaDummy498] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy495 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy495 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy495 g))).fv)
      0

theorem nb078_fresh_1164 :
    (nb078AlphaDummy541) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy537)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy537)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy537))).fv) :=
  by
  simpa only [nb078AlphaDummy541] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy537)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy537)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy537))).fv)
      0

theorem nb078_fresh_1165 (g : Var) :
    (nb078AlphaDummy542 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy539 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy539 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy539 g))).fv) :=
  by
  simpa only [nb078AlphaDummy542] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy539 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy539 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy539 g))).fv)
      0

theorem nb078_fresh_1166 :
    (nb078AlphaDummy589) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy585)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy585)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy585))).fv) :=
  by
  simpa only [nb078AlphaDummy589] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy585)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy585)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy585))).fv)
      0

theorem nb078_fresh_1167 (g : Var) :
    (nb078AlphaDummy590 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy587 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy587 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy587 g))).fv) :=
  by
  simpa only [nb078AlphaDummy590] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy587 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy587 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy587 g))).fv)
      0

theorem nb078_fresh_1168 :
    (nb078AlphaDummy625) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy621)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy621)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy621))).fv) :=
  by
  simpa only [nb078AlphaDummy625] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy621)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy621)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy621))).fv)
      0

theorem nb078_fresh_1169 (g : Var) :
    (nb078AlphaDummy626 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy623 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy623 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy623 g))).fv) :=
  by
  simpa only [nb078AlphaDummy626] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy623 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy623 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy623 g))).fv)
      0

theorem nb078_fresh_1170 :
    (nb078AlphaDummy667) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy663)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy663)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy663))).fv) :=
  by
  simpa only [nb078AlphaDummy667] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy663)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy663)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy663))).fv)
      0

theorem nb078_fresh_1171 (g : Var) :
    (nb078AlphaDummy668 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy665 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy665 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy665 g))).fv) :=
  by
  simpa only [nb078AlphaDummy668] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy665 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy665 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy665 g))).fv)
      0

theorem nb078_fresh_1172 :
    (nb078AlphaDummy703) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy699)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy699)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy699))).fv) :=
  by
  simpa only [nb078AlphaDummy703] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy699)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy699)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy699))).fv)
      0

theorem nb078_fresh_1173 (g : Var) :
    (nb078AlphaDummy704 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy701 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy701 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy701 g))).fv) :=
  by
  simpa only [nb078AlphaDummy704] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy701 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy701 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy701 g))).fv)
      0

theorem nb078_fresh_1174 :
    (nb078AlphaDummy739) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy735)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy735)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy735))).fv) :=
  by
  simpa only [nb078AlphaDummy739] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy735)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy735)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy735))).fv)
      0

theorem nb078_fresh_1175 (g : Var) :
    (nb078AlphaDummy740 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy737 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy737 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy737 g))).fv) :=
  by
  simpa only [nb078AlphaDummy740] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy737 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy737 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy737 g))).fv)
      0

theorem nb078_fresh_1176 :
    (nb078AlphaDummy787) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy783)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy783)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy783))).fv) :=
  by
  simpa only [nb078AlphaDummy787] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy783)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy783)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy783))).fv)
      0

theorem nb078_fresh_1177 (h : Var) :
    (nb078AlphaDummy788 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy785 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy785 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy785 h))).fv) :=
  by
  simpa only [nb078AlphaDummy788] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy785 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy785 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy785 h))).fv)
      0

theorem nb078_fresh_1178 :
    (nb078AlphaDummy823) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy819)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy819)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy819))).fv) :=
  by
  simpa only [nb078AlphaDummy823] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy819)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy819)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy819))).fv)
      0

theorem nb078_fresh_1179 (h : Var) :
    (nb078AlphaDummy824 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy821 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy821 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy821 h))).fv) :=
  by
  simpa only [nb078AlphaDummy824] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy821 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy821 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy821 h))).fv)
      0

theorem nb078_fresh_1180 :
    (nb078AlphaDummy865) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy861)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy861)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy861))).fv) :=
  by
  simpa only [nb078AlphaDummy865] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy861)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy861)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy861))).fv)
      0

theorem nb078_fresh_1181 (h : Var) :
    (nb078AlphaDummy866 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy863 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy863 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy863 h))).fv) :=
  by
  simpa only [nb078AlphaDummy866] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy863 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy863 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy863 h))).fv)
      0

theorem nb078_fresh_1182 :
    (nb078AlphaDummy901) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy897)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy897)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy897))).fv) :=
  by
  simpa only [nb078AlphaDummy901] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy897)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy897)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy897))).fv)
      0

theorem nb078_fresh_1183 (h : Var) :
    (nb078AlphaDummy902 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy899 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy899 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy899 h))).fv) :=
  by
  simpa only [nb078AlphaDummy902] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy899 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy899 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy899 h))).fv)
      0

theorem nb078_fresh_1184 :
    (nb078AlphaDummy937) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy933)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy933)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy933))).fv) :=
  by
  simpa only [nb078AlphaDummy937] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy933)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy933)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy933))).fv)
      0

theorem nb078_fresh_1185 (h : Var) :
    (nb078AlphaDummy938 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy935 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy935 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy935 h))).fv) :=
  by
  simpa only [nb078AlphaDummy938] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy935 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy935 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy935 h))).fv)
      0

theorem nb078_fresh_1186 :
    (nb078AlphaDummy977) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy973)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy973)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy973))).fv) :=
  by
  simpa only [nb078AlphaDummy977] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy973)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy973)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy973))).fv)
      0

theorem nb078_fresh_1187 (h : Var) :
    (nb078AlphaDummy978 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy975 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy975 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy975 h))).fv) :=
  by
  simpa only [nb078AlphaDummy978] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy975 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy975 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy975 h))).fv)
      0

theorem nb078_fresh_1188 :
    (nb078AlphaDummy203) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy203] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      0

theorem nb078_fresh_1189 :
    (nb078AlphaDummy204) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy204] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      1

theorem nb078_distinct_1190 : (nb078AlphaDummy203) ≠ (nb078AlphaDummy204) := by
  simpa only [nb078AlphaDummy203, nb078AlphaDummy204] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_fresh_1191 :
    (nb078AlphaDummy649) ∉ (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) := by
  simpa only [nb078AlphaDummy649] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) 0

theorem nb078_fresh_1192 :
    (nb078AlphaDummy650) ∉ (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) := by
  simpa only [nb078AlphaDummy650] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) 1

theorem nb078_distinct_1193 : (nb078AlphaDummy649) ≠ (nb078AlphaDummy650) := by
  simpa only [nb078AlphaDummy649, nb078AlphaDummy650] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_fresh_1194 :
    (nb078AlphaDummy569) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv) :=
  by
  simpa only [nb078AlphaDummy569] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
      0

theorem nb078_fresh_1195 :
    (nb078AlphaDummy570) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv) :=
  by
  simpa only [nb078AlphaDummy570] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
      1

theorem nb078_fresh_1196 :
    (nb078AlphaDummy571) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv) :=
  by
  simpa only [nb078AlphaDummy571] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
      2

theorem nb078_distinct_1197 : (nb078AlphaDummy569) ≠ (nb078AlphaDummy570) := by
  simpa only [nb078AlphaDummy569, nb078AlphaDummy570] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1198 : (nb078AlphaDummy569) ≠ (nb078AlphaDummy571) := by
  simpa only [nb078AlphaDummy569, nb078AlphaDummy571] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1199 : (nb078AlphaDummy570) ≠ (nb078AlphaDummy571) := by
  simpa only [nb078AlphaDummy570, nb078AlphaDummy571] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1200 :
    (nb078AlphaDummy481) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy481] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv)
      0

theorem nb078_fresh_1201 :
    (nb078AlphaDummy482) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy482] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv)
      1

theorem nb078_distinct_1202 : (nb078AlphaDummy481) ≠ (nb078AlphaDummy482) := by
  simpa only [nb078AlphaDummy481, nb078AlphaDummy482] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_fresh_1203 :
    (nb078AlphaDummy1129) ∉ (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) := by
  simpa only [nb078AlphaDummy1129] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) 0

theorem nb078_fresh_1204 :
    (nb078AlphaDummy1130) ∉ (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) := by
  simpa only [nb078AlphaDummy1130] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) 1

theorem nb078_distinct_1205 : (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1130) := by
  simpa only [nb078AlphaDummy1129, nb078AlphaDummy1130] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_fresh_1206 :
    (nb078AlphaDummy1049) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv) :=
  by
  simpa only [nb078AlphaDummy1049] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
      0

theorem nb078_fresh_1207 :
    (nb078AlphaDummy1050) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv) :=
  by
  simpa only [nb078AlphaDummy1050] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
      1

theorem nb078_fresh_1208 :
    (nb078AlphaDummy1051) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv) :=
  by
  simpa only [nb078AlphaDummy1051] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
      2

theorem nb078_distinct_1209 : (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1050) := by
  simpa only [nb078AlphaDummy1049, nb078AlphaDummy1050] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1210 : (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1051) := by
  simpa only [nb078AlphaDummy1049, nb078AlphaDummy1051] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1211 : (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1051) := by
  simpa only [nb078AlphaDummy1050, nb078AlphaDummy1051] using
    (freshVar_injective (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1212 :
    (nb078AlphaDummy961) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy961] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv)
      0

theorem nb078_fresh_1213 :
    (nb078AlphaDummy962) ∉
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy962] using
    freshVar_not_mem (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv)
      1

theorem nb078_distinct_1214 : (nb078AlphaDummy961) ≠ (nb078AlphaDummy962) := by
  simpa only [nb078AlphaDummy961, nb078AlphaDummy962] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_fresh_1215 (f : Var) :
    (nb078AlphaDummy205 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy205] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_1216 (f : Var) :
    (nb078AlphaDummy206 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy206] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_1217 (f : Var) :
    (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy206 f) := by
  simpa only [nb078AlphaDummy205, nb078AlphaDummy206] using
    (freshVar_injective (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1218 (g : Var) :
    (nb078AlphaDummy651 g) ∉ (((synCcnv (Class.cv g))).fv) := by
  simpa only [nb078AlphaDummy651] using
    freshVar_not_mem (((synCcnv (Class.cv g))).fv) 0

theorem nb078_fresh_1219 (g : Var) :
    (nb078AlphaDummy652 g) ∉ (((synCcnv (Class.cv g))).fv) := by
  simpa only [nb078AlphaDummy652] using
    freshVar_not_mem (((synCcnv (Class.cv g))).fv) 1

theorem nb078_distinct_1220 (g : Var) :
    (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy652 g) := by
  simpa only [nb078AlphaDummy651, nb078AlphaDummy652] using
    (freshVar_injective (((synCcnv (Class.cv g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1221 (g : Var) :
    (nb078AlphaDummy572 g) ∉
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) :=
  by
  simpa only [nb078AlphaDummy572] using
    freshVar_not_mem
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) 0

theorem nb078_fresh_1222 (g : Var) :
    (nb078AlphaDummy573 g) ∉
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) :=
  by
  simpa only [nb078AlphaDummy573] using
    freshVar_not_mem
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) 1

theorem nb078_fresh_1223 (g : Var) :
    (nb078AlphaDummy574 g) ∉
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) :=
  by
  simpa only [nb078AlphaDummy574] using
    freshVar_not_mem
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) 2

theorem nb078_distinct_1224 (g : Var) :
    (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy573 g) := by
  simpa only [nb078AlphaDummy572, nb078AlphaDummy573] using
    (freshVar_injective
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_distinct_1225 (g : Var) :
    (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy574 g) := by
  simpa only [nb078AlphaDummy572, nb078AlphaDummy574] using
    (freshVar_injective
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb078_distinct_1226 (g : Var) :
    (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy574 g) := by
  simpa only [nb078AlphaDummy573, nb078AlphaDummy574] using
    (freshVar_injective
      (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb078_fresh_1227 (g : Var) :
    (nb078AlphaDummy483 g) ∉ (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy483] using
    freshVar_not_mem (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_1228 (g : Var) :
    (nb078AlphaDummy484 g) ∉ (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy484] using
    freshVar_not_mem (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_1229 (g : Var) :
    (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy484 g) := by
  simpa only [nb078AlphaDummy483, nb078AlphaDummy484] using
    (freshVar_injective (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1230 (h : Var) :
    (nb078AlphaDummy1131 h) ∉ (((synCcnv (Class.cv h))).fv) := by
  simpa only [nb078AlphaDummy1131] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv) 0

theorem nb078_fresh_1231 (h : Var) :
    (nb078AlphaDummy1132 h) ∉ (((synCcnv (Class.cv h))).fv) := by
  simpa only [nb078AlphaDummy1132] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv) 1

theorem nb078_distinct_1232 (h : Var) :
    (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1132 h) := by
  simpa only [nb078AlphaDummy1131, nb078AlphaDummy1132] using
    (freshVar_injective (((synCcnv (Class.cv h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1233 (h : Var) :
    (nb078AlphaDummy1052 h) ∉
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1052] using
    freshVar_not_mem
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 0

theorem nb078_fresh_1234 (h : Var) :
    (nb078AlphaDummy1053 h) ∉
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1053] using
    freshVar_not_mem
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 1

theorem nb078_fresh_1235 (h : Var) :
    (nb078AlphaDummy1054 h) ∉
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1054] using
    freshVar_not_mem
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 2

theorem nb078_distinct_1236 (h : Var) :
    (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1053 h) := by
  simpa only [nb078AlphaDummy1052, nb078AlphaDummy1053] using
    (freshVar_injective
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb078_distinct_1237 (h : Var) :
    (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1054 h) := by
  simpa only [nb078AlphaDummy1052, nb078AlphaDummy1054] using
    (freshVar_injective
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb078_distinct_1238 (h : Var) :
    (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1054 h) := by
  simpa only [nb078AlphaDummy1053, nb078AlphaDummy1054] using
    (freshVar_injective
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb078_fresh_1239 (h : Var) :
    (nb078AlphaDummy963 h) ∉ (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy963] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_1240 (h : Var) :
    (nb078AlphaDummy964 h) ∉ (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy964] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_1241 (h : Var) :
    (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy964 h) := by
  simpa only [nb078AlphaDummy963, nb078AlphaDummy964] using
    (freshVar_injective (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1242 :
    (nb078AlphaDummy007) ∉
      (((synCcom (Class.cv (nb078AlphaDummy000))
            (synCcnv (Class.cv (nb078AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy007] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb078AlphaDummy000))
            (synCcnv (Class.cv (nb078AlphaDummy000))))).fv ∪ ((synCid)).fv)
      0

theorem nb078_fresh_1243 :
    (nb078AlphaDummy285) ∉
      (((synCcom (Class.cv (nb078AlphaDummy001))
            (synCcnv (Class.cv (nb078AlphaDummy001))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy285] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb078AlphaDummy001))
            (synCcnv (Class.cv (nb078AlphaDummy001))))).fv ∪ ((synCid)).fv)
      0

theorem nb078_fresh_1244 :
    (nb078AlphaDummy765) ∉
      (((synCcom (Class.cv (nb078AlphaDummy002))
            (synCcnv (Class.cv (nb078AlphaDummy002))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy765] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb078AlphaDummy002))
            (synCcnv (Class.cv (nb078AlphaDummy002))))).fv ∪ ((synCid)).fv)
      0

theorem nb078_fresh_1245 (f : Var) :
    (nb078AlphaDummy008 f) ∉
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy008] using
    freshVar_not_mem
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0

theorem nb078_fresh_1246 (g : Var) :
    (nb078AlphaDummy286 g) ∉
      (((synCcom (Class.cv g) (synCcnv (Class.cv g)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy286] using
    freshVar_not_mem
      (((synCcom (Class.cv g) (synCcnv (Class.cv g)))).fv ∪ ((synCid)).fv) 0

theorem nb078_fresh_1247 (h : Var) :
    (nb078AlphaDummy766 h) ∉
      (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy766] using
    freshVar_not_mem
      (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) 0

theorem nb078_fresh_1248 :
    (nb078AlphaDummy567) ∉
      (((synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001)))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy567] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001)))))).fv ∪ ((synCid)).fv)
      0

theorem nb078_fresh_1249 :
    (nb078AlphaDummy1047) ∉
      (((synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002)))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy1047] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002)))))).fv ∪ ((synCid)).fv)
      0

theorem nb078_fresh_1250 (g : Var) :
    (nb078AlphaDummy568 g) ∉
      (((synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))).fv ∪
        ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy568] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))).fv ∪
        ((synCid)).fv)
      0

theorem nb078_fresh_1251 (h : Var) :
    (nb078AlphaDummy1048 h) ∉
      (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
        ((synCid)).fv) :=
  by
  simpa only [nb078AlphaDummy1048] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
        ((synCid)).fv)
      0

theorem nb078_fresh_1252 :
    (nb078AlphaDummy021) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCphi (Class.cv (nb078AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy021] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCphi (Class.cv (nb078AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1253 (f : Var) :
    (nb078AlphaDummy022 f) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCphi (Class.cv (nb078AlphaDummy020 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy022] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCphi (Class.cv (nb078AlphaDummy020 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1254 :
    (nb078AlphaDummy057) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCphi (Class.cv (nb078AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy057] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCphi (Class.cv (nb078AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1255 (f : Var) :
    (nb078AlphaDummy058 f) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCphi (Class.cv (nb078AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy058] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCphi (Class.cv (nb078AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1256 :
    (nb078AlphaDummy099) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCphi (Class.cv (nb078AlphaDummy096)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy099] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCphi (Class.cv (nb078AlphaDummy096)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1257 (f : Var) :
    (nb078AlphaDummy100 f) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCphi (Class.cv (nb078AlphaDummy098 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy100] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCphi (Class.cv (nb078AlphaDummy098 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1258 :
    (nb078AlphaDummy1013) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCphi (Class.cv (nb078AlphaDummy1010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1013] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCphi (Class.cv (nb078AlphaDummy1010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1259 (h : Var) :
    (nb078AlphaDummy1014 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCphi (Class.cv (nb078AlphaDummy1012 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1014] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCphi (Class.cv (nb078AlphaDummy1012 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1260 :
    (nb078AlphaDummy1061) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCphi (Class.cv (nb078AlphaDummy1058)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1061] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCphi (Class.cv (nb078AlphaDummy1058)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1261 (h : Var) :
    (nb078AlphaDummy1062 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCphi (Class.cv (nb078AlphaDummy1060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1062] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCphi (Class.cv (nb078AlphaDummy1060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1262 :
    (nb078AlphaDummy1097) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCphi (Class.cv (nb078AlphaDummy1094)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1097] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCphi (Class.cv (nb078AlphaDummy1094)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1263 (h : Var) :
    (nb078AlphaDummy1098 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCphi (Class.cv (nb078AlphaDummy1096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1098] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCphi (Class.cv (nb078AlphaDummy1096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1264 :
    (nb078AlphaDummy1139) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCphi (Class.cv (nb078AlphaDummy1136)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1139] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCphi (Class.cv (nb078AlphaDummy1136)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1265 (h : Var) :
    (nb078AlphaDummy1140 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCphi (Class.cv (nb078AlphaDummy1138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1140] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCphi (Class.cv (nb078AlphaDummy1138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1266 :
    (nb078AlphaDummy1175) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCphi (Class.cv (nb078AlphaDummy1172)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1175] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCphi (Class.cv (nb078AlphaDummy1172)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1267 (h : Var) :
    (nb078AlphaDummy1176 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCphi (Class.cv (nb078AlphaDummy1174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1176] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCphi (Class.cv (nb078AlphaDummy1174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1268 :
    (nb078AlphaDummy1211) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCphi (Class.cv (nb078AlphaDummy1208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1211] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCphi (Class.cv (nb078AlphaDummy1208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1269 (h : Var) :
    (nb078AlphaDummy1212 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCphi (Class.cv (nb078AlphaDummy1210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1212] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCphi (Class.cv (nb078AlphaDummy1210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1270 :
    (nb078AlphaDummy135) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCphi (Class.cv (nb078AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy135] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCphi (Class.cv (nb078AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1271 (f : Var) :
    (nb078AlphaDummy136 f) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCphi (Class.cv (nb078AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy136] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCphi (Class.cv (nb078AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1272 :
    (nb078AlphaDummy171) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCphi (Class.cv (nb078AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy171] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCphi (Class.cv (nb078AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1273 (f : Var) :
    (nb078AlphaDummy172 f) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCphi (Class.cv (nb078AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy172] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCphi (Class.cv (nb078AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv)
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
    (nb078AlphaDummy211) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCphi (Class.cv (nb078AlphaDummy208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy211] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCphi (Class.cv (nb078AlphaDummy208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1275 (f : Var) :
    (nb078AlphaDummy212 f) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCphi (Class.cv (nb078AlphaDummy210 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy212] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCphi (Class.cv (nb078AlphaDummy210 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1276 :
    (nb078AlphaDummy251) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCphi (Class.cv (nb078AlphaDummy248)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy251] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCphi (Class.cv (nb078AlphaDummy248)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1277 (f : Var) :
    (nb078AlphaDummy252 f) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCphi (Class.cv (nb078AlphaDummy250 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy252] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCphi (Class.cv (nb078AlphaDummy250 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1278 :
    (nb078AlphaDummy299) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCphi (Class.cv (nb078AlphaDummy296)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy299] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCphi (Class.cv (nb078AlphaDummy296)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1279 (g : Var) :
    (nb078AlphaDummy300 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCphi (Class.cv (nb078AlphaDummy298 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy300] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCphi (Class.cv (nb078AlphaDummy298 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1280 :
    (nb078AlphaDummy335) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCphi (Class.cv (nb078AlphaDummy332)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy335] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCphi (Class.cv (nb078AlphaDummy332)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1281 (g : Var) :
    (nb078AlphaDummy336 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCphi (Class.cv (nb078AlphaDummy334 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy336] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCphi (Class.cv (nb078AlphaDummy334 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1282 :
    (nb078AlphaDummy377) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCphi (Class.cv (nb078AlphaDummy374)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy377] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCphi (Class.cv (nb078AlphaDummy374)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1283 (g : Var) :
    (nb078AlphaDummy378 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCphi (Class.cv (nb078AlphaDummy376 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy378] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCphi (Class.cv (nb078AlphaDummy376 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1284 :
    (nb078AlphaDummy413) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCphi (Class.cv (nb078AlphaDummy410)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy413] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCphi (Class.cv (nb078AlphaDummy410)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1285 (g : Var) :
    (nb078AlphaDummy414 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCphi (Class.cv (nb078AlphaDummy412 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy414] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCphi (Class.cv (nb078AlphaDummy412 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1286 :
    (nb078AlphaDummy449) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCphi (Class.cv (nb078AlphaDummy446)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy449] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCphi (Class.cv (nb078AlphaDummy446)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy445)
              (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
                (Wff.classEq (Class.cv (nb078AlphaDummy445))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1287 (g : Var) :
    (nb078AlphaDummy450 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCphi (Class.cv (nb078AlphaDummy448 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy450] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCphi (Class.cv (nb078AlphaDummy448 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy447 g)
              (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1288 :
    (nb078AlphaDummy489) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCphi (Class.cv (nb078AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy489] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCphi (Class.cv (nb078AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1289 (g : Var) :
    (nb078AlphaDummy490 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCphi (Class.cv (nb078AlphaDummy488 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy490] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCphi (Class.cv (nb078AlphaDummy488 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1290 :
    (nb078AlphaDummy533) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCphi (Class.cv (nb078AlphaDummy530)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy533] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCphi (Class.cv (nb078AlphaDummy530)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1291 (g : Var) :
    (nb078AlphaDummy534 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCphi (Class.cv (nb078AlphaDummy532 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy534] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCphi (Class.cv (nb078AlphaDummy532 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1292 :
    (nb078AlphaDummy581) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCphi (Class.cv (nb078AlphaDummy578)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy581] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCphi (Class.cv (nb078AlphaDummy578)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1293 (g : Var) :
    (nb078AlphaDummy582 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCphi (Class.cv (nb078AlphaDummy580 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy582] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCphi (Class.cv (nb078AlphaDummy580 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1294 :
    (nb078AlphaDummy617) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCphi (Class.cv (nb078AlphaDummy614)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy617] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCphi (Class.cv (nb078AlphaDummy614)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1295 (g : Var) :
    (nb078AlphaDummy618 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCphi (Class.cv (nb078AlphaDummy616 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy618] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCphi (Class.cv (nb078AlphaDummy616 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1296 :
    (nb078AlphaDummy659) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCphi (Class.cv (nb078AlphaDummy656)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy659] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCphi (Class.cv (nb078AlphaDummy656)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1297 (g : Var) :
    (nb078AlphaDummy660 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCphi (Class.cv (nb078AlphaDummy658 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy660] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCphi (Class.cv (nb078AlphaDummy658 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1298 :
    (nb078AlphaDummy695) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCphi (Class.cv (nb078AlphaDummy692)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy695] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCphi (Class.cv (nb078AlphaDummy692)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1299 (g : Var) :
    (nb078AlphaDummy696 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCphi (Class.cv (nb078AlphaDummy694 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy696] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCphi (Class.cv (nb078AlphaDummy694 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1300 :
    (nb078AlphaDummy731) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCphi (Class.cv (nb078AlphaDummy728)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy731] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCphi (Class.cv (nb078AlphaDummy728)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy727)
              (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
                (Wff.classEq (Class.cv (nb078AlphaDummy727))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1301 (g : Var) :
    (nb078AlphaDummy732 g) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCphi (Class.cv (nb078AlphaDummy730 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy732] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCphi (Class.cv (nb078AlphaDummy730 g)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy729 g)
              (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1302 :
    (nb078AlphaDummy779) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCphi (Class.cv (nb078AlphaDummy776)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy779] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCphi (Class.cv (nb078AlphaDummy776)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1303 (h : Var) :
    (nb078AlphaDummy780 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCphi (Class.cv (nb078AlphaDummy778 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy780] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCphi (Class.cv (nb078AlphaDummy778 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1304 :
    (nb078AlphaDummy815) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCphi (Class.cv (nb078AlphaDummy812)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy815] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCphi (Class.cv (nb078AlphaDummy812)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1305 (h : Var) :
    (nb078AlphaDummy816 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCphi (Class.cv (nb078AlphaDummy814 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy816] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCphi (Class.cv (nb078AlphaDummy814 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1306 :
    (nb078AlphaDummy857) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCphi (Class.cv (nb078AlphaDummy854)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy857] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCphi (Class.cv (nb078AlphaDummy854)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1307 (h : Var) :
    (nb078AlphaDummy858 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCphi (Class.cv (nb078AlphaDummy856 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy858] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCphi (Class.cv (nb078AlphaDummy856 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1308 :
    (nb078AlphaDummy893) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCphi (Class.cv (nb078AlphaDummy890)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy893] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCphi (Class.cv (nb078AlphaDummy890)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1309 (h : Var) :
    (nb078AlphaDummy894 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCphi (Class.cv (nb078AlphaDummy892 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy894] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCphi (Class.cv (nb078AlphaDummy892 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1310 :
    (nb078AlphaDummy929) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCphi (Class.cv (nb078AlphaDummy926)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy929] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCphi (Class.cv (nb078AlphaDummy926)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1311 (h : Var) :
    (nb078AlphaDummy930 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCphi (Class.cv (nb078AlphaDummy928 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy930] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCphi (Class.cv (nb078AlphaDummy928 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1312 :
    (nb078AlphaDummy969) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCphi (Class.cv (nb078AlphaDummy966)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy969] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCphi (Class.cv (nb078AlphaDummy966)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1313 (h : Var) :
    (nb078AlphaDummy970 h) ∉
      (((synCcompl (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCphi (Class.cv (nb078AlphaDummy968 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb078AlphaDummy970] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCphi (Class.cv (nb078AlphaDummy968 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb078_fresh_1314 :
    (nb078AlphaDummy041) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy033)))).fv) :=
  by
  simpa only [nb078AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy033)))).fv)
      0

theorem nb078_fresh_1315 (f : Var) :
    (nb078AlphaDummy042 f) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy035 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy036 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy042] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy035 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy036 f)))).fv)
      0

theorem nb078_fresh_1316 :
    (nb078AlphaDummy077) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy069)))).fv) :=
  by
  simpa only [nb078AlphaDummy077] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy069)))).fv)
      0

theorem nb078_fresh_1317 (f : Var) :
    (nb078AlphaDummy078 f) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy072 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy072 f)))).fv)
      0

theorem nb078_fresh_1318 :
    (nb078AlphaDummy1033) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1024)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1025)))).fv) :=
  by
  simpa only [nb078AlphaDummy1033] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1024)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1025)))).fv)
      0

theorem nb078_fresh_1319 (h : Var) :
    (nb078AlphaDummy1034 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1027 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1028 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1034] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1027 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1028 h)))).fv)
      0

theorem nb078_fresh_1320 :
    (nb078AlphaDummy1081) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1072)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1073)))).fv) :=
  by
  simpa only [nb078AlphaDummy1081] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1072)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1073)))).fv)
      0

theorem nb078_fresh_1321 (h : Var) :
    (nb078AlphaDummy1082 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1075 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1076 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1082] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1075 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1076 h)))).fv)
      0

theorem nb078_fresh_1322 :
    (nb078AlphaDummy119) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy110)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy111)))).fv) :=
  by
  simpa only [nb078AlphaDummy119] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy110)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy111)))).fv)
      0

theorem nb078_fresh_1323 :
    (nb078AlphaDummy1117) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1108)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1109)))).fv) :=
  by
  simpa only [nb078AlphaDummy1117] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1108)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1109)))).fv)
      0

theorem nb078_fresh_1324 (h : Var) :
    (nb078AlphaDummy1118 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1111 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1112 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1118] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1111 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1112 h)))).fv)
      0

theorem nb078_fresh_1325 (f : Var) :
    (nb078AlphaDummy120 f) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy113 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy114 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy120] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy113 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy114 f)))).fv)
      0

theorem nb078_fresh_1326 :
    (nb078AlphaDummy1159) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1150)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1151)))).fv) :=
  by
  simpa only [nb078AlphaDummy1159] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1150)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1151)))).fv)
      0

theorem nb078_fresh_1327 (h : Var) :
    (nb078AlphaDummy1160 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1153 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1154 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1160] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1153 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1154 h)))).fv)
      0

theorem nb078_fresh_1328 :
    (nb078AlphaDummy1195) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1186)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1187)))).fv) :=
  by
  simpa only [nb078AlphaDummy1195] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1186)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1187)))).fv)
      0

theorem nb078_fresh_1329 (h : Var) :
    (nb078AlphaDummy1196 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1189 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1190 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1196] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1189 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1190 h)))).fv)
      0

theorem nb078_fresh_1330 :
    (nb078AlphaDummy1231) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1223)))).fv) :=
  by
  simpa only [nb078AlphaDummy1231] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1223)))).fv)
      0

theorem nb078_fresh_1331 (h : Var) :
    (nb078AlphaDummy1232 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy1225 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1226 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1232] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy1225 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1226 h)))).fv)
      0

theorem nb078_fresh_1332 :
    (nb078AlphaDummy155) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy147)))).fv) :=
  by
  simpa only [nb078AlphaDummy155] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy147)))).fv)
      0

theorem nb078_fresh_1333 (f : Var) :
    (nb078AlphaDummy156 f) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy150 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy156] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy150 f)))).fv)
      0

theorem nb078_fresh_1334 :
    (nb078AlphaDummy191) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy183)))).fv) :=
  by
  simpa only [nb078AlphaDummy191] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy183)))).fv)
      0

theorem nb078_fresh_1335 (f : Var) :
    (nb078AlphaDummy192 f) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy186 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy192] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy186 f)))).fv)
      0

theorem nb078_fresh_1336 :
    (nb078AlphaDummy231) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy223)))).fv) :=
  by
  simpa only [nb078AlphaDummy231] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy223)))).fv)
      0

theorem nb078_fresh_1337 (f : Var) :
    (nb078AlphaDummy232 f) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy225 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy226 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy232] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy225 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy226 f)))).fv)
      0

theorem nb078_fresh_1338 :
    (nb078AlphaDummy271) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy262)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy263)))).fv) :=
  by
  simpa only [nb078AlphaDummy271] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy262)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy263)))).fv)
      0

theorem nb078_fresh_1339 (f : Var) :
    (nb078AlphaDummy272 f) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy265 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy266 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy272] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy265 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy266 f)))).fv)
      0

theorem nb078_fresh_1340 :
    (nb078AlphaDummy319) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy310)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy311)))).fv) :=
  by
  simpa only [nb078AlphaDummy319] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy310)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy311)))).fv)
      0

theorem nb078_fresh_1341 (g : Var) :
    (nb078AlphaDummy320 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy313 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy314 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy320] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy313 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy314 g)))).fv)
      0

theorem nb078_fresh_1342 :
    (nb078AlphaDummy355) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy346)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy347)))).fv) :=
  by
  simpa only [nb078AlphaDummy355] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy346)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy347)))).fv)
      0

theorem nb078_fresh_1343 (g : Var) :
    (nb078AlphaDummy356 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy349 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy350 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy356] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy349 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy350 g)))).fv)
      0

theorem nb078_fresh_1344 :
    (nb078AlphaDummy397) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy388)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy389)))).fv) :=
  by
  simpa only [nb078AlphaDummy397] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy388)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy389)))).fv)
      0

theorem nb078_fresh_1345 (g : Var) :
    (nb078AlphaDummy398 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy391 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy392 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy398] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy391 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy392 g)))).fv)
      0

theorem nb078_fresh_1346 :
    (nb078AlphaDummy433) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy424)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy425)))).fv) :=
  by
  simpa only [nb078AlphaDummy433] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy424)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy425)))).fv)
      0

theorem nb078_fresh_1347 (g : Var) :
    (nb078AlphaDummy434 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy427 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy428 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy434] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy427 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy428 g)))).fv)
      0

theorem nb078_fresh_1348 :
    (nb078AlphaDummy469) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy460)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy461)))).fv) :=
  by
  simpa only [nb078AlphaDummy469] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy460)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy461)))).fv)
      0

theorem nb078_fresh_1349 (g : Var) :
    (nb078AlphaDummy470 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy463 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy464 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy470] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy463 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy464 g)))).fv)
      0

theorem nb078_fresh_1350 :
    (nb078AlphaDummy509) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy501)))).fv) :=
  by
  simpa only [nb078AlphaDummy509] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy501)))).fv)
      0

theorem nb078_fresh_1351 (g : Var) :
    (nb078AlphaDummy510 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy503 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy504 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy510] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy503 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy504 g)))).fv)
      0

theorem nb078_fresh_1352 :
    (nb078AlphaDummy553) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy544)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy545)))).fv) :=
  by
  simpa only [nb078AlphaDummy553] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy544)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy545)))).fv)
      0

theorem nb078_fresh_1353 (g : Var) :
    (nb078AlphaDummy554 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy547 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy548 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy554] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy547 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy548 g)))).fv)
      0

theorem nb078_fresh_1354 :
    (nb078AlphaDummy601) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy592)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy593)))).fv) :=
  by
  simpa only [nb078AlphaDummy601] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy592)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy593)))).fv)
      0

theorem nb078_fresh_1355 (g : Var) :
    (nb078AlphaDummy602 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy595 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy596 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy602] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy595 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy596 g)))).fv)
      0

theorem nb078_fresh_1356 :
    (nb078AlphaDummy637) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy628)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy629)))).fv) :=
  by
  simpa only [nb078AlphaDummy637] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy628)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy629)))).fv)
      0

theorem nb078_fresh_1357 (g : Var) :
    (nb078AlphaDummy638 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy631 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy632 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy638] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy631 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy632 g)))).fv)
      0

theorem nb078_fresh_1358 :
    (nb078AlphaDummy679) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy670)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy671)))).fv) :=
  by
  simpa only [nb078AlphaDummy679] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy670)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy671)))).fv)
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
    (nb078AlphaDummy680 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy673 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy674 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy680] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy673 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy674 g)))).fv)
      0

theorem nb078_fresh_1360 :
    (nb078AlphaDummy715) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy706)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy707)))).fv) :=
  by
  simpa only [nb078AlphaDummy715] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy706)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy707)))).fv)
      0

theorem nb078_fresh_1361 (g : Var) :
    (nb078AlphaDummy716 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy709 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy710 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy716] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy709 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy710 g)))).fv)
      0

theorem nb078_fresh_1362 :
    (nb078AlphaDummy751) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy742)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy743)))).fv) :=
  by
  simpa only [nb078AlphaDummy751] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy742)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy743)))).fv)
      0

theorem nb078_fresh_1363 (g : Var) :
    (nb078AlphaDummy752 g) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy745 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy746 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy752] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy745 g)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy746 g)))).fv)
      0

theorem nb078_fresh_1364 :
    (nb078AlphaDummy799) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy790)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy791)))).fv) :=
  by
  simpa only [nb078AlphaDummy799] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy790)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy791)))).fv)
      0

theorem nb078_fresh_1365 (h : Var) :
    (nb078AlphaDummy800 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy793 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy794 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy800] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy793 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy794 h)))).fv)
      0

theorem nb078_fresh_1366 :
    (nb078AlphaDummy835) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy826)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy827)))).fv) :=
  by
  simpa only [nb078AlphaDummy835] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy826)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy827)))).fv)
      0

theorem nb078_fresh_1367 (h : Var) :
    (nb078AlphaDummy836 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy829 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy830 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy836] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy829 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy830 h)))).fv)
      0

theorem nb078_fresh_1368 :
    (nb078AlphaDummy877) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy868)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy869)))).fv) :=
  by
  simpa only [nb078AlphaDummy877] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy868)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy869)))).fv)
      0

theorem nb078_fresh_1369 (h : Var) :
    (nb078AlphaDummy878 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy871 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy872 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy878] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy871 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy872 h)))).fv)
      0

theorem nb078_fresh_1370 :
    (nb078AlphaDummy913) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy904)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy905)))).fv) :=
  by
  simpa only [nb078AlphaDummy913] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy904)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy905)))).fv)
      0

theorem nb078_fresh_1371 (h : Var) :
    (nb078AlphaDummy914 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy907 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy908 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy914] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy907 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy908 h)))).fv)
      0

theorem nb078_fresh_1372 :
    (nb078AlphaDummy949) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy940)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy941)))).fv) :=
  by
  simpa only [nb078AlphaDummy949] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy940)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy941)))).fv)
      0

theorem nb078_fresh_1373 (h : Var) :
    (nb078AlphaDummy950 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy943 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy944 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy950] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy943 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy944 h)))).fv)
      0

theorem nb078_fresh_1374 :
    (nb078AlphaDummy989) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy980)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy981)))).fv) :=
  by
  simpa only [nb078AlphaDummy989] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy980)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy981)))).fv)
      0

theorem nb078_fresh_1375 (h : Var) :
    (nb078AlphaDummy990 h) ∉
      (((synCcompl (Class.cv (nb078AlphaDummy983 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy984 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy990] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb078AlphaDummy983 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy984 h)))).fv)
      0

theorem nb078_fresh_1376 :
    (nb078AlphaDummy049) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy018))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy018))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1377 (f : Var) :
    (nb078AlphaDummy050 f) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy020 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy050] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy020 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1378 :
    (nb078AlphaDummy085) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy054))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy085] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy054))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1379 (f : Var) :
    (nb078AlphaDummy086 f) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy056 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy086] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy056 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1380 :
    (nb078AlphaDummy127) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy096))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy127] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy096))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1381 (f : Var) :
    (nb078AlphaDummy128 f) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy098 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy128] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy098 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1382 :
    (nb078AlphaDummy1041) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1010))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1041] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1010))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1383 (h : Var) :
    (nb078AlphaDummy1042 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1012 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1042] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1012 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1384 :
    (nb078AlphaDummy1089) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1058))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1089] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1058))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1385 (h : Var) :
    (nb078AlphaDummy1090 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1060 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1090] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1060 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1386 :
    (nb078AlphaDummy1125) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1094))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1125] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1094))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1387 (h : Var) :
    (nb078AlphaDummy1126 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1096 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1126] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1096 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1388 :
    (nb078AlphaDummy1167) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1136))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1167] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1136))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1389 (h : Var) :
    (nb078AlphaDummy1168 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1138 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1168] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1138 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1390 :
    (nb078AlphaDummy1203) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1172))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1203] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1172))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1391 (h : Var) :
    (nb078AlphaDummy1204 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1174 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1204] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1174 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1392 :
    (nb078AlphaDummy1239) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1208))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1239] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1208))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1393 (h : Var) :
    (nb078AlphaDummy1240 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1210 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy1240] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1210 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1394 :
    (nb078AlphaDummy163) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy132))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy163] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy132))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1395 (f : Var) :
    (nb078AlphaDummy164 f) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy134 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy164] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy134 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1396 :
    (nb078AlphaDummy199) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy168))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy199] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy168))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1397 (f : Var) :
    (nb078AlphaDummy200 f) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy170 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy200] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy170 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1398 :
    (nb078AlphaDummy239) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy208))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy239] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy208))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1399 (f : Var) :
    (nb078AlphaDummy240 f) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy210 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy240] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy210 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1400 :
    (nb078AlphaDummy279) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy248))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy279] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy248))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1401 (f : Var) :
    (nb078AlphaDummy280 f) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy250 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy280] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy250 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1402 :
    (nb078AlphaDummy327) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy296))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy327] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy296))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1403 (g : Var) :
    (nb078AlphaDummy328 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy298 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy328] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy298 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1404 :
    (nb078AlphaDummy363) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy332))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy363] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy332))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1405 (g : Var) :
    (nb078AlphaDummy364 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy334 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy364] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy334 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1406 :
    (nb078AlphaDummy405) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy374))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy405] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy374))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1407 (g : Var) :
    (nb078AlphaDummy406 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy376 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy406] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy376 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1408 :
    (nb078AlphaDummy441) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy410))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy441] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy410))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1409 (g : Var) :
    (nb078AlphaDummy442 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy412 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy442] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy412 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1410 :
    (nb078AlphaDummy477) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy446))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy477] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy446))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1411 (g : Var) :
    (nb078AlphaDummy478 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy448 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy478] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy448 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1412 :
    (nb078AlphaDummy517) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy486))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy517] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy486))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1413 (g : Var) :
    (nb078AlphaDummy518 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy488 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy518] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy488 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1414 :
    (nb078AlphaDummy561) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy530))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy561] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy530))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1415 (g : Var) :
    (nb078AlphaDummy562 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy532 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy562] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy532 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1416 :
    (nb078AlphaDummy609) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy578))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy609] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy578))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1417 (g : Var) :
    (nb078AlphaDummy610 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy580 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy610] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy580 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1418 :
    (nb078AlphaDummy645) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy614))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy645] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy614))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1419 (g : Var) :
    (nb078AlphaDummy646 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy616 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy646] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy616 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1420 :
    (nb078AlphaDummy687) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy656))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy687] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy656))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1421 (g : Var) :
    (nb078AlphaDummy688 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy658 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy688] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy658 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1422 :
    (nb078AlphaDummy723) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy692))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy723] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy692))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1423 (g : Var) :
    (nb078AlphaDummy724 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy694 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy724] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy694 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1424 :
    (nb078AlphaDummy759) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy728))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy759] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy728))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1425 (g : Var) :
    (nb078AlphaDummy760 g) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy730 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy760] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy730 g))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1426 :
    (nb078AlphaDummy807) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy776))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy807] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy776))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1427 (h : Var) :
    (nb078AlphaDummy808 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy778 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy808] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy778 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1428 :
    (nb078AlphaDummy843) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy812))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy843] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy812))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1429 (h : Var) :
    (nb078AlphaDummy844 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy814 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy844] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy814 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1430 :
    (nb078AlphaDummy885) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy854))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy885] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy854))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1431 (h : Var) :
    (nb078AlphaDummy886 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy856 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy886] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy856 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1432 :
    (nb078AlphaDummy921) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy890))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy921] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy890))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1433 (h : Var) :
    (nb078AlphaDummy922 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy892 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy922] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy892 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1434 :
    (nb078AlphaDummy957) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy926))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy957] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy926))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1435 (h : Var) :
    (nb078AlphaDummy958 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy928 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy958] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy928 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1436 :
    (nb078AlphaDummy997) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy966))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy997] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy966))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1437 (h : Var) :
    (nb078AlphaDummy998 h) ∉
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy968 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb078AlphaDummy998] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy968 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb078_fresh_1438 :
    (nb078AlphaDummy037) ∉
      (((synCnin (Class.cv (nb078AlphaDummy032)) (Class.cv (nb078AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy032))
            (Class.cv (nb078AlphaDummy033)))).fv) :=
  by
  simpa only [nb078AlphaDummy037] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy032)) (Class.cv (nb078AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy032)) (Class.cv (nb078AlphaDummy033)))).fv)
      0

theorem nb078_fresh_1439 (f : Var) :
    (nb078AlphaDummy038 f) ∉
      (((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy038] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv)
      0

theorem nb078_fresh_1440 :
    (nb078AlphaDummy073) ∉
      (((synCnin (Class.cv (nb078AlphaDummy068)) (Class.cv (nb078AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy068))
            (Class.cv (nb078AlphaDummy069)))).fv) :=
  by
  simpa only [nb078AlphaDummy073] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy068)) (Class.cv (nb078AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy068)) (Class.cv (nb078AlphaDummy069)))).fv)
      0

theorem nb078_fresh_1441 (f : Var) :
    (nb078AlphaDummy074 f) ∉
      (((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy074] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy071 f))
            (Class.cv (nb078AlphaDummy072 f)))).fv)
      0

theorem nb078_fresh_1442 :
    (nb078AlphaDummy1029) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1024)) (Class.cv (nb078AlphaDummy1025)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1024))
            (Class.cv (nb078AlphaDummy1025)))).fv) :=
  by
  simpa only [nb078AlphaDummy1029] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1024)) (Class.cv (nb078AlphaDummy1025)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1024)) (Class.cv (nb078AlphaDummy1025)))).fv)
      0

theorem nb078_fresh_1443 (h : Var) :
    (nb078AlphaDummy1030 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1030] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv)
      0

theorem nb078_fresh_1444 :
    (nb078AlphaDummy1077) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1072)) (Class.cv (nb078AlphaDummy1073)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1072))
            (Class.cv (nb078AlphaDummy1073)))).fv) :=
  by
  simpa only [nb078AlphaDummy1077] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1072)) (Class.cv (nb078AlphaDummy1073)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1072)) (Class.cv (nb078AlphaDummy1073)))).fv)
      0

theorem nb078_fresh_1445 (h : Var) :
    (nb078AlphaDummy1078 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1078] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv)
      0

theorem nb078_fresh_1446 :
    (nb078AlphaDummy115) ∉
      (((synCnin (Class.cv (nb078AlphaDummy110)) (Class.cv (nb078AlphaDummy111)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy110))
            (Class.cv (nb078AlphaDummy111)))).fv) :=
  by
  simpa only [nb078AlphaDummy115] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy110)) (Class.cv (nb078AlphaDummy111)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy110)) (Class.cv (nb078AlphaDummy111)))).fv)
      0

theorem nb078_fresh_1447 :
    (nb078AlphaDummy1113) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1108)) (Class.cv (nb078AlphaDummy1109)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1108))
            (Class.cv (nb078AlphaDummy1109)))).fv) :=
  by
  simpa only [nb078AlphaDummy1113] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1108)) (Class.cv (nb078AlphaDummy1109)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1108)) (Class.cv (nb078AlphaDummy1109)))).fv)
      0

theorem nb078_fresh_1448 (h : Var) :
    (nb078AlphaDummy1114 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1114] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv)
      0

theorem nb078_fresh_1449 (f : Var) :
    (nb078AlphaDummy116 f) ∉
      (((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy116] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy113 f))
            (Class.cv (nb078AlphaDummy114 f)))).fv)
      0

theorem nb078_fresh_1450 :
    (nb078AlphaDummy1155) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1150)) (Class.cv (nb078AlphaDummy1151)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1150))
            (Class.cv (nb078AlphaDummy1151)))).fv) :=
  by
  simpa only [nb078AlphaDummy1155] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1150)) (Class.cv (nb078AlphaDummy1151)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1150)) (Class.cv (nb078AlphaDummy1151)))).fv)
      0

theorem nb078_fresh_1451 (h : Var) :
    (nb078AlphaDummy1156 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1156] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv)
      0

theorem nb078_fresh_1452 :
    (nb078AlphaDummy1191) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1186)) (Class.cv (nb078AlphaDummy1187)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1186))
            (Class.cv (nb078AlphaDummy1187)))).fv) :=
  by
  simpa only [nb078AlphaDummy1191] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1186)) (Class.cv (nb078AlphaDummy1187)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1186)) (Class.cv (nb078AlphaDummy1187)))).fv)
      0

theorem nb078_fresh_1453 (h : Var) :
    (nb078AlphaDummy1192 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1192] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv)
      0

theorem nb078_fresh_1454 :
    (nb078AlphaDummy1227) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1222)) (Class.cv (nb078AlphaDummy1223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1222))
            (Class.cv (nb078AlphaDummy1223)))).fv) :=
  by
  simpa only [nb078AlphaDummy1227] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1222)) (Class.cv (nb078AlphaDummy1223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1222)) (Class.cv (nb078AlphaDummy1223)))).fv)
      0

theorem nb078_fresh_1455 (h : Var) :
    (nb078AlphaDummy1228 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1228] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv)
      0

theorem nb078_fresh_1456 :
    (nb078AlphaDummy151) ∉
      (((synCnin (Class.cv (nb078AlphaDummy146)) (Class.cv (nb078AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy146))
            (Class.cv (nb078AlphaDummy147)))).fv) :=
  by
  simpa only [nb078AlphaDummy151] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy146)) (Class.cv (nb078AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy146)) (Class.cv (nb078AlphaDummy147)))).fv)
      0

theorem nb078_fresh_1457 (f : Var) :
    (nb078AlphaDummy152 f) ∉
      (((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy152] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy149 f))
            (Class.cv (nb078AlphaDummy150 f)))).fv)
      0

theorem nb078_fresh_1458 :
    (nb078AlphaDummy187) ∉
      (((synCnin (Class.cv (nb078AlphaDummy182)) (Class.cv (nb078AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy182))
            (Class.cv (nb078AlphaDummy183)))).fv) :=
  by
  simpa only [nb078AlphaDummy187] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy182)) (Class.cv (nb078AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy182)) (Class.cv (nb078AlphaDummy183)))).fv)
      0

theorem nb078_fresh_1459 (f : Var) :
    (nb078AlphaDummy188 f) ∉
      (((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy188] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy185 f))
            (Class.cv (nb078AlphaDummy186 f)))).fv)
      0

theorem nb078_fresh_1460 :
    (nb078AlphaDummy227) ∉
      (((synCnin (Class.cv (nb078AlphaDummy222)) (Class.cv (nb078AlphaDummy223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy222))
            (Class.cv (nb078AlphaDummy223)))).fv) :=
  by
  simpa only [nb078AlphaDummy227] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy222)) (Class.cv (nb078AlphaDummy223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy222)) (Class.cv (nb078AlphaDummy223)))).fv)
      0

theorem nb078_fresh_1461 (f : Var) :
    (nb078AlphaDummy228 f) ∉
      (((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy228] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy225 f))
            (Class.cv (nb078AlphaDummy226 f)))).fv)
      0

theorem nb078_fresh_1462 :
    (nb078AlphaDummy267) ∉
      (((synCnin (Class.cv (nb078AlphaDummy262)) (Class.cv (nb078AlphaDummy263)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy262))
            (Class.cv (nb078AlphaDummy263)))).fv) :=
  by
  simpa only [nb078AlphaDummy267] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy262)) (Class.cv (nb078AlphaDummy263)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy262)) (Class.cv (nb078AlphaDummy263)))).fv)
      0

theorem nb078_fresh_1463 (f : Var) :
    (nb078AlphaDummy268 f) ∉
      (((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy268] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy265 f))
            (Class.cv (nb078AlphaDummy266 f)))).fv)
      0

theorem nb078_fresh_1464 :
    (nb078AlphaDummy315) ∉
      (((synCnin (Class.cv (nb078AlphaDummy310)) (Class.cv (nb078AlphaDummy311)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy310))
            (Class.cv (nb078AlphaDummy311)))).fv) :=
  by
  simpa only [nb078AlphaDummy315] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy310)) (Class.cv (nb078AlphaDummy311)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy310)) (Class.cv (nb078AlphaDummy311)))).fv)
      0

theorem nb078_fresh_1465 (g : Var) :
    (nb078AlphaDummy316 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy316] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy313 g))
            (Class.cv (nb078AlphaDummy314 g)))).fv)
      0

theorem nb078_fresh_1466 :
    (nb078AlphaDummy351) ∉
      (((synCnin (Class.cv (nb078AlphaDummy346)) (Class.cv (nb078AlphaDummy347)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy346))
            (Class.cv (nb078AlphaDummy347)))).fv) :=
  by
  simpa only [nb078AlphaDummy351] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy346)) (Class.cv (nb078AlphaDummy347)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy346)) (Class.cv (nb078AlphaDummy347)))).fv)
      0

theorem nb078_fresh_1467 (g : Var) :
    (nb078AlphaDummy352 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy352] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy349 g))
            (Class.cv (nb078AlphaDummy350 g)))).fv)
      0

theorem nb078_fresh_1468 :
    (nb078AlphaDummy393) ∉
      (((synCnin (Class.cv (nb078AlphaDummy388)) (Class.cv (nb078AlphaDummy389)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy388))
            (Class.cv (nb078AlphaDummy389)))).fv) :=
  by
  simpa only [nb078AlphaDummy393] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy388)) (Class.cv (nb078AlphaDummy389)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy388)) (Class.cv (nb078AlphaDummy389)))).fv)
      0

theorem nb078_fresh_1469 (g : Var) :
    (nb078AlphaDummy394 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy394] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy391 g))
            (Class.cv (nb078AlphaDummy392 g)))).fv)
      0

theorem nb078_fresh_1470 :
    (nb078AlphaDummy429) ∉
      (((synCnin (Class.cv (nb078AlphaDummy424)) (Class.cv (nb078AlphaDummy425)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy424))
            (Class.cv (nb078AlphaDummy425)))).fv) :=
  by
  simpa only [nb078AlphaDummy429] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy424)) (Class.cv (nb078AlphaDummy425)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy424)) (Class.cv (nb078AlphaDummy425)))).fv)
      0

theorem nb078_fresh_1471 (g : Var) :
    (nb078AlphaDummy430 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy430] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy427 g))
            (Class.cv (nb078AlphaDummy428 g)))).fv)
      0

theorem nb078_fresh_1472 :
    (nb078AlphaDummy465) ∉
      (((synCnin (Class.cv (nb078AlphaDummy460)) (Class.cv (nb078AlphaDummy461)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy460))
            (Class.cv (nb078AlphaDummy461)))).fv) :=
  by
  simpa only [nb078AlphaDummy465] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy460)) (Class.cv (nb078AlphaDummy461)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy460)) (Class.cv (nb078AlphaDummy461)))).fv)
      0

theorem nb078_fresh_1473 (g : Var) :
    (nb078AlphaDummy466 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy466] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy463 g))
            (Class.cv (nb078AlphaDummy464 g)))).fv)
      0

theorem nb078_fresh_1474 :
    (nb078AlphaDummy505) ∉
      (((synCnin (Class.cv (nb078AlphaDummy500)) (Class.cv (nb078AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy500))
            (Class.cv (nb078AlphaDummy501)))).fv) :=
  by
  simpa only [nb078AlphaDummy505] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy500)) (Class.cv (nb078AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy500)) (Class.cv (nb078AlphaDummy501)))).fv)
      0

theorem nb078_fresh_1475 (g : Var) :
    (nb078AlphaDummy506 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy506] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy503 g))
            (Class.cv (nb078AlphaDummy504 g)))).fv)
      0

theorem nb078_fresh_1476 :
    (nb078AlphaDummy549) ∉
      (((synCnin (Class.cv (nb078AlphaDummy544)) (Class.cv (nb078AlphaDummy545)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy544))
            (Class.cv (nb078AlphaDummy545)))).fv) :=
  by
  simpa only [nb078AlphaDummy549] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy544)) (Class.cv (nb078AlphaDummy545)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy544)) (Class.cv (nb078AlphaDummy545)))).fv)
      0

theorem nb078_fresh_1477 (g : Var) :
    (nb078AlphaDummy550 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy550] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy547 g))
            (Class.cv (nb078AlphaDummy548 g)))).fv)
      0

theorem nb078_fresh_1478 :
    (nb078AlphaDummy597) ∉
      (((synCnin (Class.cv (nb078AlphaDummy592)) (Class.cv (nb078AlphaDummy593)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy592))
            (Class.cv (nb078AlphaDummy593)))).fv) :=
  by
  simpa only [nb078AlphaDummy597] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy592)) (Class.cv (nb078AlphaDummy593)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy592)) (Class.cv (nb078AlphaDummy593)))).fv)
      0

theorem nb078_fresh_1479 (g : Var) :
    (nb078AlphaDummy598 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy598] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy595 g))
            (Class.cv (nb078AlphaDummy596 g)))).fv)
      0

theorem nb078_fresh_1480 :
    (nb078AlphaDummy633) ∉
      (((synCnin (Class.cv (nb078AlphaDummy628)) (Class.cv (nb078AlphaDummy629)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy628))
            (Class.cv (nb078AlphaDummy629)))).fv) :=
  by
  simpa only [nb078AlphaDummy633] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy628)) (Class.cv (nb078AlphaDummy629)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy628)) (Class.cv (nb078AlphaDummy629)))).fv)
      0

theorem nb078_fresh_1481 (g : Var) :
    (nb078AlphaDummy634 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy634] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy631 g))
            (Class.cv (nb078AlphaDummy632 g)))).fv)
      0

theorem nb078_fresh_1482 :
    (nb078AlphaDummy675) ∉
      (((synCnin (Class.cv (nb078AlphaDummy670)) (Class.cv (nb078AlphaDummy671)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy670))
            (Class.cv (nb078AlphaDummy671)))).fv) :=
  by
  simpa only [nb078AlphaDummy675] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy670)) (Class.cv (nb078AlphaDummy671)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy670)) (Class.cv (nb078AlphaDummy671)))).fv)
      0

theorem nb078_fresh_1483 (g : Var) :
    (nb078AlphaDummy676 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy676] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy673 g))
            (Class.cv (nb078AlphaDummy674 g)))).fv)
      0

theorem nb078_fresh_1484 :
    (nb078AlphaDummy711) ∉
      (((synCnin (Class.cv (nb078AlphaDummy706)) (Class.cv (nb078AlphaDummy707)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy706))
            (Class.cv (nb078AlphaDummy707)))).fv) :=
  by
  simpa only [nb078AlphaDummy711] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy706)) (Class.cv (nb078AlphaDummy707)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy706)) (Class.cv (nb078AlphaDummy707)))).fv)
      0

theorem nb078_fresh_1485 (g : Var) :
    (nb078AlphaDummy712 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy712] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy709 g))
            (Class.cv (nb078AlphaDummy710 g)))).fv)
      0

theorem nb078_fresh_1486 :
    (nb078AlphaDummy747) ∉
      (((synCnin (Class.cv (nb078AlphaDummy742)) (Class.cv (nb078AlphaDummy743)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy742))
            (Class.cv (nb078AlphaDummy743)))).fv) :=
  by
  simpa only [nb078AlphaDummy747] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy742)) (Class.cv (nb078AlphaDummy743)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy742)) (Class.cv (nb078AlphaDummy743)))).fv)
      0

theorem nb078_fresh_1487 (g : Var) :
    (nb078AlphaDummy748 g) ∉
      (((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy748] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy745 g))
            (Class.cv (nb078AlphaDummy746 g)))).fv)
      0

theorem nb078_fresh_1488 :
    (nb078AlphaDummy795) ∉
      (((synCnin (Class.cv (nb078AlphaDummy790)) (Class.cv (nb078AlphaDummy791)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy790))
            (Class.cv (nb078AlphaDummy791)))).fv) :=
  by
  simpa only [nb078AlphaDummy795] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy790)) (Class.cv (nb078AlphaDummy791)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy790)) (Class.cv (nb078AlphaDummy791)))).fv)
      0

theorem nb078_fresh_1489 (h : Var) :
    (nb078AlphaDummy796 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy796] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy793 h))
            (Class.cv (nb078AlphaDummy794 h)))).fv)
      0

theorem nb078_fresh_1490 :
    (nb078AlphaDummy831) ∉
      (((synCnin (Class.cv (nb078AlphaDummy826)) (Class.cv (nb078AlphaDummy827)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy826))
            (Class.cv (nb078AlphaDummy827)))).fv) :=
  by
  simpa only [nb078AlphaDummy831] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy826)) (Class.cv (nb078AlphaDummy827)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy826)) (Class.cv (nb078AlphaDummy827)))).fv)
      0

theorem nb078_fresh_1491 (h : Var) :
    (nb078AlphaDummy832 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy832] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy829 h))
            (Class.cv (nb078AlphaDummy830 h)))).fv)
      0

theorem nb078_fresh_1492 :
    (nb078AlphaDummy873) ∉
      (((synCnin (Class.cv (nb078AlphaDummy868)) (Class.cv (nb078AlphaDummy869)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy868))
            (Class.cv (nb078AlphaDummy869)))).fv) :=
  by
  simpa only [nb078AlphaDummy873] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy868)) (Class.cv (nb078AlphaDummy869)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy868)) (Class.cv (nb078AlphaDummy869)))).fv)
      0

theorem nb078_fresh_1493 (h : Var) :
    (nb078AlphaDummy874 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy874] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv)
      0

theorem nb078_fresh_1494 :
    (nb078AlphaDummy909) ∉
      (((synCnin (Class.cv (nb078AlphaDummy904)) (Class.cv (nb078AlphaDummy905)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy904))
            (Class.cv (nb078AlphaDummy905)))).fv) :=
  by
  simpa only [nb078AlphaDummy909] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy904)) (Class.cv (nb078AlphaDummy905)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy904)) (Class.cv (nb078AlphaDummy905)))).fv)
      0

theorem nb078_fresh_1495 (h : Var) :
    (nb078AlphaDummy910 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy910] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv)
      0

theorem nb078_fresh_1496 :
    (nb078AlphaDummy945) ∉
      (((synCnin (Class.cv (nb078AlphaDummy940)) (Class.cv (nb078AlphaDummy941)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy940))
            (Class.cv (nb078AlphaDummy941)))).fv) :=
  by
  simpa only [nb078AlphaDummy945] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy940)) (Class.cv (nb078AlphaDummy941)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy940)) (Class.cv (nb078AlphaDummy941)))).fv)
      0

theorem nb078_fresh_1497 (h : Var) :
    (nb078AlphaDummy946 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy946] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv)
      0

theorem nb078_fresh_1498 :
    (nb078AlphaDummy985) ∉
      (((synCnin (Class.cv (nb078AlphaDummy980)) (Class.cv (nb078AlphaDummy981)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy980))
            (Class.cv (nb078AlphaDummy981)))).fv) :=
  by
  simpa only [nb078AlphaDummy985] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy980)) (Class.cv (nb078AlphaDummy981)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy980)) (Class.cv (nb078AlphaDummy981)))).fv)
      0

theorem nb078_fresh_1499 (h : Var) :
    (nb078AlphaDummy986 h) ∉
      (((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy986] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv)
      0

theorem nb078_fresh_1500 :
    (nb078AlphaDummy005) ∉
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy000))
              (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy000))
              (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy005] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy000))
              (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy000))
              (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv)
      0

theorem nb078_fresh_1501 :
    (nb078AlphaDummy283) ∉
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy001))
              (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy001))
              (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy283] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy001))
              (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy001))
              (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv)
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
    (nb078AlphaDummy763) ∉
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy002))
              (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy002))
              (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy763] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy002))
              (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy002))
              (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv)
      0

theorem nb078_fresh_1503 (f : Var) :
    (nb078AlphaDummy006 f) ∉
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy006] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv)
      0

theorem nb078_fresh_1504 (g : Var) :
    (nb078AlphaDummy284 g) ∉
      (((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy284] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv)
      0

theorem nb078_fresh_1505 (h : Var) :
    (nb078AlphaDummy764 h) ∉
      (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy764] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv)
      0

theorem nb078_fresh_1506 :
    (nb078AlphaDummy565) ∉
      (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy565] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv)
      0

theorem nb078_fresh_1507 :
    (nb078AlphaDummy1045) ∉
      (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy1045] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv)
      0

theorem nb078_fresh_1508 (g : Var) :
    (nb078AlphaDummy566 g) ∉
      (((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
            (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy566] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
            (synCid))).fv)
      0

theorem nb078_fresh_1509 (h : Var) :
    (nb078AlphaDummy1046 h) ∉
      (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv) :=
  by
  simpa only [nb078AlphaDummy1046] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv)
      0

theorem nb078_fresh_1510 :
    (nb078AlphaDummy521) ∉
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv) :=
  by
  simpa only [nb078AlphaDummy521] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy003)))).fv)
      0

theorem nb078_fresh_1511 :
    (nb078AlphaDummy1001) ∉
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv) :=
  by
  simpa only [nb078AlphaDummy1001] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv)
      0

theorem nb078_fresh_1512 (x : Var) (g : Var) :
    (nb078AlphaDummy522 x g) ∉
      (((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv) :=
  by
  simpa only [nb078AlphaDummy522] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv)
      0

theorem nb078_fresh_1513 (y : Var) (h : Var) :
    (nb078AlphaDummy1002 y h) ∉
      (((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv) :=
  by
  simpa only [nb078AlphaDummy1002] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv)
      0

theorem nb078_fresh_1514 :
    (nb078AlphaDummy051) ∉
      (((synCphi (Class.cv (nb078AlphaDummy018)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy018)))).fv) :=
  by
  simpa only [nb078AlphaDummy051] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy018)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy018)))).fv)
      0

theorem nb078_fresh_1515 (f : Var) :
    (nb078AlphaDummy052 f) ∉
      (((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy052] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv)
      0

theorem nb078_fresh_1516 :
    (nb078AlphaDummy087) ∉
      (((synCphi (Class.cv (nb078AlphaDummy054)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy054)))).fv) :=
  by
  simpa only [nb078AlphaDummy087] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy054)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy054)))).fv)
      0

theorem nb078_fresh_1517 (f : Var) :
    (nb078AlphaDummy088 f) ∉
      (((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy088] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv)
      0

theorem nb078_fresh_1518 :
    (nb078AlphaDummy129) ∉
      (((synCphi (Class.cv (nb078AlphaDummy096)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy096)))).fv) :=
  by
  simpa only [nb078AlphaDummy129] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy096)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy096)))).fv)
      0

theorem nb078_fresh_1519 (f : Var) :
    (nb078AlphaDummy130 f) ∉
      (((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy130] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv)
      0

theorem nb078_fresh_1520 :
    (nb078AlphaDummy1043) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1010)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1010)))).fv) :=
  by
  simpa only [nb078AlphaDummy1043] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1010)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1010)))).fv)
      0

theorem nb078_fresh_1521 (h : Var) :
    (nb078AlphaDummy1044 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1044] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv)
      0

theorem nb078_fresh_1522 :
    (nb078AlphaDummy1091) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1058)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1058)))).fv) :=
  by
  simpa only [nb078AlphaDummy1091] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1058)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1058)))).fv)
      0

theorem nb078_fresh_1523 (h : Var) :
    (nb078AlphaDummy1092 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1092] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv)
      0

theorem nb078_fresh_1524 :
    (nb078AlphaDummy1127) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1094)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1094)))).fv) :=
  by
  simpa only [nb078AlphaDummy1127] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1094)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1094)))).fv)
      0

theorem nb078_fresh_1525 (h : Var) :
    (nb078AlphaDummy1128 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1128] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv)
      0

theorem nb078_fresh_1526 :
    (nb078AlphaDummy1169) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1136)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1136)))).fv) :=
  by
  simpa only [nb078AlphaDummy1169] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1136)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1136)))).fv)
      0

theorem nb078_fresh_1527 (h : Var) :
    (nb078AlphaDummy1170 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1170] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv)
      0

theorem nb078_fresh_1528 :
    (nb078AlphaDummy1205) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1172)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1172)))).fv) :=
  by
  simpa only [nb078AlphaDummy1205] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1172)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1172)))).fv)
      0

theorem nb078_fresh_1529 (h : Var) :
    (nb078AlphaDummy1206 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1206] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv)
      0

theorem nb078_fresh_1530 :
    (nb078AlphaDummy1241) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1208)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1208)))).fv) :=
  by
  simpa only [nb078AlphaDummy1241] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1208)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1208)))).fv)
      0

theorem nb078_fresh_1531 (h : Var) :
    (nb078AlphaDummy1242 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1242] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv)
      0

theorem nb078_fresh_1532 :
    (nb078AlphaDummy165) ∉
      (((synCphi (Class.cv (nb078AlphaDummy132)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy132)))).fv) :=
  by
  simpa only [nb078AlphaDummy165] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy132)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy132)))).fv)
      0

theorem nb078_fresh_1533 (f : Var) :
    (nb078AlphaDummy166 f) ∉
      (((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy166] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv)
      0

theorem nb078_fresh_1534 :
    (nb078AlphaDummy201) ∉
      (((synCphi (Class.cv (nb078AlphaDummy168)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy168)))).fv) :=
  by
  simpa only [nb078AlphaDummy201] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy168)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy168)))).fv)
      0

theorem nb078_fresh_1535 (f : Var) :
    (nb078AlphaDummy202 f) ∉
      (((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy202] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv)
      0

theorem nb078_fresh_1536 :
    (nb078AlphaDummy241) ∉
      (((synCphi (Class.cv (nb078AlphaDummy208)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy208)))).fv) :=
  by
  simpa only [nb078AlphaDummy241] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy208)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy208)))).fv)
      0

theorem nb078_fresh_1537 (f : Var) :
    (nb078AlphaDummy242 f) ∉
      (((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy242] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv)
      0

theorem nb078_fresh_1538 :
    (nb078AlphaDummy281) ∉
      (((synCphi (Class.cv (nb078AlphaDummy248)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy248)))).fv) :=
  by
  simpa only [nb078AlphaDummy281] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy248)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy248)))).fv)
      0

theorem nb078_fresh_1539 (f : Var) :
    (nb078AlphaDummy282 f) ∉
      (((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy282] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv)
      0

theorem nb078_fresh_1540 :
    (nb078AlphaDummy329) ∉
      (((synCphi (Class.cv (nb078AlphaDummy296)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy296)))).fv) :=
  by
  simpa only [nb078AlphaDummy329] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy296)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy296)))).fv)
      0

theorem nb078_fresh_1541 (g : Var) :
    (nb078AlphaDummy330 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy330] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv)
      0

theorem nb078_fresh_1542 :
    (nb078AlphaDummy365) ∉
      (((synCphi (Class.cv (nb078AlphaDummy332)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy332)))).fv) :=
  by
  simpa only [nb078AlphaDummy365] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy332)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy332)))).fv)
      0

theorem nb078_fresh_1543 (g : Var) :
    (nb078AlphaDummy366 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy366] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv)
      0

theorem nb078_fresh_1544 :
    (nb078AlphaDummy407) ∉
      (((synCphi (Class.cv (nb078AlphaDummy374)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy374)))).fv) :=
  by
  simpa only [nb078AlphaDummy407] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy374)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy374)))).fv)
      0

theorem nb078_fresh_1545 (g : Var) :
    (nb078AlphaDummy408 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy408] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv)
      0

theorem nb078_fresh_1546 :
    (nb078AlphaDummy443) ∉
      (((synCphi (Class.cv (nb078AlphaDummy410)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy410)))).fv) :=
  by
  simpa only [nb078AlphaDummy443] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy410)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy410)))).fv)
      0

theorem nb078_fresh_1547 (g : Var) :
    (nb078AlphaDummy444 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy444] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv)
      0

theorem nb078_fresh_1548 :
    (nb078AlphaDummy479) ∉
      (((synCphi (Class.cv (nb078AlphaDummy446)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy446)))).fv) :=
  by
  simpa only [nb078AlphaDummy479] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy446)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy446)))).fv)
      0

theorem nb078_fresh_1549 (g : Var) :
    (nb078AlphaDummy480 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy480] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv)
      0

theorem nb078_fresh_1550 :
    (nb078AlphaDummy519) ∉
      (((synCphi (Class.cv (nb078AlphaDummy486)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy486)))).fv) :=
  by
  simpa only [nb078AlphaDummy519] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy486)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy486)))).fv)
      0

theorem nb078_fresh_1551 (g : Var) :
    (nb078AlphaDummy520 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy520] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv)
      0

theorem nb078_fresh_1552 :
    (nb078AlphaDummy563) ∉
      (((synCphi (Class.cv (nb078AlphaDummy530)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy530)))).fv) :=
  by
  simpa only [nb078AlphaDummy563] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy530)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy530)))).fv)
      0

theorem nb078_fresh_1553 (g : Var) :
    (nb078AlphaDummy564 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy564] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv)
      0

theorem nb078_fresh_1554 :
    (nb078AlphaDummy611) ∉
      (((synCphi (Class.cv (nb078AlphaDummy578)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy578)))).fv) :=
  by
  simpa only [nb078AlphaDummy611] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy578)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy578)))).fv)
      0

theorem nb078_fresh_1555 (g : Var) :
    (nb078AlphaDummy612 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy612] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv)
      0

theorem nb078_fresh_1556 :
    (nb078AlphaDummy647) ∉
      (((synCphi (Class.cv (nb078AlphaDummy614)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy614)))).fv) :=
  by
  simpa only [nb078AlphaDummy647] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy614)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy614)))).fv)
      0

theorem nb078_fresh_1557 (g : Var) :
    (nb078AlphaDummy648 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy648] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv)
      0

theorem nb078_fresh_1558 :
    (nb078AlphaDummy689) ∉
      (((synCphi (Class.cv (nb078AlphaDummy656)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy656)))).fv) :=
  by
  simpa only [nb078AlphaDummy689] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy656)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy656)))).fv)
      0

theorem nb078_fresh_1559 (g : Var) :
    (nb078AlphaDummy690 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy690] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv)
      0

theorem nb078_fresh_1560 :
    (nb078AlphaDummy725) ∉
      (((synCphi (Class.cv (nb078AlphaDummy692)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy692)))).fv) :=
  by
  simpa only [nb078AlphaDummy725] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy692)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy692)))).fv)
      0

theorem nb078_fresh_1561 (g : Var) :
    (nb078AlphaDummy726 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy726] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv)
      0

theorem nb078_fresh_1562 :
    (nb078AlphaDummy761) ∉
      (((synCphi (Class.cv (nb078AlphaDummy728)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy728)))).fv) :=
  by
  simpa only [nb078AlphaDummy761] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy728)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy728)))).fv)
      0

theorem nb078_fresh_1563 (g : Var) :
    (nb078AlphaDummy762 g) ∉
      (((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy762] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv)
      0

theorem nb078_fresh_1564 :
    (nb078AlphaDummy809) ∉
      (((synCphi (Class.cv (nb078AlphaDummy776)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy776)))).fv) :=
  by
  simpa only [nb078AlphaDummy809] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy776)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy776)))).fv)
      0

theorem nb078_fresh_1565 (h : Var) :
    (nb078AlphaDummy810 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy810] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv)
      0

theorem nb078_fresh_1566 :
    (nb078AlphaDummy845) ∉
      (((synCphi (Class.cv (nb078AlphaDummy812)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy812)))).fv) :=
  by
  simpa only [nb078AlphaDummy845] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy812)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy812)))).fv)
      0

theorem nb078_fresh_1567 (h : Var) :
    (nb078AlphaDummy846 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy846] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv)
      0

theorem nb078_fresh_1568 :
    (nb078AlphaDummy887) ∉
      (((synCphi (Class.cv (nb078AlphaDummy854)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy854)))).fv) :=
  by
  simpa only [nb078AlphaDummy887] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy854)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy854)))).fv)
      0

theorem nb078_fresh_1569 (h : Var) :
    (nb078AlphaDummy888 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy888] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv)
      0

theorem nb078_fresh_1570 :
    (nb078AlphaDummy923) ∉
      (((synCphi (Class.cv (nb078AlphaDummy890)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy890)))).fv) :=
  by
  simpa only [nb078AlphaDummy923] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy890)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy890)))).fv)
      0

theorem nb078_fresh_1571 (h : Var) :
    (nb078AlphaDummy924 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy924] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv)
      0

theorem nb078_fresh_1572 :
    (nb078AlphaDummy959) ∉
      (((synCphi (Class.cv (nb078AlphaDummy926)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy926)))).fv) :=
  by
  simpa only [nb078AlphaDummy959] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy926)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy926)))).fv)
      0

theorem nb078_fresh_1573 (h : Var) :
    (nb078AlphaDummy960 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy960] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv)
      0

theorem nb078_fresh_1574 :
    (nb078AlphaDummy999) ∉
      (((synCphi (Class.cv (nb078AlphaDummy966)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy966)))).fv) :=
  by
  simpa only [nb078AlphaDummy999] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy966)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy966)))).fv)
      0

theorem nb078_fresh_1575 (h : Var) :
    (nb078AlphaDummy1000 h) ∉
      (((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1000] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv)
      0

theorem nb078_fresh_1576 :
    (nb078AlphaDummy523) ∉
      (((synCrn (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((Class.cv (nb078AlphaDummy003))).fv) :=
  by
  simpa only [nb078AlphaDummy523] using
    freshVar_not_mem
      (((synCrn (Class.cv (nb078AlphaDummy001)))).fv ∪
        ((Class.cv (nb078AlphaDummy003))).fv)
      0

theorem nb078_fresh_1577 :
    (nb078AlphaDummy1003) ∉
      (((synCrn (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((Class.cv (nb078AlphaDummy004))).fv) :=
  by
  simpa only [nb078AlphaDummy1003] using
    freshVar_not_mem
      (((synCrn (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((Class.cv (nb078AlphaDummy004))).fv)
      0

theorem nb078_fresh_1578 (x : Var) (g : Var) :
    (nb078AlphaDummy524 x g) ∉ (((synCrn (Class.cv g))).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb078AlphaDummy524] using
    freshVar_not_mem (((synCrn (Class.cv g))).fv ∪ ((Class.cv x)).fv) 0

theorem nb078_fresh_1579 (y : Var) (h : Var) :
    (nb078AlphaDummy1004 y h) ∉ (((synCrn (Class.cv h))).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb078AlphaDummy1004] using
    freshVar_not_mem (((synCrn (Class.cv h))).fv ∪ ((Class.cv y)).fv) 0

theorem nb078_fresh_1580 :
    (nb078AlphaDummy015) ∉
      (({(nb078AlphaDummy009)} : Finset Var) ∪ ({(nb078AlphaDummy010)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy011) (synWa (synWbr (Class.cv (nb078AlphaDummy009))
                (synCcnv (Class.cv (nb078AlphaDummy000)))
                (Class.cv (nb078AlphaDummy011))) (synWbr (Class.cv (nb078AlphaDummy011))
                (Class.cv (nb078AlphaDummy000)) (Class.cv (nb078AlphaDummy010)))))).fv) :=
  by
  simpa only [nb078AlphaDummy015] using
    freshVar_not_mem
      (({(nb078AlphaDummy009)} : Finset Var) ∪ ({(nb078AlphaDummy010)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy011) (synWa (synWbr (Class.cv (nb078AlphaDummy009))
                (synCcnv (Class.cv (nb078AlphaDummy000)))
                (Class.cv (nb078AlphaDummy011))) (synWbr (Class.cv (nb078AlphaDummy011))
                (Class.cv (nb078AlphaDummy000)) (Class.cv (nb078AlphaDummy010)))))).fv)
      0

theorem nb078_fresh_1581 (f : Var) :
    (nb078AlphaDummy016 f) ∉
      (({(nb078AlphaDummy012 f)} : Finset Var) ∪ ({(nb078AlphaDummy013 f)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy014 f) (synWa
              (synWbr (Class.cv (nb078AlphaDummy012 f)) (synCcnv (Class.cv f))
                (Class.cv (nb078AlphaDummy014 f)))
              (synWbr (Class.cv (nb078AlphaDummy014 f)) (Class.cv f)
                (Class.cv (nb078AlphaDummy013 f)))))).fv) :=
  by
  simpa only [nb078AlphaDummy016] using
    freshVar_not_mem
      (({(nb078AlphaDummy012 f)} : Finset Var) ∪ ({(nb078AlphaDummy013 f)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy014 f) (synWa
              (synWbr (Class.cv (nb078AlphaDummy012 f)) (synCcnv (Class.cv f))
                (Class.cv (nb078AlphaDummy014 f)))
              (synWbr (Class.cv (nb078AlphaDummy014 f)) (Class.cv f)
                (Class.cv (nb078AlphaDummy013 f)))))).fv)
      0

theorem nb078_fresh_1582 :
    (nb078AlphaDummy093) ∉
      (({(nb078AlphaDummy089)} : Finset Var) ∪ ({(nb078AlphaDummy090)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy090)) (Class.cv (nb078AlphaDummy000))
            (Class.cv (nb078AlphaDummy089)))).fv) :=
  by
  simpa only [nb078AlphaDummy093] using
    freshVar_not_mem
      (({(nb078AlphaDummy089)} : Finset Var) ∪ ({(nb078AlphaDummy090)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy090)) (Class.cv (nb078AlphaDummy000))
            (Class.cv (nb078AlphaDummy089)))).fv)
      0

theorem nb078_fresh_1583 (f : Var) :
    (nb078AlphaDummy094 f) ∉
      (({(nb078AlphaDummy091 f)} : Finset Var) ∪ ({(nb078AlphaDummy092 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy092 f)) (Class.cv f)
            (Class.cv (nb078AlphaDummy091 f)))).fv) :=
  by
  simpa only [nb078AlphaDummy094] using
    freshVar_not_mem
      (({(nb078AlphaDummy091 f)} : Finset Var) ∪ ({(nb078AlphaDummy092 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy092 f)) (Class.cv f)
            (Class.cv (nb078AlphaDummy091 f)))).fv)
      0

theorem nb078_fresh_1584 :
    (nb078AlphaDummy1055) ∉
      (({(nb078AlphaDummy1049)} : Finset Var) ∪ ({(nb078AlphaDummy1050)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy1051) (synWa (synWbr (Class.cv (nb078AlphaDummy1049))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))
                (Class.cv (nb078AlphaDummy1051)))
              (synWbr (Class.cv (nb078AlphaDummy1051))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy1050)))))).fv) :=
  by
  simpa only [nb078AlphaDummy1055] using
    freshVar_not_mem
      (({(nb078AlphaDummy1049)} : Finset Var) ∪ ({(nb078AlphaDummy1050)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy1051) (synWa (synWbr (Class.cv (nb078AlphaDummy1049))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))
                (Class.cv (nb078AlphaDummy1051)))
              (synWbr (Class.cv (nb078AlphaDummy1051))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy1050)))))).fv)
      0

theorem nb078_fresh_1585 (h : Var) :
    (nb078AlphaDummy1056 h) ∉
      (({(nb078AlphaDummy1052 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1053 h)} : Finset Var) ∪ ((synWex (nb078AlphaDummy1054 h)
            (synWa (synWbr (Class.cv (nb078AlphaDummy1052 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb078AlphaDummy1054 h)))
              (synWbr (Class.cv (nb078AlphaDummy1054 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy1053 h)))))).fv) :=
  by
  simpa only [nb078AlphaDummy1056] using
    freshVar_not_mem
      (({(nb078AlphaDummy1052 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1053 h)} : Finset Var) ∪ ((synWex (nb078AlphaDummy1054 h)
            (synWa (synWbr (Class.cv (nb078AlphaDummy1052 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb078AlphaDummy1054 h)))
              (synWbr (Class.cv (nb078AlphaDummy1054 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy1053 h)))))).fv)
      0

theorem nb078_fresh_1586 :
    (nb078AlphaDummy1133) ∉
      (({(nb078AlphaDummy1129)} : Finset Var) ∪ ({(nb078AlphaDummy1130)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1130))
            (synCcnv (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy1129)))).fv) :=
  by
  simpa only [nb078AlphaDummy1133] using
    freshVar_not_mem
      (({(nb078AlphaDummy1129)} : Finset Var) ∪ ({(nb078AlphaDummy1130)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1130))
            (synCcnv (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy1129)))).fv)
      0

theorem nb078_fresh_1587 (h : Var) :
    (nb078AlphaDummy1134 h) ∉
      (({(nb078AlphaDummy1131 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1132 h)) (synCcnv (Class.cv h))
            (Class.cv (nb078AlphaDummy1131 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy1134] using
    freshVar_not_mem
      (({(nb078AlphaDummy1131 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1132 h)) (synCcnv (Class.cv h))
            (Class.cv (nb078AlphaDummy1131 h)))).fv)
      0

theorem nb078_fresh_1588 :
    (nb078AlphaDummy293) ∉
      (({(nb078AlphaDummy287)} : Finset Var) ∪ ({(nb078AlphaDummy288)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy289) (synWa (synWbr (Class.cv (nb078AlphaDummy287))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy289))) (synWbr (Class.cv (nb078AlphaDummy289))
                (Class.cv (nb078AlphaDummy001)) (Class.cv (nb078AlphaDummy288)))))).fv) :=
  by
  simpa only [nb078AlphaDummy293] using
    freshVar_not_mem
      (({(nb078AlphaDummy287)} : Finset Var) ∪ ({(nb078AlphaDummy288)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy289) (synWa (synWbr (Class.cv (nb078AlphaDummy287))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy289))) (synWbr (Class.cv (nb078AlphaDummy289))
                (Class.cv (nb078AlphaDummy001)) (Class.cv (nb078AlphaDummy288)))))).fv)
      0

theorem nb078_fresh_1589 (g : Var) :
    (nb078AlphaDummy294 g) ∉
      (({(nb078AlphaDummy290 g)} : Finset Var) ∪ ({(nb078AlphaDummy291 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy292 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy290 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy292 g)))
              (synWbr (Class.cv (nb078AlphaDummy292 g)) (Class.cv g)
                (Class.cv (nb078AlphaDummy291 g)))))).fv) :=
  by
  simpa only [nb078AlphaDummy294] using
    freshVar_not_mem
      (({(nb078AlphaDummy290 g)} : Finset Var) ∪ ({(nb078AlphaDummy291 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy292 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy290 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy292 g)))
              (synWbr (Class.cv (nb078AlphaDummy292 g)) (Class.cv g)
                (Class.cv (nb078AlphaDummy291 g)))))).fv)
      0

theorem nb078_fresh_1590 :
    (nb078AlphaDummy371) ∉
      (({(nb078AlphaDummy367)} : Finset Var) ∪ ({(nb078AlphaDummy368)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy368)) (Class.cv (nb078AlphaDummy001))
            (Class.cv (nb078AlphaDummy367)))).fv) :=
  by
  simpa only [nb078AlphaDummy371] using
    freshVar_not_mem
      (({(nb078AlphaDummy367)} : Finset Var) ∪ ({(nb078AlphaDummy368)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy368)) (Class.cv (nb078AlphaDummy001))
            (Class.cv (nb078AlphaDummy367)))).fv)
      0

theorem nb078_fresh_1591 (g : Var) :
    (nb078AlphaDummy372 g) ∉
      (({(nb078AlphaDummy369 g)} : Finset Var) ∪ ({(nb078AlphaDummy370 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy370 g)) (Class.cv g)
            (Class.cv (nb078AlphaDummy369 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy372] using
    freshVar_not_mem
      (({(nb078AlphaDummy369 g)} : Finset Var) ∪ ({(nb078AlphaDummy370 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy370 g)) (Class.cv g)
            (Class.cv (nb078AlphaDummy369 g)))).fv)
      0

theorem nb078_fresh_1592 :
    (nb078AlphaDummy575) ∉
      (({(nb078AlphaDummy569)} : Finset Var) ∪ ({(nb078AlphaDummy570)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy571) (synWa (synWbr (Class.cv (nb078AlphaDummy569))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))
                (Class.cv (nb078AlphaDummy571))) (synWbr (Class.cv (nb078AlphaDummy571))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy570)))))).fv) :=
  by
  simpa only [nb078AlphaDummy575] using
    freshVar_not_mem
      (({(nb078AlphaDummy569)} : Finset Var) ∪ ({(nb078AlphaDummy570)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy571) (synWa (synWbr (Class.cv (nb078AlphaDummy569))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))
                (Class.cv (nb078AlphaDummy571))) (synWbr (Class.cv (nb078AlphaDummy571))
                (synCcnv (Class.cv (nb078AlphaDummy001)))
                (Class.cv (nb078AlphaDummy570)))))).fv)
      0

theorem nb078_fresh_1593 (g : Var) :
    (nb078AlphaDummy576 g) ∉
      (({(nb078AlphaDummy572 g)} : Finset Var) ∪ ({(nb078AlphaDummy573 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy574 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy572 g))
                (synCcnv (synCcnv (Class.cv g))) (Class.cv (nb078AlphaDummy574 g)))
              (synWbr (Class.cv (nb078AlphaDummy574 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy573 g)))))).fv) :=
  by
  simpa only [nb078AlphaDummy576] using
    freshVar_not_mem
      (({(nb078AlphaDummy572 g)} : Finset Var) ∪ ({(nb078AlphaDummy573 g)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy574 g) (synWa
              (synWbr (Class.cv (nb078AlphaDummy572 g))
                (synCcnv (synCcnv (Class.cv g))) (Class.cv (nb078AlphaDummy574 g)))
              (synWbr (Class.cv (nb078AlphaDummy574 g)) (synCcnv (Class.cv g))
                (Class.cv (nb078AlphaDummy573 g)))))).fv)
      0

theorem nb078_fresh_1594 :
    (nb078AlphaDummy653) ∉
      (({(nb078AlphaDummy649)} : Finset Var) ∪ ({(nb078AlphaDummy650)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy650))
            (synCcnv (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy649)))).fv) :=
  by
  simpa only [nb078AlphaDummy653] using
    freshVar_not_mem
      (({(nb078AlphaDummy649)} : Finset Var) ∪ ({(nb078AlphaDummy650)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy650))
            (synCcnv (Class.cv (nb078AlphaDummy001)))
            (Class.cv (nb078AlphaDummy649)))).fv)
      0

theorem nb078_fresh_1595 (g : Var) :
    (nb078AlphaDummy654 g) ∉
      (({(nb078AlphaDummy651 g)} : Finset Var) ∪ ({(nb078AlphaDummy652 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy652 g)) (synCcnv (Class.cv g))
            (Class.cv (nb078AlphaDummy651 g)))).fv) :=
  by
  simpa only [nb078AlphaDummy654] using
    freshVar_not_mem
      (({(nb078AlphaDummy651 g)} : Finset Var) ∪ ({(nb078AlphaDummy652 g)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy652 g)) (synCcnv (Class.cv g))
            (Class.cv (nb078AlphaDummy651 g)))).fv)
      0

theorem nb078_fresh_1596 :
    (nb078AlphaDummy773) ∉
      (({(nb078AlphaDummy767)} : Finset Var) ∪ ({(nb078AlphaDummy768)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy769) (synWa (synWbr (Class.cv (nb078AlphaDummy767))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy769))) (synWbr (Class.cv (nb078AlphaDummy769))
                (Class.cv (nb078AlphaDummy002)) (Class.cv (nb078AlphaDummy768)))))).fv) :=
  by
  simpa only [nb078AlphaDummy773] using
    freshVar_not_mem
      (({(nb078AlphaDummy767)} : Finset Var) ∪ ({(nb078AlphaDummy768)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy769) (synWa (synWbr (Class.cv (nb078AlphaDummy767))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy769))) (synWbr (Class.cv (nb078AlphaDummy769))
                (Class.cv (nb078AlphaDummy002)) (Class.cv (nb078AlphaDummy768)))))).fv)
      0

theorem nb078_fresh_1597 (h : Var) :
    (nb078AlphaDummy774 h) ∉
      (({(nb078AlphaDummy770 h)} : Finset Var) ∪ ({(nb078AlphaDummy771 h)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy772 h) (synWa
              (synWbr (Class.cv (nb078AlphaDummy770 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy772 h)))
              (synWbr (Class.cv (nb078AlphaDummy772 h)) (Class.cv h)
                (Class.cv (nb078AlphaDummy771 h)))))).fv) :=
  by
  simpa only [nb078AlphaDummy774] using
    freshVar_not_mem
      (({(nb078AlphaDummy770 h)} : Finset Var) ∪ ({(nb078AlphaDummy771 h)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy772 h) (synWa
              (synWbr (Class.cv (nb078AlphaDummy770 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy772 h)))
              (synWbr (Class.cv (nb078AlphaDummy772 h)) (Class.cv h)
                (Class.cv (nb078AlphaDummy771 h)))))).fv)
      0

theorem nb078_fresh_1598 :
    (nb078AlphaDummy851) ∉
      (({(nb078AlphaDummy847)} : Finset Var) ∪ ({(nb078AlphaDummy848)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy848)) (Class.cv (nb078AlphaDummy002))
            (Class.cv (nb078AlphaDummy847)))).fv) :=
  by
  simpa only [nb078AlphaDummy851] using
    freshVar_not_mem
      (({(nb078AlphaDummy847)} : Finset Var) ∪ ({(nb078AlphaDummy848)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy848)) (Class.cv (nb078AlphaDummy002))
            (Class.cv (nb078AlphaDummy847)))).fv)
      0

theorem nb078_fresh_1599 (h : Var) :
    (nb078AlphaDummy852 h) ∉
      (({(nb078AlphaDummy849 h)} : Finset Var) ∪ ({(nb078AlphaDummy850 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy850 h)) (Class.cv h)
            (Class.cv (nb078AlphaDummy849 h)))).fv) :=
  by
  simpa only [nb078AlphaDummy852] using
    freshVar_not_mem
      (({(nb078AlphaDummy849 h)} : Finset Var) ∪ ({(nb078AlphaDummy850 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy850 h)) (Class.cv h)
            (Class.cv (nb078AlphaDummy849 h)))).fv)
      0

theorem nb078_fresh_1600 : (nb078AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb078_fresh_1601 : (nb078AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb078_fresh_1602 : (nb078AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb078_fresh_1603 : (nb078AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb078_fresh_1604 : (nb078AlphaDummy004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078AlphaDummy004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb078_distinct_1605 : (nb078AlphaDummy000) ≠ (nb078AlphaDummy001) := by
  simpa only [nb078AlphaDummy000, nb078AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1606 : (nb078AlphaDummy000) ≠ (nb078AlphaDummy002) := by
  simpa only [nb078AlphaDummy000, nb078AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1607 : (nb078AlphaDummy000) ≠ (nb078AlphaDummy003) := by
  simpa only [nb078AlphaDummy000, nb078AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb078_distinct_1608 : (nb078AlphaDummy000) ≠ (nb078AlphaDummy004) := by
  simpa only [nb078AlphaDummy000, nb078AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb078_distinct_1609 : (nb078AlphaDummy001) ≠ (nb078AlphaDummy002) := by
  simpa only [nb078AlphaDummy001, nb078AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb078_distinct_1610 : (nb078AlphaDummy001) ≠ (nb078AlphaDummy003) := by
  simpa only [nb078AlphaDummy001, nb078AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb078_distinct_1611 : (nb078AlphaDummy001) ≠ (nb078AlphaDummy004) := by
  simpa only [nb078AlphaDummy001, nb078AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb078_distinct_1612 : (nb078AlphaDummy002) ≠ (nb078AlphaDummy003) := by
  simpa only [nb078AlphaDummy002, nb078AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb078_distinct_1613 : (nb078AlphaDummy002) ≠ (nb078AlphaDummy004) := by
  simpa only [nb078AlphaDummy002, nb078AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb078_distinct_1614 : (nb078AlphaDummy003) ≠ (nb078AlphaDummy004) := by
  simpa only [nb078AlphaDummy003, nb078AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb078_support_mem_0000 :
    (nb078AlphaDummy009) ∈
      (({(nb078AlphaDummy009)} : Finset Var) ∪ ({(nb078AlphaDummy010)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy011) (synWa (synWbr (Class.cv (nb078AlphaDummy009))
                (synCcnv (Class.cv (nb078AlphaDummy000)))
                (Class.cv (nb078AlphaDummy011))) (synWbr (Class.cv (nb078AlphaDummy011))
                (Class.cv (nb078AlphaDummy000)) (Class.cv (nb078AlphaDummy010)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0001 (f : Var) :
    (nb078AlphaDummy012 f) ∈
      (({(nb078AlphaDummy012 f)} : Finset Var) ∪ ({(nb078AlphaDummy013 f)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy014 f) (synWa
              (synWbr (Class.cv (nb078AlphaDummy012 f)) (synCcnv (Class.cv f))
                (Class.cv (nb078AlphaDummy014 f)))
              (synWbr (Class.cv (nb078AlphaDummy014 f)) (Class.cv f)
                (Class.cv (nb078AlphaDummy013 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0002 :
    (nb078AlphaDummy010) ∈
      (({(nb078AlphaDummy009)} : Finset Var) ∪ ({(nb078AlphaDummy010)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy011) (synWa (synWbr (Class.cv (nb078AlphaDummy009))
                (synCcnv (Class.cv (nb078AlphaDummy000)))
                (Class.cv (nb078AlphaDummy011))) (synWbr (Class.cv (nb078AlphaDummy011))
                (Class.cv (nb078AlphaDummy000)) (Class.cv (nb078AlphaDummy010)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0003 (f : Var) :
    (nb078AlphaDummy013 f) ∈
      (({(nb078AlphaDummy012 f)} : Finset Var) ∪ ({(nb078AlphaDummy013 f)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy014 f) (synWa
              (synWbr (Class.cv (nb078AlphaDummy012 f)) (synCcnv (Class.cv f))
                (Class.cv (nb078AlphaDummy014 f)))
              (synWbr (Class.cv (nb078AlphaDummy014 f)) (Class.cv f)
                (Class.cv (nb078AlphaDummy013 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0004 :
    (nb078AlphaDummy009) ∈
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0005 :
    (nb078AlphaDummy009) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCphi (Class.cv (nb078AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy017) from (by
          unfold nb078AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy018) from (by
            unfold nb078AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0006 (f : Var) :
    (nb078AlphaDummy012 f) ∈
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0007 (f : Var) :
    (nb078AlphaDummy012 f) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCphi (Class.cv (nb078AlphaDummy020 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy019 f) from (by
          unfold nb078AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy020 f) from (by
            unfold nb078AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0008 :
    (nb078AlphaDummy009) ∈
      (((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018))))))).fv ∪
        ((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy017) from (by
          unfold nb078AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy018) from (by
            unfold nb078AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0009 (f : Var) :
    (nb078AlphaDummy012 f) ∈
      (((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy019 f) from (by
          unfold nb078AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy020 f) from (by
            unfold nb078AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0010 :
    (nb078AlphaDummy018) ∈ (((Class.cv (nb078AlphaDummy018))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0011 (f : Var) :
    (nb078AlphaDummy020 f) ∈ (((Class.cv (nb078AlphaDummy020 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0012 :
    (nb078AlphaDummy025) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy025)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy025)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy025))).fv) :=
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
    (nb078AlphaDummy027 f) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy027 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy027 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy027 f))).fv) :=
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
    (nb078AlphaDummy025) ∈
      (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0015 (f : Var) :
    (nb078AlphaDummy027 f) ∈
      (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0016 :
    (nb078AlphaDummy032) ∈
      (((synCnin (Class.cv (nb078AlphaDummy032)) (Class.cv (nb078AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy032))
            (Class.cv (nb078AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0017 (f : Var) :
    (nb078AlphaDummy035 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0018 :
    (nb078AlphaDummy032) ∈
      (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0019 (f : Var) :
    (nb078AlphaDummy035 f) ∈
      (((Class.cv (nb078AlphaDummy035 f))).fv ∪ ((Class.cv (nb078AlphaDummy036 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0020 :
    (nb078AlphaDummy033) ∈
      (((synCnin (Class.cv (nb078AlphaDummy032)) (Class.cv (nb078AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy032))
            (Class.cv (nb078AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0021 (f : Var) :
    (nb078AlphaDummy036 f) ∈
      (((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy035 f))
            (Class.cv (nb078AlphaDummy036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0022 :
    (nb078AlphaDummy033) ∈
      (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0023 (f : Var) :
    (nb078AlphaDummy036 f) ∈
      (((Class.cv (nb078AlphaDummy035 f))).fv ∪ ((Class.cv (nb078AlphaDummy036 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0024 :
    (nb078AlphaDummy032) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0025 (f : Var) :
    (nb078AlphaDummy035 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy035 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0026 :
    (nb078AlphaDummy032) ∈
      (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy032))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0027 (f : Var) :
    (nb078AlphaDummy035 f) ∈
      (((Class.cv (nb078AlphaDummy035 f))).fv ∪ ((Class.cv (nb078AlphaDummy035 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0028 :
    (nb078AlphaDummy033) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0029 (f : Var) :
    (nb078AlphaDummy036 f) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy035 f)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy036 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0030 :
    (nb078AlphaDummy033) ∈
      (((Class.cv (nb078AlphaDummy033))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0031 (f : Var) :
    (nb078AlphaDummy036 f) ∈
      (((Class.cv (nb078AlphaDummy036 f))).fv ∪ ((Class.cv (nb078AlphaDummy036 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0032 :
    (nb078AlphaDummy010) ∈
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
