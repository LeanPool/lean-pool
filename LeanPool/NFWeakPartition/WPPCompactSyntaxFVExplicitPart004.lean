/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart003

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart004. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_cfdmem : (synCfdmem).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCfdmem]

theorem fv_syn_cfdprj0 : (synCfdprj0).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCfdprj0]

theorem fv_syn_cfdprj1 : (synCfdprj1).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCfdprj1]

theorem fv_syn_cfddom (A : Class) (B : Class) : (synCfddom A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCfddom]

theorem fv_syn_cfde0 (A : Class) (B : Class) : (synCfde0 A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCfde0, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfddom,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdprj0]

theorem fv_syn_cfde1 (A : Class) (B : Class) : (synCfde1 A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCfde1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfddom,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdprj1]

theorem fv_syn_cfdsep (A : Class) (B : Class) : (synCfdsep A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCfdsep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfde0,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfde1]

theorem fv_syn_cfdlift (R : Class) : (synCfdlift R).fv = R.fv :=
  by
  ext u
  simp [synCfdlift, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel]

theorem fv_syn_cfdnonmin (R : Class) (A : Class) (B : Class) :
    (synCfdnonmin R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdnonmin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdlift,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep]

theorem fv_syn_cfdminsep (R : Class) (A : Class) (B : Class) :
    (synCfdminsep R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdminsep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdnonmin,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep];
  aesop

theorem fv_syn_csep2 (A : Class) (B : Class) : (synCsep2 A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_z : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_z
  ext u
  simp [synCsep2, Wff.fv, Class.fv, Wff.neg]; aesop

theorem fv_syn_ckqrel (A : Class) : (synCkqrel A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCkqrel, Wff.fv, Class.fv]; aesop

theorem fv_syn_cfdminvalp (R : Class) (A : Class) (B : Class) (C : Class) :
    (synCfdminvalp R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdminvalp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep];
  aesop

theorem fv_syn_cfdminq (R : Class) (A : Class) (B : Class) :
    (synCfdminq R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdminq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel]

theorem fv_syn_cfdpivmap2 (R : Class) (A : Class) (B : Class) :
    (synCfdpivmap2 R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  have fresh_p : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_p
  ext u
  simp [synCfdpivmap2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
    Class.fv];
  aesop

theorem fv_syn_cfdpivrange2 (R : Class) (A : Class) (B : Class) :
    (synCfdpivrange2 R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdpivrange2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2]

theorem fv_syn_cfpiv (R : Class) (A : Class) (B : Class) (C : Class) :
    (synCfpiv R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  have fresh_b : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_b
  have fresh_c : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1
  simp only [Finset.mem_union] at fresh_c
  have distinct_b_c :
    freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) (by decide)
  ext u
  simp [synCfpiv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Wff.fv,
    Class.fv];
  aesop

theorem fv_syn_cfdif (R : Class) (A : Class) (B : Class) :
    (synCfdif R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  have fresh_d : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_d
  have fresh_x : freshVar (R.fv ∪ A.fv ∪ B.fv) 1 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (R.fv ∪ A.fv ∪ B.fv) 2 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 2
  simp only [Finset.mem_union] at fresh_y
  have distinct_d_x : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv) 1 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv) (by decide)
  have distinct_d_y : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv) 2 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv) (by decide)
  have distinct_x_y : freshVar (R.fv ∪ A.fv ∪ B.fv) 1 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv) 2 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv) (by decide)
  ext u
  simp [synCfdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Wff.fv,
    Class.fv];
  aesop

theorem fv_syn_cfdrow (R : Class) (A : Class) (B : Class) (C : Class) :
    (synCfdrow R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  have fresh_d : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_d
  ext u
  simp [synCfdrow, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Wff.fv,
    Class.fv];
  aesop

theorem fv_syn_cfdcode (R : Class) (A : Class) (B : Class) (C : Class) :
    (synCfdcode R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  have fresh_q : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_q
  have fresh_x : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1
  simp only [Finset.mem_union] at fresh_x
  have distinct_q_x :
    freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) (by decide)
  ext u
  simp [synCfdcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow, Wff.fv,
    Class.fv];
  aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
