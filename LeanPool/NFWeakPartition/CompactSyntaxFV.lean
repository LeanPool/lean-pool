/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.CompactSourceSyntax

/-! NF weak partition development: CompactSyntaxFV. -/


public section

namespace NFChoice.Compiler.CompactSyntaxFV

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[simp]
theorem fv_syn_wtru : syn_wtru.fv = (∅ : Finset Var) := by rfl

@[simp]
theorem fv_syn_wb (ph : Wff) (ps : Wff) : (syn_wb ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [syn_wb, Wff.fv, Wff.neg]; aesop

@[simp]
theorem fv_syn_wo (ph : Wff) (ps : Wff) : (syn_wo ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [syn_wo, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wa (ph : Wff) (ps : Wff) : (syn_wa ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [syn_wa, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_w3o (ph : Wff) (ps : Wff) (ch : Wff) :
    (syn_w3o ph ps ch).fv = (ch.fv) ∪ (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [syn_w3o]; aesop

@[simp]
theorem fv_syn_w3a (ph : Wff) (ps : Wff) (ch : Wff) :
    (syn_w3a ph ps ch).fv = (ch.fv) ∪ (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [syn_w3a]; aesop

@[simp]
theorem fv_syn_wnan (ph : Wff) (ps : Wff) : (syn_wnan ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [syn_wnan, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wex (x : Var) (ph : Wff) : (syn_wex x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [syn_wex, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wnf (x : Var) (ph : Wff) : (syn_wnf x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [syn_wnf, Wff.fv]

@[simp]
theorem fv_syn_wsb (y : Var) (x : Var) (ph : Wff) :
    (syn_wsb y x ph).fv =
      (ph.fv) ∪ ((ph.fv).erase x) ∪ ((({ y } : Finset Var)).erase x) ∪
          (({ x } : Finset Var)) ∪
        (({ y } : Finset Var)) :=
  by
  ext u
  simp [syn_wsb, Wff.fv]; aesop

@[simp]
theorem fv_syn_weu (x : Var) (ph : Wff) : (syn_weu x ph).fv = (ph.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ ph.fv) 0 ∉ (({ x } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [syn_weu, Wff.fv]; aesop

@[simp]
theorem fv_syn_wmo (x : Var) (ph : Wff) : (syn_wmo x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [syn_wmo, Wff.fv]

@[simp]
theorem fv_syn_wnfc (x : Var) (A : Class) : (syn_wnfc x A).fv = (A.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv) 0 ∉ (({ x } : Finset Var) ∪ A.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [syn_wnfc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wne (A : Class) (B : Class) : (syn_wne A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_wne, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wral (x : Var) (A : Class) (ph : Wff) :
    (syn_wral x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [syn_wral, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wrex (x : Var) (A : Class) (ph : Wff) :
    (syn_wrex x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [syn_wrex, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wreu (x : Var) (A : Class) (ph : Wff) :
    (syn_wreu x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [syn_wreu, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wrmo (x : Var) (A : Class) (ph : Wff) :
    (syn_wrmo x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [syn_wrmo, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_crab (x : Var) (A : Class) (ph : Wff) :
    (syn_crab x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [syn_crab, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cvv : (syn_cvv).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [syn_cvv, Wff.fv, Class.fv]

@[simp]
theorem fv_syn_wsbc (A : Class) (x : Var) (ph : Wff) :
    (syn_wsbc A x ph).fv = (A.fv) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [syn_wsbc, Wff.fv, Class.fv]

@[simp]
theorem fv_syn_csb (A : Class) (x : Var) (B : Class) :
    (syn_csb A x B).fv = (A.fv) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) 0 ∉
      (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [syn_csb, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cnin (A : Class) (B : Class) : (syn_cnin A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [syn_cnin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccompl (A : Class) : (syn_ccompl A).fv = A.fv :=
  by
  ext u
  simp [syn_ccompl]

@[simp]
theorem fv_syn_cin (A : Class) (B : Class) : (syn_cin A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_cin]

@[simp]
theorem fv_syn_cun (A : Class) (B : Class) : (syn_cun A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_cun]

@[simp]
theorem fv_syn_cdif (A : Class) (B : Class) : (syn_cdif A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_cdif]

@[simp]
theorem fv_syn_csymdif (A : Class) (B : Class) : (syn_csymdif A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_csymdif]; aesop

@[simp]
theorem fv_syn_wss (A : Class) (B : Class) : (syn_wss A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_wss, Wff.fv]; aesop

@[simp]
theorem fv_syn_wpss (A : Class) (B : Class) : (syn_wpss A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_wpss]

@[simp]
theorem fv_syn_c0 : (syn_c0).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_c0]

@[simp]
theorem fv_syn_cif (ph : Wff) (A : Class) (B : Class) :
    (syn_cif ph A B).fv = (A.fv) ∪ (B.fv) ∪ (ph.fv) :=
  by
  have fresh_x : freshVar (ph.fv ∪ A.fv ∪ B.fv) 0 ∉ (ph.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (ph.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [syn_cif, Wff.fv, Class.fv, Wff.neg]; aesop

@[simp]
theorem fv_syn_cpw (A : Class) : (syn_cpw A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [syn_cpw, Class.fv]; aesop

@[simp]
theorem fv_syn_csn (A : Class) : (syn_csn A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [syn_csn, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cpr (A : Class) (B : Class) : (syn_cpr A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_cpr]

@[simp]
theorem fv_syn_ctp (A : Class) (B : Class) (C : Class) :
    (syn_ctp A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) :=
  by
  ext u
  simp [syn_ctp]

@[simp]
theorem fv_syn_cuni (A : Class) : (syn_cuni A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_cuni, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cint (A : Class) : (syn_cint A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_cint, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ciun (x : Var) (A : Class) (B : Class) :
    (syn_ciun x A B).fv = ((A.fv).erase x) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0 ∉
      (({ x } : Finset Var) ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [syn_ciun, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_copk (A : Class) (B : Class) : (syn_copk A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_copk]

@[simp]
theorem fv_syn_c1c : (syn_c1c).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_c1c, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cpw1 (A : Class) : (syn_cpw1 A).fv = A.fv :=
  by
  ext u
  simp [syn_cpw1]

@[simp]
theorem fv_syn_cuni1 (A : Class) : (syn_cuni1 A).fv = A.fv :=
  by
  ext u
  simp [syn_cuni1]

@[simp]
theorem fv_syn_cxpk (A : Class) (B : Class) : (syn_cxpk A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ B.fv) 1 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have fresh_z : freshVar (A.fv ∪ B.fv) 2 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 2
  simp only [Finset.mem_union] at fresh_z
  have distinct_x_y : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 1 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  have distinct_x_z : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 2 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  have distinct_y_z : freshVar (A.fv ∪ B.fv) 1 ≠ freshVar (A.fv ∪ B.fv) 2 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_cxpk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccnvk (A : Class) : (syn_ccnvk A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have fresh_z : freshVar (A.fv) 2 ∉ (A.fv) := freshVar_not_mem (A.fv) 2
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_z : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_y_z : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_ccnvk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cins2k (A : Class) : (syn_cins2k A).fv = A.fv :=
  by
  have fresh_t : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_u : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have fresh_v : freshVar (A.fv) 2 ∉ (A.fv) := freshVar_not_mem (A.fv) 2
  have fresh_x : freshVar (A.fv) 3 ∉ (A.fv) := freshVar_not_mem (A.fv) 3
  have fresh_y : freshVar (A.fv) 4 ∉ (A.fv) := freshVar_not_mem (A.fv) 4
  have fresh_z : freshVar (A.fv) 5 ∉ (A.fv) := freshVar_not_mem (A.fv) 5
  have distinct_t_u : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_v : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_x : freshVar (A.fv) 0 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_z : freshVar (A.fv) 0 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_v : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_x : freshVar (A.fv) 1 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_y : freshVar (A.fv) 1 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_z : freshVar (A.fv) 1 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_v_x : freshVar (A.fv) 2 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_v_y : freshVar (A.fv) 2 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_v_z : freshVar (A.fv) 2 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_y : freshVar (A.fv) 3 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_z : freshVar (A.fv) 3 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_y_z : freshVar (A.fv) 4 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_cins2k, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cins3k (A : Class) : (syn_cins3k A).fv = A.fv :=
  by
  have fresh_t : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_u : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have fresh_v : freshVar (A.fv) 2 ∉ (A.fv) := freshVar_not_mem (A.fv) 2
  have fresh_x : freshVar (A.fv) 3 ∉ (A.fv) := freshVar_not_mem (A.fv) 3
  have fresh_y : freshVar (A.fv) 4 ∉ (A.fv) := freshVar_not_mem (A.fv) 4
  have fresh_z : freshVar (A.fv) 5 ∉ (A.fv) := freshVar_not_mem (A.fv) 5
  have distinct_t_u : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_v : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_x : freshVar (A.fv) 0 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_z : freshVar (A.fv) 0 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_v : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_x : freshVar (A.fv) 1 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_y : freshVar (A.fv) 1 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_z : freshVar (A.fv) 1 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_v_x : freshVar (A.fv) 2 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_v_y : freshVar (A.fv) 2 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_v_z : freshVar (A.fv) 2 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_y : freshVar (A.fv) 3 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_z : freshVar (A.fv) 3 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_y_z : freshVar (A.fv) 4 ≠ freshVar (A.fv) 5 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_cins3k, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cimak (A : Class) (B : Class) : (syn_cimak A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ B.fv) 1 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have distinct_x_y : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 1 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_cimak, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccomk (A : Class) (B : Class) : (syn_ccomk A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_ccomk]

@[simp]
theorem fv_syn_cp6 (A : Class) : (syn_cp6 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [syn_cp6, Class.fv]; aesop

@[simp]
theorem fv_syn_csik (A : Class) : (syn_csik A).fv = A.fv :=
  by
  have fresh_t : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_u : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have fresh_x : freshVar (A.fv) 2 ∉ (A.fv) := freshVar_not_mem (A.fv) 2
  have fresh_y : freshVar (A.fv) 3 ∉ (A.fv) := freshVar_not_mem (A.fv) 3
  have fresh_z : freshVar (A.fv) 4 ∉ (A.fv) := freshVar_not_mem (A.fv) 4
  have distinct_t_u : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_x : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_t_z : freshVar (A.fv) 0 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_x : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_y : freshVar (A.fv) 1 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_z : freshVar (A.fv) 1 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_y : freshVar (A.fv) 2 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_z : freshVar (A.fv) 2 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_y_z : freshVar (A.fv) 3 ≠ freshVar (A.fv) 4 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_csik, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cssetk : (syn_cssetk).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_z : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cssetk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cimagek (A : Class) : (syn_cimagek A).fv = A.fv :=
  by
  ext u
  simp [syn_cimagek]

@[simp]
theorem fv_syn_cidk : (syn_cidk).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_z : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cidk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cio (x : Var) (ph : Wff) : (syn_cio x ph).fv = (ph.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ ph.fv) 0 ∉ (({ x } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [syn_cio, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_c0c : (syn_c0c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_c0c]

@[simp]
theorem fv_syn_cplc (A : Class) (B : Class) : (syn_cplc A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ B.fv) 1 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have fresh_z : freshVar (A.fv ∪ B.fv) 2 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 2
  simp only [Finset.mem_union] at fresh_z
  have distinct_x_y : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 1 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  have distinct_x_z : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 2 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  have distinct_y_z : freshVar (A.fv ∪ B.fv) 1 ≠ freshVar (A.fv ∪ B.fv) 2 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_cplc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cnnc : (syn_cnnc).fv = (∅ : Finset Var) :=
  by
  have fresh_b : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_b_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cnnc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cfin : (syn_cfin).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cfin]

@[simp]
theorem fv_syn_clefin : (syn_clefin).fv = (∅ : Finset Var) :=
  by
  have fresh_w : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_y : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_z : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_w_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_w_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_w_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_clefin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cltfin : (syn_cltfin).fv = (∅ : Finset Var) :=
  by
  have fresh_m : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_n : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_p : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_x : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_m_n : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_m_p : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_m_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_n_p : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_n_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_p_x : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cltfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cncfin (A : Class) : (syn_cncfin A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [syn_cncfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ctfin (M : Class) : (syn_ctfin M).fv = M.fv :=
  by
  have fresh_a : freshVar (M.fv) 0 ∉ (M.fv) := freshVar_not_mem (M.fv) 0
  have fresh_n : freshVar (M.fv) 1 ∉ (M.fv) := freshVar_not_mem (M.fv) 1
  have distinct_a_n : freshVar (M.fv) 0 ≠ freshVar (M.fv) 1 :=
    freshVar_injective (M.fv) (by decide)
  ext u
  simp [syn_ctfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cevenfin : (syn_cevenfin).fv = (∅ : Finset Var) :=
  by
  have fresh_n : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_n_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cevenfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_coddfin : (syn_coddfin).fv = (∅ : Finset Var) :=
  by
  have fresh_n : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_n_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_coddfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wsfin (M : Class) (N : Class) : (syn_wsfin M N).fv = (M.fv) ∪ (N.fv) :=
  by
  have fresh_a : freshVar (M.fv ∪ N.fv) 0 ∉ (M.fv ∪ N.fv) :=
    freshVar_not_mem (M.fv ∪ N.fv) 0
  simp only [Finset.mem_union] at fresh_a
  ext u
  simp [syn_wsfin, Wff.fv, Class.fv]

@[simp]
theorem fv_syn_cspfin : (syn_cspfin).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_z : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cspfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cphi (A : Class) : (syn_cphi A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_cphi, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cop (A : Class) (B : Class) : (syn_cop A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ B.fv) 1 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have distinct_x_y : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 1 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_cop, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cproj1 (A : Class) : (syn_cproj1 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [syn_cproj1, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cproj2 (A : Class) : (syn_cproj2 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [syn_cproj2, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_copab (x : Var) (y : Var) (ph : Wff) :
    (syn_copab x y ph).fv =
      (((ph.fv).erase y).erase x) ∪ (((({ x } : Finset Var)).erase y).erase x) :=
  by
  have fresh_z :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0 ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_z
  ext u
  simp [syn_copab, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wbr (A : Class) (R : Class) (B : Class) :
    (syn_wbr A R B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [syn_wbr, Wff.fv]

@[simp]
theorem fv_syn_c1st : (syn_c1st).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_z : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_c1st, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cswap : (syn_cswap).fv = (∅ : Finset Var) :=
  by
  have fresh_w : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_y : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_z : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_w_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_w_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_w_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cswap, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_csset : (syn_csset).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_csset, Class.fv]; aesop

@[simp]
theorem fv_syn_ccom (A : Class) (B : Class) : (syn_ccom A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ B.fv) 1 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have fresh_z : freshVar (A.fv ∪ B.fv) 2 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 2
  simp only [Finset.mem_union] at fresh_z
  have distinct_x_y : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 1 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  have distinct_x_z : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 2 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  have distinct_y_z : freshVar (A.fv ∪ B.fv) 1 ≠ freshVar (A.fv ∪ B.fv) 2 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_ccom, Class.fv]; aesop

@[simp]
theorem fv_syn_cima (A : Class) (B : Class) : (syn_cima A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ B.fv) 1 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have distinct_x_y : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 1 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_cima, Class.fv]; aesop

@[simp]
theorem fv_syn_csi (A : Class) : (syn_csi A).fv = A.fv :=
  by
  have fresh_w : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_x : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have fresh_y : freshVar (A.fv) 2 ∉ (A.fv) := freshVar_not_mem (A.fv) 2
  have fresh_z : freshVar (A.fv) 3 ∉ (A.fv) := freshVar_not_mem (A.fv) 3
  have distinct_w_x : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_w_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_w_z : freshVar (A.fv) 0 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_y : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_z : freshVar (A.fv) 1 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_y_z : freshVar (A.fv) 2 ≠ freshVar (A.fv) 3 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_csi, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cid : (syn_cid).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cid, Wff.fv]; aesop

@[simp]
theorem fv_syn_cxp (A : Class) (B : Class) : (syn_cxp A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ B.fv) 1 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have distinct_x_y : freshVar (A.fv ∪ B.fv) 0 ≠ freshVar (A.fv ∪ B.fv) 1 :=
    freshVar_injective (A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_cxp, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccnv (A : Class) : (syn_ccnv A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_ccnv, Class.fv]; aesop

@[simp]
theorem fv_syn_crn (A : Class) : (syn_crn A).fv = A.fv :=
  by
  ext u
  simp [syn_crn]

@[simp]
theorem fv_syn_cdm (A : Class) : (syn_cdm A).fv = A.fv :=
  by
  ext u
  simp [syn_cdm]

@[simp]
theorem fv_syn_cres (A : Class) (B : Class) : (syn_cres A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_cres]

@[simp]
theorem fv_syn_wfun (A : Class) : (syn_wfun A).fv = A.fv :=
  by
  ext u
  simp [syn_wfun]

@[simp]
theorem fv_syn_wfn (A : Class) (B : Class) : (syn_wfn A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_wfn, Wff.fv]

@[simp]
theorem fv_syn_wf (F : Class) (A : Class) (B : Class) :
    (syn_wf F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_wf]; aesop

@[simp]
theorem fv_syn_wf1 (F : Class) (A : Class) (B : Class) :
    (syn_wf1 F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_wf1]

@[simp]
theorem fv_syn_wfo (F : Class) (A : Class) (B : Class) :
    (syn_wfo F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_wfo, Wff.fv]; aesop

@[simp]
theorem fv_syn_wf1o (F : Class) (A : Class) (B : Class) :
    (syn_wf1o F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_wf1o]

@[simp]
theorem fv_syn_cfv (F : Class) (A : Class) : (syn_cfv F A).fv = (A.fv) ∪ (F.fv) :=
  by
  have fresh_x : freshVar (F.fv ∪ A.fv) 0 ∉ (F.fv ∪ A.fv) :=
    freshVar_not_mem (F.fv ∪ A.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [syn_cfv, Class.fv]; aesop

@[simp]
theorem fv_syn_c2nd : (syn_c2nd).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_z : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_c2nd, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_co (A : Class) (F : Class) (B : Class) :
    (syn_co A F B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_co]

@[simp]
theorem fv_syn_coprab (x : Var) (y : Var) (z : Var) (ph : Wff) :
    (syn_coprab x y z ph).fv =
      ((((ph.fv).erase z).erase y).erase x) ∪
          ((((({ x } : Finset Var)).erase z).erase y).erase x) ∪
        ((((({ y } : Finset Var)).erase z).erase y).erase x) :=
  by
  have fresh_w :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv)
        0 ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_w
  ext u
  simp [syn_coprab, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cmpt (x : Var) (A : Class) (B : Class) :
    (syn_cmpt x A B).fv = ((A.fv).erase x) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0 ∉
      (({ x } : Finset Var) ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [syn_cmpt, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cmpt2 (x : Var) (A : Class) (y : Var) (B : Class) (C : Class) :
    (syn_cmpt2 x A y B C).fv =
      (((A.fv).erase y).erase x) ∪ (((B.fv).erase y).erase x) ∪
          (((C.fv).erase y).erase x) ∪
        (((({ x } : Finset Var)).erase y).erase x) :=
  by
  have fresh_z :
    freshVar (({ x } : Finset Var) ∪ A.fv ∪ ({ y } : Finset Var) ∪ B.fv ∪ C.fv) 0 ∉
      (({ x } : Finset Var) ∪ A.fv ∪ ({ y } : Finset Var) ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv ∪ ({ y } : Finset Var) ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_z
  ext u
  simp [syn_cmpt2, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ctxp (A : Class) (B : Class) : (syn_ctxp A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_ctxp]

@[simp]
theorem fv_syn_cfix (A : Class) : (syn_cfix A).fv = A.fv :=
  by
  ext u
  simp [syn_cfix]

@[simp]
theorem fv_syn_ccup : (syn_ccup).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_ccup, Class.fv]; aesop

@[simp]
theorem fv_syn_cdisj : (syn_cdisj).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cdisj, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_caddcfn : (syn_caddcfn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_caddcfn, Class.fv]; aesop

@[simp]
theorem fv_syn_ccompose : (syn_ccompose).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_ccompose, Class.fv]; aesop

@[simp]
theorem fv_syn_cins2 (A : Class) : (syn_cins2 A).fv = A.fv :=
  by
  ext u
  simp [syn_cins2]

@[simp]
theorem fv_syn_cins3 (A : Class) : (syn_cins3 A).fv = A.fv :=
  by
  ext u
  simp [syn_cins3]

@[simp]
theorem fv_syn_cimage (A : Class) : (syn_cimage A).fv = A.fv :=
  by
  ext u
  simp [syn_cimage]

@[simp]
theorem fv_syn_cins4 (A : Class) : (syn_cins4 A).fv = A.fv :=
  by
  ext u
  simp [syn_cins4]

@[simp]
theorem fv_syn_csi3 (A : Class) : (syn_csi3 A).fv = A.fv :=
  by
  ext u
  simp [syn_csi3]

@[simp]
theorem fv_syn_cfuns : (syn_cfuns).fv = (∅ : Finset Var) :=
  by
  have fresh_f : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [syn_cfuns, Class.fv]

@[simp]
theorem fv_syn_cfns : (syn_cfns).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_f : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_a_f : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cfns, Class.fv]; aesop

@[simp]
theorem fv_syn_cpw1fn : (syn_cpw1fn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [syn_cpw1fn, Class.fv]

@[simp]
theorem fv_syn_cfullfun (F : Class) : (syn_cfullfun F).fv = F.fv :=
  by
  ext u
  simp [syn_cfullfun]

@[simp]
theorem fv_syn_cclos1 (S : Class) (R : Class) : (syn_cclos1 S R).fv = (R.fv) ∪ (S.fv) :=
  by
  have fresh_a : freshVar (S.fv ∪ R.fv) 0 ∉ (S.fv ∪ R.fv) :=
    freshVar_not_mem (S.fv ∪ R.fv) 0
  simp only [Finset.mem_union] at fresh_a
  ext u
  simp [syn_cclos1, Class.fv]; aesop

@[simp]
theorem fv_syn_ctrans : (syn_ctrans).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_r : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_x : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_y : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have fresh_z : freshVar ((∅ : Finset Var)) 4 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 4
  have distinct_a_r : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 3 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_ctrans, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cref : (syn_cref).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_r : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_x : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_a_r : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cref, Class.fv]; aesop

@[simp]
theorem fv_syn_cantisym : (syn_cantisym).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_r : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_x : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_y : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_a_r : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cantisym, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cpartial : (syn_cpartial).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cpartial]

@[simp]
theorem fv_syn_cconnex : (syn_cconnex).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_r : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_x : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_y : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_a_r : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cconnex, Class.fv]; aesop

@[simp]
theorem fv_syn_cstrict : (syn_cstrict).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cstrict]

@[simp]
theorem fv_syn_cfound : (syn_cfound).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_r : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_x : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_y : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have fresh_z : freshVar ((∅ : Finset Var)) 4 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 4
  have distinct_a_r : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_z : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_z : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_z : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_y_z : freshVar ((∅ : Finset Var)) 3 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cfound, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cwe : (syn_cwe).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwe]

@[simp]
theorem fv_syn_csym : (syn_csym).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_r : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_x : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_y : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_a_r : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_r_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_csym, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cer : (syn_cer).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cer]

@[simp]
theorem fv_syn_cec (A : Class) (R : Class) : (syn_cec A R).fv = (A.fv) ∪ (R.fv) :=
  by
  ext u
  simp [syn_cec]; aesop

@[simp]
theorem fv_syn_cqs (A : Class) (R : Class) : (syn_cqs A R).fv = (A.fv) ∪ (R.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ R.fv) 0 ∉ (A.fv ∪ R.fv) :=
    freshVar_not_mem (A.fv ∪ R.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y : freshVar (A.fv ∪ R.fv) 1 ∉ (A.fv ∪ R.fv) :=
    freshVar_not_mem (A.fv ∪ R.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have distinct_x_y : freshVar (A.fv ∪ R.fv) 0 ≠ freshVar (A.fv ∪ R.fv) 1 :=
    freshVar_injective (A.fv ∪ R.fv) (by decide)
  ext u
  simp [syn_cqs, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cmap : (syn_cmap).fv = (∅ : Finset Var) :=
  by
  have fresh_f : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_y : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_f_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_f_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cmap, Class.fv]; aesop

@[simp]
theorem fv_syn_cen : (syn_cen).fv = (∅ : Finset Var) :=
  by
  have fresh_f : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_y : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_f_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_f_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cen, Class.fv]; aesop

@[simp]
theorem fv_syn_cncs : (syn_cncs).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cncs]

@[simp]
theorem fv_syn_clec : (syn_clec).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_b : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_x : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_y : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_a_b : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_clec, Class.fv]; aesop

@[simp]
theorem fv_syn_cltc : (syn_cltc).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cltc]

@[simp]
theorem fv_syn_cnc (A : Class) : (syn_cnc A).fv = A.fv :=
  by
  ext u
  simp [syn_cnc]

@[simp]
theorem fv_syn_ctc (A : Class) : (syn_ctc A).fv = A.fv :=
  by
  have fresh_b : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_x : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_b_x : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_ctc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_c2c : (syn_c2c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_c2c]

@[simp]
theorem fv_syn_c3c : (syn_c3c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_c3c]

@[simp]
theorem fv_syn_cce : (syn_cce).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_b : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_g : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_m : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  have fresh_n : freshVar ((∅ : Finset Var)) 4 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 4
  have distinct_a_b : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_g : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_m : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_n : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_g : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_m : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_n : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_g_m : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_g_n : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_m_n : freshVar ((∅ : Finset Var)) 3 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cce, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ctcfn : (syn_ctcfn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [syn_ctcfn, Class.fv]

@[simp]
theorem fv_syn_cspac : (syn_cspac).fv = (∅ : Finset Var) :=
  by
  have fresh_m : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_y : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_m_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_m_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cspac, Wff.fv, Class.fv]; aesop

end NFChoice.Compiler.CompactSyntaxFV
