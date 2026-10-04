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
theorem fv_syn_wtru : synWtru.fv = (∅ : Finset Var) := by rfl

@[simp]
theorem fv_syn_wb (ph : Wff) (ps : Wff) : (synWb ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWb, Wff.fv, Wff.neg]; aesop

@[simp]
theorem fv_syn_wo (ph : Wff) (ps : Wff) : (synWo ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWo, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wa (ph : Wff) (ps : Wff) : (synWa ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWa, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_w3o (ph : Wff) (ps : Wff) (ch : Wff) :
    (synW3o ph ps ch).fv = (ch.fv) ∪ (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synW3o]; aesop

@[simp]
theorem fv_syn_w3a (ph : Wff) (ps : Wff) (ch : Wff) :
    (synW3a ph ps ch).fv = (ch.fv) ∪ (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synW3a]; aesop

@[simp]
theorem fv_syn_wnan (ph : Wff) (ps : Wff) : (synWnan ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWnan, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wex (x : Var) (ph : Wff) : (synWex x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [synWex, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wnf (x : Var) (ph : Wff) : (synWnf x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [synWnf, Wff.fv]

@[simp]
theorem fv_syn_wsb (y : Var) (x : Var) (ph : Wff) :
    (synWsb y x ph).fv =
      (ph.fv) ∪ ((ph.fv).erase x) ∪ ((({ y } : Finset Var)).erase x) ∪
          (({ x } : Finset Var)) ∪
        (({ y } : Finset Var)) :=
  by
  ext u
  simp [synWsb, Wff.fv]; aesop

@[simp]
theorem fv_syn_weu (x : Var) (ph : Wff) : (synWeu x ph).fv = (ph.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ ph.fv) 0 ∉ (({ x } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synWeu, Wff.fv]; aesop

@[simp]
theorem fv_syn_wmo (x : Var) (ph : Wff) : (synWmo x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [synWmo, Wff.fv]

@[simp]
theorem fv_syn_wnfc (x : Var) (A : Class) : (synWnfc x A).fv = (A.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv) 0 ∉ (({ x } : Finset Var) ∪ A.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synWnfc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wne (A : Class) (B : Class) : (synWne A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWne, Wff.fv, Wff.neg]

@[simp]
theorem fv_syn_wral (x : Var) (A : Class) (ph : Wff) :
    (synWral x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWral, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wrex (x : Var) (A : Class) (ph : Wff) :
    (synWrex x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWrex, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wreu (x : Var) (A : Class) (ph : Wff) :
    (synWreu x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWreu, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wrmo (x : Var) (A : Class) (ph : Wff) :
    (synWrmo x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWrmo, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_crab (x : Var) (A : Class) (ph : Wff) :
    (synCrab x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synCrab, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cvv : (synCvv).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCvv, Wff.fv, Class.fv]

@[simp]
theorem fv_syn_wsbc (A : Class) (x : Var) (ph : Wff) :
    (synWsbc A x ph).fv = (A.fv) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWsbc, Wff.fv, Class.fv]

@[simp]
theorem fv_syn_csb (A : Class) (x : Var) (B : Class) :
    (synCsb A x B).fv = (A.fv) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) 0 ∉
      (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCsb, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cnin (A : Class) (B : Class) : (synCnin A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [synCnin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccompl (A : Class) : (synCcompl A).fv = A.fv :=
  by
  ext u
  simp [synCcompl]

@[simp]
theorem fv_syn_cin (A : Class) (B : Class) : (synCin A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCin]

@[simp]
theorem fv_syn_cun (A : Class) (B : Class) : (synCun A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCun]

@[simp]
theorem fv_syn_cdif (A : Class) (B : Class) : (synCdif A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCdif]

@[simp]
theorem fv_syn_csymdif (A : Class) (B : Class) : (synCsymdif A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCsymdif]; aesop

@[simp]
theorem fv_syn_wss (A : Class) (B : Class) : (synWss A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWss, Wff.fv]; aesop

@[simp]
theorem fv_syn_wpss (A : Class) (B : Class) : (synWpss A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWpss]

@[simp]
theorem fv_syn_c0 : (synC0).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC0]

@[simp]
theorem fv_syn_cif (ph : Wff) (A : Class) (B : Class) :
    (synCif ph A B).fv = (A.fv) ∪ (B.fv) ∪ (ph.fv) :=
  by
  have fresh_x : freshVar (ph.fv ∪ A.fv ∪ B.fv) 0 ∉ (ph.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (ph.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [synCif, Wff.fv, Class.fv, Wff.neg]; aesop

@[simp]
theorem fv_syn_cpw (A : Class) : (synCpw A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCpw, Class.fv]; aesop

@[simp]
theorem fv_syn_csn (A : Class) : (synCsn A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCsn, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cpr (A : Class) (B : Class) : (synCpr A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCpr]

@[simp]
theorem fv_syn_ctp (A : Class) (B : Class) (C : Class) :
    (synCtp A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) :=
  by
  ext u
  simp [synCtp]

@[simp]
theorem fv_syn_cuni (A : Class) : (synCuni A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCuni, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cint (A : Class) : (synCint A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCint, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ciun (x : Var) (A : Class) (B : Class) :
    (synCiun x A B).fv = ((A.fv).erase x) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0 ∉
      (({ x } : Finset Var) ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCiun, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_copk (A : Class) (B : Class) : (synCopk A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCopk]

@[simp]
theorem fv_syn_c1c : (synC1c).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synC1c, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cpw1 (A : Class) : (synCpw1 A).fv = A.fv :=
  by
  ext u
  simp [synCpw1]

@[simp]
theorem fv_syn_cuni1 (A : Class) : (synCuni1 A).fv = A.fv :=
  by
  ext u
  simp [synCuni1]

@[simp]
theorem fv_syn_cxpk (A : Class) (B : Class) : (synCxpk A B).fv = (A.fv) ∪ (B.fv) :=
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
  simp [synCxpk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccnvk (A : Class) : (synCcnvk A).fv = A.fv :=
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
  simp [synCcnvk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cins2k (A : Class) : (synCins2k A).fv = A.fv :=
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
  simp [synCins2k, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cins3k (A : Class) : (synCins3k A).fv = A.fv :=
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
  simp [synCins3k, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cimak (A : Class) (B : Class) : (synCimak A B).fv = (A.fv) ∪ (B.fv) :=
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
  simp [synCimak, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccomk (A : Class) (B : Class) : (synCcomk A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCcomk]

@[simp]
theorem fv_syn_cp6 (A : Class) : (synCp6 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCp6, Class.fv]; aesop

@[simp]
theorem fv_syn_csik (A : Class) : (synCsik A).fv = A.fv :=
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
  simp [synCsik, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cssetk : (synCssetk).fv = (∅ : Finset Var) :=
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
  simp [synCssetk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cimagek (A : Class) : (synCimagek A).fv = A.fv :=
  by
  ext u
  simp [synCimagek]

@[simp]
theorem fv_syn_cidk : (synCidk).fv = (∅ : Finset Var) :=
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
  simp [synCidk, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cio (x : Var) (ph : Wff) : (synCio x ph).fv = (ph.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ ph.fv) 0 ∉ (({ x } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCio, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_c0c : (synC0c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC0c]

@[simp]
theorem fv_syn_cplc (A : Class) (B : Class) : (synCplc A B).fv = (A.fv) ∪ (B.fv) :=
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
  simp [synCplc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cnnc : (synCnnc).fv = (∅ : Finset Var) :=
  by
  have fresh_b : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_b_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCnnc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cfin : (synCfin).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCfin]

@[simp]
theorem fv_syn_clefin : (synClefin).fv = (∅ : Finset Var) :=
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
  simp [synClefin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cltfin : (synCltfin).fv = (∅ : Finset Var) :=
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
  simp [synCltfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cncfin (A : Class) : (synCncfin A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCncfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ctfin (M : Class) : (synCtfin M).fv = M.fv :=
  by
  have fresh_a : freshVar (M.fv) 0 ∉ (M.fv) := freshVar_not_mem (M.fv) 0
  have fresh_n : freshVar (M.fv) 1 ∉ (M.fv) := freshVar_not_mem (M.fv) 1
  have distinct_a_n : freshVar (M.fv) 0 ≠ freshVar (M.fv) 1 :=
    freshVar_injective (M.fv) (by decide)
  ext u
  simp [synCtfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cevenfin : (synCevenfin).fv = (∅ : Finset Var) :=
  by
  have fresh_n : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_n_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCevenfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_coddfin : (synCoddfin).fv = (∅ : Finset Var) :=
  by
  have fresh_n : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_n_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCoddfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wsfin (M : Class) (N : Class) : (synWsfin M N).fv = (M.fv) ∪ (N.fv) :=
  by
  have fresh_a : freshVar (M.fv ∪ N.fv) 0 ∉ (M.fv ∪ N.fv) :=
    freshVar_not_mem (M.fv ∪ N.fv) 0
  simp only [Finset.mem_union] at fresh_a
  ext u
  simp [synWsfin, Wff.fv, Class.fv]

@[simp]
theorem fv_syn_cspfin : (synCspfin).fv = (∅ : Finset Var) :=
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
  simp [synCspfin, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cphi (A : Class) : (synCphi A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCphi, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cop (A : Class) (B : Class) : (synCop A B).fv = (A.fv) ∪ (B.fv) :=
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
  simp [synCop, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cproj1 (A : Class) : (synCproj1 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCproj1, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cproj2 (A : Class) : (synCproj2 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCproj2, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_copab (x : Var) (y : Var) (ph : Wff) :
    (synCopab x y ph).fv =
      (((ph.fv).erase y).erase x) ∪ (((({ x } : Finset Var)).erase y).erase x) :=
  by
  have fresh_z :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0 ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_z
  ext u
  simp [synCopab, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_wbr (A : Class) (R : Class) (B : Class) :
    (synWbr A R B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synWbr, Wff.fv]

@[simp]
theorem fv_syn_c1st : (synC1st).fv = (∅ : Finset Var) :=
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
  simp [synC1st, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cswap : (synCswap).fv = (∅ : Finset Var) :=
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
  simp [synCswap, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_csset : (synCsset).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCsset, Class.fv]; aesop

@[simp]
theorem fv_syn_ccom (A : Class) (B : Class) : (synCcom A B).fv = (A.fv) ∪ (B.fv) :=
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
  simp [synCcom, Class.fv]; aesop

@[simp]
theorem fv_syn_cima (A : Class) (B : Class) : (synCima A B).fv = (A.fv) ∪ (B.fv) :=
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
  simp [synCima, Class.fv]; aesop

@[simp]
theorem fv_syn_csi (A : Class) : (synCsi A).fv = A.fv :=
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
  simp [synCsi, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cid : (synCid).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCid, Wff.fv]; aesop

@[simp]
theorem fv_syn_cxp (A : Class) (B : Class) : (synCxp A B).fv = (A.fv) ∪ (B.fv) :=
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
  simp [synCxp, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ccnv (A : Class) : (synCcnv A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCcnv, Class.fv]; aesop

@[simp]
theorem fv_syn_crn (A : Class) : (synCrn A).fv = A.fv :=
  by
  ext u
  simp [synCrn]

@[simp]
theorem fv_syn_cdm (A : Class) : (synCdm A).fv = A.fv :=
  by
  ext u
  simp [synCdm]

@[simp]
theorem fv_syn_cres (A : Class) (B : Class) : (synCres A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCres]

@[simp]
theorem fv_syn_wfun (A : Class) : (synWfun A).fv = A.fv :=
  by
  ext u
  simp [synWfun]

@[simp]
theorem fv_syn_wfn (A : Class) (B : Class) : (synWfn A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWfn, Wff.fv]

@[simp]
theorem fv_syn_wf (F : Class) (A : Class) (B : Class) :
    (synWf F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWf]; aesop

@[simp]
theorem fv_syn_wf1 (F : Class) (A : Class) (B : Class) :
    (synWf1 F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWf1]

@[simp]
theorem fv_syn_wfo (F : Class) (A : Class) (B : Class) :
    (synWfo F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWfo, Wff.fv]; aesop

@[simp]
theorem fv_syn_wf1o (F : Class) (A : Class) (B : Class) :
    (synWf1o F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWf1o]

@[simp]
theorem fv_syn_cfv (F : Class) (A : Class) : (synCfv F A).fv = (A.fv) ∪ (F.fv) :=
  by
  have fresh_x : freshVar (F.fv ∪ A.fv) 0 ∉ (F.fv ∪ A.fv) :=
    freshVar_not_mem (F.fv ∪ A.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [synCfv, Class.fv]; aesop

@[simp]
theorem fv_syn_c2nd : (synC2nd).fv = (∅ : Finset Var) :=
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
  simp [synC2nd, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_co (A : Class) (F : Class) (B : Class) :
    (synCo A F B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCo]

@[simp]
theorem fv_syn_coprab (x : Var) (y : Var) (z : Var) (ph : Wff) :
    (synCoprab x y z ph).fv =
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
  simp [synCoprab, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cmpt (x : Var) (A : Class) (B : Class) :
    (synCmpt x A B).fv = ((A.fv).erase x) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0 ∉
      (({ x } : Finset Var) ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCmpt, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cmpt2 (x : Var) (A : Class) (y : Var) (B : Class) (C : Class) :
    (synCmpt2 x A y B C).fv =
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
  simp [synCmpt2, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ctxp (A : Class) (B : Class) : (synCtxp A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCtxp]

@[simp]
theorem fv_syn_cfix (A : Class) : (synCfix A).fv = A.fv :=
  by
  ext u
  simp [synCfix]

@[simp]
theorem fv_syn_ccup : (synCcup).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCcup, Class.fv]; aesop

@[simp]
theorem fv_syn_cdisj : (synCdisj).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCdisj, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_caddcfn : (synCaddcfn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCaddcfn, Class.fv]; aesop

@[simp]
theorem fv_syn_ccompose : (synCcompose).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCcompose, Class.fv]; aesop

@[simp]
theorem fv_syn_cins2 (A : Class) : (synCins2 A).fv = A.fv :=
  by
  ext u
  simp [synCins2]

@[simp]
theorem fv_syn_cins3 (A : Class) : (synCins3 A).fv = A.fv :=
  by
  ext u
  simp [synCins3]

@[simp]
theorem fv_syn_cimage (A : Class) : (synCimage A).fv = A.fv :=
  by
  ext u
  simp [synCimage]

@[simp]
theorem fv_syn_cins4 (A : Class) : (synCins4 A).fv = A.fv :=
  by
  ext u
  simp [synCins4]

@[simp]
theorem fv_syn_csi3 (A : Class) : (synCsi3 A).fv = A.fv :=
  by
  ext u
  simp [synCsi3]

@[simp]
theorem fv_syn_cfuns : (synCfuns).fv = (∅ : Finset Var) :=
  by
  have fresh_f : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCfuns, Class.fv]

@[simp]
theorem fv_syn_cfns : (synCfns).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_f : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_a_f : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCfns, Class.fv]; aesop

@[simp]
theorem fv_syn_cpw1fn : (synCpw1fn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCpw1fn, Class.fv]

@[simp]
theorem fv_syn_cfullfun (F : Class) : (synCfullfun F).fv = F.fv :=
  by
  ext u
  simp [synCfullfun]

@[simp]
theorem fv_syn_cclos1 (S : Class) (R : Class) : (synCclos1 S R).fv = (R.fv) ∪ (S.fv) :=
  by
  have fresh_a : freshVar (S.fv ∪ R.fv) 0 ∉ (S.fv ∪ R.fv) :=
    freshVar_not_mem (S.fv ∪ R.fv) 0
  simp only [Finset.mem_union] at fresh_a
  ext u
  simp [synCclos1, Class.fv]; aesop

@[simp]
theorem fv_syn_ctrans : (synCtrans).fv = (∅ : Finset Var) :=
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
  simp [synCtrans, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cref : (synCref).fv = (∅ : Finset Var) :=
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
  simp [synCref, Class.fv]; aesop

@[simp]
theorem fv_syn_cantisym : (synCantisym).fv = (∅ : Finset Var) :=
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
  simp [synCantisym, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cpartial : (synCpartial).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCpartial]

@[simp]
theorem fv_syn_cconnex : (synCconnex).fv = (∅ : Finset Var) :=
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
  simp [synCconnex, Class.fv]; aesop

@[simp]
theorem fv_syn_cstrict : (synCstrict).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCstrict]

@[simp]
theorem fv_syn_cfound : (synCfound).fv = (∅ : Finset Var) :=
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
  simp [synCfound, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cwe : (synCwe).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwe]

@[simp]
theorem fv_syn_csym : (synCsym).fv = (∅ : Finset Var) :=
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
  simp [synCsym, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cer : (synCer).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCer]

@[simp]
theorem fv_syn_cec (A : Class) (R : Class) : (synCec A R).fv = (A.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCec]; aesop

@[simp]
theorem fv_syn_cqs (A : Class) (R : Class) : (synCqs A R).fv = (A.fv) ∪ (R.fv) :=
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
  simp [synCqs, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_cmap : (synCmap).fv = (∅ : Finset Var) :=
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
  simp [synCmap, Class.fv]; aesop

@[simp]
theorem fv_syn_cen : (synCen).fv = (∅ : Finset Var) :=
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
  simp [synCen, Class.fv]; aesop

@[simp]
theorem fv_syn_cncs : (synCncs).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCncs]

@[simp]
theorem fv_syn_clec : (synClec).fv = (∅ : Finset Var) :=
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
  simp [synClec, Class.fv]; aesop

@[simp]
theorem fv_syn_cltc : (synCltc).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCltc]

@[simp]
theorem fv_syn_cnc (A : Class) : (synCnc A).fv = A.fv :=
  by
  ext u
  simp [synCnc]

@[simp]
theorem fv_syn_ctc (A : Class) : (synCtc A).fv = A.fv :=
  by
  have fresh_b : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_x : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_b_x : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCtc, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_c2c : (synC2c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC2c]

@[simp]
theorem fv_syn_c3c : (synC3c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC3c]

@[simp]
theorem fv_syn_cce : (synCce).fv = (∅ : Finset Var) :=
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
  simp [synCce, Wff.fv, Class.fv]; aesop

@[simp]
theorem fv_syn_ctcfn : (synCtcfn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCtcfn, Class.fv]

@[simp]
theorem fv_syn_cspac : (synCspac).fv = (∅ : Finset Var) :=
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
  simp [synCspac, Wff.fv, Class.fv]; aesop

end NFChoice.Compiler.CompactSyntaxFV
