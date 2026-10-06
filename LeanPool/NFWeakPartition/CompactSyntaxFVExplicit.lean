/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.CompactSourceSyntax

/-! NF weak partition development: CompactSyntaxFVExplicit. -/


public section

namespace NFChoice.Compiler.CompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

theorem fv_syn_wtru : synWtru.fv = (∅ : Finset Var) := by rfl

theorem fv_syn_wb (ph : Wff) (ps : Wff) : (synWb ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWb, Wff.fv, Wff.neg]; aesop

theorem fv_syn_wo (ph : Wff) (ps : Wff) : (synWo ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWo, Wff.fv, Wff.neg]

theorem fv_syn_wa (ph : Wff) (ps : Wff) : (synWa ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWa, Wff.fv, Wff.neg]

theorem fv_syn_w3o (ph : Wff) (ps : Wff) (ch : Wff) :
    (synW3o ph ps ch).fv = (ch.fv) ∪ (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synW3o, fv_syn_wo]; aesop

theorem fv_syn_w3a (ph : Wff) (ps : Wff) (ch : Wff) :
    (synW3a ph ps ch).fv = (ch.fv) ∪ (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synW3a, fv_syn_wa]; aesop

theorem fv_syn_wnan (ph : Wff) (ps : Wff) : (synWnan ph ps).fv = (ph.fv) ∪ (ps.fv) :=
  by
  ext u
  simp [synWnan, fv_syn_wa, Wff.fv, Wff.neg]

theorem fv_syn_wex (x : Var) (ph : Wff) : (synWex x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [synWex, Wff.fv, Wff.neg]

theorem fv_syn_wnf (x : Var) (ph : Wff) : (synWnf x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [synWnf, Wff.fv]

theorem fv_syn_wsb (y : Var) (x : Var) (ph : Wff) :
    (synWsb y x ph).fv =
      (ph.fv) ∪ ((ph.fv).erase x) ∪ ((({ y } : Finset Var)).erase x) ∪
          (({ x } : Finset Var)) ∪
        (({ y } : Finset Var)) :=
  by
  ext u
  simp [synWsb, fv_syn_wa, fv_syn_wex, Wff.fv]; aesop

theorem fv_syn_weu (x : Var) (ph : Wff) : (synWeu x ph).fv = (ph.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ ph.fv) 0 ∉ (({ x } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synWeu, fv_syn_wb, fv_syn_wex, Wff.fv]; aesop

theorem fv_syn_wmo (x : Var) (ph : Wff) : (synWmo x ph).fv = (ph.fv).erase x :=
  by
  ext u
  simp [synWmo, fv_syn_weu, fv_syn_wex, Wff.fv]

theorem fv_syn_wnfc (x : Var) (A : Class) : (synWnfc x A).fv = (A.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv) 0 ∉ (({ x } : Finset Var) ∪ A.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synWnfc, fv_syn_wnf, Wff.fv, Class.fv]; aesop

theorem fv_syn_wne (A : Class) (B : Class) : (synWne A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWne, Wff.fv, Wff.neg]

theorem fv_syn_wral (x : Var) (A : Class) (ph : Wff) :
    (synWral x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWral, Wff.fv, Class.fv]; aesop

theorem fv_syn_wrex (x : Var) (A : Class) (ph : Wff) :
    (synWrex x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWrex, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv]; aesop

theorem fv_syn_wreu (x : Var) (A : Class) (ph : Wff) :
    (synWreu x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWreu, fv_syn_wa, fv_syn_weu, Wff.fv, Class.fv]; aesop

theorem fv_syn_wrmo (x : Var) (A : Class) (ph : Wff) :
    (synWrmo x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWrmo, fv_syn_wa, fv_syn_wmo, Wff.fv, Class.fv]; aesop

theorem fv_syn_crab (x : Var) (A : Class) (ph : Wff) :
    (synCrab x A ph).fv = ((A.fv).erase x) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synCrab, fv_syn_wa, Wff.fv, Class.fv]; aesop

theorem fv_syn_cvv : (synCvv).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCvv, Wff.fv, Class.fv]

theorem fv_syn_wsbc (A : Class) (x : Var) (ph : Wff) :
    (synWsbc A x ph).fv = (A.fv) ∪ ((ph.fv).erase x) :=
  by
  ext u
  simp [synWsbc, Wff.fv, Class.fv]

theorem fv_syn_csb (A : Class) (x : Var) (B : Class) :
    (synCsb A x B).fv = (A.fv) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) 0 ∉
      (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ ({ x } : Finset Var) ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCsb, fv_syn_wsbc, Wff.fv, Class.fv]; aesop

theorem fv_syn_cnin (A : Class) (B : Class) : (synCnin A B).fv = (A.fv) ∪ (B.fv) :=
  by
  have fresh_x : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [synCnin, fv_syn_wnan, Wff.fv, Class.fv]; aesop

theorem fv_syn_ccompl (A : Class) : (synCcompl A).fv = A.fv :=
  by
  ext u
  simp [synCcompl, fv_syn_cnin]

theorem fv_syn_cin (A : Class) (B : Class) : (synCin A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCin, fv_syn_ccompl, fv_syn_cnin]

theorem fv_syn_cun (A : Class) (B : Class) : (synCun A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCun, fv_syn_ccompl, fv_syn_cnin]

theorem fv_syn_cdif (A : Class) (B : Class) : (synCdif A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCdif, fv_syn_ccompl, fv_syn_cin]

theorem fv_syn_csymdif (A : Class) (B : Class) : (synCsymdif A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCsymdif, fv_syn_cdif, fv_syn_cun]; aesop

theorem fv_syn_wss (A : Class) (B : Class) : (synWss A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWss, fv_syn_cin, Wff.fv]; aesop

theorem fv_syn_wpss (A : Class) (B : Class) : (synWpss A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWpss, fv_syn_wa, fv_syn_wne, fv_syn_wss]

theorem fv_syn_c0 : (synC0).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC0, fv_syn_cdif, fv_syn_cvv]

theorem fv_syn_cif (ph : Wff) (A : Class) (B : Class) :
    (synCif ph A B).fv = (A.fv) ∪ (B.fv) ∪ (ph.fv) :=
  by
  have fresh_x : freshVar (ph.fv ∪ A.fv ∪ B.fv) 0 ∉ (ph.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (ph.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [synCif, fv_syn_wa, fv_syn_wo, Wff.fv, Class.fv, Wff.neg]; aesop

theorem fv_syn_cpw (A : Class) : (synCpw A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCpw, fv_syn_wss, Class.fv]; aesop

theorem fv_syn_csn (A : Class) : (synCsn A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCsn, Wff.fv, Class.fv]; aesop

theorem fv_syn_cpr (A : Class) (B : Class) : (synCpr A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCpr, fv_syn_csn, fv_syn_cun]

theorem fv_syn_ctp (A : Class) (B : Class) (C : Class) :
    (synCtp A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) :=
  by
  ext u
  simp [synCtp, fv_syn_cpr, fv_syn_csn, fv_syn_cun]

theorem fv_syn_cuni (A : Class) : (synCuni A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCuni, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv]; aesop

theorem fv_syn_cint (A : Class) : (synCint A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCint, Wff.fv, Class.fv]; aesop

theorem fv_syn_ciun (x : Var) (A : Class) (B : Class) :
    (synCiun x A B).fv = ((A.fv).erase x) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0 ∉
      (({ x } : Finset Var) ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCiun, fv_syn_wrex, Wff.fv, Class.fv]; aesop

theorem fv_syn_copk (A : Class) (B : Class) : (synCopk A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCopk, fv_syn_cpr, fv_syn_csn]

theorem fv_syn_c1c : (synC1c).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synC1c, fv_syn_csn, fv_syn_wex, Wff.fv, Class.fv]; aesop

theorem fv_syn_cpw1 (A : Class) : (synCpw1 A).fv = A.fv :=
  by
  ext u
  simp [synCpw1, fv_syn_c1c, fv_syn_cin, fv_syn_cpw]

theorem fv_syn_cuni1 (A : Class) : (synCuni1 A).fv = A.fv :=
  by
  ext u
  simp [synCuni1, fv_syn_c1c, fv_syn_cin, fv_syn_cuni]

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
  simp [synCxpk, fv_syn_copk, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv]; aesop

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
  simp [synCcnvk, fv_syn_copk, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv]; aesop

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
  simp [synCins2k, fv_syn_copk, fv_syn_csn, fv_syn_w3a, fv_syn_wa, fv_syn_wex, Wff.fv,
    Class.fv];
  aesop

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
  simp [synCins3k, fv_syn_copk, fv_syn_csn, fv_syn_w3a, fv_syn_wa, fv_syn_wex, Wff.fv,
    Class.fv];
  aesop

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
  simp [synCimak, fv_syn_copk, fv_syn_wrex, Wff.fv, Class.fv]; aesop

theorem fv_syn_ccomk (A : Class) (B : Class) : (synCcomk A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCcomk, fv_syn_ccnvk, fv_syn_cimak, fv_syn_cin, fv_syn_cins2k, fv_syn_cins3k,
    fv_syn_cvv]

theorem fv_syn_cp6 (A : Class) : (synCp6 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCp6, fv_syn_csn, fv_syn_cvv, fv_syn_cxpk, fv_syn_wss, Class.fv]; aesop

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
  simp [synCsik, fv_syn_copk, fv_syn_csn, fv_syn_w3a, fv_syn_wa, fv_syn_wex, Wff.fv,
    Class.fv];
  aesop

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
  simp [synCssetk, fv_syn_copk, fv_syn_wa, fv_syn_wex, fv_syn_wss, Wff.fv, Class.fv];
  aesop

theorem fv_syn_cimagek (A : Class) : (synCimagek A).fv = A.fv :=
  by
  ext u
  simp [synCimagek, fv_syn_c1c, fv_syn_ccnvk, fv_syn_ccomk, fv_syn_cdif, fv_syn_cimak,
    fv_syn_cins2k, fv_syn_cins3k, fv_syn_cpw1, fv_syn_csik, fv_syn_cssetk, fv_syn_csymdif,
    fv_syn_cvv, fv_syn_cxpk]

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
  simp [synCidk, fv_syn_copk, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv]; aesop

theorem fv_syn_cio (x : Var) (ph : Wff) : (synCio x ph).fv = (ph.fv).erase x :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ ph.fv) 0 ∉ (({ x } : Finset Var) ∪ ph.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ ph.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCio, fv_syn_csn, fv_syn_cuni, Wff.fv, Class.fv]; aesop

theorem fv_syn_c0c : (synC0c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC0c, fv_syn_c0, fv_syn_csn]

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
  simp [synCplc, fv_syn_c0, fv_syn_cin, fv_syn_cun, fv_syn_wa, fv_syn_wrex, Wff.fv,
    Class.fv];
  aesop

theorem fv_syn_cnnc : (synCnnc).fv = (∅ : Finset Var) :=
  by
  have fresh_b : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_b_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCnnc, fv_syn_c0c, fv_syn_c1c, fv_syn_cint, fv_syn_cplc, fv_syn_wa,
    fv_syn_wral, Wff.fv, Class.fv];
  aesop

theorem fv_syn_cfin : (synCfin).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCfin, fv_syn_cnnc, fv_syn_cuni]

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
  simp [synClefin, fv_syn_cnnc, fv_syn_copk, fv_syn_cplc, fv_syn_wa, fv_syn_wex,
    fv_syn_wrex, Wff.fv, Class.fv];
  aesop

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
  simp [synCltfin, fv_syn_c0, fv_syn_c1c, fv_syn_cnnc, fv_syn_copk, fv_syn_cplc,
    fv_syn_wa, fv_syn_wex, fv_syn_wne, fv_syn_wrex, Wff.fv, Class.fv];
  aesop

theorem fv_syn_cncfin (A : Class) : (synCncfin A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCncfin, fv_syn_cio, fv_syn_cnnc, fv_syn_wa, Wff.fv, Class.fv]; aesop

theorem fv_syn_ctfin (M : Class) : (synCtfin M).fv = M.fv :=
  by
  have fresh_a : freshVar (M.fv) 0 ∉ (M.fv) := freshVar_not_mem (M.fv) 0
  have fresh_n : freshVar (M.fv) 1 ∉ (M.fv) := freshVar_not_mem (M.fv) 1
  have distinct_a_n : freshVar (M.fv) 0 ≠ freshVar (M.fv) 1 :=
    freshVar_injective (M.fv) (by decide)
  ext u
  simp [synCtfin, fv_syn_c0, fv_syn_cif, fv_syn_cio, fv_syn_cnnc, fv_syn_cpw1, fv_syn_wa,
    fv_syn_wrex, Wff.fv, Class.fv];
  aesop

theorem fv_syn_cevenfin : (synCevenfin).fv = (∅ : Finset Var) :=
  by
  have fresh_n : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_n_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCevenfin, fv_syn_c0, fv_syn_cnnc, fv_syn_cplc, fv_syn_wa, fv_syn_wne,
    fv_syn_wrex, Wff.fv, Class.fv];
  aesop

theorem fv_syn_coddfin : (synCoddfin).fv = (∅ : Finset Var) :=
  by
  have fresh_n : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_x : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_n_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCoddfin, fv_syn_c0, fv_syn_c1c, fv_syn_cnnc, fv_syn_cplc, fv_syn_wa,
    fv_syn_wne, fv_syn_wrex, Wff.fv, Class.fv];
  aesop

theorem fv_syn_wsfin (M : Class) (N : Class) : (synWsfin M N).fv = (M.fv) ∪ (N.fv) :=
  by
  have fresh_a : freshVar (M.fv ∪ N.fv) 0 ∉ (M.fv ∪ N.fv) :=
    freshVar_not_mem (M.fv ∪ N.fv) 0
  simp only [Finset.mem_union] at fresh_a
  ext u
  simp [synWsfin, fv_syn_cnnc, fv_syn_cpw, fv_syn_cpw1, fv_syn_w3a, fv_syn_wa,
    fv_syn_wex, Wff.fv, Class.fv]

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
  simp [synCspfin, fv_syn_cint, fv_syn_cncfin, fv_syn_cvv, fv_syn_wa, fv_syn_wral,
    fv_syn_wsfin, Wff.fv, Class.fv];
  aesop

theorem fv_syn_cphi (A : Class) : (synCphi A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCphi, fv_syn_c1c, fv_syn_cif, fv_syn_cnnc, fv_syn_cplc, fv_syn_wrex, Wff.fv,
    Class.fv];
  aesop

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
  simp [synCop, fv_syn_c0c, fv_syn_cphi, fv_syn_csn, fv_syn_cun, fv_syn_wrex, Wff.fv,
    Class.fv];
  aesop

theorem fv_syn_cproj1 (A : Class) : (synCproj1 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCproj1, fv_syn_cphi, Wff.fv, Class.fv]; aesop

theorem fv_syn_cproj2 (A : Class) : (synCproj2 A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  ext u
  simp [synCproj2, fv_syn_c0c, fv_syn_cphi, fv_syn_csn, fv_syn_cun, Wff.fv, Class.fv];
  aesop

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
  simp [synCopab, fv_syn_cop, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv]; aesop

theorem fv_syn_wbr (A : Class) (R : Class) (B : Class) :
    (synWbr A R B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synWbr, fv_syn_cop, Wff.fv]

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
  simp [synC1st, fv_syn_cop, fv_syn_copab, fv_syn_wex, Wff.fv, Class.fv]; aesop

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
  simp [synCswap, fv_syn_cop, fv_syn_copab, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv];
  aesop

theorem fv_syn_csset : (synCsset).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCsset, fv_syn_copab, fv_syn_wss, Class.fv]; aesop

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
  simp [synCcom, fv_syn_copab, fv_syn_wa, fv_syn_wbr, fv_syn_wex, Class.fv]; aesop

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
  simp [synCima, fv_syn_wbr, fv_syn_wrex, Class.fv]; aesop

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
  simp [synCsi, fv_syn_copab, fv_syn_csn, fv_syn_w3a, fv_syn_wbr, fv_syn_wex, Wff.fv,
    Class.fv];
  aesop

theorem fv_syn_cid : (synCid).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCid, fv_syn_copab, Wff.fv]; aesop

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
  simp [synCxp, fv_syn_copab, fv_syn_wa, Wff.fv, Class.fv]; aesop

theorem fv_syn_ccnv (A : Class) : (synCcnv A).fv = A.fv :=
  by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCcnv, fv_syn_copab, fv_syn_wbr, Class.fv]; aesop

theorem fv_syn_crn (A : Class) : (synCrn A).fv = A.fv :=
  by
  ext u
  simp [synCrn, fv_syn_cima, fv_syn_cvv]

theorem fv_syn_cdm (A : Class) : (synCdm A).fv = A.fv :=
  by
  ext u
  simp [synCdm, fv_syn_ccnv, fv_syn_crn]

theorem fv_syn_cres (A : Class) (B : Class) : (synCres A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCres, fv_syn_cin, fv_syn_cvv, fv_syn_cxp]

theorem fv_syn_wfun (A : Class) : (synWfun A).fv = A.fv :=
  by
  ext u
  simp [synWfun, fv_syn_ccnv, fv_syn_ccom, fv_syn_cid, fv_syn_wss]

theorem fv_syn_wfn (A : Class) (B : Class) : (synWfn A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synWfn, fv_syn_cdm, fv_syn_wa, fv_syn_wfun, Wff.fv]

theorem fv_syn_wf (F : Class) (A : Class) (B : Class) :
    (synWf F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWf, fv_syn_crn, fv_syn_wa, fv_syn_wfn, fv_syn_wss]; aesop

theorem fv_syn_wf1 (F : Class) (A : Class) (B : Class) :
    (synWf1 F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWf1, fv_syn_ccnv, fv_syn_wa, fv_syn_wf, fv_syn_wfun]

theorem fv_syn_wfo (F : Class) (A : Class) (B : Class) :
    (synWfo F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWfo, fv_syn_crn, fv_syn_wa, fv_syn_wfn, Wff.fv]; aesop

theorem fv_syn_wf1o (F : Class) (A : Class) (B : Class) :
    (synWf1o F A B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synWf1o, fv_syn_wa, fv_syn_wf1, fv_syn_wfo]

theorem fv_syn_cfv (F : Class) (A : Class) : (synCfv F A).fv = (A.fv) ∪ (F.fv) :=
  by
  have fresh_x : freshVar (F.fv ∪ A.fv) 0 ∉ (F.fv ∪ A.fv) :=
    freshVar_not_mem (F.fv ∪ A.fv) 0
  simp only [Finset.mem_union] at fresh_x
  ext u
  simp [synCfv, fv_syn_cio, fv_syn_wbr, Class.fv]; aesop

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
  simp [synC2nd, fv_syn_cop, fv_syn_copab, fv_syn_wex, Wff.fv, Class.fv]; aesop

theorem fv_syn_co (A : Class) (F : Class) (B : Class) :
    (synCo A F B).fv = (A.fv) ∪ (B.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCo, fv_syn_cfv, fv_syn_cop]

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
  simp [synCoprab, fv_syn_cop, fv_syn_wa, fv_syn_wex, Wff.fv, Class.fv]; aesop

theorem fv_syn_cmpt (x : Var) (A : Class) (B : Class) :
    (synCmpt x A B).fv = ((A.fv).erase x) ∪ ((B.fv).erase x) :=
  by
  have fresh_y :
    freshVar (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0 ∉
      (({ x } : Finset Var) ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (({ x } : Finset Var) ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  ext u
  simp [synCmpt, fv_syn_copab, fv_syn_wa, Wff.fv, Class.fv]; aesop

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
  simp [synCmpt2, fv_syn_coprab, fv_syn_wa, Wff.fv, Class.fv]; aesop

theorem fv_syn_ctxp (A : Class) (B : Class) : (synCtxp A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [synCtxp, fv_syn_c1st, fv_syn_c2nd, fv_syn_ccnv, fv_syn_ccom, fv_syn_cin]

theorem fv_syn_cfix (A : Class) : (synCfix A).fv = A.fv :=
  by
  ext u
  simp [synCfix, fv_syn_cid, fv_syn_cin, fv_syn_crn]

theorem fv_syn_ccup : (synCcup).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCcup, fv_syn_cmpt2, fv_syn_cun, fv_syn_cvv, Class.fv]; aesop

theorem fv_syn_cdisj : (synCdisj).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCdisj, fv_syn_c0, fv_syn_cin, fv_syn_copab, Wff.fv, Class.fv]; aesop

theorem fv_syn_caddcfn : (synCaddcfn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCaddcfn, fv_syn_cmpt2, fv_syn_cplc, fv_syn_cvv, Class.fv]; aesop

theorem fv_syn_ccompose : (synCcompose).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCcompose, fv_syn_ccom, fv_syn_cmpt2, fv_syn_cvv, Class.fv]; aesop

theorem fv_syn_cins2 (A : Class) : (synCins2 A).fv = A.fv :=
  by
  ext u
  simp [synCins2, fv_syn_ctxp, fv_syn_cvv]

theorem fv_syn_cins3 (A : Class) : (synCins3 A).fv = A.fv :=
  by
  ext u
  simp [synCins3, fv_syn_ctxp, fv_syn_cvv]

theorem fv_syn_cimage (A : Class) : (synCimage A).fv = A.fv :=
  by
  ext u
  simp [synCimage, fv_syn_c1c, fv_syn_ccnv, fv_syn_ccom, fv_syn_ccompl, fv_syn_cima,
    fv_syn_cins2, fv_syn_cins3, fv_syn_csi, fv_syn_csset, fv_syn_csymdif]

theorem fv_syn_cins4 (A : Class) : (synCins4 A).fv = A.fv :=
  by
  ext u
  simp [synCins4, fv_syn_c1st, fv_syn_c2nd, fv_syn_ccnv, fv_syn_ccom, fv_syn_cima,
    fv_syn_ctxp]

theorem fv_syn_csi3 (A : Class) : (synCsi3 A).fv = A.fv :=
  by
  ext u
  simp [synCsi3, fv_syn_c1st, fv_syn_c2nd, fv_syn_ccom, fv_syn_cima, fv_syn_cpw1,
    fv_syn_csi, fv_syn_ctxp]

theorem fv_syn_cfuns : (synCfuns).fv = (∅ : Finset Var) :=
  by
  have fresh_f : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCfuns, fv_syn_wfun, Class.fv]

theorem fv_syn_cfns : (synCfns).fv = (∅ : Finset Var) :=
  by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_f : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_a_f : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synCfns, fv_syn_copab, fv_syn_wfn, Class.fv]; aesop

theorem fv_syn_cpw1fn : (synCpw1fn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCpw1fn, fv_syn_c1c, fv_syn_cmpt, fv_syn_cpw1, fv_syn_cuni, Class.fv]

theorem fv_syn_cfullfun (F : Class) : (synCfullfun F).fv = F.fv :=
  by
  ext u
  simp [synCfullfun, fv_syn_c0, fv_syn_ccom, fv_syn_ccompl, fv_syn_cdif, fv_syn_cdm,
    fv_syn_cid, fv_syn_csn, fv_syn_cun, fv_syn_cxp]

theorem fv_syn_cclos1 (S : Class) (R : Class) : (synCclos1 S R).fv = (R.fv) ∪ (S.fv) :=
  by
  have fresh_a : freshVar (S.fv ∪ R.fv) 0 ∉ (S.fv ∪ R.fv) :=
    freshVar_not_mem (S.fv ∪ R.fv) 0
  simp only [Finset.mem_union] at fresh_a
  ext u
  simp [synCclos1, fv_syn_cima, fv_syn_cint, fv_syn_wa, fv_syn_wss, Class.fv]; aesop

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
  simp [synCtrans, fv_syn_copab, fv_syn_wa, fv_syn_wbr, fv_syn_wral, Wff.fv, Class.fv];
  aesop

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
  simp [synCref, fv_syn_copab, fv_syn_wbr, fv_syn_wral, Class.fv]; aesop

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
  simp [synCantisym, fv_syn_copab, fv_syn_wa, fv_syn_wbr, fv_syn_wral, Wff.fv, Class.fv];
  aesop

theorem fv_syn_cpartial : (synCpartial).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCpartial, fv_syn_cantisym, fv_syn_cin, fv_syn_cref, fv_syn_ctrans]

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
  simp [synCconnex, fv_syn_copab, fv_syn_wbr, fv_syn_wo, fv_syn_wral, Class.fv]; aesop

theorem fv_syn_cstrict : (synCstrict).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCstrict, fv_syn_cconnex, fv_syn_cin, fv_syn_cpartial]

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
  simp [synCfound, fv_syn_c0, fv_syn_copab, fv_syn_wa, fv_syn_wbr, fv_syn_wne,
    fv_syn_wral, fv_syn_wrex, fv_syn_wss, Wff.fv, Class.fv];
  aesop

theorem fv_syn_cwe : (synCwe).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwe, fv_syn_cfound, fv_syn_cin, fv_syn_cstrict]

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
  simp [synCsym, fv_syn_copab, fv_syn_wbr, fv_syn_wral, Wff.fv, Class.fv]; aesop

theorem fv_syn_cer : (synCer).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCer, fv_syn_cin, fv_syn_csym, fv_syn_ctrans]

theorem fv_syn_cec (A : Class) (R : Class) : (synCec A R).fv = (A.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCec, fv_syn_cima, fv_syn_csn]; aesop

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
  simp [synCqs, fv_syn_cec, fv_syn_wrex, Wff.fv, Class.fv]; aesop

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
  simp [synCmap, fv_syn_cmpt2, fv_syn_cvv, fv_syn_wf, Class.fv]; aesop

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
  simp [synCen, fv_syn_copab, fv_syn_wex, fv_syn_wf1o, Class.fv]; aesop

theorem fv_syn_cncs : (synCncs).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCncs, fv_syn_cen, fv_syn_cqs, fv_syn_cvv]

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
  simp [synClec, fv_syn_copab, fv_syn_wrex, fv_syn_wss, Class.fv]; aesop

theorem fv_syn_cltc : (synCltc).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCltc, fv_syn_cdif, fv_syn_cid, fv_syn_clec]

theorem fv_syn_cnc (A : Class) : (synCnc A).fv = A.fv :=
  by
  ext u
  simp [synCnc, fv_syn_cec, fv_syn_cen]

theorem fv_syn_ctc (A : Class) : (synCtc A).fv = A.fv :=
  by
  have fresh_b : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_x : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_b_x : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synCtc, fv_syn_cio, fv_syn_cnc, fv_syn_cncs, fv_syn_cpw1, fv_syn_wa, fv_syn_wrex,
    Wff.fv, Class.fv];
  aesop

theorem fv_syn_c2c : (synC2c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC2c, fv_syn_c0, fv_syn_cnc, fv_syn_cpr, fv_syn_cvv]

theorem fv_syn_c3c : (synC3c).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synC3c, fv_syn_c0, fv_syn_cdif, fv_syn_cnc, fv_syn_csn, fv_syn_ctp, fv_syn_cvv]

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
  simp [synCce, fv_syn_cen, fv_syn_cmap, fv_syn_cmpt2, fv_syn_cncs, fv_syn_co,
    fv_syn_cpw1, fv_syn_w3a, fv_syn_wbr, fv_syn_wex, Wff.fv, Class.fv];
  aesop

theorem fv_syn_ctcfn : (synCtcfn).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  ext u
  simp [synCtcfn, fv_syn_c1c, fv_syn_cmpt, fv_syn_ctc, fv_syn_cuni, Class.fv]

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
  simp [synCspac, fv_syn_c2c, fv_syn_cce, fv_syn_cclos1, fv_syn_cmpt, fv_syn_cncs,
    fv_syn_co, fv_syn_copab, fv_syn_csn, fv_syn_w3a, Wff.fv, Class.fv];
  aesop

end NFChoice.Compiler.CompactSyntaxFVExplicit
