/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Series.FormalGroupLaw.Basic

import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Tactic.LinearCombination

/-!
# Invariance: closedness of the invariant differential

The differential form `ω_i = ∑_k (M⁻¹)_{ik} dX_k` attached to a formal group law is invariant,
and — the content of this file — *closed*: `∂_l (M⁻¹)_{ik} = ∂_k (M⁻¹)_{il}`
(`ChabautyColeman.FormalGroupLaw.pderiv_diffMatrixInv_symm`). This is the technical heart of
the formal-logarithm construction: it is what lets the radial antiderivative recover the
invariant differential. The proof runs through the substitution identities
`ChabautyColeman.FormalGroupLaw.diffMatrix_subst_F` and
`ChabautyColeman.FormalGroupLaw.diffMatrixInv_subst_F` and an antisymmetrization argument.

## Main statements
* `ChabautyColeman.FormalGroupLaw.diffMatrixInv_subst_F`: the invariant differential is invariant.
* `ChabautyColeman.FormalGroupLaw.pderiv_diffMatrixInv_symm`: the invariant differential is closed.

Blueprint node: `lem:fgl-invariance`.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace ChabautyColeman

namespace FormalGroupLaw

variable {O : Type*} [CommRing O] {ι : Type*} (Φ : FormalGroupLaw O ι)
private lemma eq_zero_of_transpose_mul_mul {R : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] {M B : Matrix ι ι R} (hM : IsUnit M.det) (h : M.transpose * B * M = 0) :
    B = 0 := by
  calc B = M.transpose⁻¹ * M.transpose * B * (M * M⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose _ hM),
          Matrix.mul_nonsing_inv _ hM, one_mul, mul_one]
    _ = M.transpose⁻¹ * (M.transpose * B * M) * M⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

section invariance

private lemma subst_zero' {τ : Type*} {a : τ → MvPowerSeries (ι ⊕ ι) O}
    (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (0 : MvPowerSeries τ O) = 0 := by
  rw [← coe_substAlgHom ha]
  exact map_zero _

-- renaming by the block swap fixes `F` (commutativity)
private lemma rename_sumComm_F (j : ι) :
    rename (⇑(Equiv.sumComm ι ι)) (Φ.F j) = Φ.F j := by
  rw [rename_eq_subst]
  exact Φ.comm' j

variable [Finite ι]

-- the substitution family `F` itself, the `Y`-block embedding, `F` in the first slot
-- with `0` in the second, and the three-block specialization `(X, Y, 0) ← (A, B, C)`
lemma hasSubst_F : MvPowerSeries.HasSubst fun j : ι ↦ Φ.F j :=
  hasSubst_of_constantCoeff_zero fun j ↦ Φ.zero_constantCoeff j

lemma hasSubst_Yemb :
    MvPowerSeries.HasSubst fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O) :=
  hasSubst_of_constantCoeff_zero fun s ↦ by simp

private lemma hasSubst_C0 :
    MvPowerSeries.HasSubst
      (Sum.elim (fun a : ι ↦ X (Sum.inl a))
        (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0)
        : ι ⊕ ι ⊕ ι → MvPowerSeries (ι ⊕ ι) O) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (a | b | c) <;> simp

-- specializing the left association at `C = 0` gives `F(X, Y)` in the first slot
private lemma subst_C0_assocLeft (h : MvPowerSeries (ι ⊕ ι) O) :
    MvPowerSeries.subst
        (Sum.elim (fun a : ι ↦ X (Sum.inl a))
          (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0))
        (MvPowerSeries.subst (assocLeftFam Φ.F) h)
      = MvPowerSeries.subst (Sum.elim (fun j : ι ↦ Φ.F j) fun _ ↦ 0) h := by
  rw [subst_comp_subst_apply (hasSubst_assocLeft Φ) hasSubst_C0]
  congr 1
  funext t
  rcases t with j | j
  · rw [assocLeftFam_inl, subst_comp_subst_apply hasSubst_emb12 hasSubst_C0]
    have hfam : (fun s : ι ⊕ ι ↦ MvPowerSeries.subst
          (Sum.elim (fun a : ι ↦ X (Sum.inl a))
            (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0))
          ((Sum.elim (fun a : ι ↦ X (Sum.inl a)) fun b : ι ↦ X (Sum.inr (Sum.inl b))
            : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) s))
        = fun s : ι ⊕ ι ↦ (X s : MvPowerSeries (ι ⊕ ι) O) := by
      funext s
      rcases s with a | b <;>
        simp [MvPowerSeries.subst_X hasSubst_C0]
    rw [hfam, subst_self]
    rfl
  · rw [assocLeftFam_inr, MvPowerSeries.subst_X hasSubst_C0]
    rfl

-- the substituted differential matrix, in terms of the `(F, 0)` specialization
private lemma subst_F_diffMatrix (i k : ι) :
    MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix i k)
      = MvPowerSeries.subst (Sum.elim (fun j : ι ↦ Φ.F j) fun _ ↦ 0)
          (pderiv (Sum.inr k) (Φ.F i)) := by
  rw [Φ.diffMatrix_apply i k, subst_comp_subst_apply hasSubst_unitR (hasSubst_F Φ)]
  congr 1
  funext t
  rcases t with a | a
  · change MvPowerSeries.subst _ (X a : MvPowerSeries ι O) = _
    rw [MvPowerSeries.subst_X (hasSubst_F Φ)]
    rfl
  · change MvPowerSeries.subst _ (0 : MvPowerSeries ι O) = _
    rw [subst_zero' (hasSubst_F Φ)]
    rfl

-- the axiom `F(Y, 0) = Y`, transported to the `Y`-block of a two-block ring
private lemma subst_F_Yzero (j : ι) :
    MvPowerSeries.subst
        (Sum.elim (fun a : ι ↦ (X (Sum.inr a) : MvPowerSeries (ι ⊕ ι) O)) fun _ ↦ 0)
        (Φ.F j)
      = X (Sum.inr j) := by
  have hax := congrArg
    (MvPowerSeries.subst fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
    (Φ.add_zero' j)
  rw [MvPowerSeries.subst_X hasSubst_Yemb, subst_comp_subst_apply hasSubst_unitR hasSubst_Yemb]
    at hax
  rw [← hax]
  congr 1
  funext t
  rcases t with a | a <;>
    simp [MvPowerSeries.subst_X hasSubst_Yemb, subst_zero' hasSubst_Yemb]

-- specializing the right association at `C = 0` is the identity
private lemma subst_C0_assocRight (h : MvPowerSeries (ι ⊕ ι) O) :
    MvPowerSeries.subst
        (Sum.elim (fun a : ι ↦ X (Sum.inl a))
          (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0))
        (MvPowerSeries.subst (assocRightFam Φ.F) h)
      = h := by
  rw [subst_comp_subst_apply (hasSubst_assocRight Φ) hasSubst_C0]
  have hfam : (fun t : ι ⊕ ι ↦ MvPowerSeries.subst
        (Sum.elim (fun a : ι ↦ X (Sum.inl a))
          (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0))
        (assocRightFam Φ.F t))
      = fun t : ι ⊕ ι ↦ (X t : MvPowerSeries (ι ⊕ ι) O) := by
    funext t
    rcases t with j | j
    · rw [assocRightFam_inl, MvPowerSeries.subst_X hasSubst_C0]
      rfl
    · rw [assocRightFam_inr, subst_comp_subst_apply hasSubst_emb23 hasSubst_C0]
      have hfam2 : (fun s : ι ⊕ ι ↦ MvPowerSeries.subst
            (Sum.elim (fun a : ι ↦ X (Sum.inl a))
              (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0))
            ((Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a)))
              fun b : ι ↦ X (Sum.inr (Sum.inr b))
              : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) s))
          = (Sum.elim (fun a : ι ↦ (X (Sum.inr a) : MvPowerSeries (ι ⊕ ι) O)) fun _ ↦ 0) := by
        funext s
        rcases s with a | b <;> simp [MvPowerSeries.subst_X hasSubst_C0]
      rw [hfam2, subst_F_Yzero]
  rw [hfam, subst_self]
  rfl

-- the differential matrix in the `Y`-block, via the `C = 0` specialization
private lemma subst_C0_emb23_pderiv (j k : ι) :
    MvPowerSeries.subst
        (Sum.elim (fun a : ι ↦ X (Sum.inl a))
          (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0))
        (MvPowerSeries.subst
          (Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a))) fun b : ι ↦ X (Sum.inr (Sum.inr b))
            : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O)
          (pderiv (Sum.inr k) (Φ.F j)))
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
          (Φ.diffMatrix j k) := by
  rw [subst_comp_subst_apply hasSubst_emb23 hasSubst_C0]
  rw [Φ.diffMatrix_apply j k, subst_comp_subst_apply hasSubst_unitR hasSubst_Yemb]
  congr 1
  funext t
  rcases t with a | a
  · change MvPowerSeries.subst _ (X (Sum.inr (Sum.inl a)) : MvPowerSeries (ι ⊕ ι ⊕ ι) O)
      = MvPowerSeries.subst _ (X a : MvPowerSeries ι O)
    rw [MvPowerSeries.subst_X hasSubst_C0, MvPowerSeries.subst_X hasSubst_Yemb]
    rfl
  · change MvPowerSeries.subst _ (X (Sum.inr (Sum.inr a)) : MvPowerSeries (ι ⊕ ι ⊕ ι) O)
      = MvPowerSeries.subst _ (0 : MvPowerSeries ι O)
    rw [MvPowerSeries.subst_X hasSubst_C0, subst_zero' hasSubst_Yemb]
    rfl

-- `Y := 0` composed with the `Y`-block embedding extracts the constant coefficient
private lemma subst_unitR_Yemb (h : MvPowerSeries ι O) :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O)
        (MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) h)
      = C (constantCoeff h) := by
  rw [subst_comp_subst_apply (hasSubst_Yemb) (hasSubst_unitR)]
  have hfam : (fun s : ι ↦ MvPowerSeries.subst
        (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O)
        (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
      = (0 : ι → MvPowerSeries ι O) := by
    funext s
    rw [MvPowerSeries.subst_X (hasSubst_unitR)]
    rfl
  rw [hfam, subst_zero_eq_C_constantCoeff, Algebra.algebraMap_self, MvPowerSeries.map_id]
  rfl

-- `Y := 0` composed with `F` is the identity, by the unit axiom
private lemma subst_unitR_F (h : MvPowerSeries ι O) :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O)
        (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) h)
      = h := by
  rw [subst_comp_subst_apply (hasSubst_F Φ) (hasSubst_unitR)]
  have hfam : (fun j : ι ↦ MvPowerSeries.subst
        (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O) (Φ.F j))
      = MvPowerSeries.X :=
    funext fun j ↦ Φ.add_zero' j
  rw [hfam, subst_self]
  rfl

-- commutativity makes the mixed second derivatives symmetric
private lemma coeff_F_symm (i k l : ι) :
    coeff (Finsupp.single (Sum.inl l) 1 + Finsupp.single (Sum.inr k) 1) (Φ.F i)
      = coeff (Finsupp.single (Sum.inl k) 1 + Finsupp.single (Sum.inr l) 1) (Φ.F i) := by
  have hren : rename (Sum.swap : ι ⊕ ι → ι ⊕ ι) (Φ.F i) = Φ.F i := by
    rw [rename_eq_subst]
    exact Φ.comm' i
  have hemb := coeff_embDomain_rename (⟨Sum.swap, Sum.swap_leftInverse.injective⟩ : ι ⊕ ι ↪ ι ⊕ ι)
    (Φ.F i) (Finsupp.single (Sum.inr l) 1 + Finsupp.single (Sum.inl k) 1)
  rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single] at hemb
  change coeff (Finsupp.single (Sum.inl l) 1 + Finsupp.single (Sum.inr k) 1)
    (rename Sum.swap (Φ.F i)) = _ at hemb
  rw [hren] at hemb
  rw [hemb, add_comm]

-- `∂_{C_k}` of the left associated substitution
private lemma pderiv_substLeft (i : ι) (k : ι) :
    pderiv (Sum.inr (Sum.inr k)) (MvPowerSeries.subst (assocLeftFam Φ.F) (Φ.F i))
      = MvPowerSeries.subst (assocLeftFam Φ.F) (pderiv (Sum.inr k) (Φ.F i)) := by
  classical
  cases nonempty_fintype ι
  rw [pderiv_subst (hasSubst_assocLeft Φ), Fintype.sum_sum_type]
  have hinl (j : ι) : pderiv (Sum.inr (Sum.inr k)) (assocLeftFam Φ.F (Sum.inl j)) = 0 := by
    refine pderiv_subst_eq_zero hasSubst_emb12 _ ?_ _
    rintro (a | b) <;> simp
  have hinr (j : ι) : pderiv (Sum.inr (Sum.inr k)) (assocLeftFam Φ.F (Sum.inr j))
      = if j = k then 1 else 0 := by
    change pderiv (Sum.inr (Sum.inr k)) (X (Sum.inr (Sum.inr j))
      : MvPowerSeries (ι ⊕ ι ⊕ ι) O) = _
    simp [pderiv_X, Pi.single_apply]
  simp only [hinl, hinr, mul_zero, mul_ite, mul_one, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_ite_eq' Finset.univ k
    fun j ↦ MvPowerSeries.subst (assocLeftFam Φ.F) (pderiv (Sum.inr j) (Φ.F i)),
    ite_eq_left (Finset.mem_univ k)]

-- `∂_{C_k}` of the embedded second factor
private lemma pderiv_emb23 (j k : ι) :
    pderiv (Sum.inr (Sum.inr k)) (MvPowerSeries.subst
        (Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a))) fun b : ι ↦ X (Sum.inr (Sum.inr b))
          : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O)
        (Φ.F j))
      = MvPowerSeries.subst
          (Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a))) fun b : ι ↦ X (Sum.inr (Sum.inr b))
            : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O)
          (pderiv (Sum.inr k) (Φ.F j)) := by
  classical
  cases nonempty_fintype ι
  rw [pderiv_subst hasSubst_emb23, Fintype.sum_sum_type]
  have hinl (a : ι) : pderiv (Sum.inr (Sum.inr k))
      (X (Sum.inr (Sum.inl a)) : MvPowerSeries (ι ⊕ ι ⊕ ι) O) = 0 := by
    simp
  have hinr (b : ι) : pderiv (Sum.inr (Sum.inr k))
      (X (Sum.inr (Sum.inr b)) : MvPowerSeries (ι ⊕ ι ⊕ ι) O) = if b = k then 1 else 0 := by
    simp [pderiv_X, Pi.single_apply]
  simp only [Sum.elim_inl, Sum.elim_inr, hinl, hinr, mul_zero, mul_ite, mul_one,
    Finset.sum_const_zero, zero_add]
  rw [Finset.sum_ite_eq' Finset.univ k
    fun b ↦ MvPowerSeries.subst
      (Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a))) fun b : ι ↦ X (Sum.inr (Sum.inr b))
        : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O)
      (pderiv (Sum.inr b) (Φ.F j)),
    ite_eq_left (Finset.mem_univ k)]

-- the `Y`-block embedding commutes with `∂/∂Y`
lemma pderiv_Yemb (l : ι) (h : MvPowerSeries ι O) :
    pderiv (Sum.inr l) (MvPowerSeries.subst
        (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) h)
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
          (pderiv l h) := by
  classical
  cases nonempty_fintype ι
  rw [pderiv_subst (hasSubst_Yemb)]
  have hx (t : ι) : pderiv (Sum.inr l) (X (Sum.inr t) : MvPowerSeries (ι ⊕ ι) O)
      = if t = l then 1 else 0 := by
    simp [pderiv_X, Pi.single_apply]
  simp only [hx, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ l
    fun t ↦ MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
      (pderiv t h),
    ite_eq_left (Finset.mem_univ l)]

-- `Y := 0` intertwines `∂/∂X_l` on both sides
private lemma pderiv_unitR (l : ι) (h : MvPowerSeries (ι ⊕ ι) O) :
    pderiv l (MvPowerSeries.subst
        (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O) h)
      = MvPowerSeries.subst (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O)
          (pderiv (Sum.inl l) h) := by
  classical
  cases nonempty_fintype ι
  rw [pderiv_subst (hasSubst_unitR), Fintype.sum_sum_type]
  have hinl (a : ι) : pderiv l ((Sum.elim MvPowerSeries.X (fun _ ↦ 0)
      : ι ⊕ ι → MvPowerSeries ι O) (Sum.inl a)) = if a = l then 1 else 0 := by
    change pderiv l (MvPowerSeries.X a : MvPowerSeries ι O) = _
    simp [pderiv_X, Pi.single_apply]
  have hinr (b : ι) : pderiv l ((Sum.elim MvPowerSeries.X (fun _ ↦ 0)
      : ι ⊕ ι → MvPowerSeries ι O) (Sum.inr b)) = 0 := by
    change pderiv l (0 : MvPowerSeries ι O) = 0
    exact map_zero _
  simp only [hinl, hinr, mul_ite, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_ite_eq' Finset.univ l
    fun a ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O)
      (pderiv (Sum.inl a) h),
    ite_eq_left (Finset.mem_univ l)]

-- the linear part of `M` is a mixed second derivative of `F`
private lemma constantCoeff_pderiv_diffMatrix (i k l : ι) :
    constantCoeff (pderiv l (Φ.diffMatrix i k))
      = coeff (Finsupp.single (Sum.inl l) 1 + Finsupp.single (Sum.inr k) 1) (Φ.F i) := by
  classical
  rw [Φ.diffMatrix_apply i k,
    pderiv_unitR,
    MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero (hasSubst_unitR)
      (by rintro (a | a) <;> simp),
    ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, coeff_pderiv]
  simp

lemma hasSubst_Xemb :
    MvPowerSeries.HasSubst fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O) :=
  hasSubst_of_constantCoeff_zero fun s ↦ by simp

-- renaming by the block swap fixes substitution of `F`
private lemma rename_sumComm_subst_F (h : MvPowerSeries ι O) :
    rename (⇑(Equiv.sumComm ι ι)) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) h)
      = MvPowerSeries.subst (fun j : ι ↦ Φ.F j) h := by
  rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_F Φ) (HasSubst.X_comp _)]
  congr 1
  funext j
  exact (rename_eq_subst _ _).symm.trans (rename_sumComm_F Φ j)

-- renaming by the block swap turns the `Y`-embedding into the `X`-embedding
private lemma rename_sumComm_Yemb (h : MvPowerSeries ι O) :
    rename (⇑(Equiv.sumComm ι ι)) (MvPowerSeries.subst
        (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) h)
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) h := by
  rw [rename_eq_subst, subst_comp_subst_apply hasSubst_Yemb (HasSubst.X_comp _)]
  congr 1
  funext s
  rw [MvPowerSeries.subst_X (HasSubst.X_comp _)]
  rfl

-- the `X`-block embedding commutes with `∂/∂X`
lemma pderiv_Xemb (l : ι) (h : MvPowerSeries ι O) :
    pderiv (Sum.inl l) (MvPowerSeries.subst
        (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) h)
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O))
          (pderiv l h) := by
  classical
  cases nonempty_fintype ι
  rw [pderiv_subst (hasSubst_Xemb)]
  have hx (t : ι) : pderiv (Sum.inl l) (X (Sum.inl t) : MvPowerSeries (ι ⊕ ι) O)
      = if t = l then 1 else 0 := by
    simp [pderiv_X, Pi.single_apply]
  simp only [hx, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ l
    fun t ↦ MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O))
      (pderiv t h),
    ite_eq_left (Finset.mem_univ l)]

variable [Fintype ι]

-- `∂_{C_k}` of the right associated substitution
private lemma pderiv_substRight (i k : ι) :
    pderiv (Sum.inr (Sum.inr k)) (MvPowerSeries.subst (assocRightFam Φ.F) (Φ.F i))
      = ∑ j, MvPowerSeries.subst (assocRightFam Φ.F) (pderiv (Sum.inr j) (Φ.F i))
          * MvPowerSeries.subst
              (Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a)))
                fun b : ι ↦ X (Sum.inr (Sum.inr b))
                : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O)
              (pderiv (Sum.inr k) (Φ.F j)) := by
  classical
  rw [pderiv_subst (hasSubst_assocRight Φ), Fintype.sum_sum_type]
  have hinl (j : ι) : pderiv (Sum.inr (Sum.inr k)) (assocRightFam Φ.F (Sum.inl j)) = 0 := by
    change pderiv (Sum.inr (Sum.inr k)) (X (Sum.inl j) : MvPowerSeries (ι ⊕ ι ⊕ ι) O) = 0
    simp
  simp only [hinl, mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact pderiv_emb23 Φ j k

/-- The matrix invariance identity of the invariant differential:
`M(F(X,Y)) = (D_Y F)(X,Y) · M(Y)`, obtained by differentiating associativity in the
third block of variables at `0`. -/
theorem diffMatrix_subst_F (i k : ι) :
    MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix i k)
      = ∑ j, pderiv (Sum.inr j) (Φ.F i)
          * MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
              (Φ.diffMatrix j k) := by
  have hax := congrArg
    (MvPowerSeries.subst
      (Sum.elim (fun a : ι ↦ X (Sum.inl a))
        (Sum.elim (fun b : ι ↦ X (Sum.inr b)) fun _ ↦ 0)
        : ι ⊕ ι ⊕ ι → MvPowerSeries (ι ⊕ ι) O))
    (congrArg (pderiv (Sum.inr (Sum.inr k))) (Φ.assoc' i))
  rw [pderiv_substLeft, pderiv_substRight, subst_C0_assocLeft] at hax
  rw [← coe_substAlgHom hasSubst_C0, map_sum] at hax
  rw [subst_F_diffMatrix, hax]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, coe_substAlgHom hasSubst_C0, subst_C0_assocRight, subst_C0_emb23_pderiv]



variable [DecidableEq ι]

/-- The invariance identity for the inverse Jacobian matrix `N = M⁻¹` of a formal group
law: `N(F(X,Y)) · D_Y F(X,Y) = N(Y)`, entrywise. Equivalently, the invariant differential
`δ = N(X) dX` satisfies `δ(F(X,Y)) · D_Y F(X,Y) = δ(Y)`. -/
theorem diffMatrixInv_subst_F (i k : ι) :
    ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
        * pderiv (Sum.inr k) (Φ.F a)
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
          (Φ.diffMatrix⁻¹ i k) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp Φ.isUnit_diffMatrix
  set SF := (substAlgHom (R := O) (hasSubst_F Φ)).mapMatrix (m := ι) with hSF
  set SY := (substAlgHom (R := O) (hasSubst_Yemb (O := O) (ι := ι))).mapMatrix (m := ι)
    with hSY
  set D : Matrix ι ι (MvPowerSeries (ι ⊕ ι) O) :=
    Matrix.of fun i j ↦ pderiv (Sum.inr j) (Φ.F i) with hD
  have h1 : SF Φ.diffMatrix⁻¹ * SF Φ.diffMatrix = 1 := by
    rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
  have h2 : SY Φ.diffMatrix * SY Φ.diffMatrix⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv _ hdet, map_one]
  have hMF : SF Φ.diffMatrix = D * SY Φ.diffMatrix := by
    refine Matrix.ext fun i k ↦ ?_
    simp only [hSF, hSY, hD, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.of_apply, coe_substAlgHom]
    exact Φ.diffMatrix_subst_F i k
  have key : SF Φ.diffMatrix⁻¹ * D = SY Φ.diffMatrix⁻¹ := by
    calc SF Φ.diffMatrix⁻¹ * D
        = SF Φ.diffMatrix⁻¹ * D * (SY Φ.diffMatrix * SY Φ.diffMatrix⁻¹) := by rw [h2, mul_one]
      _ = SF Φ.diffMatrix⁻¹ * (D * SY Φ.diffMatrix) * SY Φ.diffMatrix⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = SF Φ.diffMatrix⁻¹ * SF Φ.diffMatrix * SY Φ.diffMatrix⁻¹ := by rw [← hMF]
      _ = SY Φ.diffMatrix⁻¹ := by rw [h1, one_mul]
  have hik := congrFun (congrFun key i) k
  simpa only [hSF, hSY, hD, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
    Matrix.of_apply, coe_substAlgHom] using hik

-- expansion of `∂_{Y_l}` of the left side of the inverse-matrix invariance identity
private lemma pderiv_inr_expand (i k l : ι) :
    pderiv (Sum.inr l) (∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
        * pderiv (Sum.inr k) (Φ.F a))
      = (∑ a, ∑ b, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (pderiv b (Φ.diffMatrix⁻¹ i a))
            * pderiv (Sum.inr l) (Φ.F b) * pderiv (Sum.inr k) (Φ.F a))
        + ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
            * pderiv (Sum.inr l) (pderiv (Sum.inr k) (Φ.F a)) := by
  rw [map_sum]
  have hterm (a : ι) : pderiv (Sum.inr l)
      (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
        * pderiv (Sum.inr k) (Φ.F a))
      = (∑ b, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (pderiv b (Φ.diffMatrix⁻¹ i a))
            * pderiv (Sum.inr l) (Φ.F b) * pderiv (Sum.inr k) (Φ.F a))
        + MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
            * pderiv (Sum.inr l) (pderiv (Sum.inr k) (Φ.F a)) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      mul_comm (pderiv (Sum.inr k) (Φ.F a)), pderiv_subst (hasSubst_F Φ),
      Finset.sum_mul, add_comm]
  rw [Finset.sum_congr rfl fun a _ ↦ hterm a, Finset.sum_add_distrib]

-- the antisymmetrized (in `(k,l)`) differentiated invariance identity
private lemma subst_Yemb_pderiv_sub (i k l : ι) :
    MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
        (pderiv l (Φ.diffMatrix⁻¹ i k) - pderiv k (Φ.diffMatrix⁻¹ i l))
      = ∑ a, ∑ b,
          MvPowerSeries.subst (fun j : ι ↦ Φ.F j)
              (pderiv b (Φ.diffMatrix⁻¹ i a) - pderiv a (Φ.diffMatrix⁻¹ i b))
            * pderiv (Sum.inr k) (Φ.F a) * pderiv (Sum.inr l) (Φ.F b) := by
  have hkl := congrArg (pderiv (Sum.inr l)) (diffMatrixInv_subst_F Φ i k)
  have hlk := congrArg (pderiv (Sum.inr k)) (diffMatrixInv_subst_F Φ i l)
  rw [pderiv_inr_expand, pderiv_Yemb] at hkl hlk
  rw [MvPowerSeries.subst_sub hasSubst_Yemb, ← hkl, ← hlk]
  have hsecond : ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
        * pderiv (Sum.inr l) (pderiv (Sum.inr k) (Φ.F a))
      = ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
        * pderiv (Sum.inr k) (pderiv (Sum.inr l) (Φ.F a)) :=
    Finset.sum_congr rfl fun a _ ↦ by rw [pderiv_comm]
  rw [hsecond, add_sub_add_right_eq_sub]
  have hT2 : ∑ a, ∑ b, MvPowerSeries.subst (fun j : ι ↦ Φ.F j)
        (pderiv b (Φ.diffMatrix⁻¹ i a))
        * pderiv (Sum.inr k) (Φ.F b) * pderiv (Sum.inr l) (Φ.F a)
      = ∑ a, ∑ b, MvPowerSeries.subst (fun j : ι ↦ Φ.F j)
        (pderiv a (Φ.diffMatrix⁻¹ i b))
        * pderiv (Sum.inr k) (Φ.F a) * pderiv (Sum.inr l) (Φ.F b) :=
    Finset.sum_comm
  rw [hT2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [MvPowerSeries.subst_sub (hasSubst_F Φ)]
  ring

-- the specialization of the antisymmetrized identity at `Y = 0`
private lemma closedness_C_eq (i k l : ι) :
    C (constantCoeff (pderiv l (Φ.diffMatrix⁻¹ i k) - pderiv k (Φ.diffMatrix⁻¹ i l)))
      = ∑ a, ∑ b, (pderiv b (Φ.diffMatrix⁻¹ i a) - pderiv a (Φ.diffMatrix⁻¹ i b))
          * Φ.diffMatrix a k * Φ.diffMatrix b l := by
  have h := congrArg (MvPowerSeries.subst
    (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O))
    (subst_Yemb_pderiv_sub Φ i k l)
  rw [subst_unitR_Yemb] at h
  rw [h, ← coe_substAlgHom (hasSubst_unitR), map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [map_mul, map_mul, coe_substAlgHom (hasSubst_unitR), subst_unitR_F Φ,
    ← Φ.diffMatrix_apply, ← Φ.diffMatrix_apply]

-- the linear parts of `M⁻¹` and `M` are opposite
private lemma constantCoeff_pderiv_diffMatrixInv (i k l : ι) :
    constantCoeff (pderiv l (Φ.diffMatrix⁻¹ i k))
      = - constantCoeff (pderiv l (Φ.diffMatrix i k)) := by
  have hNM : Φ.diffMatrix⁻¹ * Φ.diffMatrix = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp Φ.isUnit_diffMatrix)
  have hik := congrFun (congrFun hNM i) k
  rw [Matrix.mul_apply, Matrix.one_apply] at hik
  have h := congrArg (fun g ↦ constantCoeff (pderiv l g)) hik
  have hN (j : ι) : constantCoeff (Φ.diffMatrix⁻¹ i j) = if i = j then 1 else 0 := by
    have hc := congrFun (congrFun (diffMatrixInv_map_constantCoeff Φ) i) j
    rwa [Matrix.map_apply, Matrix.one_apply] at hc
  have hM (j : ι) : constantCoeff (Φ.diffMatrix j k) = if j = k then 1 else 0 := by
    have hc := congrFun (congrFun Φ.diffMatrix_map_constantCoeff j) k
    rwa [Matrix.map_apply, Matrix.one_apply] at hc
  have hrhs : constantCoeff (pderiv l (if i = k then (1 : MvPowerSeries ι O) else 0)) = 0 := by
    split <;> simp
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul, hN, hM, hrhs, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  linear_combination h



-- the double sum in the specialized identity vanishes
private lemma closedness_sum_eq_zero (i k l : ι) :
    ∑ a, ∑ b, (pderiv b (Φ.diffMatrix⁻¹ i a) - pderiv a (Φ.diffMatrix⁻¹ i b))
        * Φ.diffMatrix a k * Φ.diffMatrix b l
      = 0 := by
  rw [← closedness_C_eq Φ i k l, map_sub, constantCoeff_pderiv_diffMatrixInv Φ,
    constantCoeff_pderiv_diffMatrixInv Φ, constantCoeff_pderiv_diffMatrix Φ,
    constantCoeff_pderiv_diffMatrix Φ, coeff_F_symm Φ, neg_sub_neg, sub_self, map_zero]

/-- The invariant differential of a commutative formal group law is closed: the partial
derivatives of the entries of any row of the inverse Jacobian matrix `M⁻¹` satisfy the
symmetry `∂_l (M⁻¹)_{ik} = ∂_k (M⁻¹)_{il}`. Commutativity of the formal group law is
essential here. -/
theorem pderiv_diffMatrixInv_symm (i k l : ι) :
    pderiv l (Φ.diffMatrix⁻¹ i k) = pderiv k (Φ.diffMatrix⁻¹ i l) := by
  set A : Matrix ι ι (MvPowerSeries ι O) :=
    Matrix.of fun a b ↦ pderiv b (Φ.diffMatrix⁻¹ i a) - pderiv a (Φ.diffMatrix⁻¹ i b)
    with hA
  have hMAM : Φ.diffMatrix.transpose * A * Φ.diffMatrix = 0 := by
    refine Matrix.ext fun k l ↦ ?_
    calc (Φ.diffMatrix.transpose * A * Φ.diffMatrix) k l
        = ∑ a, ∑ b, A a b * Φ.diffMatrix a k * Φ.diffMatrix b l := by
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
      _ = 0 := by
          simp only [hA, Matrix.of_apply]
          exact closedness_sum_eq_zero Φ i k l
  have h := congrFun (congrFun (eq_zero_of_transpose_mul_mul
    ((Matrix.isUnit_iff_isUnit_det _).mp Φ.isUnit_diffMatrix) hMAM) k) l
  simp only [hA, Matrix.of_apply, Matrix.zero_apply] at h
  exact sub_eq_zero.mp (by simpa using h)

-- the `X`-block version of the inverse-matrix invariance identity, by commutativity
lemma diffMatrixInv_subst_F_inl (i k : ι) :
    ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
        * pderiv (Sum.inl k) (Φ.F a)
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O))
          (Φ.diffMatrix⁻¹ i k) := by
  have h := congrArg (rename (⇑(Equiv.sumComm ι ι))) (diffMatrixInv_subst_F Φ i k)
  rw [map_sum, rename_sumComm_Yemb] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_mul, rename_sumComm_subst_F, rename_pderiv, rename_sumComm_F]
  rfl

end invariance

end FormalGroupLaw

end ChabautyColeman

end
