/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Series.MvPSeries
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Formal group laws: structure, differential matrix, base change

`ChabautyColeman.FormalGroupLaw O ι` is an `ι`-dimensional commutative formal group law over
`O`: a family of power series `F i` in two blocks of `ι` variables with `F(X,0) = X`,
`F(0,Y) = Y`, `F(X,Y) = F(Y,X)` and `F(F(X,Y),Z) = F(X,F(Y,Z))`, the substitutions being
Mathlib's formal `MvPowerSeries.subst`. This file sets up the structure and its foundational
API: the `HasSubst` witnesses for the axiom families, the differential (Jacobian) matrix at the
origin, and base change along a ring homomorphism.

## Main definitions
* `ChabautyColeman.FormalGroupLaw`: the structure of a formal group law.
* `ChabautyColeman.FormalGroupLaw.diffMatrix`: the Jacobian matrix `(∂ⱼ Fᵢ)(X, 0)`.
* `ChabautyColeman.FormalGroupLaw.map`: base change of a formal group law along `f : O →+* O'`.

## Main statements
* `ChabautyColeman.FormalGroupLaw.isUnit_diffMatrix`: the differential matrix is invertible.
* `ChabautyColeman.FormalGroupLaw.diffMatrix_map`: base change commutes with `diffMatrix`.

Blueprint nodes: `def:fgl`, `def:fgl-diff`.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace ChabautyColeman
/-! ### The associativity substitution families -/

section families

variable {O : Type*} [CommRing O] {ι : Type*}

/-- The substitution family embedding `F(X,Y)` into the first two of three blocks of
variables (for the left side of associativity). -/
noncomputable def assocLeftFam (F : ι → MvPowerSeries (ι ⊕ ι) O) :
    ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O :=
  Sum.elim
    (fun j ↦ MvPowerSeries.subst
      (Sum.elim (fun a ↦ X (Sum.inl a)) fun b ↦ X (Sum.inr (Sum.inl b))) (F j))
    fun j ↦ X (Sum.inr (Sum.inr j))

@[simp] theorem assocLeftFam_inl (F : ι → MvPowerSeries (ι ⊕ ι) O) (j : ι) :
    assocLeftFam F (Sum.inl j) = MvPowerSeries.subst
      (Sum.elim (fun a ↦ X (Sum.inl a)) fun b ↦ X (Sum.inr (Sum.inl b))) (F j) :=
  rfl

@[simp] theorem assocLeftFam_inr (F : ι → MvPowerSeries (ι ⊕ ι) O) (j : ι) :
    assocLeftFam F (Sum.inr j) = X (Sum.inr (Sum.inr j)) :=
  rfl

/-- The substitution family embedding `F(Y,Z)` into the last two of three blocks of
variables (for the right side of associativity). -/
noncomputable def assocRightFam (F : ι → MvPowerSeries (ι ⊕ ι) O) :
    ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O :=
  Sum.elim
    (fun j ↦ X (Sum.inl j))
    fun j ↦ MvPowerSeries.subst
      (Sum.elim (fun a ↦ X (Sum.inr (Sum.inl a))) fun b ↦ X (Sum.inr (Sum.inr b))) (F j)

@[simp] theorem assocRightFam_inl (F : ι → MvPowerSeries (ι ⊕ ι) O) (j : ι) :
    assocRightFam F (Sum.inl j) = X (Sum.inl j) :=
  rfl

@[simp] theorem assocRightFam_inr (F : ι → MvPowerSeries (ι ⊕ ι) O) (j : ι) :
    assocRightFam F (Sum.inr j) = MvPowerSeries.subst
      (Sum.elim (fun a ↦ X (Sum.inr (Sum.inl a))) fun b ↦ X (Sum.inr (Sum.inr b))) (F j) :=
  rfl

end families

variable (O : Type*) [CommRing O] (ι : Type*)

/-- An `ι`-dimensional commutative formal group law over `O`: a family of power series
`F i` in two blocks of `ι` variables (the blocks being the two summands of `ι ⊕ ι`),
with `F(X,0) = X`, `F(0,Y) = Y`, `F(X,Y) = F(Y,X)` and `F(F(X,Y),Z) = F(X,F(Y,Z))`. -/
structure FormalGroupLaw where
  /-- The underlying family of power series in the variables `X = inl`, `Y = inr`. -/
  F : ι → MvPowerSeries (ι ⊕ ι) O
  zero_constantCoeff : ∀ i, constantCoeff (F i) = 0
  add_zero' : ∀ i, MvPowerSeries.subst
    (Sum.elim MvPowerSeries.X fun _ ↦ 0 : ι ⊕ ι → MvPowerSeries ι O) (F i)
    = MvPowerSeries.X i
  zero_add' : ∀ i, MvPowerSeries.subst
    (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : ι ⊕ ι → MvPowerSeries ι O) (F i)
    = MvPowerSeries.X i
  comm' : ∀ i, MvPowerSeries.subst (fun s ↦ MvPowerSeries.X s.swap) (F i) = F i
  assoc' : ∀ i, MvPowerSeries.subst (assocLeftFam F) (F i)
    = MvPowerSeries.subst (assocRightFam F) (F i)

namespace FormalGroupLaw

variable {O ι} (Φ : FormalGroupLaw O ι)

/-! ### `HasSubst` witnesses for the axiom substitutions -/

section hasSubst

variable [Finite ι]

-- `HasSubst` for the axiom families
lemma hasSubst_unitR :
    MvPowerSeries.HasSubst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

lemma hasSubst_unitL :
    MvPowerSeries.HasSubst
      (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : ι ⊕ ι → MvPowerSeries ι O) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

lemma hasSubst_swap :
    MvPowerSeries.HasSubst
      (fun s : ι ⊕ ι ↦ (MvPowerSeries.X s.swap : MvPowerSeries (ι ⊕ ι) O)) :=
  hasSubst_of_constantCoeff_zero fun s ↦ by simp

lemma hasSubst_emb12 :
    MvPowerSeries.HasSubst
      (Sum.elim (fun a : ι ↦ X (Sum.inl a)) (fun b : ι ↦ X (Sum.inr (Sum.inl b)))
        : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

lemma hasSubst_emb23 :
    MvPowerSeries.HasSubst
      (Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a)))
        (fun b : ι ↦ X (Sum.inr (Sum.inr b)))
        : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

lemma hasSubst_assocLeft :
    MvPowerSeries.HasSubst (assocLeftFam Φ.F) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · exact constantCoeff_subst_eq_zero (hasSubst_emb12 (O := O) (ι := ι))
      (by rintro (a | b) <;> simp) (Φ.zero_constantCoeff j)
  · simp

lemma hasSubst_assocRight :
    MvPowerSeries.HasSubst (assocRightFam Φ.F) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · simp
  · exact constantCoeff_subst_eq_zero (hasSubst_emb23 (O := O) (ι := ι))
      (by rintro (a | b) <;> simp) (Φ.zero_constantCoeff j)

end hasSubst

/-! ### The differential (Jacobian) matrix at the origin -/

section diffMatrix

/-- The Jacobian matrix `M(X) = (∂F/∂Y)(X, 0)` of a formal group law, with entries in
the power series ring in the `X`-block of variables. -/
noncomputable def diffMatrix : Matrix ι ι (MvPowerSeries ι O) :=
  Matrix.of fun i j ↦ MvPowerSeries.subst
    (Sum.elim MvPowerSeries.X fun _ ↦ 0 : ι ⊕ ι → MvPowerSeries ι O)
    (MvPowerSeries.pderiv (Sum.inr j) (Φ.F i))

theorem diffMatrix_apply (i j : ι) :
    Φ.diffMatrix i j = MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : ι ⊕ ι → MvPowerSeries ι O)
      (MvPowerSeries.pderiv (Sum.inr j) (Φ.F i)) :=
  rfl

variable [DecidableEq ι]

/-- `M(0)` is the identity matrix. -/
theorem diffMatrix_map_constantCoeff [Finite ι] :
    Φ.diffMatrix.map (constantCoeff (R := O)) = 1 := by
  cases nonempty_fintype ι
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply]
  have hch := MvPowerSeries.pderiv_subst (hasSubst_unitL (O := O) (ι := ι)) j (Φ.F i)
  rw [Φ.zero_add' i, MvPowerSeries.pderiv_X] at hch
  have hsum : ∑ t : ι ⊕ ι,
      MvPowerSeries.subst (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : ι ⊕ ι → _)
        (MvPowerSeries.pderiv t (Φ.F i))
      * MvPowerSeries.pderiv j
        ((Sum.elim (fun _ ↦ 0) MvPowerSeries.X : ι ⊕ ι → MvPowerSeries ι O) t)
      = MvPowerSeries.subst (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : ι ⊕ ι → _)
        (MvPowerSeries.pderiv (Sum.inr j) (Φ.F i)) := by
    rw [Fintype.sum_sum_type]
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  rw [hsum] at hch
  have h1 : constantCoeff (Φ.diffMatrix i j)
      = constantCoeff (MvPowerSeries.pderiv (Sum.inr j) (Φ.F i)) :=
    MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hasSubst_unitR
      (by rintro (a | a) <;> simp) _
  have h2 : constantCoeff (MvPowerSeries.subst
        (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : ι ⊕ ι → MvPowerSeries ι O)
        (MvPowerSeries.pderiv (Sum.inr j) (Φ.F i)))
      = constantCoeff (MvPowerSeries.pderiv (Sum.inr j) (Φ.F i)) :=
    MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hasSubst_unitL
      (by rintro (a | a) <;> simp) _
  rw [h1, ← h2, ← hch]
  simp [Pi.single_apply]

/-- The Jacobian matrix of a formal group law is invertible. -/
theorem isUnit_diffMatrix [Fintype ι] : IsUnit Φ.diffMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : constantCoeff Φ.diffMatrix.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Φ.diffMatrix_map_constantCoeff,
      Matrix.det_one]
  rw [MvPowerSeries.isUnit_iff_constantCoeff, hdet]
  exact isUnit_one

/-- The constant term of the inverse Jacobian matrix is the identity. -/
theorem diffMatrixInv_map_constantCoeff [Fintype ι] :
    Φ.diffMatrix⁻¹.map (constantCoeff (R := O)) = 1 := by
  have hNM : Φ.diffMatrix⁻¹ * Φ.diffMatrix = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp Φ.isUnit_diffMatrix)
  have hmap := congrArg
    (fun A : Matrix ι ι (MvPowerSeries ι O) ↦ A.map (constantCoeff (R := O))) hNM
  simp only [Matrix.map_mul, Matrix.map_one (constantCoeff (R := O)) (map_zero _)
    (map_one _)] at hmap
  rwa [Φ.diffMatrix_map_constantCoeff, mul_one] at hmap

end diffMatrix

/-! ### Base change along a ring homomorphism -/

section baseChange

variable {O' : Type*} [CommRing O'] [Finite ι]

/-- Base change of a formal group law along a ring homomorphism `f : O →+* O'`: apply
`MvPowerSeries.map f` to each defining power series. -/
noncomputable def map (f : O →+* O') (Φ : FormalGroupLaw O ι) : FormalGroupLaw O' ι where
  F i := MvPowerSeries.map f (Φ.F i)
  zero_constantCoeff i := by rw [constantCoeff_map, Φ.zero_constantCoeff i, map_zero]
  add_zero' i := by
    have h := congrArg (MvPowerSeries.map f) (Φ.add_zero' i)
    rw [MvPowerSeries.map_subst (hasSubst_unitR), MvPowerSeries.map_X] at h
    rw [← h]
    congr 1
    funext s
    rcases s with j | j <;> simp
  zero_add' i := by
    have h := congrArg (MvPowerSeries.map f) (Φ.zero_add' i)
    rw [MvPowerSeries.map_subst (hasSubst_unitL), MvPowerSeries.map_X] at h
    rw [← h]
    congr 1
    funext s
    rcases s with j | j <;> simp
  comm' i := by
    have h := congrArg (MvPowerSeries.map f) (Φ.comm' i)
    rw [MvPowerSeries.map_subst (hasSubst_swap)] at h
    rw [← h]
    congr 1
    funext s
    simp
  assoc' i := by
    have hL : (fun s ↦ MvPowerSeries.map f (assocLeftFam Φ.F s))
        = assocLeftFam (fun j ↦ MvPowerSeries.map f (Φ.F j)) := by
      funext s
      rcases s with j | j
      · rw [assocLeftFam_inl, assocLeftFam_inl,
          MvPowerSeries.map_subst (hasSubst_emb12 (O := O) (ι := ι))]
        congr 1
        funext s'; rcases s' with a | b <;> simp
      · simp
    have hR : (fun s ↦ MvPowerSeries.map f (assocRightFam Φ.F s))
        = assocRightFam (fun j ↦ MvPowerSeries.map f (Φ.F j)) := by
      funext s
      rcases s with j | j
      · simp
      · rw [assocRightFam_inr, assocRightFam_inr,
          MvPowerSeries.map_subst (hasSubst_emb23 (O := O) (ι := ι))]
        congr 1
        funext s'; rcases s' with a | b <;> simp
    have h := congrArg (MvPowerSeries.map f) (Φ.assoc' i)
    rw [MvPowerSeries.map_subst (hasSubst_assocLeft Φ),
      MvPowerSeries.map_subst (hasSubst_assocRight Φ), hL, hR] at h
    exact h

@[simp]
theorem F_map (f : O →+* O') (i : ι) :
    (Φ.map f).F i = MvPowerSeries.map f (Φ.F i) := rfl

/-- The differential matrix commutes with base change. -/
theorem diffMatrix_map (f : O →+* O') :
    (Φ.map f).diffMatrix = Φ.diffMatrix.map (MvPowerSeries.map f) := by
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.map_apply]
  have hfam : (fun s ↦ MvPowerSeries.map f ((Sum.elim MvPowerSeries.X (fun _ ↦ 0)
        : ι ⊕ ι → MvPowerSeries ι O) s))
      = (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O') := by
    funext s; rcases s with a | a <;> simp
  calc (Φ.map f).diffMatrix i j
      = MvPowerSeries.subst (Sum.elim MvPowerSeries.X (fun _ ↦ 0)
            : ι ⊕ ι → MvPowerSeries ι O')
          (MvPowerSeries.map f (pderiv (Sum.inr j) (Φ.F i))) := by
        rw [diffMatrix_apply, MvPowerSeries.map_pderiv]; rfl
    _ = MvPowerSeries.map f (MvPowerSeries.subst
          (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O)
          (pderiv (Sum.inr j) (Φ.F i))) := by
        rw [MvPowerSeries.map_subst hasSubst_unitR, hfam]
    _ = MvPowerSeries.map f (Φ.diffMatrix i j) := by rw [diffMatrix_apply]

variable [Fintype ι] [DecidableEq ι]

/-- The inverse differential matrix commutes with base change: in particular, base change
of an invertible differential matrix stays invertible. This is the integrality statement
for the invariant differential — the entries of `M⁻¹` are already defined over `O`. -/
theorem diffMatrixInv_map (f : O →+* O') :
    (Φ.map f).diffMatrix⁻¹ = Φ.diffMatrix⁻¹.map (MvPowerSeries.map f) := by
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mp Φ.isUnit_diffMatrix
  refine Matrix.inv_eq_left_inv ?_
  rw [diffMatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.nonsing_inv_mul _ hunit, map_one]

end baseChange

end FormalGroupLaw

end ChabautyColeman

end
