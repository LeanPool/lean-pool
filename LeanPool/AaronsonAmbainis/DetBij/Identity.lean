/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.DetBij.Basic

/-!
# DetBij / Identity: the matrices `P`, `U`, `Q'` and the identity `P * M = U * Q'`

`A : Cube ι → Finset ι` is a field of sets; the identity needs `A x` to be a 1-wing of `g` at
every `x` with `g x = true` (this is the only use of the wing property).

The file proves the wing identity (Lemma 3.7 of the paper, `wing_sum`) and parts (i) and (ii)
of Lemma 3.8 (`Pmat_mul_agMatrix`, `constantCoeff_det_Pmat`, `constantCoeff_det_Umat`). The
matrix `Q'` (`Qmat`) is the matrix `Q` of the paper.
-/

@[expose] public section

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `P[x,w] = ∏_{i ∈ Δ(x,w)} (-s_i)` if `Δ(x,w) ⊆ A x`, and `0` otherwise. -/
noncomputable def Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x w => if diffSet x.1 w.1 ⊆ A x.1 then ∏ i ∈ diffSet x.1 w.1, -(X i) else 0

/-- `U` is diagonal with entry `∏_{i ∈ A x} (1 - s_i^2)` at `x`. -/
noncomputable def Umat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  Matrix.diagonal fun x => ∏ i ∈ A x.1, (1 - X i ^ 2)

/-- `Q'[x,z] = M[x,z]` if the agreement set of `x` and `z` is disjoint from `A x`, else `0`. -/
noncomputable def Qmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0

theorem Pmat_apply (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    Pmat g A x w
      = if diffSet x.1 w.1 ⊆ A x.1 then ∏ i ∈ diffSet x.1 w.1, -(X i) else 0 := rfl

theorem Qmat_apply (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x z : Ones g) :
    Qmat g A x z = if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0 := rfl

omit [DecidableEq ι] in
theorem agMatrix_apply (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := rfl

/-! ### The wing identity, coordinate by coordinate -/

/-- The factor of `agMon x z` at coordinate `i`. -/
noncomputable def fAg (x z : Cube ι) (i : ι) : MvPolynomial ι ℤ := if x i = z i then X i else 1

/-- The factor at coordinate `i` of `agMon x' z`, where `x'` is `x` flipped at `i`. -/
noncomputable def gAg (x z : Cube ι) (i : ι) : MvPolynomial ι ℤ := if x i = z i then 1 else X i

omit [DecidableEq ι] in
theorem agMon_eq_prod (x z : Cube ι) : agMon x z = ∏ i, fAg x z i := rfl

omit [Fintype ι] in
theorem fAg_flipSet_of_mem (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∈ S) :
    fAg (flipSet x S) z i = gAg x z i := by
  unfold fAg gAg
  rw [flipSet_apply, ite_eq_left hi]
  cases x i <;> cases z i <;> simp

omit [Fintype ι] in
theorem fAg_flipSet_of_notMem (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∉ S) :
    fAg (flipSet x S) z i = fAg x z i := by
  unfold fAg
  rw [flipSet_apply, ite_eq_right hi]

omit [Fintype ι] [DecidableEq ι] in
/-- A coordinate of the wing contributes `0` if `x_i = z_i` and `1 - s_i^2` otherwise. -/
theorem neg_X_mul_gAg_add_fAg (x z : Cube ι) (i : ι) :
    -(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i
      = if x i = z i then 0 else 1 - (X i : MvPolynomial ι ℤ) ^ 2 := by
  unfold fAg gAg
  split_ifs <;> ring

/-- One term of the wing sum, split into the coordinates in `S`, in `A \ S` and outside `A`. -/
theorem wing_term (x z : Cube ι) {A S : Finset ι} (hSA : S ⊆ A) :
    (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = ((∏ i ∈ S, -(X i : MvPolynomial ι ℤ) * gAg x z i) * ∏ i ∈ A \ S, fAg x z i)
          * ∏ i ∈ Aᶜ, fAg x z i := by
  have h1 : agMon (flipSet x S) z
      = (∏ i ∈ A, fAg (flipSet x S) z i) * ∏ i ∈ Aᶜ, fAg (flipSet x S) z i :=
    (Finset.prod_mul_prod_compl A (fAg (flipSet x S) z)).symm
  have h2 : ∏ i ∈ Aᶜ, fAg (flipSet x S) z i = ∏ i ∈ Aᶜ, fAg x z i :=
    Finset.prod_congr rfl fun i hi =>
      fAg_flipSet_of_notMem x z fun h => (Finset.mem_compl.mp hi) (hSA h)
  have h3 : ∏ i ∈ A, fAg (flipSet x S) z i
      = (∏ i ∈ A \ S, fAg x z i) * ∏ i ∈ S, gAg x z i := by
    rw [← Finset.prod_sdiff hSA]
    congr 1
    · exact Finset.prod_congr rfl fun i hi =>
        fAg_flipSet_of_notMem x z (Finset.mem_sdiff.mp hi).2
    · exact Finset.prod_congr rfl fun i hi => fAg_flipSet_of_mem x z hi
  rw [h1, h2, h3, Finset.prod_mul_distrib]
  ring

/-- The wing identity (Lemma 3.7 of the paper), for an arbitrary set `A` and points `x`, `z`
of the cube. -/
theorem wing_sum (x z : Cube ι) (A : Finset ι) :
    ∑ S ∈ A.powerset, (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = (∏ i ∈ A, (1 - (X i : MvPolynomial ι ℤ) ^ 2))
          * (if Disjoint (agSet x z) A then agMon x z else 0) := by
  have h0 : ∑ S ∈ A.powerset, (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = ∑ S ∈ A.powerset, ((∏ i ∈ S, -(X i : MvPolynomial ι ℤ) * gAg x z i)
          * ∏ i ∈ A \ S, fAg x z i) * ∏ i ∈ Aᶜ, fAg x z i :=
    Finset.sum_congr rfl fun S hS => wing_term x z (Finset.mem_powerset.mp hS)
  rw [h0, ← Finset.sum_mul, ← Finset.prod_add]
  by_cases hd : Disjoint (agSet x z) A
  · have hne : ∀ i ∈ A, ¬ x i = z i := fun i hi h =>
      (Finset.disjoint_left.mp hd (mem_agSet.mpr h)) hi
    have e1 : ∏ i ∈ A, (-(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i)
        = ∏ i ∈ A, (1 - (X i : MvPolynomial ι ℤ) ^ 2) :=
      Finset.prod_congr rfl fun i hi => by
        rw [neg_X_mul_gAg_add_fAg, ite_eq_right (hne i hi)]
    have e2 : agMon x z = ∏ i ∈ Aᶜ, fAg x z i := by
      have e3 : ∏ i ∈ A, fAg x z i = 1 :=
        Finset.prod_eq_one fun i hi => by
          unfold fAg
          rw [ite_eq_right (hne i hi)]
      rw [agMon_eq_prod, ← Finset.prod_mul_prod_compl A (fAg x z), e3, one_mul]
    rw [ite_eq_left hd, e1, e2]
  · obtain ⟨i, hi1, hi2⟩ := Finset.not_disjoint_iff.mp hd
    have e1 : ∏ i ∈ A, (-(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i) = 0 :=
      Finset.prod_eq_zero hi2 (by rw [neg_X_mul_gAg_add_fAg, ite_eq_left (mem_agSet.mp hi1)])
    rw [ite_eq_right hd, mul_zero, e1, zero_mul]

/-! ### The matrix identity -/

/-- `P * M = U * Q'` (Lemma 3.8 (i) of the paper), using the wing property. -/
theorem Pmat_mul_agMatrix (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    Pmat g A * agMatrix g = Umat g A * Qmat g A := by
  refine Matrix.ext fun x z => ?_
  have hR : (Umat g A * Qmat g A) x z
      = (∏ i ∈ A x.1, (1 - (X i : MvPolynomial ι ℤ) ^ 2))
          * (if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0) := by
    unfold Umat
    rw [Matrix.diagonal_mul, Qmat_apply]
  have hL : (Pmat g A * agMatrix g) x z
      = ∑ w ∈ univ.filter (fun w : Ones g => diffSet x.1 w.1 ⊆ A x.1),
          (∏ i ∈ diffSet x.1 w.1, -(X i : MvPolynomial ι ℤ)) * agMon w.1 z.1 := by
    rw [Matrix.mul_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Pmat_apply, agMatrix_apply, ite_mul, zero_mul]
  rw [hL, hR, ← wing_sum]
  refine Finset.sum_bij (fun (w : Ones g) _ => diffSet x.1 w.1) ?_ ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hw).2
  · intro w₁ _ w₂ _ h
    have h' : diffSet x.1 w₁.1 = diffSet x.1 w₂.1 := h
    apply Subtype.ext
    calc w₁.1 = flipSet x.1 (diffSet x.1 w₁.1) := (flipSet_diffSet x.1 w₁.1).symm
      _ = flipSet x.1 (diffSet x.1 w₂.1) := by rw [h']
      _ = w₂.1 := flipSet_diffSet x.1 w₂.1
  · intro S hS
    have hS' : S ⊆ A x.1 := Finset.mem_powerset.mp hS
    refine ⟨⟨flipSet x.1 S, hA x S hS'⟩, ?_, diffSet_flipSet x.1 S⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [diffSet_flipSet]
    exact hS'
  · intro w _
    simp only [flipSet_diffSet]

/-! ### Constant coefficients of `det P` and `det U` -/

theorem constantCoeff_Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    constantCoeff (Pmat g A x w) = if x = w then 1 else 0 := by
  by_cases hxw : x = w
  · subst hxw
    rw [ite_eq_left rfl, Pmat_apply, diffSet_eq_empty_iff.mpr rfl,
      ite_eq_left (Finset.empty_subset _),
      Finset.prod_empty, map_one]
  · rw [ite_eq_right hxw, Pmat_apply]
    split_ifs with h
    · have hne : (diffSet x.1 w.1).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact fun h0 => hxw (Subtype.ext (diffSet_eq_empty_iff.mp h0))
      obtain ⟨i, hi⟩ := hne
      rw [map_prod]
      exact Finset.prod_eq_zero hi (by simp)
    · exact map_zero _

theorem constantCoeff_det_Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Pmat g A).det = 1 := by
  have h1 : (constantCoeff : MvPolynomial ι ℤ →+* ℤ).mapMatrix (Pmat g A) = 1 := by
    refine Matrix.ext fun x w => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    exact constantCoeff_Pmat g A x w
  rw [RingHom.map_det, h1, Matrix.det_one]

theorem constantCoeff_det_Umat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Umat g A).det = 1 := by
  unfold Umat
  rw [Matrix.det_diagonal, map_prod]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  simp

end AaronsonAmbainis.DetBij
