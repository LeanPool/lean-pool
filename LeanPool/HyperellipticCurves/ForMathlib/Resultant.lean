/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Bézout certificates from unit resultants

`Polynomial.exists_bezout_of_isUnit_resultant`: over any commutative ring, if the
`(m, n)`-resultant of `u` and `g` is a unit, then `s·u + t·g = 1` is solvable with `deg s < n`,
`deg t < m` (a degree-controlled version of `Polynomial.isUnit_resultant_iff_isCoprime`;
Mathlib-bound). This is how the Cantor pipeline obtains its Bézout certificates: a resultant of
universal pipeline data that does not vanish at a specialization to a field yields a certificate
there. `Polynomial.isUnit_resultant_of_isCoprime` is the converse at a monic first member:
coprimality makes the padded resultant a unit, so a field specialization carrying a Bézout
certificate keeps these resultants nonzero. `Polynomial.separable_of_isUnit_resultant` is the
Bézout certificate read as separability: a polynomial whose discriminant-style resultant
`Res(f, f')` is a unit is separable. Over a local ring this gives
`Polynomial.separable_map_of_separable_residue`: separability of the reduction of a monic
polynomial modulo the maximal ideal lifts through any ring homomorphism out of the local ring.

The remaining sections concern Mathlib's polynomial discriminant `Polynomial.discr`.
`Polynomial.discrOfDegree f n` is the discriminant of `f` viewed as a polynomial of degree `n`
(the discriminant of the binary form `Z ^ n * f (X / Z)`): Mathlib's discriminant matrix
`Polynomial.sylvesterDeriv` with the degree replaced by `n`. It is a polynomial in the coefficients
of `f` up to degree `n`, so it commutes with every ring homomorphism
(`Polynomial.discrOfDegree_map`), and the **drop-by-one formula**
`Polynomial.discrOfDegree_add_two` — `D_{n+2}(f) = a_{n+1}^2 · D_{n+1}(f)` for `deg f ≤ n + 1`,
proved by expanding the modified Sylvester matrix along its normalized last row, whose two
minors are padded Sylvester matrices (`Polynomial.det_submatrix_sylvester_succ_left`/`_right`) —
identifies it with `discr f`, `leadingCoeff f ^ 2 * discr f` or `0` according to the degree of `f`.
This is the discriminant condition of `HyperellipticCurve`, which therefore behaves well under
reduction. `Polynomial.discr_map` (the discriminant commutes with a degree-preserving ring
homomorphism) is a corollary, and `Polynomial.isUnit_discr_iff_separable` says that for a unit
leading coefficient the discriminant is a unit if and only if the polynomial is separable.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] {u g : R[X]} {m n : ℕ}

/-- **Bézout certificate from a unit resultant**, with degree control: if the
`(m, n)`-resultant of `u` and `g` is a unit, there are `s, t` with
`s·u + t·g = 1`, `deg s < n` and `deg t < m`. -/
theorem exists_bezout_of_isUnit_resultant (hu : u.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (H : m ≠ 0 ∨ n ≠ 0) (hres : IsUnit (u.resultant g m n)) :
    ∃ s t : R[X], s.degree < (n : WithBot ℕ) ∧ t.degree < (m : WithBot ℕ)
      ∧ s * u + t * g = 1 := by
  obtain ⟨p, q, hp, hq, he⟩ := exists_mul_add_mul_eq_C_resultant u g hu hg H
  obtain ⟨c, hc⟩ := hres.exists_left_inv
  have hCle : ∀ r : R[X], (C c * r).degree ≤ r.degree := fun r ↦
    calc (C c * r).degree ≤ (C c).degree + r.degree := degree_mul_le _ _
      _ ≤ 0 + r.degree := by gcongr; exact degree_C_le
      _ = r.degree := zero_add _
  refine ⟨C c * p, C c * q, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (hCle p) hp
  · exact lt_of_le_of_lt (hCle q) hq
  · calc C c * p * u + C c * q * g = C c * (u * p + g * q) := by ring
      _ = 1 := by rw [he, ← map_mul, hc, map_one]

/-- **A coprime pair has unit resultant**, at the exact degree of the monic member and any
degree bound for the other: the converse supplier for
`Polynomial.exists_bezout_of_isUnit_resultant`. -/
theorem isUnit_resultant_of_isCoprime (hu : u.Monic) (hg : g.natDegree ≤ n)
    (hcop : IsCoprime u g) : IsUnit (u.resultant g u.natDegree n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = g.natDegree + k := ⟨n - g.natDegree, by lia⟩
  rw [resultant_add_right_deg u g u.natDegree g.natDegree k le_rfl, coeff_natDegree,
    hu.leadingCoeff, one_pow, one_mul]
  exact (isUnit_resultant_iff_isCoprime hu).mpr hcop

/-- **A polynomial with unit resultant `Res(f, f')` is separable**: the Bézout certificate of
`Polynomial.exists_bezout_of_isUnit_resultant` is a separability certificate. -/
theorem separable_of_isUnit_resultant {f : R[X]} {d : ℕ} (hf : f.natDegree ≤ d) (hd : d ≠ 0)
    (hres : IsUnit (f.resultant f.derivative d d)) : f.Separable :=
  let ⟨s, t, _, _, hst⟩ := exists_bezout_of_isUnit_resultant hf
    ((natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hf)) (.inl hd) hres
  ⟨s, t, hst⟩

open IsLocalRing in
/-- **Separability of the reduction lifts through a local ring**: if the reduction of a
monic polynomial `f` of positive degree over a local ring `O` modulo the maximal ideal is
separable, then the image of `f` under any ring homomorphism out of `O` is separable — the
residue resultant of `f` with `f'` is a unit, hence the resultant of `f` with `f'` is a
unit in `O` and its image provides the Bézout certificate. -/
theorem separable_map_of_separable_residue {O : Type*} [CommRing O] [IsLocalRing O]
    {S : Type*} [CommRing S] (φ : O →+* S) {f : O[X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hsep : (f.map (residue O)).Separable) : (f.map φ).Separable := by
  set d := f.natDegree
  have hres : IsUnit ((f.map (residue O)).resultant (f.map (residue O)).derivative
      (f.map (residue O)).natDegree d) :=
    isUnit_resultant_of_isCoprime (hf.map _)
      ((natDegree_derivative_le _).trans (by rw [hf.natDegree_map]; exact Nat.sub_le _ _)) hsep
  rw [hf.natDegree_map, derivative_map, resultant_map_map _ _ d d] at hres
  have hresO : IsUnit (f.resultant f.derivative d d) :=
    notMem_maximalIdeal.mp fun hm ↦ hres.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
  refine separable_of_isUnit_resultant natDegree_map_le hd.ne' ?_
  rw [derivative_map, resultant_map_map _ _ d d]
  exact hresO.map φ

/-! ### Minors of Sylvester matrices -/

section minors

variable {f : R[X]}

/-- Deleting the last row and the last `g`-column of `sylvester f g (m + 1) (n + 1)` leaves
`sylvester f g m (n + 1)` when `f` has degree at most `m`. -/
theorem det_submatrix_sylvester_succ_left (hf : f.natDegree ≤ m) :
    ((sylvester f g (m + 1) (n + 1)).submatrix (Fin.last _).succAbove
      ((Fin.last m).castAdd (n + 1)).succAbove).det = resultant f g m (n + 1) := by
  rw [resultant, ← Matrix.det_reindex_self (finCongr (show m + 1 + n = m + (n + 1) by lia))]
  congr 1
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
    Fin.succAbove_last]
  induction j using Fin.addCases with
  | left j =>
    rw [show ((Fin.last m).castAdd (n + 1)).succAbove (Fin.cast _ (j.castAdd (n + 1))) =
        (Fin.castSucc j).castAdd (n + 1) from ?_]
    · simp [sylvester, Fin.addCases_left]
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
      exact Fin.ext rfl
  | right j =>
    rw [show ((Fin.last m).castAdd (n + 1)).succAbove (Fin.cast _ (j.natAdd m)) =
        j.natAdd (m + 1) from ?_]
    · simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_castSucc, Fin.val_cast,
        Set.mem_Icc]
      split_ifs <;> first | rfl | lia | exact coeff_eq_zero_of_natDegree_lt (by lia)
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def])]
      exact Fin.ext (by simp; lia)

/-- Deleting the last row and the last column of `sylvester f g m (n + 1)` leaves
`sylvester f g m n` when `g` has degree at most `n`. -/
theorem det_submatrix_sylvester_succ_right (hg : g.natDegree ≤ n) :
    ((sylvester f g m (n + 1)).submatrix (Fin.last _).succAbove (Fin.last _).succAbove).det =
      resultant f g m n := by
  rw [resultant]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_last]
  induction j using Fin.addCases with
  | left j =>
    rw [show Fin.castSucc (j.castAdd n) = j.castAdd (n + 1) from Fin.ext rfl]
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castSucc, Set.mem_Icc]
    split_ifs <;> first | rfl | lia | exact coeff_eq_zero_of_natDegree_lt (by lia)
  | right j =>
    rw [show Fin.castSucc (j.natAdd m) = (Fin.castSucc j).natAdd m from Fin.ext rfl]
    simp [sylvester, Fin.addCases_right]

end minors

/-! ### The discriminant of a polynomial viewed as a polynomial of given degree -/

section discr

variable {S : Type*} [CommRing S] {f : R[X]}

/-- `Polynomial.sylvesterDeriv` for `f` viewed as a polynomial of degree `n`: the Sylvester matrix
of `f'` and `f` padded to the degrees `n - 1` and `n`, with the last row normalized as in
`Polynomial.sylvesterDeriv`. At `n = f.natDegree` it is `f.sylvesterDeriv` definitionally. -/
noncomputable def sylvesterDerivOfDegree (f : R[X]) (n : ℕ) :
    Matrix (Fin (n - 1 + n)) (Fin (n - 1 + n)) R :=
  if hn : n = 0 then 0
  else (f.derivative.sylvester f (n - 1) n).updateRow ⟨2 * n - 2, by lia⟩
    (fun j ↦ if ↑j = n - 2 then 1 else if ↑j = 2 * n - 2 then (n : R) else 0)

theorem sylvesterDerivOfDegree_natDegree (f : R[X]) :
    f.sylvesterDerivOfDegree f.natDegree = f.sylvesterDeriv := rfl

lemma sylvesterDerivOfDegree_map (φ : R →+* S) (f : R[X]) (n : ℕ) :
    (f.map φ).sylvesterDerivOfDegree n = φ.mapMatrix (f.sylvesterDerivOfDegree n) := by
  simp only [sylvesterDerivOfDegree]
  split_ifs
  · simp
  · rw [RingHom.mapMatrix_apply, Matrix.map_updateRow, derivative_map, sylvester_map_map,
      RingHom.mapMatrix_apply]
    congr 1
    ext j
    simp [apply_ite φ]

/-- `sylvesterDerivOfDegree f (n + 2)` in the form used to expand its determinant: the last row is
the unit vector at the last `f`-column plus `n + 2` times the unit vector at the last
`f'`-column. -/
lemma sylvesterDerivOfDegree_add_two (f : R[X]) (n : ℕ) :
    f.sylvesterDerivOfDegree (n + 2) =
      (f.derivative.sylvester f (n + 1) (n + 1 + 1)).updateRow (Fin.last _)
        (Pi.single ((Fin.last n).castAdd (n + 1 + 1)) 1 +
          ((n + 2 : ℕ) : R) • Pi.single (Fin.last _) 1) := by
  ext i j
  rw [sylvesterDerivOfDegree, dite_eq_right (by lia)]
  simp only [Matrix.updateRow_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
    Fin.val_castAdd, Fin.val_last, Nat.add_eq, smul_eq_mul]
  split_ifs <;> first | rfl | lia | simp

/-- The discriminant of `f` viewed as a polynomial of degree `n`, i.e. the discriminant of the
binary form `Z ^ n * f (X / Z)` of degree `n` (for `f.natDegree ≤ n`): the determinant of
`Polynomial.sylvesterDerivOfDegree f n`, with the sign convention of `Polynomial.discr`. It depends
only on the coefficients of `f` in degrees `≤ n`, hence commutes with every ring homomorphism
(`Polynomial.discrOfDegree_map`); it equals `f.discr` at `n = f.natDegree`,
`f.leadingCoeff ^ 2 * f.discr` at `n = f.natDegree + 1` and `0` for larger `n`
(`Polynomial.discrOfDegree_add_two`). -/
noncomputable def discrOfDegree (f : R[X]) (n : ℕ) : R :=
  (f.sylvesterDerivOfDegree n).det * (-1) ^ (n * (n - 1) / 2)

@[simp]
theorem discrOfDegree_natDegree (f : R[X]) : f.discrOfDegree f.natDegree = f.discr := rfl

theorem discrOfDegree_of_natDegree_eq (h : f.natDegree = n) : f.discrOfDegree n = f.discr :=
  h ▸ rfl

@[simp] theorem discrOfDegree_zero (f : R[X]) : f.discrOfDegree 0 = 1 := by
  simp [discrOfDegree, sylvesterDerivOfDegree]

@[simp] theorem discrOfDegree_one (f : R[X]) : f.discrOfDegree 1 = 1 := by
  simp [discrOfDegree, sylvesterDerivOfDegree, Matrix.det_unique]

/-- The discriminant at a fixed degree commutes with every ring homomorphism (in contrast to
`Polynomial.discr_map`, which needs the degree to be preserved). -/
theorem discrOfDegree_map (φ : R →+* S) (f : R[X]) (n : ℕ) :
    (f.map φ).discrOfDegree n = φ (f.discrOfDegree n) := by
  rw [discrOfDegree, discrOfDegree, sylvesterDerivOfDegree_map, ← RingHom.map_det]
  simp

private lemma det_sylvesterDerivOfDegree_add_two (hf : f.natDegree ≤ n + 1) :
    (f.sylvesterDerivOfDegree (n + 2)).det =
      (-1) ^ (n + 1) * f.coeff (n + 1) * resultant f.derivative f n (n + 1) := by
  have hf' : f.derivative.natDegree ≤ n := (natDegree_derivative_le f).trans (by lia)
  rw [sylvesterDerivOfDegree_add_two, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    ← Matrix.adjugate_apply, ← Matrix.adjugate_apply, Matrix.adjugate_fin_succ_eq_det_submatrix,
    Matrix.adjugate_fin_succ_eq_det_submatrix, det_submatrix_sylvester_succ_left hf',
    det_submatrix_sylvester_succ_right hf, resultant_add_right_deg f.derivative f n (n + 1) 1 hf,
    resultant_add_left_deg f.derivative f n (n + 1) (k := 1) hf', coeff_derivative]
  have h1 : (-1 : R) ^ (n + 1 + (n + 1) + n) = (-1) ^ n := by
    rw [show n + 1 + (n + 1) + n = n + 2 * (n + 1) by ring, pow_add, pow_mul]
    simp
  have h2 : (-1 : R) ^ (n + 1 + (n + 1) + (n + 1 + (n + 1))) = 1 := by
    rw [show n + 1 + (n + 1) + (n + 1 + (n + 1)) = 2 * (2 * (n + 1)) by ring, pow_mul]
    simp
  simp only [Fin.val_last, Fin.val_castAdd, Nat.add_eq, h1, h2, pow_one]
  push_cast
  ring

/-- **Drop-by-one formula**: the discriminant of `f` as a polynomial of degree `n + 2` is the
square of its coefficient in degree `n + 1` times its discriminant as a polynomial of degree
`n + 1`. (This fails for `n + 1` in place of `n + 2`: `discrOfDegree (C c) 1 = 1`.) -/
theorem discrOfDegree_add_two (hf : f.natDegree ≤ n + 1) :
    f.discrOfDegree (n + 2) = f.coeff (n + 1) ^ 2 * f.discrOfDegree (n + 1) := by
  rw [discrOfDegree, det_sylvesterDerivOfDegree_add_two hf]
  rcases hf.lt_or_eq with hlt | heq
  · simp [coeff_eq_zero_of_natDegree_lt hlt]
  have hres := resultant_deriv (natDegree_pos_iff_degree_pos.mp (show 0 < f.natDegree by lia))
  rw [heq, Nat.add_sub_cancel] at hres
  have hlc : f.coeff (n + 1) = f.leadingCoeff := by rw [leadingCoeff, heq]
  have hexp : (n + 2) * (n + 2 - 1) / 2 = (n + 1) * n / 2 + (n + 1) := by
    rw [show n + 2 - 1 = n + 1 from rfl, show (n + 2) * (n + 1) = (n + 1) * n + (n + 1) * 2 by ring,
      Nat.add_mul_div_right _ _ two_pos]
  rw [resultant_comm, hres, ← discrOfDegree_of_natDegree_eq heq, hlc, hexp, pow_add,
    (Nat.even_mul_succ_self n).neg_one_pow]
  have hs : (-1 : R) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have ht : (-1 : R) ^ ((n + 1) * n / 2) * (-1) ^ ((n + 1) * n / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (f.leadingCoeff ^ 2 * f.discrOfDegree (n + 1) *
    ((-1 : R) ^ ((n + 1) * n / 2)) ^ 2) * hs + (f.leadingCoeff ^ 2 * f.discrOfDegree (n + 1)) * ht

/-- The discriminant of a nonconstant `f` as a polynomial of degree `natDegree f + 1` is
`leadingCoeff f ^ 2 * discr f`. -/
theorem discrOfDegree_natDegree_add_one (hf : 0 < f.natDegree) :
    f.discrOfDegree (f.natDegree + 1) = f.leadingCoeff ^ 2 * f.discr := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hf.ne'
  rw [hk, discrOfDegree_add_two hk.le, ← hk, coeff_natDegree, discrOfDegree_natDegree]

theorem discrOfDegree_eq_zero_of_natDegree_add_two_le (h : f.natDegree + 2 ≤ n) :
    f.discrOfDegree n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
  rw [discrOfDegree_add_two (by lia), coeff_eq_zero_of_natDegree_lt (by lia)]
  simp

theorem le_natDegree_add_one_of_isUnit_discrOfDegree [Nontrivial R]
    (h : IsUnit (f.discrOfDegree n)) : n ≤ f.natDegree + 1 := by
  by_contra! hn
  exact h.ne_zero (discrOfDegree_eq_zero_of_natDegree_add_two_le hn)

/-- For a polynomial with unit leading coefficient, the discriminant as a polynomial of degree
`natDegree f` or `natDegree f + 1` is a unit if and only if the discriminant is. -/
theorem isUnit_discrOfDegree_iff_isUnit_discr (hn : f.natDegree ≤ n) (hn' : n ≤ f.natDegree + 1)
    (hlc : IsUnit f.leadingCoeff) : IsUnit (f.discrOfDegree n) ↔ IsUnit f.discr := by
  rcases hn.eq_or_lt with rfl | hlt
  · rw [discrOfDegree_natDegree]
  obtain rfl : n = f.natDegree + 1 := by lia
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0
    simp
  · rw [discrOfDegree_natDegree_add_one h0, (hlc.pow 2).mul_left_iff]

/-- If the discriminant of `f` as a polynomial of some degree `≥ natDegree f` is a unit, so is the
discriminant of `f`. -/
theorem isUnit_discr_of_isUnit_discrOfDegree (hf : f.natDegree ≤ n)
    (h : IsUnit (f.discrOfDegree n)) : IsUnit f.discr := by
  rcases lt_or_ge n (f.natDegree + 2) with hn | hn
  · rcases hf.eq_or_lt with rfl | hlt
    · rwa [discrOfDegree_natDegree] at h
    obtain rfl : n = f.natDegree + 1 := by lia
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0
      simp
    · rw [discrOfDegree_natDegree_add_one h0] at h
      exact (IsUnit.mul_iff.mp h).2
  · rw [discrOfDegree_eq_zero_of_natDegree_add_two_le hn, isUnit_zero_iff] at h
    have := subsingleton_of_zero_eq_one h
    exact isUnit_of_subsingleton _

/-- If the discriminant of a nonconstant `f` as a polynomial of degree `natDegree f + 1` is a unit,
its leading coefficient is a unit. -/
theorem isUnit_leadingCoeff_of_isUnit_discrOfDegree (hf : 0 < f.natDegree)
    (h : IsUnit (f.discrOfDegree (f.natDegree + 1))) : IsUnit f.leadingCoeff := by
  rw [discrOfDegree_natDegree_add_one hf, IsUnit.mul_iff, isUnit_pow_iff two_ne_zero] at h
  exact h.1

/-- The discriminant commutes with a ring homomorphism that preserves the degree. -/
theorem discr_map (φ : R →+* S) (h : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  rw [← discrOfDegree_natDegree, h, discrOfDegree_map, discrOfDegree_natDegree]

/-- The discriminant of a monic polynomial commutes with any ring homomorphism into a nontrivial
ring. -/
theorem Monic.discr_map (hf : f.Monic) (φ : R →+* S) [Nontrivial S] :
    (f.map φ).discr = φ f.discr :=
  Polynomial.discr_map φ (hf.natDegree_map φ)

/-- For a monic polynomial, the padded resultant `Res(f, f', n, n - 1)` of
`Polynomial.resultant_deriv` is a unit if and only if `f` is separable. The padding matters: in
characteristic dividing `n` the derivative has degree below `n - 1`. -/
lemma Monic.isUnit_resultant_derivative_iff (hf : f.Monic) :
    IsUnit (resultant f f.derivative f.natDegree (f.natDegree - 1)) ↔ f.Separable := by
  obtain ⟨k, hk⟩ : ∃ k, f.natDegree - 1 = f.derivative.natDegree + k :=
    ⟨_, (Nat.add_sub_cancel' (natDegree_derivative_le f)).symm⟩
  rw [hk, resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree k le_rfl,
    hf.coeff_natDegree, one_pow, one_mul, isUnit_resultant_iff_isCoprime hf, ← separable_def]

/-- A polynomial with unit leading coefficient has unit discriminant if and only if it is
separable. -/
theorem isUnit_discr_iff_separable (hlc : IsUnit f.leadingCoeff) :
    IsUnit f.discr ↔ f.Separable := by
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0
    rw [leadingCoeff_C] at hlc
    simp [separable_C, hlc]
  obtain ⟨c, hc⟩ := hlc.exists_left_inv
  have hcu : IsUnit c := .of_mul_eq_one _ hc
  have hmonic : (C c * f).Monic := by rw [Monic.def, leadingCoeff_C_mul_of_isUnit hcu, hc]
  have hsep : (C c * f).Separable ↔ f.Separable := by
    rw [separable_def, separable_def, derivative_C_mul,
      isCoprime_mul_unit_left_left (isUnit_C.mpr hcu),
      isCoprime_mul_unit_left_right (isUnit_C.mpr hcu)]
  rw [← hsep, ← hmonic.isUnit_resultant_derivative_iff, natDegree_C_mul_of_isUnit hcu,
    derivative_C_mul, resultant_C_mul_left, resultant_C_mul_right,
    resultant_deriv (natDegree_pos_iff_degree_pos.mp h0), (hcu.pow _).mul_left_iff,
    (hcu.pow _).mul_left_iff, ((isUnit_one.neg.pow _ : IsUnit ((-1 : R) ^ _)).mul hlc).mul_left_iff]

/-- A monic polynomial has unit discriminant if and only if it is separable. -/
theorem Monic.isUnit_discr_iff (hf : f.Monic) : IsUnit f.discr ↔ f.Separable :=
  isUnit_discr_iff_separable (hf.leadingCoeff ▸ isUnit_one)

end discr

end Polynomial

end
