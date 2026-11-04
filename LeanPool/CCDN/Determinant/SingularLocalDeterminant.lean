/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.LocalDeterminant
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.MvPolynomial.Ideal
import LeanPool.CCDN.Determinant.SingularApproximation
import LeanPool.CCDN.Determinant.SingularTangent
import LeanPool.CCDN.ForMathlib.Matrix

/-! Singular plane-curve local determinant divisibility, obtained from
finite-precision homogeneous generators of the local maximal-ideal filtration. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma sum_fin_zero_pad {A : Type*} [AddCommMonoid A] {r μ : ℕ}
    (h : r ≤ μ) (f : Fin r → A) :
    (∑ i : Fin μ, if hi : i.val < r then f ⟨i.val, hi⟩ else 0) = ∑ j, f j := by
  classical
  let J := Finset.univ.image (Fin.castLE h)
  have hsum : (∑ i : Fin μ, if hi : i.val < r then f ⟨i.val, hi⟩ else 0) =
      ∑ i ∈ J, if hi : i.val < r then f ⟨i.val, hi⟩ else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ J)
    intro i _ hi
    have hn : ¬ i.val < r := by
      intro hit
      apply hi
      exact Finset.mem_image.mpr ⟨⟨i.val, hit⟩, Finset.mem_univ _, rfl⟩
    simp only [dite_eq_right hn]
  rw [hsum]
  dsimp [J]
  rw [Finset.sum_image (fun _ _ _ _ he => Fin.castLE_injective h he)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.val_castLE, dite_eq_left j.isLt]

/-- Every square evaluation determinant of integral zeros in one singular
residue class has the repeated-weight multiplicity exponent. The curve's
multiplicity is determined by its reduction. -/
theorem singular_plane_pow_dvd_det_mod {p μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0)
    (x : Fin s → Fin 2 → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j)
    (hfx : ∀ i, (p : ℤ) ^ multiplicityExponent s μ ∣ eval (x i) f)
    (F : Fin s → MvPolynomial (Fin 2) ℤ) :
    (p : ℤ) ^ multiplicityExponent s μ ∣ (Matrix.of fun i j => eval (x i) (F j)).det := by
  classical
  let N := multiplicityExponent s μ
  obtain ⟨r, g, hr, hg, happrox⟩ := exists_singular_plane_approximation_mod f hf hμ
  choose c hc using fun j => happrox N (F j)
  let G (k : Fin N) (j : Fin μ) : MvPolynomial (Fin 2) ℤ :=
    if hj : j.val < r k.val then g k.val ⟨j.val, hj⟩ else 0
  let Cc (l : Fin s) (k : Fin N) (j : Fin μ) : ℤ :=
    if hj : j.val < r k.val then c l k ⟨j.val, hj⟩ else 0
  have hG (k : Fin N) (j : Fin μ) : (G k j).IsHomogeneous k.val := by
    dsimp [G]
    split
    · exact hg _ _
    · exact isHomogeneous_zero _ _ _
  have hdiv (i : Fin s) (z : Fin (N * μ)) :
      (p : ℤ) ^ (z.val / μ) ∣ eval (x i) (G z.divNat z.modNat) := by
    exact origin_power_eval_dvd (p : ℤ) (x i) (hx i)
      (homogeneous_mem_origin_power (hG z.divNat z.modNat))
  choose U₀ hU using hdiv
  let U : Matrix (Fin s) (Fin (N * μ)) ℤ := U₀
  let V : Matrix (Fin (N * μ)) (Fin s) ℤ :=
    fun z l => (p : ℤ) ^ (z.val / μ) * Cc l z.divNat z.modNat
  have hdet : (p : ℤ) ^ N ∣ (U * V).det :=
    multiplicity_pow_dvd_det_of_factorization U V (p : ℤ) μ
      (fun z l => dvd_mul_right _ _)
  have hprod (i l : Fin s) : (U * V) i l =
      ∑ k : Fin N, ∑ j, c l k j * eval (x i) (g k.val j) := by
    rw [Matrix.mul_apply]
    have he : (∑ z : Fin (N * μ), U i z * V z l) =
        ∑ z : Fin (N * μ), Cc l z.divNat z.modNat * eval (x i) (G z.divNat z.modNat) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hU]
      dsimp [V]
      ring
    rw [he, ← Equiv.sum_comp finProdFinEquiv]
    rw [Fintype.sum_prod_type]
    have hd (k : Fin N) (j : Fin μ) : (finProdFinEquiv (k, j)).divNat = k :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (k, j))
    have hm (k : Fin N) (j : Fin μ) : (finProdFinEquiv (k, j)).modNat = j :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (k, j))
    simp only [hd, hm]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (∑ j : Fin μ, Cc l k j * eval (x i) (G k j)) =
        ∑ j : Fin μ, if hj : j.val < r k.val then
          c l k ⟨j.val, hj⟩ * eval (x i) (g k.val ⟨j.val, hj⟩) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [Cc, G]
      split <;> simp_all
    rw [hp]
    exact sum_fin_zero_pad (hr k.val) (fun j => c l k j * eval (x i) (g k.val j))
  have hd := Matrix.dvd_det_sub_det_of_dvd_sub (Matrix.of fun i j => eval (x i) (F j))
    (U * V) ((p : ℤ) ^ N) (fun i j => by
      rw [Matrix.of_apply, hprod]
      exact hc j (x i) (hfx i) (hx i))
  simpa only [sub_add_cancel] using dvd_add hd hdet

/-- The exact-zero form follows from finite-precision divisibility. -/
theorem singular_plane_pow_dvd_det {p μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0)
    (x : Fin s → Fin 2 → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j)
    (hfx : ∀ i, eval (x i) f = 0) (F : Fin s → MvPolynomial (Fin 2) ℤ) :
    (p : ℤ) ^ multiplicityExponent s μ ∣ (Matrix.of fun i j => eval (x i) (F j)).det := by
  exact singular_plane_pow_dvd_det_mod f hf hμ x hx
    (fun i => by rw [hfx]; exact dvd_zero _) F

end
end CCDN
