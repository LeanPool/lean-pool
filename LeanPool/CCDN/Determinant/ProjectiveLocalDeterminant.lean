/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Determinant.SingularPlaneChart
import LeanPool.CCDN.Determinant.BlockDeterminant
import LeanPool.CCDN.ForMathlib.Matrix
import LeanPool.CCDN.Height.ProjectiveZeroLocus

/-! Local divisibility for homogeneous evaluation matrices at projective
points. Normalize a unit coordinate modulo the required prime power,
apply the singular affine estimate to the resulting approximate zeros,
then cancel the invertible row factors. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If `x ≡ y` coordinatewise modulo `q`, then `f(x) ≡ f(y)` modulo `q` for every integer polynomial
`f`. -/
lemma dvd_eval_sub_of_dvd_coordinates {σ : Type*} (q : ℤ)
    (x y : σ → ℤ) (hxy : ∀ j, q ∣ x j - y j) (f : MvPolynomial σ ℤ) :
    q ∣ eval x f - eval y f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    simpa only [eval_add, add_sub_add_comm] using dvd_add hf hg
  | mul_X f j hf =>
    rw [eval_mul, eval_mul, eval_X, eval_X]
    have he : eval x f * x j - eval y f * y j =
        (eval x f - eval y f) * x j + eval y f * (x j - y j) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hf _) (dvd_mul_of_dvd_right (hxy j) _)

/-- An integer `a` coprime to `q` has an inverse `u` modulo `q`, itself coprime to `q`. -/
lemma exists_integer_inverse_of_isCoprime {q a : ℤ} (h : IsCoprime q a) :
    ∃ u : ℤ, q ∣ u * a - 1 ∧ IsCoprime q u := by
  obtain ⟨v, u, he⟩ := h
  refine ⟨u, ⟨-v, by linear_combination he⟩, v, a, ?_⟩
  simpa only [mul_comm a u] using he

/-- Unit normalization in the first homogeneous coordinate preserves the
evaluation of a degree-M form, up to the corresponding unit row factor. -/
private lemma projective_chart_eval_congr {M : ℕ} {q u : ℤ}
    (z : Fin 3 → ℤ) (hu : q ∣ u * z 0 - 1)
    (F : MvPolynomial (Fin 3) ℤ) (hF : F.IsHomogeneous M) :
    q ∣ eval (fun j : Fin 2 => u * z j.succ) (affineChart 2 F) -
      u ^ M * eval z F := by
  rw [affineChart_eval, ← homogeneous_eval_smul hF]
  apply dvd_eval_sub_of_dvd_coordinates
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, neg_sub] using
      (show q ∣ -(u * z 0 - 1) from dvd_neg.mpr hu)
  · simp

/-- Projective local determinant estimate in a chart whose first coordinate
is a p-adic unit. The affine multiplicity belongs to the chart equation. -/
private theorem projective_plane_chart_det_divisibility {p μ s d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin 3 → ℤ) (a : Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (affineChart 2 f)) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (affineChart 2 f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i 0))
    (hres : ∀ i j, (p : ℤ) ∣ z i j.succ - a j * z i 0)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ multiplicityExponent s μ ∣
      (Matrix.of fun i j => eval (z i) (F j)).det := by
  classical
  let N := multiplicityExponent s μ
  by_cases hN : N = 0
  · change (p : ℤ) ^ N ∣ _
    simp [hN]
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  let q : ℤ := (p : ℤ) ^ N
  have hpq : (p : ℤ) ∣ q := by
    simpa only [pow_one] using pow_dvd_pow (p : ℤ) hNpos
  have hex (i : Fin s) := exists_integer_inverse_of_isCoprime
    (show IsCoprime q (z i 0) from (hunit i).pow_left)
  choose u hu huc using hex
  let x : Fin s → Fin 2 → ℤ := fun i j => u i * z i j.succ
  have hx (i : Fin s) (j : Fin 2) : (p : ℤ) ∣ x i j - a j := by
    have he : x i j - a j =
        u i * (z i j.succ - a j * z i 0) + a j * (u i * z i 0 - 1) := by
      dsimp [x]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right (hres i j) _)
      (dvd_mul_of_dvd_right (hpq.trans (hu i)) _)
  have hxf (i : Fin s) : q ∣ eval (x i) (affineChart 2 f) := by
    have h := projective_chart_eval_congr (z i) (hu i) f hfhom
    simpa only [hz, mul_zero, sub_zero] using h
  let A := Matrix.of fun i j : Fin s => eval (x i) (affineChart 2 (F j))
  let D := Matrix.of fun i j : Fin s => u i ^ M * eval (z i) (F j)
  have hA : q ∣ A.det :=
    singular_plane_chart_det_divisibility_mod (affineChart 2 f)
      (fun j => affineChart 2 (F j)) x a hf hμ hx hxf
  have hAD : q ∣ A.det - D.det := by
    apply Matrix.dvd_det_sub_det_of_dvd_sub
    intro i j
    exact projective_chart_eval_congr (z i) (hu i) (F j) (hF j)
  have hD : q ∣ D.det := by
    simpa only [sub_sub_cancel] using dvd_sub hA hAD
  have hprod : IsCoprime q (∏ i, u i ^ M) :=
    IsCoprime.prod_right fun i _ => (huc i).pow_right
  have he : D.det = (∏ i, u i ^ M) *
      (Matrix.of fun i j => eval (z i) (F j)).det :=
    Matrix.det_mul_column _ _
  rw [he] at hD
  exact hprod.dvd_of_dvd_mul_left hD

/-- Move coordinate `k` to the first position before taking the affine chart. -/
def projectivePlaneChart (k : Fin 3) (f : MvPolynomial (Fin 3) ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  affineChart 2 (rename (Equiv.swap 0 k) f)

private lemma eval_swap_plane_coordinates (k : Fin 3) (z : Fin 3 → ℤ)
    (f : MvPolynomial (Fin 3) ℤ) :
    eval (z ∘ Equiv.swap 0 k) (rename (Equiv.swap 0 k) f) = eval z f := by
  rw [eval_rename]
  have he : (z ∘ Equiv.swap 0 k) ∘ Equiv.swap 0 k = z := by
    funext j
    simp
  rw [he]

/-- The local projective divisor is available in every coordinate chart. -/
private theorem projective_plane_local_det_divisibility {p μ s d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin 3 → ℤ) (k : Fin 3) (a : Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (projectivePlaneChart k f)) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (projectivePlaneChart k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ multiplicityExponent s μ ∣
      (Matrix.of fun i j => eval (z i) (F j)).det := by
  have h := projective_plane_chart_det_divisibility
    (rename (Equiv.swap 0 k) f) hfhom.rename_isHomogeneous
    (fun j => rename (Equiv.swap 0 k) (F j)) (fun j => (hF j).rename_isHomogeneous)
    (fun i => z i ∘ Equiv.swap 0 k) a hf hμ
    (fun i => by simpa using hunit i)
    (fun i j => by simpa using hres i j)
    (fun i => by rw [eval_swap_plane_coordinates]; exact hz i)
  simpa only [eval_swap_plane_coordinates] using h

/-- Assemble local projective residue classes in their own coordinate charts.
Every maximal minor acquires the sum of their local multiplicity exponents. -/
theorem projective_plane_residue_minorGcd {p c s N d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin 3 → ℤ) (label : Fin s → Fin c)
    (k : Fin c → Fin 3) (a : Fin c → Fin 2 → ℤ) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectivePlaneChart (k i) f)) ∈
        idealOfVars (Fin 2) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i) (map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectivePlaneChart (k i) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i (k (label i))))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 (k (label i)) j.succ) -
      a (label i) j * z i (k (label i)))
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, multiplicityExponent
      (Fintype.card {j : Fin s // label j = i}) (μ i)) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  apply projective_plane_local_det_divisibility f hfhom
    (fun j => F (cols j)) (fun j => hF (cols j))
    (fun j => z (residueRows label i j)) (k i) (a i) (hf i) (hμ i)
  · intro j
    simpa only [residueRows_label] using hunit (residueRows label i j)
  · intro j l
    simpa only [residueRows_label] using hres (residueRows label i j) l
  · intro j
    exact hz _

end
end CCDN
