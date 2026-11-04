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
lemma projective_chart_eval_congr {n M : ℕ} {q u : ℤ}
    (z : Fin (n + 1) → ℤ) (hu : q ∣ u * z 0 - 1)
    (F : MvPolynomial (Fin (n + 1)) ℤ) (hF : F.IsHomogeneous M) :
    q ∣ eval (fun j : Fin n => u * z j.succ) (affineChart n F) -
      u ^ M * eval z F := by
  rw [affineChart_eval, ← homogeneous_eval_smul hF]
  apply dvd_eval_sub_of_dvd_coordinates
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, neg_sub] using
      (show q ∣ -(u * z 0 - 1) from dvd_neg.mpr hu)
  · simp

/-- An affine determinant bound modulo `p ^ e` transfers to homogeneous evaluations
when the first coordinate is a unit. The exponent is unchanged. -/
theorem projective_chart_det_divisibility_of_affine {p n s d M e : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 1)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 1) → ℤ) (a : Fin n → ℤ)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i 0))
    (hres : ∀ i j, (p : ℤ) ∣ z i j.succ - a j * z i 0)
    (hz : ∀ i, eval (z i) f = 0)
    (haffine : ∀ x : Fin s → Fin n → ℤ, (∀ i j, (p : ℤ) ∣ x i j - a j) →
      (∀ i, (p : ℤ) ^ e ∣ eval (x i) (affineChart n f)) →
      ∀ G : Fin s → MvPolynomial (Fin n) ℤ,
        (p : ℤ) ^ e ∣ (Matrix.of fun i j => eval (x i) (G j)).det) :
    (p : ℤ) ^ e ∣ (Matrix.of fun i j => eval (z i) (F j)).det := by
  classical
  by_cases he : e = 0
  · simp [he]
  have hepos : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
  let q : ℤ := (p : ℤ) ^ e
  have hpq : (p : ℤ) ∣ q := by
    simpa only [pow_one] using pow_dvd_pow (p : ℤ) hepos
  have hex (i : Fin s) := exists_integer_inverse_of_isCoprime
    (show IsCoprime q (z i 0) from (hunit i).pow_left)
  choose u hu huc using hex
  let x : Fin s → Fin n → ℤ := fun i j => u i * z i j.succ
  have hx (i : Fin s) (j : Fin n) : (p : ℤ) ∣ x i j - a j := by
    have he : x i j - a j =
        u i * (z i j.succ - a j * z i 0) + a j * (u i * z i 0 - 1) := by
      dsimp [x]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right (hres i j) _)
      (dvd_mul_of_dvd_right (hpq.trans (hu i)) _)
  have hxf (i : Fin s) : q ∣ eval (x i) (affineChart n f) := by
    have h := projective_chart_eval_congr (z i) (hu i) f hfhom
    simpa only [hz, mul_zero, sub_zero] using h
  let A := Matrix.of fun i j : Fin s => eval (x i) (affineChart n (F j))
  let D := Matrix.of fun i j : Fin s => u i ^ M * eval (z i) (F j)
  have hA : q ∣ A.det :=
    haffine x hx hxf (fun j => affineChart n (F j))
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
def projectiveChart {n : ℕ} (k : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial (Fin n) ℤ :=
  affineChart n (rename (Equiv.swap 0 k) f)

private lemma eval_swap_projective_coordinates {n : ℕ} (k : Fin (n + 1))
    (z : Fin (n + 1) → ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    eval (z ∘ Equiv.swap 0 k) (rename (Equiv.swap 0 k) f) = eval z f := by
  rw [eval_rename]
  have he : (z ∘ Equiv.swap 0 k) ∘ Equiv.swap 0 k = z := by
    funext j
    simp
  rw [he]

/-- Transfer an affine determinant bound in any coordinate chart, with its exact exponent. -/
theorem projective_local_det_divisibility_of_affine {p n s d M e : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 1)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 1) → ℤ) (k : Fin (n + 1)) (a : Fin n → ℤ)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0)
    (haffine : ∀ x : Fin s → Fin n → ℤ, (∀ i j, (p : ℤ) ∣ x i j - a j) →
      (∀ i, (p : ℤ) ^ e ∣ eval (x i) (projectiveChart k f)) →
      ∀ G : Fin s → MvPolynomial (Fin n) ℤ,
        (p : ℤ) ^ e ∣ (Matrix.of fun i j => eval (x i) (G j)).det) :
    (p : ℤ) ^ e ∣ (Matrix.of fun i j => eval (z i) (F j)).det := by
  have h := projective_chart_det_divisibility_of_affine
    (rename (Equiv.swap 0 k) f) hfhom.rename_isHomogeneous
    (fun j => rename (Equiv.swap 0 k) (F j)) (fun j => (hF j).rename_isHomogeneous)
    (fun i => z i ∘ Equiv.swap 0 k) a
    (fun i => by simpa using hunit i)
    (fun i j => by simpa using hres i j)
    (fun i => by rw [eval_swap_projective_coordinates]; exact hz i) haffine
  simpa only [eval_swap_projective_coordinates] using h

/-- Assemble affine bounds in separate projective charts into the common minor divisor.
Each residue class retains the exponent supplied by its own affine bound. -/
theorem projective_residue_minorGcd_of_affine {p n c s N d M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin (n + 1)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 1) → ℤ) (label : Fin s → Fin c)
    (k : Fin c → Fin (n + 1)) (a : Fin c → Fin n → ℤ) (e : Fin c → ℕ)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i (k (label i))))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 (k (label i)) j.succ) -
      a (label i) j * z i (k (label i)))
    (hz : ∀ i, eval (z i) f = 0)
    (haffine : ∀ i, ∀ x : Fin (Fintype.card {j : Fin s // label j = i}) → Fin n → ℤ,
      (∀ r j, (p : ℤ) ∣ x r j - a i j) →
      (∀ r, (p : ℤ) ^ e i ∣ eval (x r) (projectiveChart (k i) f)) →
      ∀ G : Fin (Fintype.card {j : Fin s // label j = i}) → MvPolynomial (Fin n) ℤ,
        (p : ℤ) ^ e i ∣ (Matrix.of fun r j => eval (x r) (G j)).det) :
    (p : ℤ) ^ (∑ i, e i) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  apply projective_local_det_divisibility_of_affine f hfhom
    (fun j => F (cols j)) (fun j => hF (cols j))
    (fun j => z (residueRows label i j)) (k i) (a i)
  · intro j
    simpa only [residueRows_label] using hunit (residueRows label i j)
  · intro j l
    simpa only [residueRows_label] using hres (residueRows label i j) l
  · intro j
    exact hz _
  · exact haffine i

/-- Move coordinate `k` to the first position before taking the plane affine chart. -/
def projectivePlaneChart (k : Fin 3) (f : MvPolynomial (Fin 3) ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  projectiveChart k f

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
  apply projective_residue_minorGcd_of_affine f hfhom F hF z label k a
    (fun i => multiplicityExponent (Fintype.card {j : Fin s // label j = i}) (μ i))
    hunit hres hz
  intro i x hx hxf G
  exact singular_plane_chart_det_divisibility_mod (projectivePlaneChart (k i) f)
    G x (a i) (hf i) (hμ i) hx hxf

end
end CCDN
