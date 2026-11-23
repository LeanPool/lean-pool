/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.RealEquation

/-!
# The equality case

The four-term support theorem and irreducibility exclude every degenerate parameter in the
equality case of the rotation bound.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- The two-parameter family `X^m (a + b X Y) + Y^m (conj a + conj b X Y)` of the equality case. -/
noncomputable def twoParameter (m : ℕ) (a b : ℂ) : BPoly :=
  X 0 ^ m * (C a + C b * X 0 * X 1) +
    X 1 ^ m * (C (star a) + C (star b) * X 0 * X 1)

lemma twoParameter_top_ne_zero {m : ℕ} (hm : 2 ≤ m) {a b : ℂ}
    (hP : Irreducible (twoParameter m a b)) : b ≠ 0 := by
  intro hb
  apply not_irreducible_pure_powers m hm a (star a)
  simpa [twoParameter, hb, mul_comm] using hP

lemma binary_sum_not_isUnit {m : ℕ} (hm : 0 < m) (b : ℂ) :
    ¬ IsUnit (C b * (X 0 : BPoly) ^ m + C (star b) * X 1 ^ m) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun _ : Fin 2 => (0 : ℂ)))
  simp [hm.ne'] at h

lemma twoParameter_low_ne_zero {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (hP : Irreducible (twoParameter m a b)) : a ≠ 0 := by
  intro ha
  have he : twoParameter m a b = ((X 0 : BPoly) * X 1) *
      (C b * X 0 ^ m + C (star b) * X 1 ^ m) := by
    simp only [twoParameter, ha, star_zero, C_0, zero_add]
    ring
  have hfirst : ¬ IsUnit ((X 0 : BPoly) * X 1) := by
    simpa using radial_factor_not_isUnit 0
  exact (hP.isUnit_or_isUnit he).elim hfirst (binary_sum_not_isUnit hm b)

/-- A real coefficient ratio would give a radial factor. -/
lemma twoParameter_ratio_nonreal {m : ℕ} (hm : 2 ≤ m) {a b : ℂ}
    (hP : Irreducible (twoParameter m a b)) : a / b ≠ star (a / b) := by
  have hb := twoParameter_top_ne_zero hm hP
  intro hreal
  have hba : b * (a / b) = a := mul_div_cancel₀ _ hb
  have hbar : star b * (a / b) = star a := by
    have h := congrArg star hba
    simp only [star_mul, ← hreal] at h
    simpa [mul_comm] using h
  have he : twoParameter m a b = ((X 0 : BPoly) * X 1 + C (a / b)) *
      (C b * X 0 ^ m + C (star b) * X 1 ^ m) := by
    have he0 := congrArg (C : ℂ →+* BPoly) hba
    have he1 := congrArg (C : ℂ →+* BPoly) hbar
    rw [map_mul] at he0 he1
    dsimp [twoParameter]
    simp only [Complex.star_def] at he1 ⊢
    linear_combination -(X 0 : BPoly) ^ m * he0 - (X 1 : BPoly) ^ m * he1
  have hfirst : ¬ IsUnit ((X 0 : BPoly) * X 1 + C (a / b)) := by
    simpa using radial_factor_not_isUnit (-(a / b))
  exact (hP.isUnit_or_isUnit he).elim hfirst (binary_sum_not_isUnit (by omega) b)

/-- The four-term support theorem plus irreducibility excludes every degenerate parameter. -/
theorem irreducible_anti_normal_form {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly} (hP : Irreducible P)
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ a / b ≠ star (a / b) ∧ P = twoParameter m a b := by
  obtain ⟨a, b, he⟩ := anti_real_normal_form hm hζ hdeg hanti hreal
  change P = twoParameter m a b at he
  have hi : Irreducible (twoParameter m a b) := he ▸ hP
  exact ⟨a, b, twoParameter_low_ne_zero (by omega) hi, twoParameter_top_ne_zero (by omega) hi,
    twoParameter_ratio_nonreal (by omega) hi, he⟩

end CurveSymmetry
