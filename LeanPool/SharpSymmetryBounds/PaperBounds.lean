/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.DirectIsometries
public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Theorem 1, library form

The bounds, their sharpness and the equality classification of Theorem 1 on the actual isometry
subgroups and real Cartesian input.
-/

@[expose] public section

namespace CurveSymmetry

/-- The affine description of direct isometries agrees with determinant `+1`
of the real-linear part supplied by Mazur--Ulam. -/
lemma direct_form_iff_det (f : ℂ ≃ᵢ ℂ) :
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * z + b) ↔
      LinearEquiv.det f.toRealLinearIsometryEquiv.toLinearEquiv = 1 := by
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex f.toRealLinearIsometryEquiv
  · have hf : ∀ z : ℂ, f z = (a : ℂ) * z + f 0 := by
      intro z
      have he := congrArg (fun L : ℂ ≃ₗᵢ[ℝ] ℂ => L z) ha
      rw [IsometryEquiv.toRealLinearIsometryEquiv_apply, rotation_apply] at he
      exact eq_add_of_sub_eq he
    rw [ha, linearEquiv_det_rotation]
    exact ⟨fun _ => rfl, fun _ => ⟨a, f 0, Circle.norm_coe a, hf⟩⟩
  · have hf : ∀ z : ℂ, f z = (a : ℂ) * star z + f 0 := by
      intro z
      have he := congrArg (fun L : ℂ ≃ₗᵢ[ℝ] ℂ => L z) ha
      rw [IsometryEquiv.toRealLinearIsometryEquiv_apply] at he
      exact eq_add_of_sub_eq he
    have hdet : LinearEquiv.det f.toRealLinearIsometryEquiv.toLinearEquiv = -1 := by
      rw [ha]
      change LinearEquiv.det (Complex.conjLIE.toLinearEquiv.trans (rotation a).toLinearEquiv) = -1
      rw [LinearEquiv.det_trans, Complex.linearEquiv_det_conjLIE, linearEquiv_det_rotation, one_mul]
    constructor
    · rintro ⟨b, c, hb, hg⟩
      have hb0 : b ≠ 0 := by intro h; simp [h] at hb
      exact (direct_ne_opposite hb0 (fun z => (hg z).symm.trans (hf z))).elim
    · intro h
      rw [hdet] at h
      have he := congrArg (fun u : ℝˣ => (u : ℝ)) h
      norm_num at he

lemma mem_direct_isometry_iff_det (S : Set ℂ) (f : ℂ ≃ᵢ ℂ) :
    f ∈ directIsometryGroup S ↔ f ∈ isometrySetGroup S ∧
      LinearEquiv.det f.toRealLinearIsometryEquiv.toLinearEquiv = 1 := by
  exact and_congr_right (fun _ => direct_form_iff_det f)

/-- The extremal curve `Re(z^m (|z|^2 + α)) = 0`. -/
def extremalCurve (m : ℕ) (α : ℂ) : Set ℂ :=
  {z | (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re = 0}

lemma family_locus_eq (m : ℕ) (α : ℂ) :
    realLocus (familyPolynomial m α) = extremalCurve m α := by
  ext z
  change MvPolynomial.eval _ (familyPolynomial m α) = 0 ↔ _
  rw [eval_familyPolynomial, mul_star_norm_sq, add_comm α]
  have he : z ^ m * ((‖z‖ : ℂ) ^ 2 + α) + star (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)) =
      ((2 * (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re : ℝ) : ℂ) :=
    Complex.add_conj _
  change _ + star _ = 0 ↔ (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re = 0
  rw [he, Complex.ofReal_eq_zero]
  simp

lemma cartesian_direct_card (f : RPoly) :
    Nat.card (CartesianDirectSymmetries f) = Nat.card (directIsometryGroup (cartesianLocus f)) := by
  have he := Nat.card_congr (directIsometryEquiv (complexifyReal f))
  simpa only [DirectSymmetries, complexifyReal_locus] using he

/-- The two bounds in Theorem 1, on actual isometry subgroups and real Cartesian input. -/
theorem paper_sharp_bounds {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (isometrySetGroup (cartesianLocus f)) ∧
      Finite (directIsometryGroup (cartesianLocus f)) ∧
      IsCyclic (directIsometryGroup (cartesianLocus f)) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) ≤
        max f.totalDegree (2 * f.totalDegree - 4) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) ≤ 2 * f.totalDegree := by
  obtain ⟨hfull, hbfull⟩ := cartesian_isometry_bound hf hd hinf hnc
  obtain ⟨hdir, hcyc, hbdir⟩ := cartesian_direct_isometry_bound hf hd hinf hnc
  exact ⟨hfull, hdir, hcyc, hbdir, hbfull⟩

/-- The equality clause of Theorem 1, with the explicit inverse similarity
sending the original curve onto the real-part equation printed in the paper. -/
theorem paper_equality_classification {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 5 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    (hcard : Nat.card (directIsometryGroup (cartesianLocus f)) = 2 * f.totalDegree - 4) :
    ∃ a b α : ℂ, a ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      (fun z : ℂ => a * z + b) '' cartesianLocus f = extremalCurve (f.totalDegree - 2) α := by
  obtain ⟨c, t, α, hc, hα, hαr, he⟩ := cartesian_extremal_classification hf hd hinf hnc
    ((cartesian_direct_card f).trans hcard)
  refine ⟨c⁻¹, -c⁻¹ * t, α, inv_ne_zero hc, hα, hαr, ?_⟩
  rw [he, ← family_locus_eq, Set.image_image]
  have hm : (fun z : ℂ => c⁻¹ * (c * z + t) + -c⁻¹ * t) = id := by
    funext z
    change _ = z
    calc
      c⁻¹ * (c * z + t) + -c⁻¹ * t = (c⁻¹ * c) * z := by ring
      _ = z := by rw [inv_mul_cancel₀ hc, one_mul]
  change (fun z : ℂ => c⁻¹ * (c * z + t) + -c⁻¹ * t) '' _ = _
  rw [hm, Set.image_id]

theorem paper_rotation_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) = max d (2 * d - 4) := by
  obtain ⟨f, hf, hdeg, hinf, hnc, hc⟩ := cartesian_rotation_bound_sharp d hd
  exact ⟨f, hf, hdeg, hinf, hnc, (cartesian_direct_card f).symm.trans hc⟩

theorem paper_full_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) = 2 * d :=
  cartesian_full_bound_sharp d hd

/-- Conversely the displayed family attains the rotation bound; this version
even permits any nonreal parameter, without needing modulus one. -/
theorem paper_family_converse {m : ℕ} (hm : 3 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = m + 2 ∧
      cartesianLocus f = extremalCurve m α ∧ (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) = 2 * m := by
  have hP := familyPolynomial_irreducible (by omega : 0 < m) ha
  have hdeg := family_degree (by omega : 0 < m) α
  have hinf := family_realLocus_infinite (by omega : 0 < m) ha
  obtain ⟨f, hf, hfd, hfl⟩ := exists_cartesian_equation hP (by omega) hinf
  refine ⟨f, hf, hfd.trans hdeg, hfl.trans (family_locus_eq m α), hfl ▸ hinf, ?_, ?_⟩
  · simpa only [hfl, NotCircle] using family_not_circle (by omega : 0 < m) ha
  · rw [hfl, ← Nat.card_congr (directIsometryEquiv (familyPolynomial m α))]
    exact family_direct_card (by omega) ha

end CurveSymmetry
