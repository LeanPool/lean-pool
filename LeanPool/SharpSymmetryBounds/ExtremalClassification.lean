/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Normalization

/-!
# Classification of extremal curves

A curve attaining the rotation bound for `d ≥ 5` is, up to a direct similarity, a member of the
family `Re(z^(d-2) (|z|^2 + α)) = 0`.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

lemma centered_extremal_generator {m : ℕ} (hm : 3 ≤ m) {P : BPoly}
    (hP : Irreducible P) (hdeg : P.totalDegree = m + 2) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    (hcard : Nat.card (centeredRotationGroup P) = 2 * m) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ (2 * m) ∧ rotate ζ P = -P := by
  let := centeredRotationGroup_finite hP hinf hcircle
  let := isCyclic_of_injective_ringHom (rotationValue P) (rotationValue_injective P)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := centeredRotationGroup P)
  have hroot : IsPrimitiveRoot (rotationValue P u) (2 * m) := by
    rw [← hcard, ← hu]
    exact (IsPrimitiveRoot.orderOf u).map_of_injective (rotationValue_injective P)
  refine ⟨rotationValue P u, hroot, ?_⟩
  rcases rotation_sign_of_realLocus hP hinf u.prop.1 (fun z hz => (u.prop.2 z).mpr hz) with h | h
  · obtain ⟨a, b, hab, hc⟩ := exists_off_diagonal_coeff hP hinf hcircle
    have he := fixed_support hroot (by omega) h (mem_support_iff.mpr hc)
    exact (hab (by simpa using he)).elim
  · exact h

/-- An extremal centered curve is the normalized family after a nonzero complex dilation. -/
theorem centered_extremal_classification {m : ℕ} (hm : 3 ≤ m) {P : BPoly}
    (hP : Irreducible P) (hdeg : P.totalDegree = m + 2) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    (hcard : Nat.card (centeredRotationGroup P) = 2 * m) :
    ∃ c α : ℂ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      ∀ z : ℂ, z ∈ realLocus (familyPolynomial m α) ↔ c * z ∈ realLocus P := by
  obtain ⟨ζ, hζ, hanti⟩ := centered_extremal_generator hm hP hdeg hinf hcircle hcard
  obtain ⟨s, hs, hreal⟩ := exists_real_equation hP (by omega) hinf
  have hirr := C_mul_irreducible hs hP
  have hdegree : (C s * P).totalDegree ≤ m + 2 := by
    have he := totalDegree_mul (C s : BPoly) P
    simpa [hdeg] using he
  have hanti' : rotate ζ (C s * P) = -(C s * P) := by
    rw [map_mul, hanti]
    simp [rotate]
  obtain ⟨a, b, _, hb, hab, hform⟩ := irreducible_anti_normal_form hm hζ hirr hdegree hanti' hreal
  obtain ⟨c, α, k, hc, hα, hαr, hk, hn⟩ := normalize_twoParameter (m := m) (by omega) hb hab
  have he : dilate c (C s * P) = C (k : ℂ) * familyPolynomial m α := by
    rw [hform]
    exact hn
  refine ⟨c, α, hc, hα, hαr, ?_⟩
  intro z
  have hv := congrArg (eval (fun i : Fin 2 => if i = 0 then z else star z)) he
  rw [eval_dilate, map_mul, eval_C, map_mul, eval_C] at hv
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hz := congrArg (fun w : ℂ => w = 0) hv
  change eval _ (familyPolynomial m α) = 0 ↔ eval _ P = 0
  simpa only [mul_eq_zero, hs, hk0, false_or] using Iff.of_eq hz.symm

/-- Equality classification for arbitrary centers, with an explicit direct similarity.
The map `z ↦ cz+t` sends the normalized family onto the original real locus. -/
theorem extremal_classification {P : BPoly} (hP : Irreducible P)
    (hd : 5 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P)
    (hcard : Nat.card (DirectSymmetries P) = 2 * P.totalDegree - 4) :
    ∃ c t α : ℂ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      realLocus P =
        (fun z : ℂ => c * z + t) '' realLocus (familyPolynomial (P.totalDegree - 2) α) := by
  obtain ⟨t, ht⟩ := direct_symmetries_common_center hP (by omega) hinf.nonempty
  have hirr : Irreducible (shift t P) := hP.map (shiftEquiv t).toMulEquiv
  have hdegree : (shift t P).totalDegree = (P.totalDegree - 2) + 2 := by rw [shift_degree]; omega
  have hc : Nat.card (centeredRotationGroup (shift t P)) = 2 * (P.totalDegree - 2) := by
    rw [← Nat.card_congr (directRotationEquiv P t ht), hcard]
    omega
  obtain ⟨c, α, hc0, hα, hαr, he⟩ := centered_extremal_classification (by omega) hirr hdegree
    (realLocus_shift_infinite t hinf) (shifted_not_circle t hcircle) hc
  refine ⟨c, t, α, hc0, hα, hαr, ?_⟩
  ext z
  constructor
  · intro hz
    have hback : c * ((z - t) / c) + t = z := by rw [mul_div_cancel₀ _ hc0]; ring
    refine ⟨(z - t) / c, ?_, hback⟩
    rw [he, mem_realLocus_shift, hback]
    exact hz
  · rintro ⟨w, hw, rfl⟩
    exact (mem_realLocus_shift t P (c * w)).mp ((he w).mp hw)

end CurveSymmetry
