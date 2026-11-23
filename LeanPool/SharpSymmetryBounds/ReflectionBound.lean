/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.EuclideanParameters

/-!
# The bound for the full group

A reflection improves the direct bound to `d`, and the full Euclidean symmetry group is finite of
order at most `2d`.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

lemma reflect_pair {a r : ℂ} (ha : ‖a‖ = 1) (hr : ‖r‖ = 1) (P : BPoly) :
    reflect a (reflect (r * a) P) = rotate r P := by
  have hc := mul_star_eq_one_of_norm ha
  have h0 : ∀ b : ℂ, reflect b (X 0) = C b * X 1 := by intro b; simp [reflect]
  have h1 : ∀ b : ℂ, reflect b (X 1) = C (star b) * X 0 := by intro b; simp [reflect]
  have hC : ∀ b c : ℂ, reflect b (C c) = C c := by intro b c; simp [reflect]
  have he0 : r * a * star a = r := by linear_combination r * hc
  have he1 : star (r * a) * a = r⁻¹ := by
    change (starRingEnd ℂ) (r * a) * a = r⁻¹
    rw [Complex.inv_eq_conj hr]
    change star (r * a) * a = star r
    simp only [star_mul]
    linear_combination star r * hc
  induction P using MvPolynomial.induction_on with
  | C c => simp [reflect, rotate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i
      · change rotate r P * reflect a (reflect (r * a) (X 0)) = rotate r P * rotate r (X 0)
        rw [h0, map_mul, hC, h1, ← mul_assoc (C (r * a)), ← C_mul, he0]
        simp [rotate]
      · change rotate r P * reflect a (reflect (r * a) (X 1)) = rotate r P * rotate r (X 1)
        rw [h1, map_mul, hC, h0, ← mul_assoc (C (star (r * a))), ← C_mul, he1]
        simp [rotate]

lemma rotation_fixes_equation_with_reflection {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    {a : ℂ} (ha : OppositeSymmetry (realLocus P) a 0)
    (u : centeredRotationGroup P) : rotate (u.val : ℂ) P = P := by
  have hfirst := reflection_fixes_equation hP hd hinf ha.1 (by
    intro z hz
    simpa using (ha.2 z).mpr hz)
  have hnorm : ‖(u.val : ℂ) * a‖ = 1 := by simp [u.prop.1, ha.1]
  have hsecond := reflection_fixes_equation hP hd hinf hnorm (by
    intro z hz
    have h := (u.prop.2 (a * star z)).mpr (by simpa using (ha.2 z).mpr hz)
    simpa [mul_assoc] using h)
  rw [← reflect_pair ha.1 u.prop.1, hsecond, hfirst]

/-- A centered reflection improves the rotation bound from `max(d,2d-4)` to `d`. -/
theorem centered_rotation_bound_with_reflection {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    {a : ℂ} (ha : OppositeSymmetry (realLocus P) a 0) :
    Nat.card (centeredRotationGroup P) ≤ P.totalDegree := by
  let := centeredRotationGroup_finite hP hinf hcircle
  let := isCyclic_of_injective_ringHom (rotationValue P) (rotationValue_injective P)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := centeredRotationGroup P)
  have hroot : IsPrimitiveRoot (rotationValue P u) (Nat.card (centeredRotationGroup P)) := by
    rw [← hu]
    exact (IsPrimitiveRoot.orderOf u).map_of_injective (rotationValue_injective P)
  by_contra h
  obtain ⟨a, b, hab, hc⟩ := exists_off_diagonal_coeff hP hinf hcircle
  have hs := fixed_support hroot (by omega)
    (rotation_fixes_equation_with_reflection hP hd hinf ha u) (mem_support_iff.mpr hc)
  exact hab (by simpa using hs)

lemma shift_centered {P : BPoly} {c : ℂ}
    (hc : ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = (1 - a) * c) :
    ∀ a b : ℂ, DirectSymmetry (realLocus (shift c P)) a b → b = 0 := by
  intro a b h
  have hback : DirectSymmetry (realLocus P) a (b + c - a * c) := by
    refine ⟨h.1, ?_⟩
    intro z
    have he := h.2 (z - c)
    rw [mem_realLocus_shift, mem_realLocus_shift] at he
    have he' : a * (z - c) + b + c = a * z + (b + c - a * c) := by ring
    simpa only [he', sub_add_cancel] using he
  have he := hc _ _ hback
  linear_combination he

/-- The presence of any opposite symmetry improves the bound for all direct symmetries. -/
theorem direct_bound_with_opposite {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P)
    (g : OppositeSymmetries P) : Nat.card (DirectSymmetries P) ≤ P.totalDegree := by
  classical
  obtain ⟨c, hc⟩ := direct_symmetries_common_center hP hd hinf.nonempty
  have hirr : Irreducible (shift c P) := hP.map (shiftEquiv c).toMulEquiv
  have hdegree : 2 ≤ (shift c P).totalDegree := by simpa [shift_degree] using hd
  have hi := realLocus_shift_infinite c hinf
  have hn := shifted_not_circle c hcircle
  rw [Nat.card_congr (directRotationEquiv P c hc)]
  let := centeredRotationGroup_finite hirr hi hn
  by_cases hex : ∃ u : centeredRotationGroup (shift c P), (u.val : ℂ) ≠ 1
  · obtain ⟨u, hu⟩ := hex
    have hrot : DirectSymmetry (realLocus (shift c P)) (u.val : ℂ) 0 :=
      ⟨u.prop.1, by simpa using u.prop.2⟩
    have hg := opposite_shift (c := c) g.prop
    have hb := opposite_centered (shift_centered hc) hu hrot hg
    rw [hb] at hg
    simpa [shift_degree] using centered_rotation_bound_with_reflection hirr hdegree hi hn hg
  · have hsub : Subsingleton (centeredRotationGroup (shift c P)) := by
      refine ⟨fun u v => rotationValue_injective _ ?_⟩
      have hu : (u.val : ℂ) = 1 := by by_contra h; exact hex ⟨u, h⟩
      have hv : (v.val : ℂ) = 1 := by by_contra h; exact hex ⟨v, h⟩
      exact hu.trans hv.symm
    let := hsub
    have he : Nat.card (centeredRotationGroup (shift c P)) = 1 := Nat.card_unique
    omega

/-- The complete Euclidean group is finite and has at most twice the degree.
This proves the upper bound, not its sharpness or the equality classification. -/
theorem full_euclidean_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P) :
    Finite (EuclideanSymmetries P) ∧ Nat.card (EuclideanSymmetries P) ≤ 2 * P.totalDegree := by
  classical
  obtain ⟨hf, hb⟩ := direct_euclidean_bound hP hd hinf hcircle
  let := hf
  by_cases hex : Nonempty (OppositeSymmetries P)
  · let g := Classical.choice hex
    let : Finite (OppositeSymmetries P) := Finite.of_injective
      (oppositeDirectEquiv P g) (oppositeDirectEquiv P g).injective
    refine ⟨inferInstance, ?_⟩
    change Nat.card (DirectSymmetries P ⊕ OppositeSymmetries P) ≤ _
    rw [Nat.card_sum, Nat.card_congr (oppositeDirectEquiv P g)]
    have h := direct_bound_with_opposite hP hd hinf hcircle g
    omega
  · let : IsEmpty (OppositeSymmetries P) := not_nonempty_iff.mp hex
    refine ⟨inferInstance, ?_⟩
    change Nat.card (DirectSymmetries P ⊕ OppositeSymmetries P) ≤ _
    rw [Nat.card_sum, Nat.card_of_isEmpty (α := OppositeSymmetries P)]
    omega

end CurveSymmetry
