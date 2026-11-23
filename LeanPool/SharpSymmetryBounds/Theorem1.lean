/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.PaperBounds

/-!
# Theorem 1: sharp symmetry bounds for real plane algebraic curves

Let `C` be an infinite real plane curve defined by a polynomial `f` of degree `d ≥ 2` that is
irreducible over `ℂ`, and suppose `C` is not a circle. Its group of Euclidean symmetries is finite,
the orientation-preserving part is cyclic of order at most `max(d, 2d - 4)`, and the full group has
order at most `2d` (`sharp_bounds`). Both bounds are attained in every degree `d ≥ 2`
(`rotation_bound_sharp`, `full_bound_sharp`). For `d ≥ 5`, the curves attaining the rotation bound
are exactly, up to an orientation-preserving similarity, the curves `Re(z^(d-2) (|z|^2 + α)) = 0`
with `|α| = 1` and `α` not real (`equality_classification`); conversely every such curve with
`d - 2 ≥ 3` attains the bound (`family_attains_bound`).

The four definitions and five theorem statements are the ones registered with Palomar as
`PALOMAR-2026-09-18-000007`, unchanged. Each theorem is derived from the corresponding endpoint of
the library (`CurveSymmetry.paper_sharp_bounds` and the following ones); the library notions agree
with these definitions by `rfl`, except that "not a circle" and "nonreal" are restated.
-/

@[expose] public section

namespace SharpSymmetryBounds

open MvPolynomial

/-- The real zero set `{(x, y) : f(x, y) = 0}` of a real polynomial in two
variables, viewed inside `ℂ` via `z = x + i y`. -/
def realCurve (f : MvPolynomial (Fin 2) ℝ) : Set ℂ :=
  {z | eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f = 0}

/-- All Euclidean isometries of the plane mapping `C` onto itself:
`T z ∈ C` exactly when `z ∈ C`. -/
def symmetries (C : Set ℂ) : Set (ℂ ≃ᵢ ℂ) :=
  {T | ∀ z : ℂ, T z ∈ C ↔ z ∈ C}

/-- The orientation-preserving symmetries of `C`: those of the form
`z ↦ a z + b` with `|a| = 1` (rotations and translations). -/
def directSymmetries (C : Set ℂ) : Set (ℂ ≃ᵢ ℂ) :=
  {T | T ∈ symmetries C ∧ ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, T z = a * z + b}

/-- The extremal curve `Re(z^m (|z|^2 + α)) = 0`. -/
def extremalCurve (m : ℕ) (α : ℂ) : Set ℂ :=
  {z | (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re = 0}

/-! ### Bridges to the library -/

lemma realCurve_eq (f : MvPolynomial (Fin 2) ℝ) : realCurve f = CurveSymmetry.cartesianLocus f :=
  rfl

lemma symmetries_eq (C : Set ℂ) :
    symmetries C = (CurveSymmetry.isometrySetGroup C : Set (ℂ ≃ᵢ ℂ)) :=
  rfl

lemma directSymmetries_eq (C : Set ℂ) :
    directSymmetries C = (CurveSymmetry.directIsometryGroup C : Set (ℂ ≃ᵢ ℂ)) :=
  rfl

lemma extremalCurve_eq (m : ℕ) (α : ℂ) : extremalCurve m α = CurveSymmetry.extremalCurve m α :=
  rfl

lemma not_circle_iff (f : MvPolynomial (Fin 2) ℝ) :
    (∀ (c : ℂ) (R : ℝ), 0 < R → realCurve f ≠ Metric.sphere c R) ↔
      ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ CurveSymmetry.cartesianLocus f = Metric.sphere c R := by
  constructor
  · rintro h ⟨c, R, hR, he⟩
    exact h c R hR he
  · intro h c R hR he
    exact h ⟨c, R, hR, he⟩

lemma ncard_symmetries (C : Set ℂ) :
    (symmetries C).ncard = Nat.card (CurveSymmetry.isometrySetGroup C) :=
  (Nat.card_coe_set_eq (symmetries C)).symm

lemma ncard_directSymmetries (C : Set ℂ) :
    (directSymmetries C).ncard = Nat.card (CurveSymmetry.directIsometryGroup C) :=
  (Nat.card_coe_set_eq (directSymmetries C)).symm

lemma im_ne_zero_iff (α : ℂ) : α.im ≠ 0 ↔ α ≠ star α := by
  constructor
  · intro h he
    apply h
    have him := congrArg Complex.im he
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith
  · intro h him
    apply h
    apply Complex.ext <;> simp [him]

/-! ### Theorem 1 -/

theorem sharp_bounds (f : MvPolynomial (Fin 2) ℝ)
    (hirr : Irreducible (MvPolynomial.map Complex.ofRealHom f))
    (hdeg : 2 ≤ f.totalDegree) (hinf : (realCurve f).Infinite)
    (hcircle : ∀ (c : ℂ) (R : ℝ), 0 < R → realCurve f ≠ Metric.sphere c R) :
    (symmetries (realCurve f)).Finite ∧
      (∃ g : ℂ ≃ᵢ ℂ, directSymmetries (realCurve f) = Set.range (fun n : ℤ => g ^ n)) ∧
      (directSymmetries (realCurve f)).ncard ≤ max f.totalDegree (2 * f.totalDegree - 4) ∧
      (symmetries (realCurve f)).ncard ≤ 2 * f.totalDegree := by
  obtain ⟨hfin, -, hcyc, hbd, hbf⟩ :=
    CurveSymmetry.paper_sharp_bounds hirr hdeg hinf ((not_circle_iff f).mp hcircle)
  refine ⟨Set.finite_coe_iff.mp hfin, ?_, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hcyc.exists_zpow_surjective
    refine ⟨g.1, Set.ext fun T => ⟨fun hT => ?_, ?_⟩⟩
    · obtain ⟨n, hn⟩ := hg ⟨T, hT⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    · rintro ⟨n, rfl⟩
      exact (CurveSymmetry.directIsometryGroup (realCurve f)).zpow_mem g.2 n
  · rw [ncard_directSymmetries]
    exact hbd
  · rw [ncard_symmetries]
    exact hbf

theorem rotation_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : MvPolynomial (Fin 2) ℝ, Irreducible (MvPolynomial.map Complex.ofRealHom f) ∧
      f.totalDegree = d ∧ (realCurve f).Infinite ∧
      (∀ (c : ℂ) (R : ℝ), 0 < R → realCurve f ≠ Metric.sphere c R) ∧
      (directSymmetries (realCurve f)).ncard = max d (2 * d - 4) := by
  obtain ⟨f, hf, hfd, hinf, hnc, hc⟩ := CurveSymmetry.paper_rotation_sharp d hd
  exact ⟨f, hf, hfd, hinf, (not_circle_iff f).mpr hnc, (ncard_directSymmetries _).trans hc⟩

theorem full_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : MvPolynomial (Fin 2) ℝ, Irreducible (MvPolynomial.map Complex.ofRealHom f) ∧
      f.totalDegree = d ∧ (realCurve f).Infinite ∧
      (∀ (c : ℂ) (R : ℝ), 0 < R → realCurve f ≠ Metric.sphere c R) ∧
      (symmetries (realCurve f)).ncard = 2 * d := by
  obtain ⟨f, hf, hfd, hinf, hnc, hc⟩ := CurveSymmetry.paper_full_sharp d hd
  exact ⟨f, hf, hfd, hinf, (not_circle_iff f).mpr hnc, (ncard_symmetries _).trans hc⟩

theorem equality_classification (f : MvPolynomial (Fin 2) ℝ)
    (hirr : Irreducible (MvPolynomial.map Complex.ofRealHom f))
    (hdeg : 5 ≤ f.totalDegree) (hinf : (realCurve f).Infinite)
    (hcircle : ∀ (c : ℂ) (R : ℝ), 0 < R → realCurve f ≠ Metric.sphere c R)
    (hcard : (directSymmetries (realCurve f)).ncard = 2 * f.totalDegree - 4) :
    ∃ a b α : ℂ, a ≠ 0 ∧ ‖α‖ = 1 ∧ α.im ≠ 0 ∧
      (fun z : ℂ => a * z + b) '' realCurve f = extremalCurve (f.totalDegree - 2) α := by
  obtain ⟨a, b, α, ha, hα, hαr, he⟩ := CurveSymmetry.paper_equality_classification hirr hdeg hinf
    ((not_circle_iff f).mp hcircle) ((ncard_directSymmetries _).symm.trans hcard)
  exact ⟨a, b, α, ha, hα, (im_ne_zero_iff α).mpr hαr, he⟩

theorem family_attains_bound (m : ℕ) (hm : 3 ≤ m) (α : ℂ) (hα : α.im ≠ 0) :
    ∃ f : MvPolynomial (Fin 2) ℝ, Irreducible (MvPolynomial.map Complex.ofRealHom f) ∧
      f.totalDegree = m + 2 ∧ realCurve f = extremalCurve m α ∧ (realCurve f).Infinite ∧
      (∀ (c : ℂ) (R : ℝ), 0 < R → realCurve f ≠ Metric.sphere c R) ∧
      (directSymmetries (realCurve f)).ncard = 2 * m := by
  obtain ⟨f, hf, hfd, hloc, hinf, hnc, hc⟩ :=
    CurveSymmetry.paper_family_converse hm ((im_ne_zero_iff α).mp hα)
  exact ⟨f, hf, hfd, hloc, hinf, (not_circle_iff f).mpr hnc, (ncard_directSymmetries _).trans hc⟩

end SharpSymmetryBounds
