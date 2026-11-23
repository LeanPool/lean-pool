/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.CartesianDescent

/-!
# Orientation-preserving isometries

The direct-isometry subgroup is finite, cyclic and obeys the sharp bound.
-/

@[expose] public section

namespace CurveSymmetry

/-- The orientation-preserving Euclidean isometries, in their complex affine form. -/
def directIsometryGroup (S : Set ℂ) : Subgroup (ℂ ≃ᵢ ℂ) where
  carrier := {f | (∀ z : ℂ, f z ∈ S ↔ z ∈ S) ∧
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * z + b}
  one_mem' := ⟨by simp, 1, 0, norm_one, by simp⟩
  mul_mem' := by
    rintro f g ⟨hf, a, b, ha, he⟩ ⟨hg, c, d, hc, hk⟩
    refine ⟨fun z => (hf (g z)).trans (hg z), a * c, a * d + b, ?_, ?_⟩
    · rw [norm_mul, ha, hc, one_mul]
    · intro z
      change f (g z) = _
      rw [he, hk]
      ring
  inv_mem' := by
    rintro f ⟨hf, a, b, ha, he⟩
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    refine ⟨?_, a⁻¹, -a⁻¹ * b, ?_, ?_⟩
    · intro z
      simpa using (hf (f⁻¹ z)).symm
    · rw [norm_inv, ha, inv_one]
    · intro z
      have h := he (f⁻¹ z)
      have heq : a * (f⁻¹ z) + b = z := by simpa using h.symm
      calc
        f⁻¹ z = a⁻¹ * (a * (f⁻¹ z)) := by rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
        _ = a⁻¹ * z + -a⁻¹ * b := by linear_combination a⁻¹ * heq

/-- The Mathlib isometry `z ↦ a z + b` attached to the parameters of a direct symmetry. -/
noncomputable def directParametersToIsometry (P : BPoly) :
    DirectSymmetries P → directIsometryGroup (realLocus P) := fun u =>
  ⟨affineDirectIsometry u.val.1 u.val.2 u.prop.1,
    u.prop.2, u.val.1, u.val.2, u.prop.1, fun _ => rfl⟩

lemma directParametersToIsometry_bijective (P : BPoly) :
    Function.Bijective (directParametersToIsometry P) := by
  constructor
  · intro u v he
    apply Subtype.ext
    apply direct_parameters_unique
    intro z
    exact congrArg (fun f : directIsometryGroup (realLocus P) => f.val z) he
  · rintro ⟨f, hf, a, b, ha, he⟩
    have hab : DirectSymmetry (realLocus P) a b :=
      ⟨ha, fun z => by rw [← he]; exact hf z⟩
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    exact fun z => (he z).symm

/-- Direct-symmetry parameters are equivalent to the direct isometries preserving the locus. -/
noncomputable def directIsometryEquiv (P : BPoly) :
    DirectSymmetries P ≃ directIsometryGroup (realLocus P) :=
  Equiv.ofBijective (directParametersToIsometry P) (directParametersToIsometry_bijective P)

lemma direct_isometry_formula {S : Set ℂ} (f : directIsometryGroup S) (z : ℂ) :
    f.val z = (f.val 1 - f.val 0) * z + f.val 0 := by
  obtain ⟨a, b, _, he⟩ := f.prop.2
  rw [he z, he 1, he 0]
  ring

/-- The linear coefficient `f 1 - f 0` of a direct isometry, as a monoid homomorphism. -/
noncomputable def directSlope (S : Set ℂ) : directIsometryGroup S →* ℂ where
  toFun f := f.val 1 - f.val 0
  map_one' := by simp
  map_mul' := by
    intro f g
    change f.val (g.val 1) - f.val (g.val 0) = _
    rw [direct_isometry_formula f (g.val 1), direct_isometry_formula f (g.val 0)]
    ring

lemma directSlope_injective {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    Function.Injective (directSlope (realLocus P)) := by
  obtain ⟨t, ht⟩ := direct_symmetries_common_center hP hd hinf.nonempty
  intro f g he
  obtain ⟨a, b, ha, hf⟩ := f.prop.2
  obtain ⟨c, d, hc, hg⟩ := g.prop.2
  have hab : DirectSymmetry (realLocus P) a b :=
    ⟨ha, fun z => by rw [← hf]; exact f.prop.1 z⟩
  have hcd : DirectSymmetry (realLocus P) c d :=
    ⟨hc, fun z => by rw [← hg]; exact g.prop.1 z⟩
  change f.val 1 - f.val 0 = g.val 1 - g.val 0 at he
  rw [hf, hf, hg, hg] at he
  have hac : a = c := by linear_combination he
  have hbd : b = d := by rw [ht a b hab, ht c d hcd, hac]
  apply Subtype.ext
  apply IsometryEquiv.ext
  intro z
  rw [hf, hg, hac, hbd]

/-- The actual direct-isometry subgroup is finite, cyclic, and obeys the sharp bound. -/
theorem direct_isometry_group_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hnc : NotCircle P) :
    Finite (directIsometryGroup (realLocus P)) ∧ IsCyclic (directIsometryGroup (realLocus P)) ∧
      Nat.card (directIsometryGroup (realLocus P)) ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  obtain ⟨hf, hb⟩ := direct_euclidean_bound hP hd hinf hnc
  let := hf
  let := Finite.of_equiv _ (directIsometryEquiv P)
  refine ⟨inferInstance, isCyclic_of_injective_ringHom _ (directSlope_injective hP hd hinf), ?_⟩
  rwa [← Nat.card_congr (directIsometryEquiv P)]

theorem cartesian_direct_isometry_bound {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (directIsometryGroup (cartesianLocus f)) ∧
      IsCyclic (directIsometryGroup (cartesianLocus f)) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) ≤
        max f.totalDegree (2 * f.totalDegree - 4) := by
  have h := direct_isometry_group_bound (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus])
    (by simpa only [NotCircle, complexifyReal_locus] using hnc)
  rw [complexifyReal_locus, complexifyReal_degree] at h
  exact h

end CurveSymmetry
