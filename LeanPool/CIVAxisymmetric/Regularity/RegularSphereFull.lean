/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.TimeZeroSingularSetNull
public import LeanPool.CIVAxisymmetric.Regularity.HausdorffLipschitzRadius
public import LeanPool.CIVAxisymmetric.Regularity.SingularSlice

/-!
# The axis-inclusive regular sphere of `lem:aniso:annulus`

This file derives, from the statement `CIV.timeZeroSingularSetNull` (the one-dimensional
Hausdorff measure of the singular slice in the open unit ball is zero, axis included), the two
steps of the regular-sphere argument of `lem:aniso:annulus`:

* `hausdorffMeasure_singularSlice_closedBall_eq_zero`: `H¹(S₀) = 0` on `closure (vec3Ball 0 R₀)`
  for `R₀ < 1`, matching the manuscript's `S₀ ⊆ closure B(R₀)`.
* `exists_annulus_bound_of_timeZeroSingularSetNull`: a uniform bound on a space-time annulus
  with radii in `(R₁, R₀)`. The Euclidean radius `vec3EuclideanNorm : Vec3 → ℝ` is Lipschitz for
  the ambient (sup) metric on `Vec3` that `μH[1]` is computed against
  (`vec3EuclideanNorm_lipschitzWith`, with the dimensional constant `√3`, since `Vec3` carries
  the sup norm rather than the Euclidean one), so a null `μH[1]` set has a Lebesgue-null image
  under it (`CIV.ae_notMem_image_of_hausdorffMeasure_one_eq_zero`); almost every radius in
  `(R₁, R₀)` therefore carries no point of the singular slice, and the compactness step
  `CIV.exists_annulus_bound_of_sphere_disjoint` turns such a sphere into a uniform bound on a
  whole space-time annulus around it, shrunk to keep its radii inside `(R₁, R₀)`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-! ### The Euclidean radius is Lipschitz for the ambient (sup) metric on `Vec3` -/

/-- `vec3EuclideanNorm` is Lipschitz for the ambient (sup) metric on `Vec3` (`Vec3` carries the
sup norm, not the Euclidean one), with Lipschitz constant `√3`: the dimensional constant relating
the two norms, `CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sqrt_three_mul_norm`. -/
theorem vec3EuclideanNorm_lipschitzWith :
    LipschitzWith (Real.sqrt 3).toNNReal (vec3EuclideanNorm : Vec3 → ℝ) := by
  refine LipschitzWith.of_le_add_mul' (Real.sqrt 3) (fun x y => ?_)
  have heq : x = (x - y) + y := by abel
  have htri : vec3EuclideanNorm x ≤ vec3EuclideanNorm (x - y) + vec3EuclideanNorm y := by
    conv_lhs => rw [heq]
    exact vec3EuclideanNorm_add_le _ _
  have hle : vec3EuclideanNorm (x - y) ≤ Real.sqrt 3 * ‖x - y‖ :=
    vec3EuclideanNorm_le_sqrt_three_mul_norm (x - y)
  have hdist : ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
  calc vec3EuclideanNorm x ≤ vec3EuclideanNorm (x - y) + vec3EuclideanNorm y := htri
    _ ≤ Real.sqrt 3 * ‖x - y‖ + vec3EuclideanNorm y := by linarith only [hle]
    _ = vec3EuclideanNorm y + Real.sqrt 3 * dist x y := by rw [hdist]; ring

/-! ### `H¹(S₀) = 0` on `closure B(R₀)` -/

/-- The one-dimensional Hausdorff measure of the singular slice of the blow-up time,
restricted to `closure (vec3Ball 0 R₀)` for `R₀ < 1`, is zero. An immediate corollary of the
statement `CIV.timeZeroSingularSetNull`, since `closure (vec3Ball 0 R₀) ⊆ vec3Ball 0 1` for
`0 < R₀ < 1`. -/
theorem hausdorffMeasure_singularSlice_closedBall_eq_zero
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₀ : ℝ) (hR₀pos : 0 < R₀) (hR₀ : R₀ < 1) :
    μH[(1 : ℝ)] (singularSlice u ∩ closure (vec3Ball (0 : Vec3) R₀)) = 0 := by
  have hnull : μH[(1 : ℝ)] (singularSlice u ∩ vec3Ball (0 : Vec3) 1) = 0 :=
    CIV.timeZeroSingularSetNull q u Du p f hsol henergy hu hp hf hMf
  have hsub : singularSlice u ∩ closure (vec3Ball (0 : Vec3) R₀) ⊆
      singularSlice u ∩ vec3Ball (0 : Vec3) 1 := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [closure_vec3Ball hR₀pos] at hx
    have hx2 : vec3EuclideanNorm x ≤ R₀ := by simpa using hx.2
    rw [mem_vec3Ball, sub_zero]
    linarith only [hx2, hR₀]
  exact measure_mono_null hsub hnull

/-! ### The axis-inclusive null radial projection -/

/-- Almost every radius carries no point of the (axis-inclusive) singular slice inside the
open unit ball: the conclusion `μH[1] (singularSlice u ∩ vec3Ball 0 1) = 0` of the statement
`CIV.timeZeroSingularSetNull` pushed forward along the Lipschitz map `vec3EuclideanNorm`
(`vec3EuclideanNorm_lipschitzWith`), using `CIV.ae_notMem_image_of_hausdorffMeasure_one_eq_zero`.
This is the radial-projection step of `lem:aniso:annulus`. -/
theorem ae_forall_vec3EuclideanNorm_ne_of_singularSlice
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f) :
    ∀ᵐ R : ℝ, ∀ x : Vec3, x ∈ singularSlice u ∩ vec3Ball (0 : Vec3) 1 →
      vec3EuclideanNorm x ≠ R := by
  have hnull : μH[(1 : ℝ)] (singularSlice u ∩ vec3Ball (0 : Vec3) 1) = 0 :=
    CIV.timeZeroSingularSetNull q u Du p f hsol henergy hu hp hf hMf
  have h := ae_notMem_image_of_hausdorffMeasure_one_eq_zero vec3EuclideanNorm_lipschitzWith hnull
  filter_upwards [h] with R hR x hx heq
  exact hR ⟨x, hx, heq⟩

/-! ### A uniform bound on a space-time annulus in `(R₁, R₀)` -/

/-- The choice of radius in `lem:aniso:annulus`: given `0 ≤ R₁ < R₀ < 1`, there are radii
`R₋ < R₊` inside `(R₁, R₀)`, a time `t₀ ∈ (-1, 0)`, and a bound `M` such that `u` is
uniformly bounded, in Euclidean norm, on the cylindrical annulus `{R₋ < |x| < R₊} × (t₀, 0)`.
Almost every radius in `(R₁, R₀)` carries no point of the singular slice on its sphere
(`ae_forall_vec3EuclideanNorm_ne_of_singularSlice`, from `CIV.timeZeroSingularSetNull`); since
`Ioo R₁ R₀` has positive Lebesgue measure such a radius `R` exists, and
`CIV.exists_annulus_bound_of_sphere_disjoint` turns the sphere `{|x| = R}`, disjoint from
the singular slice, into a uniform bound on an annulus around it by compactness; the annulus
is finally shrunk so its inner and outer radii stay inside `(R₁, R₀)`. -/
theorem exists_annulus_bound_of_timeZeroSingularSetNull
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1) :
    ∃ Rlo Rhi t₀ M : ℝ, R₁ < Rlo ∧ Rlo < Rhi ∧ Rhi < R₀ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧
      ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
        ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ M := by
  have hae := ae_forall_vec3EuclideanNorm_ne_of_singularSlice q u Du p f hsol henergy hu hp hf hMf
  have hIooPos : volume (Ioo R₁ R₀) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by linarith only [hR₁R₀])).ne'
  have hexists : ∃ R ∈ Ioo R₁ R₀, ∀ x : Vec3, x ∈ singularSlice u ∩ vec3Ball (0 : Vec3) 1 →
      vec3EuclideanNorm x ≠ R := by
    by_contra hcon
    push Not at hcon
    have hsub : Ioo R₁ R₀ ⊆ {R : ℝ | ¬ ∀ x : Vec3, x ∈ singularSlice u ∩ vec3Ball (0 : Vec3) 1 →
        vec3EuclideanNorm x ≠ R} := by
      intro R hR hp
      obtain ⟨x, hx, hxeq⟩ := hcon R hR
      exact hp x hx hxeq
    have hnullset : volume {R : ℝ | ¬ ∀ x : Vec3, x ∈ singularSlice u ∩ vec3Ball (0 : Vec3) 1 →
        vec3EuclideanNorm x ≠ R} = 0 := ae_iff.mp hae
    have hle : volume (Ioo R₁ R₀) ≤
        volume {R : ℝ | ¬ ∀ x : Vec3, x ∈ singularSlice u ∩ vec3Ball (0 : Vec3) 1 →
          vec3EuclideanNorm x ≠ R} := measure_mono hsub
    rw [hnullset] at hle
    exact hIooPos (le_antisymm hle zero_le)
  obtain ⟨R, hRmem, hRprop⟩ := hexists
  have hRpos : 0 < R := lt_of_le_of_lt hR₁ hRmem.1
  have hRlt1 : R < 1 := lt_trans hRmem.2 hR₀
  have hdisj : ∀ x : Vec3, vec3EuclideanNorm x = R → x ∉ singularSlice u := by
    intro x hxeq hxsing
    have hxball : x ∈ vec3Ball (0 : Vec3) 1 := by
      rw [mem_vec3Ball, sub_zero, hxeq]
      exact hRlt1
    exact hRprop x ⟨hxsing, hxball⟩ hxeq
  obtain ⟨δ, t₀, M, hδpos, ht₀, hbound⟩ := exists_annulus_bound_of_sphere_disjoint hRpos hdisj
  set δ' : ℝ := min δ (min ((R - R₁) / 2) ((R₀ - R) / 2)) with hδ'def
  have hδ'pos : 0 < δ' :=
    lt_min hδpos (lt_min (by linarith only [hRmem.1]) (by linarith only [hRmem.2]))
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'left : δ' ≤ (R - R₁) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'right : δ' ≤ (R₀ - R) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R - δ', R + δ', t₀, M, ?_, ?_, ?_, ht₀, ?_⟩
  · linarith only [hδ'left, hRmem.1]
  · linarith only [hδ'pos]
  · linarith only [hδ'right, hRmem.2]
  · intro x hxlo hxhi t ht
    refine hbound x ?_ ?_ t ht
    · linarith only [hxlo, hδ'δ]
    · linarith only [hxhi, hδ'δ]

end CIV
