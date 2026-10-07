/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Circulation
public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
### Circulation bounds from pointwise and annulus bounds

The circulation `Γ = x₁ u₂ − x₂ u₁` of a vector field `u` on a parabolic point `z`
satisfies a plain bound `2RM` whenever `|u| ≤ M` on a ball of radius `R`.  On a
sub‑annulus of the regular annulus where only the order‑0 derivative is bounded,
the circulation is controlled by `2 R⋆ M` for any `R⋆ < Rₚ`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The circulation `Γ = x₁ u₂ − x₂ u₁` of a field bounded by `M` on a ball of
radius `R` is itself bounded by `2RM` there. -/
theorem abs_circulation_le_two_mul_of_bound {u : ParabolicPoint → Vec3} {z : ParabolicPoint}
    {R M : ℝ} (hR : vec3EuclideanNorm z.1 ≤ R) (h0 : |u z 0| ≤ M) (h1 : |u z 1| ≤ M) :
    |circulation u z| ≤ 2 * R * M := by
  unfold circulation
  calc
    |z.1 0 * u z 1 - z.1 1 * u z 0| ≤ |z.1 0 * u z 1| + |z.1 1 * u z 0| := abs_sub _ _
    _ = |z.1 0| * |u z 1| + |z.1 1| * |u z 0| := by
      simp [abs_mul]
    _ ≤ R * M + R * M := by
      have hz0 : |z.1 0| ≤ R := (abs_apply_le_vec3EuclideanNorm z.1 0).trans hR
      have hz1 : |z.1 1| ≤ R := (abs_apply_le_vec3EuclideanNorm z.1 1).trans hR
      have hn0 : 0 ≤ |u z 0| := abs_nonneg _
      have hn1 : 0 ≤ |u z 1| := abs_nonneg _
      have hRnonneg : 0 ≤ R := by
        linarith only [hz0, abs_nonneg (z.1 0)]
      apply add_le_add
      · exact mul_le_mul hz0 h1 hn1 hRnonneg
      · exact mul_le_mul hz1 h0 hn0 hRnonneg
    _ = 2 * R * M := by ring

/-- On a sub‑annulus `Rm < |x| < R⋆` of the regular annulus of `lem:aniso:annulus`,
the circulation of `u` is bounded, using only the order‑0 case of the annulus's
derivative bound. -/
theorem exists_circulation_bound_of_annulus_bound {u : ParabolicPoint → Vec3}
    {Rm Rp t₀ M : ℝ}
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M)
    {Rstar : ℝ} (hRstar : Rstar ≤ Rp) :
    ∃ CΓ : ℝ, ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rstar →
      ∀ t ∈ Ioo t₀ (0 : ℝ), |circulation u (x, t)| ≤ CΓ := by
  refine ⟨2 * Rstar * M, fun x hx1 hx2 t ht => ?_⟩
  have hx2' : vec3EuclideanNorm x < Rp := hx2.trans_le hRstar
  have hbound0 := hbound x hx1 hx2' t ht 0 ![0, 0, 0] (by decide)
  have hbound1 := hbound x hx1 hx2' t ht 1 ![0, 0, 0] (by decide)
  have hx := hx2.le
  simp only [multiPartial, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.iterate_zero, id] at hbound0 hbound1
  have h0 : |u (x, t) 0| ≤ M := hbound0
  have h1 : |u (x, t) 1| ≤ M := hbound1
  exact abs_circulation_le_two_mul_of_bound hx h0 h1

/-- The circulation bound of the previous theorem, quantified over every radius
`R⋆ ∈ Ioo Rm Rp`.

The conclusion is confined to the open sub-annulus `Rm < |x| < R⋆`. It asserts nothing at
`|x| ≤ Rm`, hence nothing on the symmetry axis or on the inner ball, so it is weaker than the
circulation clause of `lem:aniso:annulus`, which bounds `Γ` on the whole ball `B(R⋆)`. The
whole-ball statement is `CIV.forall_Rstar_exists_circulation_bound_ball_of_annulus_bound`; it
needs the maximum principle to fill in the inner ball and does not follow from the algebraic
bound used here. -/
theorem forall_Rstar_exists_circulation_bound_of_annulus_bound {u : ParabolicPoint → Vec3}
    {Rm Rp t₀ M : ℝ}
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M) :
    ∀ Rstar ∈ Ioo Rm Rp, ∃ CΓ : ℝ, ∀ x : Vec3, Rm < vec3EuclideanNorm x →
      vec3EuclideanNorm x < Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ), |circulation u (x, t)| ≤ CΓ := by
  intro Rstar hRstar
  exact exists_circulation_bound_of_annulus_bound hbound hRstar.2.le

end CIV
