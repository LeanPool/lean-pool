/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.AxisQuotients
public import LeanPool.CIVAxisymmetric.Zoom.SubsequenceDichotomy

/-! ### Helper lemmas for the contradiction dichotomy -/

public section

open Set Filter
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem strictMono_comp_and_tendsto_zero_of_reindex {t : ℕ → ℝ} (ht_mono : StrictMono t)
    (ht_tendsto : Tendsto t atTop (nhds 0)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (t ∘ φ) ∧ Tendsto (t ∘ φ) atTop (nhds 0) := by
  exact ⟨ht_mono.comp hφ, ht_tendsto.comp hφ.tendsto_atTop⟩

theorem zoomScale_sq_eq_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    Real.sqrt (-t) ^ 2 = -t := by
  rw [Real.sq_sqrt (by linarith only [ht.2] : (0 : ℝ) ≤ -t)]

/-! ### Dichotomy for `prop:aniso:small`'s proof by contradiction -/

/-- The reindexed contradiction data and finite-axis/receding-axis dichotomy for
`prop:aniso:small`'s proof by contradiction (its common set-up): from a failure of
`MeridionalSmallness`, a sequence of points and times realizing the
`eq:aniso:G`-lower-bound, refined along a subsequence on which the radial coordinate divided by the
zoom scale `λ n = √(−t n)` is either bounded (Step 2, finite axis) or tends to infinity (Step 3,
receding axis). -/
theorem exists_seq_three_terms_dichotomy {ρ h C : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hb : AnisotropicBounds C h u) (hh : 0 < h)
    (hρ : ρ ≤ 1) (hnot : ¬ MeridionalSmallness ρ u) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ t x₁ x₃ : ℕ → ℝ, (∀ n, 0 ≤ x₁ n) ∧ StrictMono t ∧
      Tendsto t atTop (nhds 0) ∧
      (∀ n, meridional (x₁ n) (x₃ n) ∈ vec3Ball (0 : Vec3) ρ) ∧
      (∀ n, t n ∈ Set.Ioo (-1 : ℝ) 0) ∧
      (∀ n, c₀ < (-(t n)) *
        (|spatialPartial (fun w => u w 0) 0 (meridional (x₁ n) (x₃ n), t n)| +
          |radialQuotient u (meridional (x₁ n) (x₃ n), t n)| +
          |spatialPartial (fun w => u w 2) 2 (meridional (x₁ n) (x₃ n), t n)|)) ∧
      ((∃ A : ℝ, ∀ n, x₁ n / Real.sqrt (-(t n)) ≤ A) ∨
        Tendsto (fun n => x₁ n / Real.sqrt (-(t n))) atTop atTop) := by
  obtain ⟨c₀, hc₀, t, x₁, x₃, hx₁nn, ht_mono, ht_tendsto, hmem, ht_mem, hineq⟩ :=
    exists_seq_three_terms hu haxi hb hh hρ hnot
  obtain ⟨φ, hφ, hdich⟩ := exists_subseq_bounded_or_tendsto_atTop (fun n => x₁ n / Real.sqrt
    (-(t n)))
  obtain ⟨hmono', htend'⟩ := strictMono_comp_and_tendsto_zero_of_reindex ht_mono ht_tendsto hφ
  refine ⟨c₀, hc₀, t ∘ φ, x₁ ∘ φ, x₃ ∘ φ, fun n => hx₁nn (φ n), hmono', htend', fun n => hmem (φ n),
    fun n => ht_mem (φ n), fun n => hineq (φ n), hdich⟩

end CIV
