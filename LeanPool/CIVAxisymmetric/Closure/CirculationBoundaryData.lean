/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.RegularSphereFull
public import LeanPool.CIVAxisymmetric.Reduction.AnnulusCirculationBound

/-! ### Circulation bounds from an annulus bound

The circulation `Γ = x₁ u₂ − x₂ u₁` of a vector field `u` satisfies a plain bound
`|Γ| ≤ 2RM` whenever `|u| ≤ M` on a ball of radius `R` (by `abs_circulation_le_two_mul_of_bound`).
On a sub‑annulus of the regular annulus where only the order‑0 derivative is bounded,
the circulation is controlled by `2 R⋆ M` for any `R⋆` of the annulus, via
`circulation_hbdry_of_annulus_bound`.  The third theorem assembles the main-result statement
`CIV.timeZeroSingularSetNull` with the elementary circulation bound to produce the
parabolic‑boundary data that `lem:aniso:axis` needs for the lateral boundary of its
regular‑sphere closure argument.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem abs_circulation_le_of_vec3EuclideanNorm_bound {u : ParabolicPoint → Vec3}
    {x : Vec3} {t R M : ℝ} (hR : vec3EuclideanNorm x = R)
    (hbound : vec3EuclideanNorm (u (x, t)) ≤ M) :
    |circulation u (x, t)| ≤ 2 * R * M := by
  have hRle : vec3EuclideanNorm x ≤ R := hR.le
  have h0 : |u (x, t) 0| ≤ M :=
    (abs_apply_le_vec3EuclideanNorm (u (x, t)) 0).trans hbound
  have h1 : |u (x, t) 1| ≤ M :=
    (abs_apply_le_vec3EuclideanNorm (u (x, t)) 1).trans hbound
  exact abs_circulation_le_two_mul_of_bound hRle h0 h1

theorem circulation_hbdry_of_annulus_bound {u : ParabolicPoint → Vec3} {Rlo Rhi t₀ M : ℝ}
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ M) :
    ∀ Rstar ∈ Ioo Rlo Rhi, ∀ x : Vec3, vec3EuclideanNorm x = Rstar →
      ∀ t ∈ Ioo t₀ (0 : ℝ), |circulation u (x, t)| ≤ 2 * Rstar * M := by
  intro Rstar hRstar x hx t ht
  rcases hRstar with ⟨hRstar_lo, hRstar_hi⟩
  have hlo : Rlo < vec3EuclideanNorm x := by rwa [hx]
  have hhi : vec3EuclideanNorm x < Rhi := by rwa [hx]
  have hM := hbound x hlo hhi t ht
  exact abs_circulation_le_of_vec3EuclideanNorm_bound hx hM

theorem exists_circulation_hbdry_of_timeZeroSingularSetNull
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1) :
    ∃ Rlo Rhi t₀ M : ℝ, R₁ < Rlo ∧ Rlo < Rhi ∧ Rhi < R₀ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧
      ∀ Rstar ∈ Ioo Rlo Rhi, ∀ x : Vec3, vec3EuclideanNorm x = Rstar →
        ∀ t ∈ Ioo t₀ (0 : ℝ), |circulation u (x, t)| ≤ 2 * Rstar * M := by
  obtain ⟨Rlo, Rhi, t₀, M, hR₁lo, hlo_hi, hhi_R₀, ht₀, hbound⟩ :=
    exists_annulus_bound_of_timeZeroSingularSetNull q u Du p f hsol henergy hu hp hf hMf
      R₁ R₀ hR₁ hR₁R₀ hR₀
  exact ⟨Rlo, Rhi, t₀, M, hR₁lo, hlo_hi, hhi_R₀, ht₀, circulation_hbdry_of_annulus_bound hbound⟩

end CIV
