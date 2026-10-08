/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.RegularSphereFull
public import LeanPool.CIVAxisymmetric.Reduction.AnnulusDerivativeBounds
public import LeanPool.CIVAxisymmetric.Reduction.AnnulusCirculationBound

/-!
### Assembly of the regular-annulus lemma

`lem:aniso:annulus` is the paper's regular-annulus lemma: from a suitable weak solution smooth on
compact subsets of Q with a `C²`-bounded force, and radii `R₁ < R₀ < 1`, it produces a strictly
smaller annulus and a time `t₀` on which `u`, `∇u`, `∇²u` are bounded, and a circulation bound on
every sub-radius. It has three ingredients: the choice of the annulus via the null Hausdorff
measure of the singular set (`exists_annulus_bound_of_timeZeroSingularSetNull`), the circulation
bound from an order-0 velocity bound (`forall_Rstar_exists_circulation_bound_of_annulus_bound`),
and the interior derivative estimate for the Navier–Stokes system (Serrin, Section 4, m = 1). The
`*_conditional_on_serrin` statements take the last as an explicit hypothesis `hserrin`, as
`step_annulus_derivative_bounds` does; `CIV.Main.regularAnnulus` discharges it with
`CIV.Main.serrinInteriorEstimates`. In this file the circulation bound is restricted to the
annulus `Rm < |x| < Rstar` that `forall_Rstar_exists_circulation_bound_of_annulus_bound`
delivers; `exists_annulus_bound_wholeBall_conditional_on_serrin` gives it on the full ball
`B(Rstar)`, as stated in the manuscript.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_derivative_bound_conditional_on_serrin
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1)
    (hserrin : ∀ Rm Rp t₀ Mu : ℝ, 0 ≤ Rm → Rm < Rp → Rp ≤ 1 → t₀ ∈ Ioo (-1 : ℝ) 0 →
      (∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ Mu) →
      ∀ Rm' Rp' t₀' : ℝ, Rm < Rm' → Rm' < Rp' → Rp' < Rp → t₀ < t₀' → t₀' < 0 →
      ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
        ∀ t ∈ Ioo t₀' (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K) :
    ∃ Rm Rp t₀ K : ℝ, R₁ < Rm ∧ Rm < Rp ∧ Rp < R₀ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧
      ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K := by
  obtain ⟨Rlo, Rhi, t₀, M, hR1lo, hlohi, hhiR0, ht₀, hbdd⟩ :=
    exists_annulus_bound_of_timeZeroSingularSetNull q u Du p f hsol henergy hu hp hf hMf R₁ R₀
      hR₁ hR₁R₀ hR₀
  have hRlo0 : 0 ≤ Rlo := by linarith only [hR₁, hR1lo.le]
  have hRhi1 : Rhi ≤ 1 := by linarith only [hhiR0.le, hR₀.le]
  have hinst := hserrin Rlo Rhi t₀ M hRlo0 hlohi hRhi1 ht₀
  obtain ⟨Rm', Rp', t₀', hRmRm', hRm'Rp', hRp'Rp, ht₀t₀', ht₀'0, K, hK⟩ :=
    step_annulus_derivative_bounds u Rlo Rhi t₀ ⟨hRlo0, hlohi, hRhi1⟩ ht₀ M hbdd hinst
  refine ⟨Rm', Rp', t₀', K, by linarith only [hR1lo, hRmRm'], hRm'Rp', by linarith only [hRp'Rp,
    hhiR0],
    ⟨ht₀.1.trans (by linarith only [ht₀t₀']), ht₀'0⟩, hK⟩

theorem exists_circulation_bound_conditional_on_serrin
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1)
    (hserrin : ∀ Rm Rp t₀ Mu : ℝ, 0 ≤ Rm → Rm < Rp → Rp ≤ 1 → t₀ ∈ Ioo (-1 : ℝ) 0 →
      (∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ Mu) →
      ∀ Rm' Rp' t₀' : ℝ, Rm < Rm' → Rm' < Rp' → Rp' < Rp → t₀ < t₀' → t₀' < 0 →
      ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
        ∀ t ∈ Ioo t₀' (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K) :
    ∃ Rm Rp t₀ : ℝ, R₁ < Rm ∧ Rm < Rp ∧ Rp < R₀ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧
      ∀ Rstar ∈ Ioo Rm Rp, ∃ CΓ : ℝ, ∀ x : Vec3, Rm < vec3EuclideanNorm x →
        vec3EuclideanNorm x < Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ), |circulation u (x, t)| ≤ CΓ := by
  obtain ⟨Rm, Rp, t₀, K, h1, h2, h3, h4, hbound⟩ :=
    exists_derivative_bound_conditional_on_serrin q u Du p f hsol henergy hu hp hf hMf R₁ R₀
      hR₁ hR₁R₀ hR₀ hserrin
  exact ⟨Rm, Rp, t₀, h1, h2, h3, h4, forall_Rstar_exists_circulation_bound_of_annulus_bound hbound⟩

theorem exists_annulus_bound_conditional_on_serrin
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1)
    (hserrin : ∀ Rm Rp t₀ Mu : ℝ, 0 ≤ Rm → Rm < Rp → Rp ≤ 1 → t₀ ∈ Ioo (-1 : ℝ) 0 →
      (∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ Mu) →
      ∀ Rm' Rp' t₀' : ℝ, Rm < Rm' → Rm' < Rp' → Rp' < Rp → t₀ < t₀' → t₀' < 0 →
      ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
        ∀ t ∈ Ioo t₀' (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K) :
    ∃ Rm Rp t₀ : ℝ, R₁ < Rm ∧ Rm < Rp ∧ Rp < R₀ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧
      (∃ K : ℝ, ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K) ∧
      ∀ Rstar ∈ Ioo Rm Rp, ∃ CΓ : ℝ, ∀ x : Vec3, Rm < vec3EuclideanNorm x →
        vec3EuclideanNorm x < Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ), |circulation u (x, t)| ≤ CΓ := by
  obtain ⟨Rm, Rp, t₀, K, h1, h2, h3, h4, hbound⟩ :=
    exists_derivative_bound_conditional_on_serrin q u Du p f hsol henergy hu hp hf hMf R₁ R₀
      hR₁ hR₁R₀ hR₀ hserrin
  exact ⟨Rm, Rp, t₀, h1, h2, h3, h4, ⟨K, hbound⟩,
    forall_Rstar_exists_circulation_bound_of_annulus_bound hbound⟩

theorem circulation_bound_at_representative_radius_conditional_on_serrin
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1)
    (hserrin : ∀ Rm Rp t₀ Mu : ℝ, 0 ≤ Rm → Rm < Rp → Rp ≤ 1 → t₀ ∈ Ioo (-1 : ℝ) 0 →
      (∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ Mu) →
      ∀ Rm' Rp' t₀' : ℝ, Rm < Rm' → Rm' < Rp' → Rp' < Rp → t₀ < t₀' → t₀' < 0 →
      ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
        ∀ t ∈ Ioo t₀' (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K) :
    ∃ Rm Rp t₀ Rstar CΓ : ℝ, R₁ < Rm ∧ Rm < Rstar ∧ Rstar < Rp ∧ Rp < R₀ ∧
      t₀ ∈ Ioo (-1 : ℝ) 0 ∧ ∀ x : Vec3, Rm < vec3EuclideanNorm x →
        vec3EuclideanNorm x < Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ), |circulation u (x, t)| ≤ CΓ := by
  obtain ⟨Rm, Rp, t₀, h1, h2, h3, h4, hcirc⟩ :=
    exists_circulation_bound_conditional_on_serrin q u Du p f hsol henergy hu hp hf hMf R₁ R₀
      hR₁ hR₁R₀ hR₀ hserrin
  set Rstar := (Rm + Rp) / 2 with hRstar
  have hRmRstar : Rm < Rstar := by
    dsimp [Rstar]
    linarith only [h2]
  have hRstarRp : Rstar < Rp := by
    dsimp [Rstar]
    linarith only [h2]
  obtain ⟨CΓ, hCΓ⟩ := hcirc Rstar ⟨hRmRstar, hRstarRp⟩
  exact ⟨Rm, Rp, t₀, Rstar, CΓ, h1, hRmRstar, hRstarRp, h3, h4, hCΓ⟩

end CIV
