/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AnnulusBoundAssembly
public import LeanPool.CIVAxisymmetric.Closure.CirculationBound

/-!
### Assembly of the regular-annulus lemma with whole-ball circulation

`lem:aniso:annulus` is the paper's regular-annulus lemma: from a suitable weak solution smooth on
compact subsets of Q with a `C²`-bounded force, and radii `R₁ < R₀ < 1`, it produces a strictly
smaller annulus and a time `t₀` on which `u`, `∇u`, `∇²u` are bounded, and a circulation bound on
every sub-radius. It has three ingredients: the choice of the annulus via the null Hausdorff
measure of the singular set (`exists_annulus_bound_of_timeZeroSingularSetNull`), the circulation
bound from an order-0 velocity bound, and the interior derivative estimate for the Navier–Stokes
system (Serrin, Section 4, m = 1). The last is the explicit hypothesis `hserrin`, as in
`step_annulus_derivative_bounds`; `CIV.Main.regularAnnulus` discharges it with
`CIV.Main.serrinInteriorEstimates`. The circulation bound here is the whole-ball form
`forall_Rstar_exists_circulation_bound_ball_of_annulus_bound`, which delivers the circulation
clause in the shape of the statement `CIV.regularAnnulus`, in place of the sub-annulus form
`forall_Rstar_exists_circulation_bound_of_annulus_bound` used by
`exists_annulus_bound_conditional_on_serrin`. The hypotheses `hsolClassical`, `haxi` and `hfaxi`
carry the data of the axis maximum principle that the whole-ball bound requires.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_annulus_bound_wholeBall_conditional_on_serrin
    (q : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hsolClassical : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
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
      (∃ M : ℝ, ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ M) ∧
      ∀ Rstar ∈ Ioo Rm Rp, ∃ CΓ : ℝ,
        ∀ x : Vec3, vec3EuclideanNorm x < Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ),
          |circulation u (x, t)| ≤ CΓ := by
  obtain ⟨Rlo, Rhi, t₀, M, hR1lo, hlohi, hhiR0, ht₀, hbdd⟩ :=
    exists_annulus_bound_of_timeZeroSingularSetNull q u Du p f hsol henergy hu hp hf hMf R₁ R₀
      hR₁ hR₁R₀ hR₀
  have hRlo0 : 0 ≤ Rlo := by linarith only [hR₁, hR1lo.le]
  have hRhi1 : Rhi ≤ 1 := by linarith only [hhiR0.le, hR₀.le]
  have hinst := hserrin Rlo Rhi t₀ M hRlo0 hlohi hRhi1 ht₀
  obtain ⟨Rm, Rp, t₀', hRloRm, hRmRp, hRpRhi, ht₀t₀', ht₀'0, K, hK⟩ :=
    step_annulus_derivative_bounds u Rlo Rhi t₀ ⟨hRlo0, hlohi, hRhi1⟩ ht₀ M hbdd hinst
  obtain ⟨Mf, hMf1⟩ := exists_bound_force_swirl_of_forceC2Bounded f hMf
  have hRhi1' : Rhi < 1 := lt_trans hhiR0 hR₀
  have hcirc :=
    forall_Rstar_exists_circulation_bound_ball_of_annulus_bound u p f hsolClassical haxi hfaxi
      Mf hMf1 Rlo Rhi t₀ M hRlo0 hRhi1' ht₀ hbdd
  refine ⟨Rm, Rp, t₀', by linarith only [hR1lo, hRloRm], hRmRp, by linarith only [hRpRhi, hhiR0],
    ⟨ht₀.1.trans (by linarith only [ht₀t₀']), ht₀'0⟩, ⟨K, hK⟩, ?_⟩
  intro Rstar hRstar
  have hRstar_lo_hi : Rstar ∈ Ioo Rlo Rhi :=
    ⟨lt_trans hRloRm hRstar.1, lt_trans hRstar.2 hRpRhi⟩
  obtain ⟨CΓ, hCΓ⟩ := hcirc Rstar hRstar_lo_hi
  refine ⟨CΓ, ?_⟩
  intro x hxnorm t ht
  have ht_t₀ : t ∈ Ioo t₀ (0 : ℝ) := ⟨lt_trans ht₀t₀' ht.1, ht.2⟩
  have hx_mem : x ∈ vec3Ball (0 : Vec3) Rstar := by
    simpa [mem_vec3Ball, sub_zero] using hxnorm
  exact hCΓ t ht_t₀ x hx_mem

/-!
### Representative radius between two annulus bounds

The second theorem picks out a representative radius strictly between the two
annulus bounds `Rm` and `Rp` produced by the regular-annulus lemma, exactly as
`lem:aniso:closure`'s proof does when it fixes `R_*` inside `(R_-, R_+)`. -/

theorem circulation_bound_wholeBall_at_representative_radius_conditional_on_serrin
    {u : ParabolicPoint → Vec3} {Rm Rp t₀ : ℝ}
    (h1 : ∀ Rstar ∈ Ioo Rm Rp, ∃ CΓ : ℝ,
        ∀ x : Vec3, vec3EuclideanNorm x < Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ),
          |circulation u (x, t)| ≤ CΓ)
    (h2 : Rm < Rp) :
    ∃ Rstar CΓ : ℝ, Rm < Rstar ∧ Rstar < Rp ∧
      ∀ x : Vec3, vec3EuclideanNorm x < Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ),
        |circulation u (x, t)| ≤ CΓ := by
  set Rstar := (Rm + Rp) / 2 with hRstar
  have hRmRstar : Rm < Rstar := by
    dsimp [Rstar]
    linarith only [h2]
  have hRstarRp : Rstar < Rp := by
    dsimp [Rstar]
    linarith only [h2]
  obtain ⟨CΓ, hCΓ⟩ := h1 Rstar ⟨hRmRstar, hRstarRp⟩
  exact ⟨Rstar, CΓ, hRmRstar, hRstarRp, hCΓ⟩

end CIV
