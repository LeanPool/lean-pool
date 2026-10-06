/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointDeriv
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointSmooth

/-!
# Jointly smooth representative from all-order slice curves

`lem:lps-Bochner-joint-smooth`: if the slices of a scalar space-time field are
`L²`-continuous curves of all-order Sobolev families whose spatial pairings are
differentiable in time with derivative the next slice, then the field has a
representative that is `C^∞` on `ℝ³ × [a,b]`, with one-sided time derivatives at
the endpoints.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Fréchet derivative of a differentiable function on `ℝ³` is the sum of its
coordinate derivatives. -/
theorem lps_hasFDerivAt_sum_spatialDeriv {h : Vec3 → ℝ} (hd : Differentiable ℝ h) (x : Vec3) :
    HasFDerivAt h (∑ i : Fin 3, spatialDeriv h i x •
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) x := by
  have hfder : fderiv ℝ h x = ∑ i : Fin 3, spatialDeriv h i x •
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ) := by
    ext v
    simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hv : v = ∑ j : Fin 3, v j • basisVec j := by
      simpa using (CKN.sum_smul_basisVec v).symm
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  rw [← hfder]
  exact (hd x).hasFDerivAt

/-- `lem:lps-Bochner-joint-smooth`: a scalar space-time field whose slices form
`L²`-continuous curves of all-order Sobolev families with pairing-differentiable
time chain has a representative that is `C^∞` on the closed slab. -/
theorem lps_smooth_rep_of_curves {a b : ℝ} (hab : a < b)
    {Z : ℕ → ℝ → List (Fin 3) → Vec3 → ℝ}
    (hfam : ∀ j : ℕ, ∀ t ∈ Icc a b, ∀ m : ℕ, IsSobolevFamilyOn m univ (Z j t []) (Z j t))
    (hcont : ∀ (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z j s α - Z j t α) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (hderiv : ∀ (j : ℕ) (α : List (Fin 3)) (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s => ∫ x, Z j s α x * ψ x)
          (∫ x, Z (j + 1) t α x * ψ x) (Icc a b) t) :
    ∃ R : Vec3 × ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) R ((univ : Set Vec3) ×ˢ Icc a b) ∧
      ∀ t ∈ Icc a b, (fun x => R (x, t)) =ᵐ[volume] Z 0 t [] := by
  choose! B hB using fun (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) =>
    lps_sobolevFamily_smooth_rep (hfam j t ht)
  have hmem : ∀ (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc a b, MemLp (Z j t α) 2 volume := by
    intro j α t ht
    simpa only [Measure.restrict_univ] using (hfam j t ht α.length).memL2 α le_rfl
  have hBs : ∀ (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc a b,
      ContDiff ℝ (⊤ : ℕ∞) (wordDeriv α (B j t)) ∧ wordDeriv α (B j t) =ᵐ[volume] Z j t α :=
    fun j α t ht => ⟨contDiff_wordDeriv (hB j t ht).1 α, (hB j t ht).2.2.1 α⟩
  have hBs0 : ∀ (j : ℕ), ∀ t ∈ Icc a b,
      ContDiff ℝ (⊤ : ℕ∞) (B j t) ∧ B j t =ᵐ[volume] Z j t [] :=
    fun j t ht => ⟨(hB j t ht).1, (hB j t ht).2.1⟩
  have hcW : ∀ (j : ℕ) (α : List (Fin 3)),
      ContinuousOn (fun z : Vec3 × ℝ => wordDeriv α (B j z.2) z.1)
        ((univ : Set Vec3) ×ˢ Icc a b) := fun j α =>
    lps_wordDeriv_rep_jointContinuousOn (hfam j) (hcont j) (hBs0 j) α
  let w : ℕ → List (Fin 3) → Vec3 × ℝ → ℝ := fun j α z => wordDeriv α (B j z.2) z.1
  have hx : ∀ j α, ∀ t ∈ Icc a b, ∀ x : Vec3,
      HasFDerivAt (fun y => w j α (y, t))
        (∑ i : Fin 3, w j (α ++ [i]) (x, t) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) x := by
    intro j α t ht x
    have hd : Differentiable ℝ (wordDeriv α (B j t)) :=
      (contDiff_wordDeriv (hB j t ht).1 α).differentiable (by simp)
    have := lps_hasFDerivAt_sum_spatialDeriv hd x
    simp only [w, ← wordDeriv_append] at this ⊢
    exact this
  have ht : ∀ j α, ∀ x : Vec3, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => w j α (x, s)) (w (j + 1) α (x, t)) (Icc a b) t := by
    intro j α x t ht
    exact lps_pointwise_time_hasDerivWithinAt hab
      (Z := fun s => Z j s α) (Z' := fun s => Z (j + 1) s α)
      (B := fun s => wordDeriv α (B j s)) (B' := fun s => wordDeriv α (B (j + 1) s))
      (hBs j α) (hBs (j + 1) α) (hmem (j + 1) α) (hcont (j + 1) α)
      (fun ψ hψ hψc => hderiv j α ψ hψ hψc) (hcW (j + 1) α) x t ht
  refine ⟨w 0 [], lps_slab_contDiffOn hab hcW hx ht 0 [], fun t ht => ?_⟩
  exact (hB 0 t ht).2.1

end ESS

end
