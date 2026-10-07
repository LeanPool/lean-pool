/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateChain
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateStrongFormAE
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit

/-!
# The energy balance for the gradient of a strong solution

Testing the strong form of the equation against `Δu ∈ J` at almost every time
and using the chain rule for `‖∇u‖²` gives
`d/dt ‖∇u‖² + 2‖Δu‖² = 2 ∫ (u·∇)u · Δu` (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The energy balance of `lem:lps-H1-estimate`: the gradient energy is
absolutely continuous and, almost everywhere,
`d/dt ‖∇u‖² + 2‖Δu‖² = 2 ∫ (u·∇)u · Δu`. -/
theorem lps_h1_energy_balance
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hU : IsLpsStrongSolution t₀ t₁ u Du p)
    (hD : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu)
    (hMD2 : MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hIdentity : ∀ s t, s ∈ Icc t₀ t₁ → t ∈ Icc t₀ t₁ → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) -
          2 * ∫ z in spaceTimeSet Set.univ (Ioo s t),
            ∑ i, Dtu z i * (∑ j, D2u z i j j)) :
    AbsolutelyContinuousOnInterval
        (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) t₀ t₁ ∧
      ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
        deriv (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) t +
            2 * (∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) ^ 2) =
          2 * ∫ x : Vec3, ∑ i : Fin 3,
            (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * (∑ j : Fin 3, D2u (x, t) i j j) := by
  have hlt : t₀ < t₁ := hU.1
  obtain ⟨hAC, hderiv⟩ := ESS.LPS.lps_h1_energy_ac_of_ordered_identity hlt.le hMDt hMD2
    hIdentity
  obtain ⟨hMu, hMDu⟩ : MemLp u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) := by
    rcases hU with ⟨-, -, -, ⟨_, _, -, h1, h2, -, -⟩, -, -⟩
    exact ⟨h1, h2⟩
  refine ⟨hAC, ?_⟩
  have hderiv' := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hderiv
  filter_upwards [hderiv', lps_strong_form_orthogonal_J_ae hU hD hMu hMDu hMD2 hMDt,
    lps_strong_good_slices hU hD hMu hMDu hMD2 hMDt,
    ae_restrict_mem measurableSet_Ioo] with t hdt hJ hgood htI
  obtain ⟨hDt, hD2, hgrad, htr⟩ := hgood
  have htIcc : t ∈ Icc t₀ t₁ := ⟨htI.1.le, htI.2.le⟩
  obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hU htIcc
  have hH1t := (lps_strong_solution_slice_h1 hU htIcc).2.2
  have hgu := lps_strong_solution_slice_weak_gradient hU htIcc
  have hN (i : Fin 3) := lps_h1_convection_memLp_two (u := fun x => u (x, t))
    (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t)) hu2t hDu2t hD2 hH1t hgrad i
  have hlapJ : IsInJ (fun x i => ∑ j : Fin 3, D2u (x, t) i j j) :=
    isInJ_iff_weakDivFree.mpr (lps_h1_laplacian_weak_div_free hu2t hDu2t hD2 hgu hgrad
      (lps_strong_solution_slice_weak_div_free hU htIcc).2)
  have hlap (i : Fin 3) : MemLp (fun x : Vec3 => ∑ j : Fin 3, D2u (x, t) i j j) 2 volume :=
    memLp_finsetSum Finset.univ fun j _ => ((hD2.eval i).eval j).eval j
  have hz := hJ _ hlapJ
  have i1 : Integrable (fun x : Vec3 => ∑ i : Fin 3,
      Dtu (x, t) i * (∑ j : Fin 3, D2u (x, t) i j j)) volume :=
    integrable_finsetSum _ fun i _ => (hDt.eval i).integrable_mul (hlap i)
  have i2 : Integrable (fun x : Vec3 => ∑ i : Fin 3,
      (∑ j : Fin 3, D2u (x, t) i j j) * (∑ j : Fin 3, D2u (x, t) i j j)) volume :=
    integrable_finsetSum _ fun i _ => (hlap i).integrable_mul (hlap i)
  have i3 : Integrable (fun x : Vec3 => ∑ i : Fin 3,
      (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * (∑ j : Fin 3, D2u (x, t) i j j)) volume :=
    integrable_finsetSum _ fun i _ => (hN i).integrable_mul (hlap i)
  have hpt (x : Vec3) : (∑ i : Fin 3, (Dtu (x, t) i - ∑ j : Fin 3, D2u (x, t) i j j +
        ∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * (∑ j : Fin 3, D2u (x, t) i j j)) =
      (∑ i : Fin 3, Dtu (x, t) i * (∑ j : Fin 3, D2u (x, t) i j j)) -
        (∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) * (∑ j : Fin 3, D2u (x, t) i j j)) +
        ∑ i : Fin 3, (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) *
          (∑ j : Fin 3, D2u (x, t) i j j) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hpt] at hz
  rw [lps_integral_sub_add i1 i2 i3] at hz
  have hsq : (∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) ^ 2) =
      ∫ x : Vec3, ∑ i : Fin 3,
        (∑ j : Fin 3, D2u (x, t) i j j) * (∑ j : Fin 3, D2u (x, t) i j j) := by
    congr 1
    funext x
    exact Finset.sum_congr rfl fun i _ => sq _
  rw [hdt, hsq]
  linarith only [hz]

end ESS

end
