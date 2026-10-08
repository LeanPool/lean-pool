/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateBalance
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateGronwall
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSerrinSlices
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSliceNorms
public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointEssSup

/-!
# Serrin control of the `H¹` norm of a strong solution

The gradient energy of a strong solution with finite mixed Serrin norm obeys
the Grönwall bound of `lem:lps-H1-estimate`, with a constant depending only on
the Serrin exponent.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Laplacian energy of a strong solution is integrable in time. -/
theorem lps_h1_laplacian_energy_integrable {a b : ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    (hMD2 : MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo a b)))) :
    Integrable (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) ^ 2)
      (volume.restrict (Ioo a b)) := by
  have hν := lps_memLp_slab_to_prod hMD2
  have hlap (i : Fin 3) : MemLp (fun q : Vec3 × ℝ =>
      ∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) 2
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    memLp_finsetSum Finset.univ fun j _ => ((hν.eval i).eval j).eval j
  have hint : Integrable (fun q : Vec3 × ℝ =>
      ∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    integrable_finsetSum _ fun i _ =>
      (memLp_two_iff_integrable_sq (hlap i).aestronglyMeasurable).mp (hlap i)
  exact hint.integral_prod_right

/-- Serrin control of the `H¹` norm in the finite branch (`lem:lps-H1-estimate`):
for a strong solution on `[t₀, t₁]` with finite mixed Serrin integral, the
gradient energy plus the integrated Laplacian energy is bounded by the initial
gradient energy times `exp (C ∫ ‖u‖ₛ^ℓ)`, `ℓ = 2s/(s-3)`, with `C` depending only
on `s`. The chain-rule identity of the strong class enters as an explicit
hypothesis. -/
theorem lps_h1_estimate_finite {s : ℝ} (hs : 3 < s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
        {Dtu : ParabolicPoint → Vec3},
      IsLpsStrongSolution t₀ t₁ u Du p →
      HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu →
      MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) →
      MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) →
      (∀ s t, s ∈ Icc t₀ t₁ → t ∈ Icc t₀ t₁ → s ≤ t →
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) -
            2 * ∫ z in spaceTimeSet Set.univ (Ioo s t),
              ∑ i, Dtu z i * (∑ j, D2u z i j j)) →
      (∫⁻ t in Ioo t₀ t₁,
        (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤ →
      ∀ t ∈ Icc t₀ t₁,
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) +
            ∫ τ in t₀..t, ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, τ) i j j) ^ 2 ≤
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2) *
            Real.exp (C * ∫ τ in t₀..t,
              (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, τ)))
                (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3))) := by
  obtain ⟨C₁, hC₁, hAbs⟩ := lps_h1_finite_differential_absorption hs
  set K : ℝ := 243 * (gagliardoNirenbergSobolevConstant.toReal) ^ (3 / s) * (2 : ℝ) ^ (3 / s)
    with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * C₁ * K ^ (2 * s / (s - 3)), by positivity, ?_⟩
  intro t₀ t₁ u Du p D2u Dtu hU hD hMD2 hMDt hIdentity hmix
  have hlt : t₀ < t₁ := hU.1
  obtain ⟨hMu, hMDu⟩ : MemLp u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) := by
    rcases hU with ⟨-, -, -, ⟨_, _, -, h1, h2, -, -⟩, -, -⟩
    exact ⟨h1, h2⟩
  obtain ⟨hAC, hbal⟩ := lps_h1_energy_balance hU hD hMD2 hMDt hIdentity
  let f : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2
  let d : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) ^ 2
  let m : ℝ → ℝ := fun t => (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
    (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3))
  have hf0 : ∀ t, 0 ≤ f t := fun t =>
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg _
  have hd0 : ∀ t, 0 ≤ d t := fun t =>
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdint : Integrable d (volume.restrict (Ioo t₀ t₁)) :=
    lps_h1_laplacian_energy_integrable hMD2
  have hmint : IntegrableOn m (Icc t₀ t₁) :=
    lps_h1_finite_time_moment_integrable_closed hMu.aestronglyMeasurable hs hmix
  have hIoo : (volume.restrict (Ioo t₀ t₁) : Measure ℝ) = volume.restrict (Icc t₀ t₁) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  have hdintIcc : IntegrableOn d (Icc t₀ t₁) := by
    rw [IntegrableOn, ← hIoo]
    exact hdint
  -- the differential inequality
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      deriv f t + d t ≤ (2 * C₁ * K ^ (2 * s / (s - 3))) * m t * f t := by
    filter_upwards [hbal, lps_strong_good_slices hU hD hMu hMDu hMD2 hMDt,
      lps_h1_finite_slice_memLp_ae hMu.aestronglyMeasurable hs hmix,
      ESS.LPS.lps_spatial_sobolev_slices_ae_of_weak_derivs hD hMu hMDu hMD2,
      ae_restrict_mem measurableSet_Ioo] with t hb hgood hUs hfam htI
    obtain ⟨hDt, hD2, hgrad, htr⟩ := hgood
    have htIcc : t ∈ Icc t₀ t₁ := ⟨htI.1.le, htI.2.le⟩
    obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hU htIcc
    have hlap2 : MemLp (fun x : Vec3 => (fun i => ∑ j : Fin 3, D2u (x, t) i j j : Vec3)) 2
        volume :=
      ESS.LPS.lps_h1_laplacian_memLp_two hD2 (fun x i => rfl)
    have hnl := ESS.LPS.lps_h1_finite_nonlinear_pairing_bound hs
      (u := fun x => u (x, t)) (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t))
      (lap := fun x i => ∑ j : Fin 3, D2u (x, t) i j j)
      hu2t.aestronglyMeasurable hUs hDu2t hD2 hgrad (fun x i => rfl)
    -- the norms of the derivatives
    have hB : (eLpNorm (fun x => Du (x, t)) 2 volume).toReal ≤ Real.sqrt (f t) :=
      lps_h1_gradient_norm_le hDu2t
    have hHess := lps_h1_slice_hessian_energy_eq (t := t) (u := u) (Du := Du) (D2u := D2u) hfam
    have hD' : (eLpNorm (fun x => D2u (x, t)) 2 volume).toReal ≤ Real.sqrt (d t) := by
      have := lps_h1_hessian_norm_le hD2
      rwa [hHess] at this
    have hf0t := hf0 t
    have hd0t := hd0 t
    set A : ℝ := (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal s) volume).toReal with hA
    have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
    have hθ0 : 0 ≤ (s - 3) / s := by
      have : 0 < s := by linarith only [hs]
      have : 0 ≤ s - 3 := by linarith only [hs]
      positivity
    have hθ1 : 0 ≤ 1 + 3 / s := by
      have : 0 < s := by linarith only [hs]
      positivity
    have hle : (∫ x : Vec3, ∑ i : Fin 3,
        (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * (∑ j : Fin 3, D2u (x, t) i j j)) ≤
        (K * A) * Real.sqrt (f t) ^ (1 - 3 / s) * Real.sqrt (d t) ^ (1 + 3 / s) := by
      refine (le_abs_self _).trans (hnl.trans ?_)
      have h1 : (eLpNorm (fun x => Du (x, t)) 2 volume).toReal ^ ((s - 3) / s) ≤
          Real.sqrt (f t) ^ ((s - 3) / s) := Real.rpow_le_rpow ENNReal.toReal_nonneg hB hθ0
      have h2 : (eLpNorm (fun x => D2u (x, t)) 2 volume).toReal ^ (1 + 3 / s) ≤
          Real.sqrt (d t) ^ (1 + 3 / s) := Real.rpow_le_rpow ENNReal.toReal_nonneg hD' hθ1
      have hex : (s - 3) / s = 1 - 3 / s := by
        have : s ≠ 0 := by linarith only [hs]
        field_simp
      rw [hex] at h1 ⊢
      calc _ = K * A * (eLpNorm (fun x => Du (x, t)) 2 volume).toReal ^ (1 - 3 / s) *
            (eLpNorm (fun x => D2u (x, t)) 2 volume).toReal ^ (1 + 3 / s) := by
            simp only [hK, hA]
        _ ≤ K * A * Real.sqrt (f t) ^ (1 - 3 / s) * Real.sqrt (d t) ^ (1 + 3 / s) := by
            gcongr
    have hbal' : deriv f t + 2 * d t ≤
        2 * ((K * A) * Real.sqrt (f t) ^ (1 - 3 / s) * Real.sqrt (d t) ^ (1 + 3 / s)) := by
      have : deriv f t + 2 * d t = 2 * ∫ x : Vec3, ∑ i : Fin 3,
          (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * (∑ j : Fin 3, D2u (x, t) i j j) := hb
      rw [this]
      linarith only [hle]
    have habs := hAbs (dy := deriv f t) (d := d t) (A := K * A) (B := Real.sqrt (f t))
      (D := Real.sqrt (d t)) (f := f t) (by positivity) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (Real.sq_sqrt hf0t) (Real.sq_sqrt hd0t) hbal'
    calc deriv f t + d t ≤ 2 * C₁ * (K * A) ^ (2 * s / (s - 3)) * f t := habs
      _ = (2 * C₁ * K ^ (2 * s / (s - 3))) * m t * f t := by
          rw [Real.mul_rpow hK0 hA0]
          simp only [m, hA]
          ring
  have hdiffIcc : ∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)),
      deriv f t + d t ≤ (2 * C₁ * K ^ (2 * s / (s - 3))) * m t * f t := by
    rw [← hIoo]
    exact hdiff
  have hgron := ESS.LPS.lps_h1_finite_branch_gronwall hlt.le hAC hdintIcc
    (Eventually.of_forall fun t => hd0 t) hmint (Eventually.of_forall fun t =>
      Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (by positivity) (fun t _ => hf0 t) hdiffIcc
  intro t ht
  exact hgron t ht

/-- Serrin control of the `H¹` norm in the endpoint branch `s = ∞`
(`lem:lps-H1-estimate`): the gradient energy plus the integrated Laplacian energy
is bounded by the initial gradient energy times `exp (C ∫ ‖u‖∞²)` with an
absolute constant `C`. -/
theorem lps_h1_estimate_infinite :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
        {Dtu : ParabolicPoint → Vec3},
      IsLpsStrongSolution t₀ t₁ u Du p →
      HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu →
      MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) →
      MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) →
      (∀ s t, s ∈ Icc t₀ t₁ → t ∈ Icc t₀ t₁ → s ≤ t →
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) -
            2 * ∫ z in spaceTimeSet Set.univ (Ioo s t),
              ∑ i, Dtu z i * (∑ j, D2u z i j j)) →
      (∫⁻ t in Ioo t₀ t₁,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤ →
      ∀ t ∈ Icc t₀ t₁,
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) +
            ∫ τ in t₀..t, ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, τ) i j j) ^ 2 ≤
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2) *
            Real.exp (C * ∫ τ in t₀..t,
              (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, τ))) ⊤ volume).toReal ^ 2) := by
  refine ⟨81, by norm_num, ?_⟩
  intro t₀ t₁ u Du p D2u Dtu hU hD hMD2 hMDt hIdentity hEndpoint
  have hlt : t₀ < t₁ := hU.1
  obtain ⟨hMu, hMDu⟩ : MemLp u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) := by
    rcases hU with ⟨-, -, -, ⟨_, _, -, h1, h2, -, -⟩, -, -⟩
    exact ⟨h1, h2⟩
  obtain ⟨hAC, hbal⟩ := lps_h1_energy_balance hU hD hMD2 hMDt hIdentity
  obtain ⟨-, -, hβbound, hmIoo⟩ := lps_endpoint_norm_slice_facts hMu.aestronglyMeasurable
    hEndpoint
  let f : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2
  let d : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) ^ 2
  let m : ℝ → ℝ := fun t => 81 * (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
    ⊤ volume).toReal ^ 2
  have hf0 : ∀ t, 0 ≤ f t := fun t =>
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg _
  have hd0 : ∀ t, 0 ≤ d t := fun t =>
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdint : Integrable d (volume.restrict (Ioo t₀ t₁)) :=
    lps_h1_laplacian_energy_integrable hMD2
  have hIoo : (volume.restrict (Ioo t₀ t₁) : Measure ℝ) = volume.restrict (Icc t₀ t₁) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  have hmint : IntegrableOn m (Icc t₀ t₁) := by
    rw [IntegrableOn, ← hIoo]
    exact hmIoo.const_mul 81
  have hdintIcc : IntegrableOn d (Icc t₀ t₁) := by
    rw [IntegrableOn, ← hIoo]
    exact hdint
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), deriv f t + d t ≤ m t * f t := by
    filter_upwards [hbal, lps_strong_good_slices hU hD hMu hMDu hMD2 hMDt, hβbound,
      (lps_aesm_slab_to_prod hMu.aestronglyMeasurable).prodMk_right,
      ae_restrict_mem measurableSet_Ioo] with t hb hgood hβ hum htI
    obtain ⟨hDt, hD2, hgrad, htr⟩ := hgood
    have htIcc : t ∈ Icc t₀ t₁ := ⟨htI.1.le, htI.2.le⟩
    obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hU htIcc
    have huInf : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) ⊤ volume :=
      memLp_top_of_bound
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
          hu2t.aestronglyMeasurable)
        _ (hβ.mono fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
          exact hx)
    have hlap2 : MemLp (fun x : Vec3 => (fun i => ∑ j : Fin 3, D2u (x, t) i j j : Vec3)) 2
        volume :=
      ESS.LPS.lps_h1_laplacian_memLp_two hD2 (fun x i => rfl)
    have hnl := ESS.LPS.lps_h1_infinite_nonlinear_pairing_bound
      (u := fun x => u (x, t)) (Du := fun x => Du (x, t))
      (lap := fun x i => ∑ j : Fin 3, D2u (x, t) i j j)
      hu2t.aestronglyMeasurable huInf hDu2t hlap2
    have hf0t := hf0 t
    have hd0t := hd0 t
    set M : ℝ := (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) ⊤ volume).toReal
      with hM
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    have hG : (∫ x : Vec3, ‖Du (x, t)‖ ^ 2) ≤ f t :=
      lps_h1_gradient_norm_sq_integral_le hDu2t
    have hL : (∫ x : Vec3, vec3EuclideanNorm (fun i => ∑ j : Fin 3, D2u (x, t) i j j) ^ 2) =
        d t := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [vec3EuclideanNorm]
      exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    rw [hL] at hnl
    have hle : (∫ x : Vec3, ∑ i : Fin 3,
        (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * (∑ j : Fin 3, D2u (x, t) i j j)) ≤
        (9 * M) * Real.sqrt (f t) * Real.sqrt (d t) := by
      refine (le_abs_self _).trans (hnl.trans ?_)
      have := Real.sqrt_le_sqrt hG
      calc _ ≤ 9 * M * Real.sqrt (f t) * Real.sqrt (d t) := by gcongr
        _ = _ := by ring
    have hbal' : deriv f t + 2 * d t ≤ 2 * ((9 * M) * Real.sqrt (f t) * Real.sqrt (d t)) := by
      have : deriv f t + 2 * d t = 2 * ∫ x : Vec3, ∑ i : Fin 3,
          (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * (∑ j : Fin 3, D2u (x, t) i j j) := hb
      rw [this]
      linarith only [hle]
    have habs := lps_h1_infinite_differential_absorption (dy := deriv f t) (d := d t)
      (A := 9 * M) (B := Real.sqrt (f t)) (D := Real.sqrt (d t)) (f := f t)
      (Real.sq_sqrt hf0t) (Real.sq_sqrt hd0t) hbal'
    calc deriv f t + d t ≤ (9 * M) ^ 2 * f t := habs
      _ = m t * f t := by simp only [m, hM]; ring
  have hdiffIcc : ∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)), deriv f t + d t ≤ m t * f t := by
    rw [← hIoo]
    exact hdiff
  have hgron := ESS.LPS.lps_h1_endpoint_branch_gronwall hlt.le hAC hdintIcc
    (Eventually.of_forall fun t => hd0 t) hmint (Eventually.of_forall fun t => by
      simp only [m]; positivity)
    (fun t _ => hf0 t) hdiffIcc
  intro t ht
  refine (hgron t ht).trans (le_of_eq ?_)
  have hint : (∫ τ in t₀..t, m τ) = 81 * ∫ τ in t₀..t,
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, τ))) ⊤ volume).toReal ^ 2 := by
    simp only [m]
    exact intervalIntegral.integral_const_mul _ _
  rw [hint]

end ESS

end
