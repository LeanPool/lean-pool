/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateStrongForm
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateGoodSlices
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSolenoidalDense
public import LeanPool.EscauriazaSereginSverak.LPS.OverlapStrongSerrin
public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointPairingSlice
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The strong equation at almost every time

Testing against countably many separated solenoidal fields shows that at almost
every time the strong form `∂ₜu - Δu + (u·∇)u` of the equation is orthogonal to
every solenoidal test field, hence to `J` (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_prod_integrable_mul_fst
    {a b : ℝ} {f : Vec3 × ℝ → ℝ} {g : Vec3 → ℝ}
    (hf : MemLp f 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hg : MemLp g 2 (volume : Measure Vec3)) :
    Integrable (fun q : Vec3 × ℝ => f q * g q.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
  hf.integrable_mul (q := 2) (hg.comp_fst (volume.restrict (Ioo a b)))

/-- At almost every time, the strong form of the equation is orthogonal to a
fixed smooth compactly supported solenoidal field (`lem:lps-H1-estimate`). -/
theorem lps_strong_form_orthogonal_test_ae
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hU : IsLpsStrongSolution t₀ t₁ u Du p)
    (hD : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu)
    (hMu : MemLp u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDu : MemLp Du 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMD2 : MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    {ψ : Vec3 → Vec3} (hψ : ψ ∈ LpsSolenoidalTest) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, t) i - ∑ j : Fin 3, D2u (x, t) i j j +
        ∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i = 0 := by
  obtain ⟨hψs, hψc, hψdiv⟩ := hψ
  have hψsi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i) := contDiff_pi.mp hψs i
  have hψci (i : Fin 3) : HasCompactSupport (fun x => ψ x i) :=
    hψc.comp_left (g := fun v : Vec3 => v i) rfl
  set ν : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo t₀ t₁)) with hν
  have hMU : MemLp (fun q : Vec3 × ℝ => u (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hMu
  have hMD2U : MemLp (fun q : Vec3 × ℝ => D2u (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hMD2
  have hMDtU : MemLp (fun q : Vec3 × ℝ => Dtu (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hMDt
  have hψ2 (i : Fin 3) : MemLp (fun x => ψ x i) 2 (volume : Measure Vec3) :=
    (hψsi i).continuous.memLp_of_hasCompactSupport (hψci i)
  have hψ1b (i j : Fin 3) : ∃ C, ∀ x, ‖spatialDeriv (fun y => ψ y i) j x‖ ≤ C :=
    (contDiff_spatialDeriv_smooth (hψsi i) j).continuous.bounded_above_of_compact_support
      ((hψci i).fderiv_apply (𝕜 := ℝ) (basisVec j))
  -- the time-independent part of the density
  let H : Vec3 × ℝ → ℝ := fun q =>
    (∑ i : Fin 3, Dtu (parabolicHomeomorph.symm q) i * ψ q.1 i) -
      (∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
        u (parabolicHomeomorph.symm q) j * spatialDeriv (fun y => ψ y i) j q.1) -
      (∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) * ψ q.1 i)
  have hH : Integrable H ν := by
    have h1 : Integrable (fun q : Vec3 × ℝ =>
        ∑ i : Fin 3, Dtu (parabolicHomeomorph.symm q) i * ψ q.1 i) ν :=
      integrable_finsetSum _ fun i _ =>
        lps_prod_integrable_mul_fst (hMDtU.eval i) (hψ2 i)
    have h2 : Integrable (fun q : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
          u (parabolicHomeomorph.symm q) j * spatialDeriv (fun y => ψ y i) j q.1) ν := by
      refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
      obtain ⟨C, hC⟩ := hψ1b i j
      have hprod : Integrable (fun q : Vec3 × ℝ =>
          u (parabolicHomeomorph.symm q) i * u (parabolicHomeomorph.symm q) j) ν :=
        memLp_one_iff_integrable.mp ((hMU.eval i).mul (hMU.eval j) (hpqr := inferInstance))
      have := hprod.bdd_mul (f := fun q : Vec3 × ℝ => spatialDeriv (fun y => ψ y i) j q.1)
        (c := C)
        (((contDiff_spatialDeriv_smooth (hψsi i) j).continuous.comp
          continuous_fst).aestronglyMeasurable)
        (Eventually.of_forall fun q => hC q.1)
      simpa [mul_comm] using this
    have h3 : Integrable (fun q : Vec3 × ℝ =>
        ∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) * ψ q.1 i) ν := by
      refine integrable_finsetSum _ fun i _ => ?_
      exact lps_prod_integrable_mul_fst (f := fun q : Vec3 × ℝ =>
        ∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j)
        (memLp_finsetSum Finset.univ fun j _ => ((hMD2U.eval i).eval j).eval j) (hψ2 i)
    exact (h1.sub h2).sub h3
  set f : ℝ → ℝ := fun t => ∫ x : Vec3, H (x, t) with hf
  have hfint : Integrable f (volume.restrict (Ioo t₀ t₁)) := hH.integral_prod_right
  -- for each cutoff, the time integral of `χ · f` vanishes
  have hzero : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo t₀ t₁ → ∫ t in Ioo t₀ t₁, χ t * f t = 0 := by
    intro χ hχ hχc hχs
    have hsf1 := lps_strong_separated_identity hU hD hMu hMDu hMD2 hMDt hχ hχc hχs hψsi hψc
      hψdiv
    have hpt (q : Vec3 × ℝ) :
        ((∑ i : Fin 3, Dtu (parabolicHomeomorph.symm q) i * (χ q.2 * ψ q.1 i)) -
          (∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
            u (parabolicHomeomorph.symm q) j *
              (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) -
          (∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) *
            (χ q.2 * ψ q.1 i))) = χ q.2 * H q := by
      simp only [H, mul_sub, Finset.mul_sum]
      congr 1
      · congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hpt] at hsf1
    obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    have hmul : Integrable (fun q : Vec3 × ℝ => χ q.2 * H q) ν :=
      hH.bdd_mul (f := fun q : Vec3 × ℝ => χ q.2) (c := C)
        ((hχ.continuous.comp continuous_snd).aestronglyMeasurable)
        (Eventually.of_forall fun q => hC q.2)
    rw [integral_prod_symm _ hmul] at hsf1
    simpa [hf, integral_const_mul] using hsf1
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), t ∈ Ioo t₀ t₁ → f t = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hfint.locallyIntegrable.locallyIntegrableOn _)
      (fun g hg hgc hgs => by simpa using hzero g hg hgc hgs)
  filter_upwards [hae, lps_strong_good_slices hU hD hMu hMDu hMD2 hMDt,
    ae_restrict_mem measurableSet_Ioo] with t hft hgood htI
  have hf0 : f t = 0 := hft htI
  obtain ⟨hDt, hD2, hgrad, htr⟩ := hgood
  have htIcc : t ∈ Icc t₀ t₁ := ⟨htI.1.le, htI.2.le⟩
  obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hU htIcc
  have hH1t := (lps_strong_solution_slice_h1 hU htIcc).2.2
  have hgu := lps_strong_solution_slice_weak_gradient hU htIcc
  have K := lps_h1_convection_test_identity (u := fun x => u (x, t))
    (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t)) (ψ := ψ)
    hu2t hDu2t hD2 hH1t hgu hgrad htr hψsi hψci
  have hN (i : Fin 3) := lps_h1_convection_memLp_two (u := fun x => u (x, t))
    (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t)) hu2t hDu2t hD2 hH1t hgrad i
  -- slice integrability
  have i1 : Integrable (fun x : Vec3 => ∑ i : Fin 3, Dtu (x, t) i * ψ x i) volume :=
    integrable_finsetSum _ fun i _ => (hDt.eval i).integrable_mul (hψ2 i)
  have i3 : Integrable (fun x : Vec3 => ∑ i : Fin 3,
      (∑ j : Fin 3, D2u (x, t) i j j) * ψ x i) volume :=
    integrable_finsetSum _ fun i _ =>
      (memLp_finsetSum Finset.univ fun j _ => ((hD2.eval i).eval j).eval j).integrable_mul
        (hψ2 i)
  have i4 : Integrable (fun x : Vec3 => ∑ i : Fin 3,
      (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i) volume :=
    integrable_finsetSum _ fun i _ => (hN i).integrable_mul (hψ2 i)
  have i2 : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x) volume := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    obtain ⟨C, hC⟩ := hψ1b i j
    have hprod : Integrable (fun x : Vec3 => u (x, t) i * u (x, t) j) volume :=
      memLp_one_iff_integrable.mp ((hu2t.eval i).mul (hu2t.eval j) (hpqr := inferInstance))
    have := hprod.bdd_mul (f := fun x : Vec3 => spatialDeriv (fun y => ψ y i) j x) (c := C)
      (contDiff_spatialDeriv_smooth (hψsi i) j).continuous.aestronglyMeasurable
      (Eventually.of_forall hC)
    simpa [mul_comm] using this
  have hft' : f t = (∫ x : Vec3, ∑ i : Fin 3, Dtu (x, t) i * ψ x i) -
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x) -
      ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) * ψ x i := by
    change (∫ x : Vec3, H (x, t)) = _
    exact lps_integral_sub_sub i1 i2 i3
  have hpt (x : Vec3) : (∑ i : Fin 3, (Dtu (x, t) i - ∑ j : Fin 3, D2u (x, t) i j j +
        ∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i) =
      (∑ i : Fin 3, Dtu (x, t) i * ψ x i) -
        (∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) * ψ x i) +
        ∑ i : Fin 3, (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsplit : (∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, t) i - ∑ j : Fin 3, D2u (x, t) i j j +
        ∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i) =
      (∫ x : Vec3, ∑ i : Fin 3, Dtu (x, t) i * ψ x i) -
        (∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) * ψ x i) +
        ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i := by
    simp only [hpt]
    exact lps_integral_sub_add i1 i3 i4
  rw [hsplit]
  have K' : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x) =
      -∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i := K
  linarith only [hft', hf0, K']

/-- The `L²` pairing of two vector fields is bounded by the product of their
`L²` norms. -/
theorem lps_abs_pairing_le {F g : Vec3 → Vec3} (hF : MemLp F 2 volume) (hg : MemLp g 2 volume) :
    |∫ x : Vec3, ∑ i : Fin 3, F x i * g x i| ≤
      3 * (eLpNorm F 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  have hint (i : Fin 3) : Integrable (fun x => F x i * g x i) volume :=
    (hF.eval i).integrable_mul (hg.eval i)
  have hcomp (i : Fin 3) : ∫ x : Vec3, |F x i * g x i| ≤
      (eLpNorm F 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
    have h1 : eLpNorm (fun x => F x i) 2 volume ≤ eLpNorm F 2 volume :=
      eLpNorm_mono_ae (hF.eval i).aestronglyMeasurable
        (Eventually.of_forall fun x => norm_le_pi_norm (F x) i)
    have h2 : eLpNorm (fun x => g x i) 2 volume ≤ eLpNorm g 2 volume :=
      eLpNorm_mono_ae (hg.eval i).aestronglyMeasurable
        (Eventually.of_forall fun x => norm_le_pi_norm (g x) i)
    have h3 : (∫⁻ x : Vec3, ‖F x i‖ₑ * ‖g x i‖ₑ) ≤
        eLpNorm (fun x => F x i) 2 volume * eLpNorm (fun x => g x i) 2 volume :=
      lps_lintegral_mul_le_two (hF.eval i).aestronglyMeasurable (hg.eval i).aestronglyMeasurable
    have hfin : eLpNorm F 2 volume * eLpNorm g 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top hF.eLpNorm_ne_top hg.eLpNorm_ne_top
    have h4 : (∫⁻ x : Vec3, ‖F x i * g x i‖ₑ) ≤ eLpNorm F 2 volume * eLpNorm g 2 volume := by
      refine le_trans (le_of_eq ?_) (h3.trans (mul_le_mul' h1 h2))
      refine lintegral_congr fun x => ?_
      rw [enorm_mul]
    have h5 := ENNReal.toReal_mono hfin h4
    rw [ENNReal.toReal_mul] at h5
    have hI : ∫ x : Vec3, ‖F x i * g x i‖ = (∫⁻ x : Vec3, ‖F x i * g x i‖ₑ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
        (hint i).aestronglyMeasurable.norm]
      congr 1
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal_abs]
      simp
    have hI' : ∫ x : Vec3, |F x i * g x i| = ∫ x : Vec3, ‖F x i * g x i‖ := by
      simp [Real.norm_eq_abs]
    rw [hI', hI]
    exact h5
  calc |∫ x : Vec3, ∑ i : Fin 3, F x i * g x i|
      = |∑ i : Fin 3, ∫ x : Vec3, F x i * g x i| := by
        rw [integral_finsetSum _ fun i _ => hint i]
    _ ≤ ∑ i : Fin 3, |∫ x : Vec3, F x i * g x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∫ x : Vec3, |F x i * g x i| :=
        Finset.sum_le_sum fun i _ => by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => F x i * g x i)
    _ ≤ ∑ _i : Fin 3, (eLpNorm F 2 volume).toReal * (eLpNorm g 2 volume).toReal :=
        Finset.sum_le_sum fun i _ => hcomp i
    _ = 3 * (eLpNorm F 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- At almost every time, the strong form `∂ₜu - Δu + (u·∇)u` of the equation
is orthogonal to every element of `J` (`lem:lps-H1-estimate`). -/
theorem lps_strong_form_orthogonal_J_ae
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hU : IsLpsStrongSolution t₀ t₁ u Du p)
    (hD : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu)
    (hMu : MemLp u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDu : MemLp Du 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMD2 : MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), ∀ w : Vec3 → Vec3, IsInJ w →
      ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, t) i - ∑ j : Fin 3, D2u (x, t) i j j +
        ∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * w x i = 0 := by
  obtain ⟨D, hDc, hDS, hDdense⟩ := lps_exists_countable_solenoidal_dense
  have hall : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), ∀ ψ ∈ D,
      ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, t) i - ∑ j : Fin 3, D2u (x, t) i j j +
        ∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i = 0 :=
    (ae_ball_iff hDc).mpr fun ψ hψ =>
      lps_strong_form_orthogonal_test_ae hU hD hMu hMDu hMD2 hMDt (hDS hψ)
  filter_upwards [hall, lps_strong_good_slices hU hD hMu hMDu hMD2 hMDt,
    ae_restrict_mem measurableSet_Ioo] with t ht hgood htI
  obtain ⟨hDt, hD2, hgrad, htr⟩ := hgood
  have htIcc : t ∈ Icc t₀ t₁ := ⟨htI.1.le, htI.2.le⟩
  obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hU htIcc
  have hH1t := (lps_strong_solution_slice_h1 hU htIcc).2.2
  have hN (i : Fin 3) := lps_h1_convection_memLp_two (u := fun x => u (x, t))
    (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t)) hu2t hDu2t hD2 hH1t hgrad i
  let Ft : Vec3 → Vec3 := fun x i => Dtu (x, t) i - ∑ j : Fin 3, D2u (x, t) i j j +
    ∑ j : Fin 3, u (x, t) j * Du (x, t) i j
  have hFt : MemLp Ft 2 volume := by
    refine memLp_pi_iff.mpr fun i => ?_
    exact ((hDt.eval i).sub
      (memLp_finsetSum Finset.univ fun j _ => ((hD2.eval i).eval j).eval j)).add (hN i)
  intro w hw
  have hw2 : MemLp w 2 volume := hw.1
  -- approximate `w` by elements of the dense family
  have hM : 0 ≤ 3 * (eLpNorm Ft 2 volume).toReal := by positivity
  refine abs_nonpos_iff.mp ?_
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  rw [zero_add]
  obtain ⟨ψ, hψD, hψlt⟩ := hDdense w hw (ENNReal.ofReal (δ / (3 * (eLpNorm Ft 2 volume).toReal +
    1)))
    (ENNReal.ofReal_pos.mpr (by positivity))
  have hψ2 : MemLp ψ 2 volume := by
    obtain ⟨hψs, hψc, -⟩ := hDS hψD
    exact hψs.continuous.memLp_of_hasCompactSupport hψc
  have hzero := ht ψ hψD
  have hint (g : Vec3 → Vec3) (hg : MemLp g 2 volume) :
      Integrable (fun x => ∑ i : Fin 3, Ft x i * g x i) volume :=
    integrable_finsetSum _ fun i _ => (hFt.eval i).integrable_mul (hg.eval i)
  have hdiff : (∫ x : Vec3, ∑ i : Fin 3, Ft x i * w x i) =
      ∫ x : Vec3, ∑ i : Fin 3, Ft x i * (w x - ψ x) i := by
    have h1 : (∫ x : Vec3, ∑ i : Fin 3, Ft x i * (w x - ψ x) i) =
        (∫ x : Vec3, ∑ i : Fin 3, Ft x i * w x i) -
          ∫ x : Vec3, ∑ i : Fin 3, Ft x i * ψ x i := by
      rw [← integral_sub (hint w hw2) (hint ψ hψ2)]
      congr 1
      funext x
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp [mul_sub]
    rw [h1]
    have hz' : (∫ x : Vec3, ∑ i : Fin 3, Ft x i * ψ x i) = 0 := hzero
    rw [hz', sub_zero]
  have hbound := lps_abs_pairing_le hFt (hw2.sub hψ2)
  have hnorm : (eLpNorm (fun x => w x - ψ x) 2 volume).toReal <
      δ / (3 * (eLpNorm Ft 2 volume).toReal + 1) := by
    have h1 : eLpNorm (fun x => w x - ψ x) 2 volume = eLpNorm (fun x => ψ x - w x) 2 volume := by
      rw [← eLpNorm_neg]
      refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
      simp
    rw [h1]
    have hfin : eLpNorm (fun x => ψ x - w x) 2 volume ≠ ⊤ := ne_top_of_lt hψlt
    have := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hψlt
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  rw [hdiff]
  refine hbound.trans ?_
  have hpos : 0 ≤ 3 * (eLpNorm Ft 2 volume).toReal := hM
  calc 3 * (eLpNorm Ft 2 volume).toReal * (eLpNorm (fun x => w x - ψ x) 2 volume).toReal
      ≤ 3 * (eLpNorm Ft 2 volume).toReal * (δ / (3 * (eLpNorm Ft 2 volume).toReal + 1)) :=
        mul_le_mul_of_nonneg_left hnorm.le hpos
    _ ≤ δ := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith only [hδ, hpos]

end ESS

end
