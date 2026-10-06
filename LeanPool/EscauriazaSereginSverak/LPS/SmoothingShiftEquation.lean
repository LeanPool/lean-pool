/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingShiftCore
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTestLp
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace

/-!
# The strong equation with its time derivative, and solenoidality

For a strong solution in the class of `prop:lps-local-strong`, integrating the term
`-u · ∂ₜφ` of the weak momentum equation by parts in time gives the equation with the
weak time derivative `∂ₜu` tested against `φ`, and every time slice being weakly
solenoidal gives `∑ᵢ ∂ᵢuᵢ = 0` almost everywhere on the slab. Both are inputs of the
difference-quotient argument of `prop:lps-smoothing`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS.LPS

/-- Integrability, against a space-time test field, of the integrand of the weak momentum
equation written with a time-derivative field `A`, a flux `F`, a gradient field `G` and
a pressure `q` (`prop:lps-smoothing`). Only `F` is merely integrable. -/
theorem lps_weakEquation_integrand_integrable {I J : Set ℝ} {A : ParabolicPoint → Vec3}
    {F : ParabolicPoint → Fin 3 → Fin 3 → ℝ} {G : ParabolicPoint → Fin 3 → Vec3}
    {q : ParabolicPoint → ℝ}
    (hA : MemLp A 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)))
    (hF : ∀ i j : Fin 3, Integrable (fun z => F z i j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)))
    (hq : MemLp q 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)))
    {φ : ParabolicPoint → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) J) :
    Integrable (fun z =>
        ∑ i, A z i * φ z i - ∑ i, ∑ j, F z i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, G z i j * spatialPartial (fun y => φ y i) j z
          - q z * ∑ i, spatialPartial (fun y => φ y i) i z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) := by
  set μ := volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I) with hμ
  have hc := fun i => CKN.component_mem_spaceTimeTestFunction hφ i
  have hL2 := fun i => lps_spaceTimeTest_spatial_memLp_two (hc i).1 (hc i).2.1 I
  have h1 : Integrable (fun z => ∑ i, A z i * φ z i) μ :=
    integrable_finsetSum _ fun i _ => (hA.eval i).integrable_mul (hL2 i).1
  have h2 : Integrable
      (fun z => ∑ i, ∑ j, F z i j * spatialPartial (fun y => φ y i) j z) μ := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    obtain ⟨C, hC⟩ := CKN.exists_bound_spatialPartial_of_mem_spaceTimeTestFunction (hc i) j
    exact (hF i j).mul_bdd ((hL2 i).2 j).aestronglyMeasurable (ae_of_all _ fun z => hC z)
  have h3 : Integrable
      (fun z => ∑ i, ∑ j, G z i j * spatialPartial (fun y => φ y i) j z) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hG.eval i).eval j).integrable_mul ((hL2 i).2 j)
  have hdiv : MemLp (fun z => ∑ i, spatialPartial (fun y => φ y i) i z) 2 μ :=
    memLp_finsetSum _ fun i _ => (hL2 i).2 i
  have h4 : Integrable (fun z => q z * ∑ i, spatialPartial (fun y => φ y i) i z) μ :=
    hq.integrable_mul hdiv
  exact ((h1.sub h2).add h3).sub h4

/-- The weak momentum equation of a strong solution, with the term `-u · ∂ₜφ` integrated
by parts in time against a weak time derivative `Dtu` of `u` (`prop:lps-smoothing`). -/
theorem lps_strong_solution_equation_Dtu {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo t₀ T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
        (∑ i, Dtu z i * φ z i - ∑ i, ∑ j, (u z i * u z j) * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0 := by
  obtain ⟨-, -, -, ⟨-, -, -, hu, hDu, -, -⟩, hp, heq⟩ := hsol
  intro φ hφ
  set μ := volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)) with hμ
  have hc := fun i => CKN.component_mem_spaceTimeTestFunction hφ i
  have hL2 := fun i => lps_spaceTimeTest_spatial_memLp_two (hc i).1 (hc i).2.1 (Ioo t₀ T)
  have hT2 : ∀ i : Fin 3, MemLp (fun z => timePartial (fun y => φ y i) z) 2 μ := fun i =>
    (lps_spaceTimeTest_spatial_memLp_two (CKN.contDiff_timePartial (hc i).1)
      (CKN.hasCompactSupport_timePartial (hc i).2.1) (Ioo t₀ T)).1
  have hTarget := lps_weakEquation_integrand_integrable (A := Dtu)
    (F := fun z i j => u z i * u z j) (G := Du) (q := p) hDtu
    (fun i j => (hu.eval i).integrable_mul (hu.eval j)) hDu hp hφ
  have hA : ∀ i : Fin 3, Integrable (fun z => Dtu z i * φ z i) μ := fun i =>
    (hDtu.eval i).integrable_mul (hL2 i).1
  have hB : ∀ i : Fin 3, Integrable (fun z => u z i * timePartial (fun y => φ y i) z) μ :=
    fun i => (hu.eval i).integrable_mul (hT2 i)
  have hAB : ∀ i : Fin 3, Integrable
      (fun z => Dtu z i * φ z i + u z i * timePartial (fun y => φ y i) z) μ :=
    fun i => (hA i).add (hB i)
  have hExtra : Integrable
      (fun z => ∑ i, (Dtu z i * φ z i + u z i * timePartial (fun y => φ y i) z)) μ :=
    integrable_finsetSum _ fun i _ => hAB i
  have hExtra0 :
      ∫ z, ∑ i, (Dtu z i * φ z i + u z i * timePartial (fun y => φ y i) z) ∂μ = 0 := by
    rw [integral_finsetSum _ fun i _ => hAB i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_add (hA i) (hB i)]
    have hibp : ∫ z, u z i * timePartial (fun y => φ y i) z ∂μ =
        -∫ z, Dtu z i * φ z i ∂μ :=
      (hderiv.2.2.2.2 (fun y => φ y i) (hc i)).2.2 i
    rw [hibp, add_neg_cancel]
  have hsub := integral_sub hTarget hExtra
  rw [hExtra0, sub_zero] at hsub
  rw [← hsub]
  refine (integral_congr_ae (ae_of_all _ fun z => ?_)).trans (heq φ hφ)
  simp only [Fin.sum_univ_three]
  ring

/-- Every time slice of a strong solution has an almost everywhere trace-free gradient. -/
private theorem lps_strong_solution_slice_div_free {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsLpsStrongSolution t₀ T u Du p) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ∀ᵐ x ∂(volume : Measure Vec3), ∑ i, Du (x, t) i i = 0 := by
  obtain ⟨-, hslice, -⟩ := hsol
  obtain ⟨hJ, hH1⟩ := hslice t ht
  have hDw : MemLp (fun x : Vec3 => Du (x, t)) 2 volume := by
    refine memLp_pi_iff.2 fun i => ?_
    obtain ⟨g, -, hgr⟩ := hH1 i
    refine memLp_pi_iff.2 fun j => ?_
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ, hgr] using
      g.gradMemL2 j
  have hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u (x, t) i) (fun x => Du (x, t) i) := by
    intro i
    obtain ⟨g, hfun, hgr⟩ := hH1 i
    rw [← hfun, ← hgr]
    exact g.hasWeakGradient
  exact serrin_trace_zero_of_divFree hJ.1 hDw hgrad (isInJ_weakDivFree hJ).2

/-- The gradient of a strong solution is trace free almost everywhere on the slab: every
time slice lies in `J` (`prop:lps-local-strong`, used in `prop:lps-smoothing`). -/
theorem lps_strong_solution_div_free {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsLpsStrongSolution t₀ T u Du p) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))),
      ∑ i, Du z i i = 0 := by
  have hslice : ∀ t ∈ Ioo t₀ T, ∀ᵐ x ∂(volume : Measure Vec3), ∑ i, Du (x, t) i i = 0 :=
    fun t ht => lps_strong_solution_slice_div_free hsol (Ioo_subset_Icc_self ht)
  obtain ⟨-, -, -, ⟨-, -, -, -, hDu, -, -⟩, -, -⟩ := hsol
  have hDii : ∀ i : Fin 3, MemLp (fun z => Du z i i) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) :=
    fun i => (hDu.eval i).eval i
  have hmeas : AEStronglyMeasurable (fun z : ParabolicPoint => ∑ i, Du z i i)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) :=
    (memLp_finsetSum _ fun i _ => hDii i).aestronglyMeasurable
  let f : Vec3 × ℝ → ℝ := fun z => ∑ i, Du z i i
  change ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T)),
    f z = 0
  have hm : AEMeasurable (fun z => ‖f z‖ₑ)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo t₀ T))) := by
    rw [← lps_measure_slab_eq_prod]
    exact hmeas.enorm
  rw [lps_measure_slab_eq_prod]
  have hlint : ∫⁻ z, ‖f z‖ₑ ∂((volume : Measure Vec3).prod (volume.restrict (Ioo t₀ T))) = 0 := by
    rw [lintegral_prod_symm _ hm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    refine ae_of_all _ fun t ht => ?_
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hslice t ht] with x hx
    simp [f, hx]
  filter_upwards [(lintegral_eq_zero_iff' hm).1 hlint] with z hz
  simpa using hz

end ESS.LPS
