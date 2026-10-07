/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinMollifiedPairing

/-!
# Joint measurability of mollified pairings

The mollified components and their tested fluxes are almost everywhere strongly
measurable jointly in time and the mollification point. They are the
integrands exchanged in the cross-testing identity of
`lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Reading a space-time field at `(x, τ)` from the triple `((τ, y), x)` preserves
null sets. -/
theorem serrin_quasiMeasurePreserving_triple (T : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun w : (ℝ × Vec3) × Vec3 => (w.2, w.1.1))
      (((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)).prod
        (volume : Measure Vec3))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  refine ⟨by fun_prop, Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_⟩
  have hmeas : Measurable (fun w : (ℝ × Vec3) × Vec3 => (w.2, w.1.1)) := by fun_prop
  rw [Measure.map_apply hmeas hS]
  have hpre : MeasurableSet ((fun w : (ℝ × Vec3) × Vec3 => (w.2, w.1.1)) ⁻¹' S) :=
    hmeas hS
  rw [Measure.prod_apply hpre]
  -- the inner measure depends only on the time coordinate
  have hinner : ∀ q : ℝ × Vec3,
      (volume : Measure Vec3)
        (Prod.mk q ⁻¹' ((fun w : (ℝ × Vec3) × Vec3 => (w.2, w.1.1)) ⁻¹' S)) =
        (volume : Measure Vec3) ((fun x : Vec3 => (x, q.1)) ⁻¹' S) := by
    intro q
    rfl
  simp_rw [hinner]
  have hS0' : ∫⁻ τ, (volume : Measure Vec3) ((fun x : Vec3 => (x, τ)) ⁻¹' S)
      ∂(volume.restrict (Ioo 0 T)) = 0 := by
    rw [← Measure.prod_apply_symm hS]
    exact hS0
  have hzero : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (volume : Measure Vec3) ((fun x : Vec3 => (x, τ)) ⁻¹' S) = 0 := by
    have hm : Measurable (fun τ : ℝ =>
        (volume : Measure Vec3) ((fun x : Vec3 => (x, τ)) ⁻¹' S)) :=
      measurable_measure_prodMk_right hS
    exact (lintegral_eq_zero_iff hm).mp hS0'
  have hzero' : ∀ᵐ q ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)),
      (volume : Measure Vec3) ((fun x : Vec3 => (x, q.1)) ⁻¹' S) = 0 :=
    Measure.quasiMeasurePreserving_fst.ae hzero
  rw [lintegral_congr_ae hzero']
  simp

/-- Almost everywhere strong measurability on the parabolic slab, in product
coordinates. -/
theorem serrin_aesm_prod {E : Type} [TopologicalSpace E] {T : ℝ}
    {f : ParabolicPoint → E}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    AEStronglyMeasurable (fun z : Vec3 × ℝ => f z)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  have h : AEStronglyMeasurable f
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))]
    exact hf
  rw [Measure.restrict_univ] at h
  exact h

/-- A space-time field read at `(x, τ)` from the triple `((τ, y), x)`. -/
theorem serrin_aesm_triple {E : Type} [TopologicalSpace E] {T : ℝ}
    {f : ParabolicPoint → E}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    AEStronglyMeasurable (fun w : (ℝ × Vec3) × Vec3 => f (w.2, w.1.1))
      (((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)).prod
        (volume : Measure Vec3)) :=
  (serrin_aesm_prod hf).comp_quasiMeasurePreserving
    (serrin_quasiMeasurePreserving_triple T)

/-- The mollified component is jointly almost everywhere strongly measurable. -/
theorem serrinMol_aestronglyMeasurable {T : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    {ρ : Vec3 → ℝ} (hρ : Continuous ρ) (k : Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Vec3 => serrinMol u ρ k z.2 z.1)
      ((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
  have hF : AEStronglyMeasurable
      (fun w : (ℝ × Vec3) × Vec3 => u (w.2, w.1.1) k * ρ (w.1.2 - w.2))
      (((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)).prod
        (volume : Measure Vec3)) := by
    have h1 := (continuous_apply k).comp_aestronglyMeasurable (serrin_aesm_triple hu)
    have h2 : Continuous (fun w : (ℝ × Vec3) × Vec3 => ρ (w.1.2 - w.2)) := by fun_prop
    exact h1.mul h2.aestronglyMeasurable
  exact hF.integral_prod_right'

/-- The tested flux of the mollified component is jointly almost everywhere
strongly measurable. -/
theorem serrinMolFlux_aestronglyMeasurable {T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (k : Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Vec3 => serrinMolFlux u Du p ρ k z.2 z.1)
      ((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
  have hdρ (j : Fin 3) : Continuous (spatialDeriv ρ j) :=
    (hρ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hu3 := serrin_aesm_triple hu
  have hDu3 := serrin_aesm_triple hDu
  have hp3 := serrin_aesm_triple hp
  have hc (j : Fin 3) : Continuous
      (fun w : (ℝ × Vec3) × Vec3 => spatialDeriv ρ j (w.1.2 - w.2)) :=
    (hdρ j).comp (by fun_prop)
  have huc (i : Fin 3) := (continuous_apply i).comp_aestronglyMeasurable hu3
  have hDuc (i j : Fin 3) := (continuous_apply j).comp_aestronglyMeasurable
    ((continuous_apply i).comp_aestronglyMeasurable hDu3)
  have hF : AEStronglyMeasurable
      (fun w : (ℝ × Vec3) × Vec3 =>
        serrinMolFluxDensity u Du p ρ k w.1.2 (w.2, w.1.1))
      (((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)).prod
        (volume : Measure Vec3)) := by
    unfold serrinMolFluxDensity
    refine ((Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_).neg.add
      (Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_)).sub ?_
    · exact ((huc k).mul (huc j)).mul (hc j).aestronglyMeasurable
    · exact (hDuc k j).mul (hc j).aestronglyMeasurable
    · exact hp3.mul (hc k).aestronglyMeasurable
  exact hF.integral_prod_right'

end ESS
