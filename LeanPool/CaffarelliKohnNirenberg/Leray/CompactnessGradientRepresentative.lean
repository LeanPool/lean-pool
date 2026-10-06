/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientLocal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSupport

/-!
# Compactness Gradient Representative

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section

namespace CKN.Leray

/-- A measurable representative of a local matrix-gradient L² class. -/
@[expose]
def compactnessGradientLocalRepresentative
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (D : ∀ j, Lp CompactnessGradientFiber 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))))
    (j : ℕ) : Vec3 × ℝ → CompactnessGradientFiber :=
  (Lp.aestronglyMeasurable (D j)).aemeasurable.mk (D j)

/-- The chosen representative of a local gradient class is measurable. -/
theorem measurable_compactnessGradientLocalRepresentative
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (D : ∀ j, Lp CompactnessGradientFiber 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))))
    (j : ℕ) :
    Measurable (compactnessGradientLocalRepresentative K J D j) :=
  (Lp.aestronglyMeasurable (D j)).aemeasurable.measurable_mk

/-- The local measurable representative agrees with its L² class almost
everywhere on the extraction rectangle. -/
theorem compactnessGradientLocalRepresentative_ae_eq
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (D : ∀ j, Lp CompactnessGradientFiber 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))))
    (j : ℕ) :
    (fun z => D j z) =ᵐ[
      ((volume.restrict (K j)).prod (volume.restrict (J j)))]
      compactnessGradientLocalRepresentative K J D j :=
  (Lp.aestronglyMeasurable (D j)).aemeasurable.ae_eq_mk

/-- On each open inner rectangle, the measurable local matrix limit is an
almost-every-time weak spatial gradient of the strong velocity limit. -/
theorem compactnessGradientLocalRepresentative_weak_partial
    {U : Set Vec3} {I : Set ℝ}
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (v : Vec3 × ℝ → Vec3)
    (σ : ℕ → ℕ)
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U)
    (hJ : ∀ j, IsCompact (J j) ∧ J j ⊆ I)
    (hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u n (x,t) i)
        (fun x => Du n (x,t) i))
    (D : ∀ j, Lp CompactnessGradientFiber 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))))
    (hDweak : ∀ j,
      ∃ hgrad : ∀ k, MemLp
        (fun z : Vec3 × ℝ => toCompactnessGradientFiber (Du (σ k) z)) 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))),
        ∀ w, Tendsto
          (fun k => inner ℝ ((hgrad k).toLp
            (fun z => toCompactnessGradientFiber (Du (σ k) z))) w) atTop
          (nhds (inner ℝ (D j) w)))
    (hstrong : ∀ j, ∃ _hf : ∀ k, MemLp
      (fun z : Vec3 × ℝ => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))),
      Tendsto (fun k => eLpNorm
        ((fun z : Vec3 × ℝ => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) -
          (fun z : Vec3 × ℝ => (WithLp.toLp 2 (v z) : L2Vec3))) 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))))
        atTop (nhds 0))
    (j : ℕ) (i m : Fin 3) :
    ∀ᵐ t ∂(volume.restrict (J j)),
      LocallyIntegrableOn
        (fun x => compactnessGradientLocalRepresentative K J D j (x,t) i m)
        (interior (K j)) volume ∧
      HasWeakPartialDerivOn (interior (K j)) m
        (fun x => v (x,t) i)
        (fun x => compactnessGradientLocalRepresentative K J D j (x,t) i m) := by
  let μ : Measure Vec3 := volume.restrict (K j)
  let ν : Measure ℝ := volume.restrict (J j)
  let ρ : Measure (Vec3 × ℝ) := μ.prod ν
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (hK j).1.measure_lt_top.ne
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (hJ j).1.measure_lt_top.ne
  let : IsFiniteMeasure ρ := inferInstance
  let gLocal := compactnessGradientLocalRepresentative K J D j
  have hgMem : MemLp gLocal 2 ρ := by
    exact (memLp_congr_ae
      (compactnessGradientLocalRepresentative_ae_eq K J D j)).1
        (Lp.memLp (D j))
  have hcoord : MemLp (fun z => gLocal z i m) 2 ρ := by
    have h := (gradientCoordinateCLM i m).comp_memLp' hgMem
    simpa only [Function.comp_def, gradientCoordinateCLM_apply] using h
  have hcoordInt : Integrable (fun z => gLocal z i m) ρ :=
    memLp_one_iff_integrable.mp
      (hcoord.mono_exponent (by norm_num))
  have hcoordTime : ∀ᵐ t ∂ν,
      LocallyIntegrableOn (fun x => gLocal (x,t) i m)
        (interior (K j)) volume := by
    filter_upwards [hcoordInt.prod_left_ae] with t ht
    exact (show IntegrableOn (fun x => gLocal (x,t) i m)
      (K j) volume from ht).mono_set interior_subset |>.locallyIntegrableOn
  have hEqTime : ∀ᵐ t ∂ν,
      (fun x => D j (x,t)) =ᵐ[μ] (fun x => gLocal (x,t)) :=
    ae_ae_of_ae_prod_snd
      (compactnessGradientLocalRepresentative_ae_eq K J D j)
  obtain ⟨hf, hstrongj⟩ := hstrong j
  obtain ⟨hgrad, hgradWeak⟩ := hDweak j
  have hsourcePartial (k : ℕ) :
      ∀ᵐ t ∂ν, HasWeakPartialDerivOn (interior (K j)) m
        (fun x => u (σ k) (x,t) i)
        (fun x => Du (σ k) (x,t) i m) := by
    have ht := ae_restrict_of_ae_restrict_of_subset
      (hJ j).2 (hweakGrad (σ k))
    filter_upwards [ht] with t hwt
    exact (hwt i m).restrict isOpen_interior
      (interior_subset.trans (hK j).2)
  have hpartial : ∀ᵐ t ∂ν,
      HasWeakPartialDerivOn (interior (K j)) m
        (fun x => v (x,t) i)
        (fun x => gradientCoordinateCLM i m (D j (x,t))) := by
    exact weak_partial_of_strong_velocity_and_weak_matrix_on_inner_rectangle
      (hK j).1 isOpen_interior interior_subset (hJ j).1
      (fun k z => (WithLp.toLp 2 (u (σ k) z) : L2Vec3))
      (fun z => (WithLp.toLp 2 (v z) : L2Vec3))
      (fun k z => Du (σ k) z) (D j)
      hf hstrongj hgrad hgradWeak i m hsourcePartial
  filter_upwards [hpartial, hEqTime, hcoordTime] with t hp heq hInt
  refine ⟨hInt, ?_⟩
  have heq' :
      (fun x => gradientCoordinateCLM i m (D j (x,t))) =ᵐ[
        volume.restrict (interior (K j))]
      (fun x => gLocal (x,t) i m) := by
    have heqΩ := ae_restrict_of_ae_restrict_of_subset interior_subset heq
    filter_upwards [heqΩ] with x hx
    simpa only [gradientCoordinateCLM_apply] using
      congrArg (gradientCoordinateCLM i m) hx
  exact hp.congr_deriv_ae heq'

end CKN.Leray
