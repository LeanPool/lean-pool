/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Setting.MeridionalNorm
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Slice Bounds

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If `q` is locally bounded on `I`, then for every compact `J ⊆ I` there exists `M ≥ 0` such
that for almost every time slice `τ ∈ J`, the spatial function `x ↦ q(x, τ)` is bounded by `M`
almost everywhere in `x`. -/
theorem IsLocallyBoundedOn.ae_slice_bound {m : ℕ} {I J : Set ℝ} {q : Vec m × ℝ → ℝ}
    (hq : IsLocallyBoundedOn m I q) (hJ : IsCompact J) (hJI : J ⊆ I) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ τ ∂(volume.restrict J), ∀ᵐ x : Vec m, |q (x, τ)| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := hq.2 J hJ hJI
  have hM₀' : ∀ᵐ z ∂((volume : Measure (Vec m)).prod (volume.restrict J)), |q z| ≤ M₀ := by
    have heq : (volume : Measure (Vec m)).prod (volume.restrict J) =
        volume.restrict (univ ×ˢ J) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    rw [heq]
    exact hM₀
  have hM₀'' : ∀ᵐ w ∂((volume.restrict J).prod (volume : Measure (Vec m))), |q w.swap| ≤ M₀ := by
    refine ae_of_ae_map (f := (Prod.swap : ℝ × Vec m → Vec m × ℝ))
      (p := fun z : Vec m × ℝ => |q z| ≤ M₀)
      (measurable_swap.aemeasurable (μ := (volume.restrict J).prod (volume : Measure (Vec m)))) ?_
    rw [Measure.prod_swap]
    exact hM₀'
  have h_target := Measure.ae_ae_of_ae_prod hM₀''
  refine ⟨max M₀ 0, le_max_right _ _, ?_⟩
  filter_upwards [h_target] with τ hτ
  filter_upwards [hτ] with x hx
  exact le_trans hx (le_max_left _ _)

/-- If `q` is locally bounded on `I`, then for almost every `τ ∈ I` the slice
`x ↦ q(x, τ)` is AEStronglyMeasurable on `ℝ^m`. -/
theorem IsLocallyBoundedOn.ae_slice_measurable {m : ℕ} {I : Set ℝ} {q : Vec m × ℝ → ℝ}
    (hq : IsLocallyBoundedOn m I q) :
    ∀ᵐ τ ∂(volume.restrict I), AEStronglyMeasurable (fun x : Vec m => q (x, τ)) volume := by
  have hq1' : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
    have heq : (volume : Measure (Vec m)).prod (volume.restrict I) =
        volume.restrict (univ ×ˢ I) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    rw [heq]
    exact hq.1
  rcases hq1' with ⟨g, hg_meas, hg_ae⟩
  -- g is strongly measurable, so for every τ the slice x ↦ g (x, τ) is strongly measurable
  have hg_slice_strongly (τ : ℝ) : StronglyMeasurable (fun x : Vec m => g (x, τ)) :=
    hg_meas.comp_measurable measurable_prodMk_right
  have hg_slice (τ : ℝ) : AEStronglyMeasurable (fun x : Vec m => g (x, τ)) volume :=
    (hg_slice_strongly τ).aestronglyMeasurable
  -- From hg_ae : q =ᵐ[volume.prod (volume.restrict I)] g, we get a.e. equality of slices
  have h_ae_eq_slice : ∀ᵐ τ ∂(volume.restrict I), (fun x : Vec m => q (x, τ)) =ᵐ[volume] (fun x
    : Vec m => g (x, τ)) := by
    have hg_ae' : ∀ᵐ w ∂((volume.restrict I).prod (volume : Measure (Vec m))),
        q w.swap = g w.swap := by
      refine ae_of_ae_map (f := (Prod.swap : ℝ × Vec m → Vec m × ℝ))
        (p := fun z : Vec m × ℝ => q z = g z)
        (measurable_swap.aemeasurable (μ := (volume.restrict I).prod (volume : Measure (Vec m)))) ?_
      rw [Measure.prod_swap]
      exact hg_ae
    exact Measure.ae_ae_of_ae_prod hg_ae'
  filter_upwards [h_ae_eq_slice] with τ hτ
  -- hτ : (fun x => q (x, τ)) =ᵐ[volume] (fun x => g (x, τ))
  -- We need AEStronglyMeasurable (fun x => q (x, τ)) volume
  -- Since g(·,τ) is AEStronglyMeasurable, and q(·,τ) = g(·,τ) a.e., we get the result
  exact (hg_slice τ).congr hτ.symm

/-- If `B` is an admissible drift on `I`, then for every compact `J ⊆ I` there exists `Λ ≥ 0`
such that for almost every `τ ∈ J` the slice `B(·, τ)` is bounded and `Λ`-Lipschitz in `x`,
`|divB(·, τ)| ≤ Λ`, and `divB(·, τ)` is the weak divergence of `B(·, τ)`. -/
theorem IsAdmissibleDrift.ae_slice {m : ℕ} {I J : Set ℝ} {B : Vec m × ℝ → Vec m}
    {divB : Vec m × ℝ → ℝ} (hB : IsAdmissibleDrift m I B divB) (hJ : IsCompact J) (hJI : J ⊆ I) :
    ∃ Λ : NNReal, ∀ᵐ τ ∂(volume.restrict J),
      (∀ x, ‖B (x, τ)‖ ≤ Λ) ∧ LipschitzWith Λ (fun x => B (x, τ)) ∧ (∀ x, |divB (x, τ)| ≤ Λ) := by
  obtain ⟨Λ, hΛ⟩ := hB.2.2 J hJ hJI
  refine ⟨Λ, ?_⟩
  filter_upwards [hΛ] with τ hτ
  exact ⟨hτ.1, hτ.2.1, hτ.2.2.1⟩

end CIV
