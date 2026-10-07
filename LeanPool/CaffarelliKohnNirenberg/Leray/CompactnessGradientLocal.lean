/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientCoordinates
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientClosure

/-!
# Compactness Gradient Local

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- A weak local matrix limit is the almost-every-time spatial gradient of
the strong local velocity limit on an open inner rectangle. -/
theorem weak_partial_of_strong_velocity_and_weak_matrix_on_inner_rectangle
    {K Ω : Set Vec3} {J : Set ℝ}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (hJ : IsCompact J)
    (f : ℕ → Vec3 × ℝ → L2Vec3)
    (g : Vec3 × ℝ → L2Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (D : Lp CompactnessGradientFiber 2
      ((volume.restrict K).prod (volume.restrict J)))
    (hf : ∀ k, MemLp (f k) 2
      ((volume.restrict K).prod (volume.restrict J)))
    (hstrong : Tendsto (fun k => eLpNorm (f k - g) 2
      ((volume.restrict K).prod (volume.restrict J))) atTop (nhds 0))
    (hDmem : ∀ k, MemLp
      (fun z => toCompactnessGradientFiber (Du k z)) 2
        ((volume.restrict K).prod (volume.restrict J)))
    (hDweak : ∀ v, Tendsto
      (fun k => inner ℝ ((hDmem k).toLp
        (fun z => toCompactnessGradientFiber (Du k z))) v) atTop
      (nhds (inner ℝ D v)))
    (i j : Fin 3)
    (hpartial : ∀ k, ∀ᵐ t ∂(volume.restrict J),
      HasWeakPartialDerivOn Ω j (fun x => f k (x, t) i)
        (fun x => Du k (x, t) i j)) :
    ∀ᵐ t ∂(volume.restrict J),
      HasWeakPartialDerivOn Ω j (fun x => g (x, t) i)
        (fun x => gradientCoordinateCLM i j (D (x, t))) := by
  let ρK : Measure (Vec3 × ℝ) :=
    (volume.restrict K).prod (volume.restrict J)
  let ρΩ : Measure (Vec3 × ℝ) :=
    (volume.restrict Ω).prod (volume.restrict J)
  have hμ : ρΩ ≤ ρK := by
    exact Measure.prod_mono
      (Measure.restrict_mono_set volume hΩK) le_rfl
  have hΩfinite : (volume : Measure Vec3) Ω < ⊤ :=
    lt_of_le_of_lt (measure_mono hΩK) hK.measure_lt_top
  have hJfinite : (volume : Measure ℝ) J < ⊤ := hJ.measure_lt_top
  have hfΩ (k : ℕ) : MemLp (f k) 2 ρΩ :=
    (hf k).mono_measure hμ
  have hgK : MemLp g 2 ρK :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) hf g hstrong
  have hgΩ : MemLp g 2 ρΩ := hgK.mono_measure hμ
  have hstrongΩ : Tendsto (fun k => eLpNorm (f k - g) 2 ρΩ)
      atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hstrong
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall fun k =>
        eLpNorm_mono_measure (f k - g) hμ)
  let P : L2Vec3 →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  have hfScalar (k : ℕ) :
      MemLp (fun z => f k z i) 2 ρΩ := by
    simpa only [P, Function.comp_def, PiLp.proj_apply] using
      P.comp_memLp' (hfΩ k)
  have hgScalar : MemLp (fun z => g z i) 2 ρΩ := by
    simpa only [P, Function.comp_def, PiLp.proj_apply] using
      P.comp_memLp' hgΩ
  have hstrongScalar :
      Tendsto (fun k => eLpNorm
        (fun z => f k z i - g z i) 2 ρΩ) atTop (nhds 0) := by
    have hle (k : ℕ) :
        eLpNorm (fun z => f k z i - g z i) 2 ρΩ ≤
          eLpNorm (f k - g) 2 ρΩ := by
      have hmeas : AEStronglyMeasurable
          (fun z => f k z i - g z i) ρΩ :=
        (hfScalar k).aestronglyMeasurable.sub hgScalar.aestronglyMeasurable
      have h := eLpNorm_mono_ae (p := (2 : ℝ≥0∞)) hmeas
        (Filter.Eventually.of_forall fun z =>
          PiLp.norm_apply_le (f k z - g z) i)
      change eLpNorm (fun z => f k z i - g z i) 2 ρΩ ≤
        eLpNorm (fun z => f k z - g z) 2 ρΩ
      simpa only [PiLp.sub_apply] using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hstrongΩ
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hle)
  have hDΩ (k : ℕ) : MemLp
      (fun z => Du k z i j) 2 ρΩ := by
    have h := (gradientCoordinateCLM i j).comp_memLp'
      ((hDmem k).mono_measure hμ)
    simpa only [Function.comp_def,
      gradientCoordinateCLM_toCompactnessGradientFiber] using h
  have hdΩ : MemLp
      (fun z => gradientCoordinateCLM i j (D z)) 2 ρΩ := by
    simpa only [Function.comp_def] using
      (gradientCoordinateCLM i j).comp_memLp'
        ((Lp.memLp D).mono_measure hμ)
  have hweakΩ (w : Vec3 × ℝ → ℝ) (hw : MemLp w 2 ρΩ) :
      Tendsto (fun k => ∫ z, Du k z i j * w z ∂ρΩ) atTop
        (nhds (∫ z, gradientCoordinateCLM i j (D z) * w z ∂ρΩ)) :=
    weak_gradient_coordinate_integrals_on_subrectangle
      hΩ hΩK hJ.measurableSet Du D hDmem hDweak i j w hw
  exact weak_partial_on_local_rectangle_of_product_limits
    hΩ hΩfinite hJfinite
    (fun k z => f k z i) (fun k z => Du k z i j)
    (fun z => g z i)
    (fun z => gradientCoordinateCLM i j (D z)) j
    hfScalar hDΩ hdΩ hstrongScalar hweakΩ hpartial

end CKN.Leray
