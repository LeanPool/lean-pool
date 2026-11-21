/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.WeakDerivativeMollification

/-! # Actual finite coordinate assembly in Euclidean L²

Finite-dimensional coordinate strong convergence is assembled in the actual
vector-valued Lebesgue L² Hilbert space, using actual bounded linear maps.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology ContinuousLinearMap

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual Euclidean coordinate decomposition. -/
theorem euclidean_sum_coordinate_smul_single (x : E) :
    (∑ j : Fin d, x j • EuclideanSpace.single j (1 : ℝ)) = x := by
  apply PiLp.ext
  intro i
  change (EuclideanSpace.proj i : E →L[ℝ] ℝ) (∑ j : Fin d, x j • EuclideanSpace.single j (1 : ℝ)) =
    x i
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ j : Fin d, x j * (EuclideanSpace.single j (1 : ℝ)) i) = x i
  simp [PiLp.single_apply]

/-- Assemble actual scalar L² coordinates into the genuine Euclidean L² space. -/
@[expose] noncomputable def euclideanL2Assemble (f : Fin d → E →₂[volume] ℝ) : E →₂[volume] E :=
  ∑ j : Fin d, (toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLp (f j)

/-- Actual scalar projection of an assembled L² vector is the original coordinate. -/
theorem euclideanL2_project_assemble (f : Fin d → E →₂[volume] ℝ) (i : Fin d) :
    (EuclideanSpace.proj i : E →L[ℝ] ℝ).compLp (euclideanL2Assemble f) = f i := by
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Fin d => (toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLp (f j))
  have hEmb : ∀ᵐ x ∂(volume : Measure E), ∀ j : Fin d,
      ((toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLp (f j)) x =
        (f j x) • EuclideanSpace.single j (1 : ℝ) := by
    apply ae_all_iff.mpr
    intro j
    exact (toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).coeFn_compLp (f j)
  filter_upwards [(EuclideanSpace.proj i : E →L[ℝ] ℝ).coeFn_compLp (euclideanL2Assemble f), hsum,
    hEmb]
    with x hproj hs he
  rw [hproj]
  change (EuclideanSpace.proj i : E →L[ℝ] ℝ) (euclideanL2Assemble f x) = _
  change (EuclideanSpace.proj i : E →L[ℝ] ℝ)
    ((∑ j : Fin d, (toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLp (f j)) x) = _
  rw [hs, map_sum]
  simp_rw [he]
  simp only [map_smul, smul_eq_mul]
  change (∑ j : Fin d, f j x * (EuclideanSpace.single j (1 : ℝ)) i) = f i x
  simp [PiLp.single_apply]

/-- Actual vector-valued L² is recovered from its genuine coordinate projections. -/
theorem euclideanL2_assemble_projections (f : E →₂[volume] E) :
    euclideanL2Assemble (fun j => (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp f) = f := by
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Fin d => (toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLp
      ((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp f))
  have hEmb : ∀ᵐ x ∂(volume : Measure E), ∀ j : Fin d,
      ((toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLp
        ((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp f)) x =
      (((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp f) x) • EuclideanSpace.single j (1 : ℝ) := by
    apply ae_all_iff.mpr
    intro j
    exact (toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).coeFn_compLp _
  have hProj : ∀ᵐ x ∂(volume : Measure E), ∀ j : Fin d,
      ((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp f) x = (f x) j := by
    apply ae_all_iff.mpr
    intro j
    exact (EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp f
  filter_upwards [hsum, hEmb, hProj] with x hs he hp
  change (∑ j : Fin d, (toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLp
      ((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp f)) x = f x
  rw [hs]
  simp_rw [he, hp]
  exact euclidean_sum_coordinate_smul_single (f x)

/-- Genuine coordinatewise strong L² convergence implies genuine vector
strong L² convergence, by finite bounded-linear reconstruction. -/
theorem tendsto_euclideanL2_of_coordinate_tendsto {f : ℕ → E →₂[volume] E} {g : E →₂[volume] E}
    (hcoord : ∀ j : Fin d, Tendsto (fun n => (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp (f n))
      atTop (𝓝 ((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp g))) :
    Tendsto f atTop (𝓝 g) := by
  have hterm (j : Fin d) :=
    (((toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLpL 2 volume).continuous.tendsto
      ((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp g)).comp (hcoord j)
  have hs := tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  change Tendsto (fun n => euclideanL2Assemble (fun j => (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp
    (f n)))
    atTop (𝓝 (euclideanL2Assemble (fun j => (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp g))) at hs
  simpa only [euclideanL2_assemble_projections] using hs

end CutoffRigidity
