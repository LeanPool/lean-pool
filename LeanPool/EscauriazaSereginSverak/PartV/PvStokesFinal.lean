/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PvStokes
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatStrongContinuity

/-!
# The zero-data Stokes estimate

`lem:pv-stokes`: for a tensor `F ∈ L^{5/2}(Q_τ) ∩ L²(Q_τ)` with pressure
`q = -P[F]`, the zero-data Stokes response `z` exists, is continuous into `L²` and
`L³` with `z(0) = 0`, lies in `L²(0, τ; H¹) ∩ L⁵ ∩ L⁴`, is divergence free, solves
`∂ₜz - Δz = div F - ∇q` in the sense of distributions with
`∂ₜz ∈ L²(0, τ; V')`, satisfies the `L³`/`L⁵`, `L⁴` and energy bounds with a
constant independent of `τ`, and is unique among square-integrable
distributional solutions with the same pressure and zero initial trace.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `lem:pv-stokes`. -/
theorem pvStokes :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ F : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 2))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) →
      (∀ i j, MemLp (F i j) 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) →
      ∃ z : ParabolicPoint → Vec3, ∃ Dz : ParabolicPoint → Fin 3 → Vec3,
        -- zero initial datum and continuity into `L²` and `L³`
        (∀ x : Vec3, z (x, 0) = 0) ∧
        (∀ t ∈ Icc 0 τ, MemLp (fun x : Vec3 => z (x, t)) 2 volume ∧
          MemLp (fun x : Vec3 => z (x, t)) 3 volume) ∧
        (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 => z (x, s) - z (x, t)) 2 volume)
          (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
        (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 => z (x, s) - z (x, t)) 3 volume)
          (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
        -- `L²(0, τ; H¹)`, divergence free, `L⁵ ∩ L⁴`
        MemLp z 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        MemLp Dz 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        (∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), ∀ i : Fin 3,
          HasWeakGradientOn (Set.univ : Set Vec3) (fun x => z (x, s) i) (fun x => Dz (x, s) i)) ∧
        (∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
          ∫ x : Vec3, ∑ i : Fin 3, z (x, s) i * ψ.partialDeriv i x = 0) ∧
        MemLp z 5 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        MemLp z 4 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        -- the pressure `q = -P[F]`
        MemLp (pvStokesPressureSlab τ F) (ENNReal.ofReal 2)
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        MemLp (pvStokesPressureSlab τ F) (ENNReal.ofReal (5 / 2))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        -- `∂ₜz - Δz = div F - ∇q` in the sense of distributions on `Q_τ`
        (∀ φ : ParabolicPoint → Vec3,
          φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
          ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, z p i *
              (-timePartial (fun y => φ y i) p -
                ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) =
            ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
              (-(∑ i : Fin 3, ∑ j : Fin 3, F i j p * spatialPartial (fun y => φ y j) i p) +
                pvStokesPressureSlab τ F p * ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p)) ∧
        -- `∂ₜz ∈ L²(0, τ; V')`: `∂ₜz = div H` against divergence-free tests, `H ∈ L²`
        (∃ H : ParabolicPoint → Fin 3 → Fin 3 → ℝ,
          MemLp H 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
          eLpNorm H 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
            ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) 2
              (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
          ∀ φ : ParabolicPoint → Vec3,
            φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
            (∀ p : ParabolicPoint, ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p = 0) →
            ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
                ∑ j : Fin 3, z p j * timePartial (fun y => φ y j) p =
              ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
                ∑ i : Fin 3, ∑ j : Fin 3, H p i j * spatialPartial (fun y => φ y j) i p) ∧
        -- the estimates
        (∀ t ∈ Icc 0 τ, eLpNorm (fun x : Vec3 => z (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) (ENNReal.ofReal (5 / 2))
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm z 5 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) (ENNReal.ofReal (5 / 2))
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        eLpNorm z 4 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * (eLpNorm (fun p => fun i j => F i j p) (ENNReal.ofReal (5 / 2))
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) +
            eLpNorm (fun p => fun i j => F i j p) 2
              (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        (∀ t ∈ Icc 0 τ, eLpNorm (fun x : Vec3 => z (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm Dz 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        -- uniqueness among square-integrable distributional solutions with zero trace
        (∀ z' : ParabolicPoint → Vec3,
          MemLp z' 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) →
          (∀ φ : ParabolicPoint → Vec3,
            φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
            ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, z' p i *
                (-timePartial (fun y => φ y i) p -
                  ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) =
              ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
                (-(∑ i : Fin 3, ∑ j : Fin 3, F i j p * spatialPartial (fun y => φ y j) i p) +
                  pvStokesPressureSlab τ F p * ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p)) →
          (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
              ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), c t = ∫ x, ∑ i : Fin 3, z' (x, t) i * ψ x i) →
          z' =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))] z) :=
  pvStokes_of_strongContinuity forcedHeat_strong_continuity

end ESS

end
