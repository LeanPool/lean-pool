/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselGridPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselUniformStepGrid
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMollifiedInitialLocalRepresentation

/-!
# Global complete Sobolev paths of the regularized mild solution

Uniform Sobolev restarts and the physical L² energy bound give a continuous
complete Sobolev realization on every finite interval.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- An initial H²ᵏ realization of the regularized mild curve extends as a
continuous H²ᵏ representative on every finite time interval. -/
theorem regularisedBesselGlobalFinitePath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval T,
        regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
          (by positivity) (v t) =
          complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ t.1) := by
  let δ := regularisedBesselUniformEnergyStep ρ ε hε k ‖b₀‖
  have hδ : 0 < δ :=
    regularisedBesselUniformEnergyStep_pos ρ ε hε k ‖b₀‖
      (norm_nonneg b₀)
  obtain ⟨n, -, hTgrid⟩ :=
    regularisedUniformStepGrid_cover δ T hδ hT
  obtain ⟨w, hw⟩ :=
    regularisedBesselGlobalGridPath ρ ε hε k b₀ hbJ b hb (n + 1)
  let L : ℝ := (((n + 1 : ℕ) : ℝ) * δ)
  let incl : RegularizedMildTimeInterval T → RegularizedMildTimeInterval L :=
    fun t => ⟨t.1, t.2.1, t.2.2.trans hTgrid⟩
  have hincl : Continuous incl :=
    continuous_subtype_val.subtype_mk
      (fun t => ⟨t.2.1, t.2.2.trans hTgrid⟩)
  let v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :=
    ⟨fun t => w (incl t), w.continuous.comp hincl⟩
  refine ⟨v, ?_⟩
  intro t
  exact hw (incl t)

/-- The global regularized mild curve from mollified Leray data has a
continuous H²ᵏ realization on every finite interval. -/
theorem regUniformMollifiedInitial_global_bessel_path
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    let b₀ := realVectorL2OfCoordinateFunction
      (regUniformMollifiedInitial ρ ε hε a)
      (regMollifiedInitial_isInJ ρ ε hε ha).1
    ∃ v : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval T,
        regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
            (v t) =
          complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀
              (regUniformMollifiedInitial_mildJData ρ ε hε ha) t.1) := by
  dsimp only
  let b₀ := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a)
    (regMollifiedInitial_isInJ ρ ε hε ha).1
  obtain ⟨b, hb, -⟩ :=
    regUniformMollifiedInitial_local_bessel_representation
      ρ ε hε a ha k
  exact regularisedBesselGlobalFinitePath
    ρ ε hε k b₀
      (regUniformMollifiedInitial_mildJData ρ ε hε ha)
      b hb T hT

end CKN.Leray

end
