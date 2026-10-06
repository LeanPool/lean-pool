/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzDensity

/-!
# Genuine Schwartz fields in complete Bessel spaces

The canonical Sobolev lift of a Schwartz distribution has dense range
in every complete Bessel potential space.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The canonical complete Sobolev field represented by a Schwartz map. -/
@[expose]
def regularisedBesselOfSchwartz (s : ℝ)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) :
    BesselPotentialSpace L2Vec3 ComplexVec3 s 2 :=
  (ψ.memSobolev (s := s) (p := 2)).toBesselPotentialSpace

/-- The canonical Schwartz Sobolev lift represents the original
Schwartz distribution. -/
theorem regularisedBesselOfSchwartz_toDistr
    (s : ℝ) (ψ : 𝓢(L2Vec3, ComplexVec3)) :
    (regularisedBesselOfSchwartz s ψ).toDistr =
      (ψ : 𝓢'(L2Vec3, ComplexVec3)) :=
  (ψ.memSobolev (s := s) (p := 2)).toBesselPotentialSpace_toDistr

/-- Every Bessel lift of a Schwartz L² field is represented by a
Schwartz distribution in the same complete Sobolev space. -/
theorem regularisedBesselSchwartzLift_range_subset (s : ℝ) :
    Set.range
      (fun φ : 𝓢(L2Vec3, ComplexVec3) =>
        BesselPotentialSpace.ofLp s (φ.toLp 2)) ⊆
      Set.range (regularisedBesselOfSchwartz s) := by
  intro v hv
  obtain ⟨φ, rfl⟩ := hv
  obtain ⟨ψ, hψ⟩ :=
    regularisedBesselSchwartzLift_hasSchwartzRepresentative s φ
  refine ⟨ψ, ?_⟩
  apply BesselPotentialSpace.ext
  rw [regularisedBesselOfSchwartz_toDistr]
  exact hψ.symm


end CKN.Leray

end
