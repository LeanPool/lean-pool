/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.Envelopes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ManifoldPluripolar

/-!
# Rooftop envelopes with genuine pluripolar exceptional sets

Source: `transcendental-nakamaye-revised-20260831:sec:npp`.
The obstacle comparison is quasi-everywhere, exactly as in the revised source.
All order statements here are proved. Analytic preservation of the obstacle
and theta-PSH regularity remain unformalized. Pending contains only the
quasi-everywhere order compositions that still need finite-union closure.
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual theta-PSH functions below the obstacle outside a pluripolar set.
The exceptional set may depend on the competitor. -/
def rooftopCompetitors (θ : SmoothRealForm n M 2) (f : M → EReal) :
    Set (M → EReal) :=
  {u | IsThetaPshPotential θ u ∧ QuasiEverywhere (n := n) (fun x => u x ≤ f x)}

/-- The pointwise supremum before regularization. -/
def rooftopSupremum (θ : SmoothRealForm n M 2) (f : M → EReal) : M → EReal :=
  sSup (rooftopCompetitors θ f)

/-- The revised manuscript's rooftop envelope, with both infinities retained. -/
def rooftopEnvelope (θ : SmoothRealForm n M 2) (f : M → EReal) : M → EReal :=
  uscRegularization (rooftopSupremum θ f)

theorem rooftopSupremum_apply (θ : SmoothRealForm n M 2) (f : M → EReal) (x : M) :
    rooftopSupremum θ f x = ⨆ u ∈ rooftopCompetitors θ f, u x := by
  simp only [rooftopSupremum, sSup_apply, iSup_subtype]

theorem mem_rooftopCompetitors_of_le {θ : SmoothRealForm n M 2} {u f : M → EReal}
    (hu : IsThetaPshPotential θ u) (huf : u ≤ f) : u ∈ rooftopCompetitors θ f :=
  ⟨hu, quasiEverywhere_of_forall huf⟩

theorem rooftopSupremum_le_envelope (θ : SmoothRealForm n M 2) (f : M → EReal) :
    rooftopSupremum θ f ≤ rooftopEnvelope θ f := le_uscRegularization _

theorem le_rooftopSupremum {θ : SmoothRealForm n M 2} {u f : M → EReal}
    (hu : IsThetaPshPotential θ u)
    (huf : QuasiEverywhere (n := n) (fun x => u x ≤ f x)) :
    u ≤ rooftopSupremum θ f := le_sSup ⟨hu, huf⟩

/-- Every quasi-everywhere competitor lies below the envelope everywhere. -/
theorem le_rooftopEnvelope {θ : SmoothRealForm n M 2} {u f : M → EReal}
    (hu : IsThetaPshPotential θ u)
    (huf : QuasiEverywhere (n := n) (fun x => u x ≤ f x)) :
    u ≤ rooftopEnvelope θ f :=
  (le_rooftopSupremum hu huf).trans (rooftopSupremum_le_envelope θ f)

theorem self_le_rooftopEnvelope {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) : u ≤ rooftopEnvelope θ u :=
  le_rooftopEnvelope hu (quasiEverywhere_of_forall (fun _ => le_rfl))

theorem upperSemicontinuous_rooftopEnvelope (θ : SmoothRealForm n M 2) (f : M → EReal) :
    UpperSemicontinuous (rooftopEnvelope θ f) := upperSemicontinuous_uscRegularization _

theorem rooftopSupremum_le_iff {θ : SmoothRealForm n M 2} {f g : M → EReal} :
    rooftopSupremum θ f ≤ g ↔ ∀ u, IsThetaPshPotential θ u →
      QuasiEverywhere (n := n) (fun x => u x ≤ f x) → u ≤ g := by
  simp only [rooftopSupremum, sSup_le_iff, rooftopCompetitors, mem_ofPred_eq, and_imp]

/-- The least USC majorant of all genuine competitors. This does not by
itself assert that the envelope is theta-PSH or below the obstacle. -/
theorem rooftopEnvelope_le_iff {θ : SmoothRealForm n M 2} {f g : M → EReal}
    (hg : UpperSemicontinuous g) :
    rooftopEnvelope θ f ≤ g ↔ ∀ u, IsThetaPshPotential θ u →
      QuasiEverywhere (n := n) (fun x => u x ≤ f x) → u ≤ g := by
  simpa only [rooftopEnvelope, rooftopSupremum, rooftopCompetitors,
    mem_ofPred_eq, and_imp] using
    (uscRegularization_sSup_le_iff (F := rooftopCompetitors θ f) hg)

theorem rooftopCompetitors_mono {θ : SmoothRealForm n M 2} {f g : M → EReal}
    (hfg : f ≤ g) : rooftopCompetitors θ f ⊆ rooftopCompetitors θ g :=
  fun _ hu => ⟨hu.1, hu.2.mono (fun x hx => hx.trans (hfg x))⟩

theorem rooftopSupremum_mono {θ : SmoothRealForm n M 2} {f g : M → EReal}
    (hfg : f ≤ g) : rooftopSupremum θ f ≤ rooftopSupremum θ g :=
  sSup_le_sSup (rooftopCompetitors_mono hfg)

theorem rooftopEnvelope_mono {θ : SmoothRealForm n M 2} {f g : M → EReal}
    (hfg : f ≤ g) : rooftopEnvelope θ f ≤ rooftopEnvelope θ g :=
  uscRegularization_mono (rooftopSupremum_mono hfg)

theorem rooftopSupremum_of_empty {θ : SmoothRealForm n M 2} {f : M → EReal}
    (h : rooftopCompetitors θ f = ∅) : rooftopSupremum θ f = ⊥ := by
  simp [rooftopSupremum, h]

theorem rooftopEnvelope_of_empty {θ : SmoothRealForm n M 2} {f : M → EReal}
    (h : rooftopCompetitors θ f = ∅) : rooftopEnvelope θ f = ⊥ := by
  unfold rooftopEnvelope
  rw [rooftopSupremum_of_empty h]
  exact uscRegularization_const ⊥

theorem rooftopEnvelope_locallyNondegenerate {θ : SmoothRealForm n M 2} {f : M → EReal}
    (hne : (rooftopCompetitors θ f).Nonempty) :
    LocallyNondegenerate (rooftopEnvelope θ f) := by
  obtain ⟨u, hu, huf⟩ := hne
  exact hu.2.mono (le_rooftopEnvelope hu huf)

theorem rooftopCompetitors_geometricallyEq {θ η : SmoothRealForm n M 2}
    (hθη : θ.GeometricallyEq η) (f : M → EReal) :
    rooftopCompetitors θ f = rooftopCompetitors η f := by
  ext u
  exact and_congr (hθη.thetaPshPotential_iff u) Iff.rfl

theorem rooftopEnvelope_geometricallyEq {θ η : SmoothRealForm n M 2}
    (hθη : θ.GeometricallyEq η) (f : M → EReal) :
    rooftopEnvelope θ f = rooftopEnvelope η f := by
  unfold rooftopEnvelope rooftopSupremum
  rw [rooftopCompetitors_geometricallyEq hθη]

end

end SGPT.Foundations.Analysis.FirstPass
