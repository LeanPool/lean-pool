/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import LeanPool.VacuumBellSeparation.Bell.BipartiteNormalStateDefs
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
Positive functionals and full directed-set order-normality transported by an
actual star-algebra equivalence between concrete VNAs. Normality of the
inverse is derived from order reflection and surjectivity, not assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

instance normalTransport_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

theorem vnaStarEquiv_le_iff (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra) {a b : M.toStarSubalgebra} :
    e a ≤ e b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff
    (A := M.toStarSubalgebra) (B := N.toStarSubalgebra) e.toNonUnitalStarAlgHom e.injective

/-- No directedness or positivity restriction is needed for this order fact. -/
theorem vnaStarEquiv_isLUB_image (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    {s : Set M.toStarSubalgebra} {a : M.toStarSubalgebra} (ha : IsLUB s a) :
    IsLUB (e '' s) (e a) := by
  constructor
  · rintro _ ⟨b, hb, rfl⟩
    exact (vnaStarEquiv_le_iff M N e).mpr (ha.1 hb)
  · intro c hc
    obtain ⟨b, rfl⟩ := e.surjective c
    apply (vnaStarEquiv_le_iff M N e).mpr
    apply ha.2
    intro x hx
    exact (vnaStarEquiv_le_iff M N e).mp (hc ⟨x, hx, rfl⟩)

theorem isNormalFunctional_pullback_starEquiv
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (f : N.toStarSubalgebra → ℂ) (hf : IsNormalFunctional N f) :
    IsNormalFunctional M (fun a => f (e a)) := by
  intro s hs hdir hpos a ha
  have hd : DirectedOn (· ≤ ·) (e '' s) := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨d, hd, hbd, hcd⟩ := hdir b hb c hc
    exact ⟨e d, ⟨d, hd, rfl⟩,
      (vnaStarEquiv_le_iff M N e).mpr hbd, (vnaStarEquiv_le_iff M N e).mpr hcd⟩
  have hp : ∀ b ∈ e '' s, 0 ≤ b := by
    rintro _ ⟨b, hb, rfl⟩
    simpa only [map_zero] using (vnaStarEquiv_le_iff M N e).mpr (hpos b hb)
  have h := hf (e '' s) (hs.image e) hd hp (e a) (vnaStarEquiv_isLUB_image M N e ha)
  simpa only [Set.image_image] using h

theorem isNormalFunctional_pullback_starEquiv_iff
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra) (f : N.toStarSubalgebra → ℂ) :
    IsNormalFunctional M (fun a => f (e a)) ↔ IsNormalFunctional N f := by
  constructor
  · intro h
    have h' := isNormalFunctional_pullback_starEquiv N M e.symm (fun a => f (e a)) h
    simpa only [StarAlgEquiv.apply_symm_apply] using h'
  · exact isNormalFunctional_pullback_starEquiv M N e f

/-- Pushforward along e is literal precomposition with its inverse. -/
def positiveFunctionalPushforward
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) : N.toStarSubalgebra →ₚ[ℂ] ℂ where
  toLinearMap := φ.toLinearMap.comp e.symm.toAlgEquiv.toLinearEquiv.toLinearMap
  monotone' := fun _ _ h => OrderHomClass.mono φ
    ((vnaStarEquiv_le_iff N M e.symm).mpr h)

@[simp] theorem positiveFunctionalPushforward_apply
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (b : N.toStarSubalgebra) :
    positiveFunctionalPushforward M N e φ b = φ (e.symm b) := rfl

theorem positiveFunctionalPushforward_one
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    positiveFunctionalPushforward M N e φ 1 = φ 1 := by
  simp only [positiveFunctionalPushforward_apply, map_one]

@[simp] theorem positiveFunctionalPushforward_symm
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    positiveFunctionalPushforward N M e.symm (positiveFunctionalPushforward M N e φ) = φ := by
  apply PositiveLinearMap.ext
  intro a
  simp only [positiveFunctionalPushforward_apply, StarAlgEquiv.symm_symm,
    StarAlgEquiv.symm_apply_apply]

theorem positiveFunctionalPushforward_normal_iff
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    IsNormalFunctional N (positiveFunctionalPushforward M N e φ) ↔ IsNormalFunctional M φ :=
  isNormalFunctional_pullback_starEquiv_iff N M e.symm φ

/-- The genuine full-dual norm is preserved, including differences of positives.
This uses both isometry and surjectivity, not just a bound on positive inputs. -/
theorem positiveFunctionalPushforward_difference_norm
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    ‖(PositiveContinuousLinearMap.ofClass (positiveFunctionalPushforward M N e
      φ)).toContinuousLinearMap -
      (PositiveContinuousLinearMap.ofClass (positiveFunctionalPushforward M N e
        ψ)).toContinuousLinearMap‖ =
    ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap -
      (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap‖ := by
  let f := (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap -
    (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap
  let g := (PositiveContinuousLinearMap.ofClass (positiveFunctionalPushforward M N e
    φ)).toContinuousLinearMap -
    (PositiveContinuousLinearMap.ofClass (positiveFunctionalPushforward M N e
      ψ)).toContinuousLinearMap
  have hg (b : N.toStarSubalgebra) : g b = f (e.symm b) := rfl
  have hn (a : M.toStarSubalgebra) : ‖e a‖ = ‖a‖ :=
    NonUnitalStarAlgHom.norm_map
      (A := M.toStarSubalgebra) (B := N.toStarSubalgebra) e.toNonUnitalStarAlgHom e.injective a
  have hninv (b : N.toStarSubalgebra) : ‖e.symm b‖ = ‖b‖ :=
    NonUnitalStarAlgHom.norm_map
      (A := N.toStarSubalgebra) (B := M.toStarSubalgebra)
      e.symm.toNonUnitalStarAlgHom e.symm.injective b
  change ‖g‖ = ‖f‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro b
    rw [hg]
    simpa only [hninv] using f.le_opNorm (e.symm b)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
    intro a
    have h := g.le_opNorm (e a)
    simpa only [hg, StarAlgEquiv.symm_apply_apply,
      hn] using h

end VacuumBellSeparation.Bipartite
