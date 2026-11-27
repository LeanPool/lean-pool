/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalFunctionalStarEquiv
public import LeanPool.VacuumBellSeparation.Bell.FaithfulNormalGNSImage
public import LeanPool.VacuumBellSeparation.Bell.SeparatingCommutantCyclic

/-!
The original algebra and the literal faithful normal GNS VNA are actually
star-isomorphic. Every positive functional transports by the genuine inverse,
with both directions of full order-normality and exact full-dual norm already
proved generically. The reference is the actual separating GNS vector.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance faithfulTransport_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Composition algebra of bounded operators on the completed GNS Hilbert space. -/
local instance faithfulTransportGNSOperatorAlgebra (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) : Algebra ℂ (φ.GNS →L[ℂ] φ.GNS) :=
  ContinuousLinearMap.algebra

-- Prove the algebraic restriction before specializing to the completed GNS carrier.
/-- Restrict an injective star algebra homomorphism to its identified range. -/
def faithfulTransportEquivOfRange {A B : Type*}
    [Ring A] [Algebra ℂ A] [StarRing A]
    [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (π : A →⋆ₐ[ℂ] B) (hπ : Function.Injective π)
    (S : StarSubalgebra ℂ B) (hS : S = π.range) : A ≃⋆ₐ[ℂ] S := by
  let πS : A →⋆ₐ[ℂ] S := π.codRestrict S (fun a => by rw [hS]; exact ⟨a, rfl⟩)
  apply StarAlgEquiv.ofBijective πS
  constructor
  · intro a b hab
    exact hπ (congrArg (fun z : S => (z : B)) hab)
  · intro b
    have hb : (b : B) ∈ π.range := by rw [← hS]; exact b.2
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, Subtype.ext ha⟩

private theorem faithfulTransport_equivOfRange_apply {A B : Type*}
    [Ring A] [Algebra ℂ A] [StarRing A]
    [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (π : A →⋆ₐ[ℂ] B) (hπ : Function.Injective π)
    (S : StarSubalgebra ℂ B) (hS : S = π.range) (a : A) :
    (faithfulTransportEquivOfRange π hπ S hS a : B) = π a := rfl

/-- Codomain restriction uses the proved literal image equality. The equality
is not replaced by density in, or generation of, a larger algebra. -/
def gnsEquivOfRangeEquality (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0)
    (N : VonNeumannAlgebra φ.GNS) (hN : N.toStarSubalgebra = φ.gnsStarAlgHom.range) :
    M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra :=
  faithfulTransportEquivOfRange (A := M.toStarSubalgebra) (B := φ.GNS →L[ℂ] φ.GNS)
    φ.gnsStarAlgHom (gnsStarAlgHom_injective_of_faithful φ hf) N.toStarSubalgebra hN

theorem gnsEquivOfRangeEquality_apply (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0)
    (N : VonNeumannAlgebra φ.GNS) (hN : N.toStarSubalgebra = φ.gnsStarAlgHom.range)
    (a : M.toStarSubalgebra) :
    (gnsEquivOfRangeEquality M φ hf N hN a : φ.GNS →L[ℂ] φ.GNS) = φ.gnsStarAlgHom a :=
  faithfulTransport_equivOfRange_apply φ.gnsStarAlgHom
    (gnsStarAlgHom_injective_of_faithful φ hf) N.toStarSubalgebra hN a

-- Eliminate the range witness and construct all transport data on an abstract
-- Hilbert carrier. The completed GNS carrier is substituted only afterwards.
private theorem faithfulTransport_exists_of_range
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (π : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    (hπ : Function.Injective π)
    (hrange : ∃ N : VonNeumannAlgebra K, N.toStarSubalgebra = π.range)
    (hsep : ∀ T : K →L[ℂ] K, T ∈ π.range → T Ω = 0 → T = 0)
    (hcoeff : ∀ a : M.toStarSubalgebra, inner ℂ Ω (π a Ω) = φ a) :
    ∃ (N : VonNeumannAlgebra K) (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra),
      N.toStarSubalgebra = π.range ∧
      (∀ a, (e a : K →L[ℂ] K) = π a) ∧
      IsSeparatingForAlgebra N Ω ∧
      (∀ b, positiveFunctionalPushforward M N e φ b = vectorFunctional N Ω b) ∧
      (∀ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ,
        IsNormalFunctional N (positiveFunctionalPushforward M N e ψ) ↔ IsNormalFunctional M ψ) := by
  obtain ⟨N, hN⟩ := hrange
  let e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra :=
    faithfulTransportEquivOfRange π hπ N.toStarSubalgebra hN
  have he (a : M.toStarSubalgebra) : (e a : K →L[ℂ] K) = π a :=
    faithfulTransport_equivOfRange_apply π hπ N.toStarSubalgebra hN a
  refine ⟨N, e, hN, he, ?_, ?_, ?_⟩
  · intro T hT hz
    apply hsep T _ hz
    change T ∈ N.toStarSubalgebra at hT
    rwa [hN] at hT
  · intro b
    rw [positiveFunctionalPushforward_apply]
    change φ (e.symm b) = inner ℂ Ω ((b : K →L[ℂ] K) Ω)
    have hb : (b : K →L[ℂ] K) = π (e.symm b) := by
      simpa only [StarAlgEquiv.apply_symm_apply] using he (e.symm b)
    rw [hb]
    exact (hcoeff (e.symm b)).symm
  · exact fun ψ => positiveFunctionalPushforward_normal_iff M N e ψ

/-- All positive normal original functionals can be moved to this actual VNA.
There is no normality or representation hypothesis on an inverse map. -/
theorem exists_faithful_normal_gns_transport
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    ∃ (N : VonNeumannAlgebra φ.GNS) (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra),
      N.toStarSubalgebra = φ.gnsStarAlgHom.range ∧
      (∀ a, (e a : φ.GNS →L[ℂ] φ.GNS) = φ.gnsStarAlgHom a) ∧
      IsSeparatingForAlgebra N (gnsUnitVector φ) ∧
      (∀ b, positiveFunctionalPushforward M N e φ b = vectorFunctional N (gnsUnitVector φ) b) ∧
      (∀ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ,
        IsNormalFunctional N (positiveFunctionalPushforward M N e ψ) ↔ IsNormalFunctional M ψ) := by
  exact faithfulTransport_exists_of_range (K := φ.GNS) M φ
    φ.gnsStarAlgHom (gnsUnitVector φ)
    (gnsStarAlgHom_injective_of_faithful φ hf)
    (exists_vna_eq_gns_range_of_faithful_normal M φ hn hf)
    (gns_unitVector_separates_range_of_faithful φ hf)
    (gnsUnitVector_expectation φ)

end VacuumBellSeparation.Bipartite
