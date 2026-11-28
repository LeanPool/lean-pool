/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels
public import LeanPool.FunctionSpaces.ApproximationSpaces.Scheme

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Band-limited functions

For `1 ≤ p < ∞` the **band-limited class** of level `k` is
`E_k = {g ∈ L_p(V) : Θ_k ⋆ g = g}` (`Rd.bandSpace`), with the band-limiting kernel
`Θ_k = 2^(kn) Θ(2^k ·)` of `Rd.Theta`, whose Fourier transform is `1` on the ball of radius
`2^(k+1)` and vanishes outside the ball of radius `2^(k+2)`. On the Fourier side `Θ_k ⋆ g = g`
says `𝓕g = 𝓕Θ_k · 𝓕g`: the spectrum of `g` lies in the ball of radius `2^(k+2)`, and every `g`
with spectrum in the ball of radius `2^(k+1)` satisfies it. These are the functions of exponential
type of Nikol'skii's theory; the definition by the kernel works in every `L_p` without
distributions.

The classes are closed subspaces (`Rd.isClosed_bandSpace`) and increase with `k`, since
`Θ_{k+1} ⋆ Θ_k = Θ_k` (`Rd.bandSpace_mono`). The **band-limited scheme** `Rd.bandScheme` has `E_k`
at complexity `2^k`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **band-limited class** `E_k = {g ∈ L_p : Θ_k ⋆ g = g}`, a real subspace of `L_p(V)`. -/
noncomputable def bandSpace (hp : p ≠ ∞) (k : ℕ) : Submodule ℝ (Lp ℂ p (volume : Measure V)) :=
  LinearMap.ker (((convLp hp (integrable_Theta (V := V) k)).restrictScalars ℝ).toLinearMap -
    LinearMap.id)

/-- `g ∈ E_k` iff `Θ_k ⋆ g = g`. -/
theorem mem_bandSpace {hp : p ≠ ∞} {k : ℕ} {g : Lp ℂ p (volume : Measure V)} :
    g ∈ bandSpace hp k ↔ convLp hp (integrable_Theta k) g = g := by
  rw [bandSpace, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- The band-limited classes are closed under complex scalars. -/
theorem smul_mem_bandSpace {hp : p ≠ ∞} {k : ℕ} (c : ℂ) {g : Lp ℂ p (volume : Measure V)}
    (hg : g ∈ bandSpace hp k) : c • g ∈ bandSpace hp k := by
  rw [mem_bandSpace] at hg ⊢
  rw [map_smul, hg]

/-- The band-limited classes are closed in `L_p`. -/
theorem isClosed_bandSpace (hp : p ≠ ∞) (k : ℕ) :
    IsClosed (bandSpace (V := V) hp k : Set (Lp ℂ p (volume : Measure V))) := by
  have h : (bandSpace (V := V) hp k : Set (Lp ℂ p (volume : Measure V))) =
      {g | convLp hp (integrable_Theta k) g = g} := by
    ext g
    exact mem_bandSpace
  rw [h]
  exact isClosed_eq (convLp hp (integrable_Theta k)).continuous continuous_id

/-- **The band-limited classes increase**: `E_k ⊆ E_{k+1}`, since `Θ_{k+1} ⋆ Θ_k = Θ_k`. -/
theorem bandSpace_mono (hp : p ≠ ∞) : Monotone (bandSpace (V := V) hp) := by
  refine monotone_nat_of_le_succ fun k g hg => ?_
  rw [mem_bandSpace] at hg ⊢
  calc convLp hp (integrable_Theta (k + 1)) g
      = convLp hp (integrable_Theta (k + 1)) (convLp hp (integrable_Theta k) g) := by rw [hg]
    _ = convLp hp (integrable_Theta k) g :=
        convLp_convLp_of_eq hp _ _ _ (conv_Theta_succ k) g
    _ = g := hg

/-- The **band-limited scheme**: `E_k` at complexity `2^k`, that is, `E_⌊log₂ n⌋` at complexity
`n ≥ 1`, and `{0}` at complexity `0` (`ApproximationScheme.ofMonotoneSubmodules`). -/
noncomputable def bandScheme (hp : p ≠ ∞) : ApproximationScheme (Lp ℂ p (volume : Measure V)) :=
  ApproximationScheme.ofMonotoneSubmodules (bandSpace hp) (bandSpace_mono hp)

/-- The level `2^k` of the band-limited scheme is `E_k`. -/
theorem mem_bandScheme_two_pow {hp : p ≠ ∞} {k : ℕ} {g : Lp ℂ p (volume : Measure V)} :
    g ∈ bandScheme hp (2 ^ k) ↔ g ∈ bandSpace hp k :=
  ApproximationScheme.mem_ofMonotoneSubmodules_two_pow

end Rd
