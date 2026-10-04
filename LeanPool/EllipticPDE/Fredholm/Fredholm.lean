/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Existence.Garding
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative


/-!
# Fredholm alternative for the elliptic Dirichlet problem

Evans §6.2.3, Theorem 4.

For the full divergence-form operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu` the Gårding inequality
makes the shifted form `B_γ = B + γ⟨·,·⟩_{L²}` coercive (`shiftedBilin_coercive`), so `L + γ` is
invertible by Lax-Milgram. Writing the solution operator of `L + γ` and the `L²` form as bounded
operators on `H₀¹(Ω)` reduces the weak problem `Lu = f` to a compact-operator equation
`(1 - K)u = h`, to which Mathlib's Fredholm alternative for compact operators
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) applies at the eigenvalue `1`.

The reduction is exact:

* `opA` / `opT`: the Riesz representatives of the full form `B` and of the `L²` form
  `⟨u₀, v₀⟩` as bounded operators on `H₀¹(Ω)` (`InnerProductSpace.continuousLinearMapOfBilin`),
  with `⟪opA u, v⟫ = B[u,v]` and `⟪opT u, v⟫ = ⟨u₀, v₀⟩`.
* `opE`: the coercive Lax-Milgram equivalence of `B_γ` (for `γ = gardingγ`), so
  `opA = opE - γ·opT` (`opA_eq`) and hence `opA = opE ∘ (1 - opK)` (`opA_factor`) with
  `opK = γ·opE⁻¹·opT`.
* `fredholm_alternative`: assuming `opK` is a **compact** operator (the Rellich-Kondrachov
  input, that the embedding `H₀¹(Ω) ↪ L²(Ω)` is compact, exactly as the box geometry was the
  external input for coercivity): either `Lu = 0` has a nontrivial weak solution, or `Lu = f`
  has a unique weak solution for every `f`. `fredholm_unique_imp_exists` is the usual corollary:
  uniqueness for the homogeneous problem forces solvability of the inhomogeneous one.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

namespace FullEllipticOp

variable (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-! ### Riesz representatives of the forms as bounded operators on `H₀¹(Ω)` -/

/-- The Riesz representative of the full divergence form `B` as an operator on `H₀¹(Ω)`:
`⟪opA u, v⟫ = B[u, v]`. -/
def opA : H01 Ω →L[ℝ] H01 Ω := continuousLinearMapOfBilin (Op.fullBilin Ω)

/-- The Riesz representative of the `L²` form `⟨u₀, v₀⟩` as an operator on `H₀¹(Ω)`. -/
def opT : H01 Ω →L[ℝ] H01 Ω := continuousLinearMapOfBilin (zerothForm Ω)

/-- The coercive Lax-Milgram equivalence of the shifted form `B_γ`, `γ = gardingγ`. -/
def opE : H01 Ω ≃L[ℝ] H01 Ω :=
  (Op.shiftedBilin_coercive Ω (le_refl Op.gardingγ)).continuousLinearEquivOfBilin

/-- Riesz identity: `⟪Op.opA Ω u, v⟫ = Op.fullBilin Ω u v`. -/
lemma inner_opA (u v : H01 Ω) : ⟪Op.opA Ω u, v⟫ = Op.fullBilin Ω u v :=
  continuousLinearMapOfBilin_apply (Op.fullBilin Ω) u v

/-- Riesz identity: `⟪opT Ω u, v⟫ = zerothForm Ω u v = ⟨u₀, v₀⟩_{L²}`. -/
lemma inner_opT (u v : H01 Ω) : ⟪opT Ω u, v⟫ = zerothForm Ω u v :=
  continuousLinearMapOfBilin_apply (zerothForm Ω) u v

/-- Riesz identity: `⟪Op.opE Ω u, v⟫ = Op.shiftedBilin Ω Op.gardingγ u v`. -/
lemma inner_opE (u v : H01 Ω) :
    ⟪Op.opE Ω u, v⟫ = Op.shiftedBilin Ω Op.gardingγ u v :=
  (Op.shiftedBilin_coercive Ω (le_refl Op.gardingγ)).continuousLinearEquivOfBilin_apply u v

/-! ### Reduction to `1 - opK` -/

/-- `opA = opE - γ·opT`: subtracting the shift recovers the unshifted form. -/
lemma opA_eq :
    Op.opA Ω = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - Op.gardingγ • opT Ω := by
  refine ContinuousLinearMap.ext (fun u => ext_inner_right (𝕜 := ℝ) (fun v => ?_))
  rw [_root_.sub_apply, _root_.smul_apply, inner_sub_left,
    real_inner_smul_left, ContinuousLinearEquiv.coe_coe, Op.inner_opA Ω, Op.inner_opE Ω,
    inner_opT Ω, Op.shiftedBilin_apply, zerothForm_apply]
  ring

/-- The compact part of the reduction: `opK = γ·opE⁻¹·opT`. -/
def opK : H01 Ω →L[ℝ] H01 Ω :=
  Op.gardingγ • ((Op.opE Ω).symm : H01 Ω →L[ℝ] H01 Ω).comp (opT Ω)

/-- `opA = opE ∘ (1 - opK)`: the weak problem `Lu = f` becomes `(1 - opK)u = opE⁻¹(opA⁻¹…)`. -/
lemma opA_factor :
    Op.opA Ω = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp (1 - Op.opK Ω) := by
  have hcomp : (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp (1 - Op.opK Ω)
      = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - Op.gardingγ • opT Ω := by
    refine ContinuousLinearMap.ext (fun u => ?_)
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      one_apply_eq_self, _root_.smul_apply, opK,
      ContinuousLinearEquiv.coe_coe, map_sub, map_smul,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [Op.opA_eq Ω, hcomp]

/-! ### Fredholm alternative -/

/-- **Fredholm alternative for the elliptic Dirichlet problem** (Evans §6.2.3,
Theorem 4). Assume the
operator `opK` is compact: the Rellich-Kondrachov input, that `H₀¹(Ω) ↪ L²(Ω)` is a compact
embedding. Then exactly one of two alternatives holds: either the homogeneous problem `Lu = 0`
has a nontrivial weak solution `u ≠ 0` (`∀ v, B[u, v] = 0`), or the inhomogeneous problem
`Lu = f` has a unique weak solution for every continuous functional `f`. -/
theorem fredholm_alternative (hK : IsCompactOperator (Op.opK Ω)) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) := by
  rcases hK.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℝ)) one_ne_zero with he | hr
  · -- Eigenvalue `1`: a nonzero `u` with `opK u = u`, hence `opA u = 0`, i.e. `Lu = 0`.
    left
    obtain ⟨x, hx_mem, hx_ne⟩ := he.exists_hasEigenvector
    have hKx : Op.opK Ω x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx_mem
    have hAx : Op.opA Ω x = 0 := by
      rw [Op.opA_factor Ω, ContinuousLinearMap.comp_apply]
      have h0 : (1 - Op.opK Ω) x = 0 := by
        rw [_root_.sub_apply, one_apply_eq_self, hKx, sub_self]
      rw [h0, map_zero]
    refine ⟨x, hx_ne, fun v => ?_⟩
    have hv := Op.inner_opA Ω x v
    rw [hAx, inner_zero_left] at hv
    exact hv.symm
  · -- Resolvent: `1 - opK` is bijective, hence so is `opA`, giving unique solvability.
    right
    have hunit : IsUnit ((1 : H01 Ω →L[ℝ] H01 Ω) - Op.opK Ω) := by
      have h := spectrum.mem_resolventSet_iff.mp hr
      rwa [map_one] at h
    have hKbij : Function.Bijective ((1 : H01 Ω →L[ℝ] H01 Ω) - Op.opK Ω) :=
      ContinuousLinearMap.isUnit_iff_bijective.mp hunit
    have hEbij : Function.Bijective (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) := by
      simpa using (Op.opE Ω).bijective
    have hbij : Function.Bijective (Op.opA Ω) := by
      rw [Op.opA_factor Ω]
      exact hEbij.comp hKbij
    intro f
    set g : H01 Ω := (InnerProductSpace.toDual ℝ (H01 Ω)).symm f with hgdef
    have hg : ∀ v, ⟪g, v⟫ = f v := fun v => InnerProductSpace.toDual_symm_apply
    have hiff : ∀ u : H01 Ω, Op.opA Ω u = g ↔ ∀ v, Op.fullBilin Ω u v = f v := by
      intro u
      constructor
      · intro hu v; rw [← Op.inner_opA Ω u v, hu, hg]
      · intro hu
        refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
        rw [Op.inner_opA Ω u v, hu v, hg]
    exact (existsUnique_congr hiff).mp (hbij.existsUnique g)

/-- **Fredholm corollary** (the usual working form, Evans §6.2.3): if the homogeneous problem
`Lu = 0` has only the trivial weak solution, then `Lu = f` has a unique weak solution for every
`f`. Uniqueness of the homogeneous problem rules out the eigenvalue alternative. -/
theorem fredholm_unique_imp_exists (hK : IsCompactOperator (Op.opK Ω))
    (huniq : ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = 0) → u = 0)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v := by
  rcases Op.fredholm_alternative Ω hK with ⟨u, hu_ne, hu_hom⟩ | hexists
  · exact absurd (huniq u hu_hom) hu_ne
  · exact hexists f

end FullEllipticOp

end EllipticPdes.Sobolev
