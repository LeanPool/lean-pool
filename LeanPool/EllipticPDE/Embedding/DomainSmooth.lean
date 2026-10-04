/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.DomainHolder
public import LeanPool.EllipticPDE.Embedding.ClassicalDeriv


/-!
# Classical derivatives up to the boundary

`EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain` produces a bounded
Hölder representative of each member separately. `u ∈ C^{k-1-⌊n/p⌋,γ}(closure Ω)` says more: one
function, differentiable to order `k - 1 - ⌊n/p⌋` on `Ω`, whose derivatives are the members
themselves and whose top derivatives are `γ`-Hölder on `closure Ω`. This file supplies that.

The representatives are chosen once, before any of them is read, so a single family `v` serves
every index. Each `v i` is continuous on `closure Ω`, hence on `Ω`, and integrable there, and
it has the weak gradient `fun k => v (nxt i k)` because a weak gradient sees only the
almost-everywhere class.
`EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn` then makes the weak
gradient a classical one at every point of `Ω`, and an induction on the order remaining reads
`ContDiffOn` off the chain.

The estimate is the one the clause states: the constant is quantified before the family, and it
bounds the supremum and the Hölder seminorm of every member on `closure Ω` by a uniform
`L^{p₀}` bound.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem IV.2.3 case
(ii); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (ii).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary)

variable {d : ℕ}

/-- **Clause (ii) of the embedding with classical derivatives.** One family of representatives
serves every index: each is bounded and Hölder on `closure Ω` under the constant the clause
names, each of low enough depth is differentiable on `Ω` with the next members as its partial
derivatives,
and each is `n` times continuously differentiable on `Ω` whenever the supply leaves `n` orders
above it. -/
theorem exists_const_contDiffOn_holderOnWith_of_gradClosed_domain (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (ι : Type*) {p₀ P : ℝ≥0} (hp₀ : 1 ≤ p₀) {s : ℕ}
    (hsd : (p₀ : ℝ) * s ≤ (d : ℝ)) (hp₀P : p₀ ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ i, dep i + 1 + s ≤ m → v i =ᵐ[volume.restrict Ω] F i) ∧
        (∀ i, dep i + 1 + s ≤ m → ∀ y ∈ closure Ω, ‖v i y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
        (∀ i, dep i + 1 + s ≤ m →
          HolderOnWith (C * M) (morreyExponent d (P : ℝ)) (v i) (closure Ω)) ∧
        (∀ (n : ℕ) (i : ι), dep i + n + 1 + s ≤ m → ContDiffOn ℝ (n : ℕ) (v i) Ω) ∧
        (∀ i, dep i + 2 + s ≤ m → ∀ y ∈ Ω,
          HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y) := by
  classical
  obtain ⟨C, hC⟩ :=
    exists_const_holderOnWith_of_gradClosed_domain hd hΩopen hΩb hC1 ι hp₀ hsd hp₀P hPd hPs
  refine ⟨C, ?_⟩
  intro F nxt dep m hdep hgrad hmem M hM
  have hd0 : 0 < d := by omega
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  have hp₀E : (1 : ℝ≥0∞) ≤ (p₀ : ℝ≥0∞) := by exact_mod_cast hp₀
  have hP0 : (0 : ℝ) < (P : ℝ) := lt_of_le_of_lt (by positivity) hPd
  have hγpos : 0 < morreyExponent d (P : ℝ) := by
    rw [← NNReal.coe_pos, coe_morreyExponent hPd hd0, sub_pos, div_lt_one hP0]
    exact hPd
  have hFint : ∀ i, dep i ≤ m → IntegrableOn (F i) Ω volume := fun i hi =>
    (hmem i hi).integrable hp₀E
  -- The representatives, chosen once. Indices the clause does not reach keep `F` itself.
  have hqual : ∀ i, ∃ w : EuclideanSpace ℝ (Fin d) → ℝ, dep i + 1 + s ≤ m →
      w =ᵐ[volume.restrict Ω] F i ∧ (∀ y ∈ closure Ω, ‖w y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
        HolderOnWith (C * M) (morreyExponent d (P : ℝ)) w (closure Ω) := by
    intro i
    by_cases hi : dep i + 1 + s ≤ m
    · obtain ⟨w, hwae, hwsup, hwhol⟩ := hC hdep hgrad hmem M hM i hi
      exact ⟨w, fun _ => ⟨hwae, hwsup, hwhol⟩⟩
    · exact ⟨F i, fun h => absurd h hi⟩
  choose v hv using hqual
  have hvae : ∀ i, dep i + 1 + s ≤ m → v i =ᵐ[volume.restrict Ω] F i := fun i hi => (hv i hi).1
  have hvsup : ∀ i, dep i + 1 + s ≤ m → ∀ y ∈ closure Ω, ‖v i y‖ ≤ ((C * M : ℝ≥0) : ℝ) :=
    fun i hi => (hv i hi).2.1
  have hvhol : ∀ i, dep i + 1 + s ≤ m →
      HolderOnWith (C * M) (morreyExponent d (P : ℝ)) (v i) (closure Ω) := fun i hi =>
    (hv i hi).2.2
  have hvc : ∀ i, dep i + 1 + s ≤ m → ContinuousOn (v i) Ω := fun i hi =>
    ((hvhol i hi).continuousOn hγpos).mono subset_closure
  have hvint : ∀ i, dep i + 1 + s ≤ m → IntegrableOn (v i) Ω volume := fun i hi =>
    (hFint i (by omega)).congr (hvae i hi).symm
  have hvgrad : ∀ i, dep i + 2 + s ≤ m →
      HasWeakGradOn Ω (v i) (fun k => v (nxt i k)) := fun i hi =>
    (hgrad i (by omega)).congr_ae (hvae i (by omega)).symm
      fun k => (hvae (nxt i k) (by have := hdep i k; omega)).symm
  -- The classical derivative of a representative is the representative of the derivative.
  have hfd : ∀ i, dep i + 2 + s ≤ m → ∀ y ∈ Ω,
      HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y := by
    intro i hi y hy
    exact hasFDerivAt_of_continuousOn_hasWeakGradOn hΩopen.measurableSet hΩopen
      (hvint i (by omega)) (fun k => hvint (nxt i k) (by have := hdep i k; omega))
      (hvc i (by omega)) (fun k => hvc (nxt i k) (by have := hdep i k; omega)) (hvgrad i hi) hy
  -- Every order the supply pays for, by induction.
  have hcn : ∀ (n : ℕ) (i : ι), dep i + n + 1 + s ≤ m →
      ContDiffOn ℝ (n : ℕ) (v i) Ω := by
    intro n
    induction n with
    | zero => intro i hi; simpa using hvc i (by omega)
    | succ n ih =>
      intro i hi
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring,
        contDiffOn_succ_iff_fderiv_of_isOpen hΩopen]
      refine ⟨fun y hy =>
        ((hfd i (by omega) y hy).differentiableAt).differentiableWithinAt, by simp, ?_⟩
      have hsum : ContDiffOn ℝ (n : ℕ) (fun y => gradCLM (fun k => v (nxt i k)) y) Ω := by
        change ContDiffOn ℝ (n : ℕ)
          (fun y => ∑ k, v (nxt i k) y •
            (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) Ω
        exact ContDiffOn.sum fun k _ =>
          (ih (nxt i k) (by have := hdep i k; omega)).smul contDiffOn_const
      exact hsum.congr fun y hy => (hfd i (by omega) y hy).fderiv
  exact ⟨v, hvae, hvsup, hvhol, hcn, hfd⟩

end EllipticPdes.Embedding
