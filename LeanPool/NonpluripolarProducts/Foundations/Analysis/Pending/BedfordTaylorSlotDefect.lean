/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotAdd

/-!
# The slot defect of a test function

A test function `φ` is not by itself an admissible Bedford–Taylor slot: the
recursion needs a positive semidefinite Hessian, which `φ` does not have. The
standard device is to regularize, putting `φ + p` in the slot for a smooth
positive semidefinite `p` (in practice `p = C‖z‖²` with `C` large), and to read
`ddᶜφ ∧ S` off the *difference* of the two limits, `μ(φ + p) - μ(p)`.

For that difference to deserve the name `ddᶜφ ∧ S` it must not depend on the
regularizer, and it must be additive in `φ`. Both follow formally from slot
additivity `IsBTLimit.add_slot` by comparing through a common third tuple:
`φ + p + q` computed in two orders. Statements are phrased additively, as
`μ₁ + ν₂ = ν₁ + μ₂`, because measures admit no subtraction.

This is the linearity the compact total-mass argument needs: on a compact
manifold a partition of unity `Σ χ_b = 1` makes the corresponding defects
telescope, and the defect of a constant is zero.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- The tuple obtained by adding two admissible slot functions is itself a
Bedford–Taylor tuple: admissible families add. -/
theorem exists_isBTLimit_update_add {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {a b : ComplexModel n → ℝ}
    {μa μb : Measure (ComplexModel n)}
    (hμa : IsBTLimit Ω (Function.update v i₀ a) μa)
    (hμb : IsBTLimit Ω (Function.update v i₀ b) μb) :
    ∃ ρ, IsBTLimit Ω (Function.update v i₀ fun z ↦ a z + b z) ρ := by
  classical
  refine exists_isBTLimit fun U hU ↦ ?_
  obtain ⟨F, hF, -⟩ := hμa.2.2 U hU
  obtain ⟨G, hG, -⟩ := hμb.2.2 U hU
  have hb : IsDecApprox U b (G i₀) := by simpa using hG.1 i₀
  exact ⟨_, hF.update_add i₀ hb⟩

/-- **The slot defect is independent of the regularizer.** If `p` and `q` are
two slot functions for which both `φ + p` and `φ + q` have Bedford–Taylor
limits, then
`μ(φ + p) - μ(p) = μ(φ + q) - μ(q)`, stated without subtraction. -/
theorem IsBTLimit.slotDefect_regularizer_congr {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {φ p q : ComplexModel n → ℝ}
    {μ₁ μ₂ ν₁ ν₂ : Measure (ComplexModel n)}
    (hμ₁ : IsBTLimit Ω (Function.update v i₀ fun z ↦ φ z + p z) μ₁)
    (hμ₂ : IsBTLimit Ω (Function.update v i₀ p) μ₂)
    (hν₁ : IsBTLimit Ω (Function.update v i₀ fun z ↦ φ z + q z) ν₁)
    (hν₂ : IsBTLimit Ω (Function.update v i₀ q) ν₂) :
    μ₁ + ν₂ = ν₁ + μ₂ := by
  obtain ⟨ρ, hρ⟩ := exists_isBTLimit_update_add i₀ hμ₁ hν₂
  have h1 : ρ = μ₁ + ν₂ := IsBTLimit.add_slot i₀ hρ hμ₁ hν₂
  have hfun : (fun z ↦ (φ z + q z) + p z) = fun z ↦ (φ z + p z) + q z := by
    funext z; ring
  have hρ' : IsBTLimit Ω (Function.update v i₀ fun z ↦ (φ z + q z) + p z) ρ := by
    rw [hfun]; exact hρ
  have h2 : ρ = ν₁ + μ₂ := IsBTLimit.add_slot i₀ hρ' hν₁ hμ₂
  rw [← h1, h2]

/-- **The slot defect is additive in the test function.** Writing
`D(φ) = μ(φ + p) - μ(p)` for a common regularizer `p`, the identity
`D(φ + ψ) = D(φ) + D(ψ)` reads, without subtraction, as follows. The common
refinement is the tuple with `φ + ψ + p + p` in the slot, read in two ways. -/
theorem IsBTLimit.slotDefect_add {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {φ ψ p : ComplexModel n → ℝ}
    {μφψ μφ μψ μp : Measure (ComplexModel n)}
    (hμφψ : IsBTLimit Ω (Function.update v i₀ fun z ↦ (φ z + ψ z) + p z) μφψ)
    (hμφ : IsBTLimit Ω (Function.update v i₀ fun z ↦ φ z + p z) μφ)
    (hμψ : IsBTLimit Ω (Function.update v i₀ fun z ↦ ψ z + p z) μψ)
    (hμp : IsBTLimit Ω (Function.update v i₀ p) μp) :
    μφψ + μp = μφ + μψ := by
  obtain ⟨ρ, hρ⟩ := exists_isBTLimit_update_add i₀ hμφψ hμp
  have h1 : ρ = μφψ + μp := IsBTLimit.add_slot i₀ hρ hμφψ hμp
  have hfun : (fun z ↦ (φ z + p z) + (ψ z + p z))
      = fun z ↦ ((φ z + ψ z) + p z) + p z := by
    funext z; ring
  have hρ' : IsBTLimit Ω (Function.update v i₀ fun z ↦ (φ z + p z) + (ψ z + p z)) ρ := by
    rw [hfun]; exact hρ
  have h2 : ρ = μφ + μψ := IsBTLimit.add_slot i₀ hρ' hμφ hμψ
  rw [← h1, h2]

/-- Adding a real constant to one slot does not change the limit measure:
a constant is smooth pluriharmonic, so `ddᶜ` of it vanishes. -/
theorem IsBTLimit.update_const_add {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {p : ComplexModel n → ℝ}
    {μp : Measure (ComplexModel n)} (hμp : IsBTLimit Ω (Function.update v i₀ p) μp)
    (c : ℝ) : IsBTLimit Ω (Function.update v i₀ fun z ↦ c + p z) μp := by
  classical
  have hconst : ∀ d : ℝ, IsSmoothPluriharmonicOn Ω (fun _ : ComplexModel n ↦ d) := by
    intro d
    refine ⟨contDiffOn_const, fun z _ ↦ ?_⟩
    simp
  have hh : ∀ i, IsSmoothPluriharmonicOn Ω (Function.update (fun _ ↦ fun _ : ComplexModel n ↦ (0 :
    ℝ))
      i₀ (fun _ : ComplexModel n ↦ c) i) := by
    intro i
    by_cases h : i = i₀
    · subst h; simp [hconst c]
    · simpa [Function.update_of_ne h] using hconst 0
  have h := hμp.add_pluriharmonic hh
  have hfun : (fun i z ↦ Function.update v i₀ p i z +
        Function.update (fun _ ↦ fun _ : ComplexModel n ↦ (0 : ℝ)) i₀
          (fun _ : ComplexModel n ↦ c) i z)
      = Function.update v i₀ fun z ↦ c + p z := by
    funext i z
    by_cases hi : i = i₀
    · subst hi; simp [add_comm]
    · simp [Function.update_of_ne hi]
  rwa [hfun] at h

/-- **The slot defect of a constant vanishes.** This is `ddᶜc = 0`, the step
that makes a partition of unity telescope on a compact manifold. -/
theorem IsBTLimit.slotDefect_const {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {p : ComplexModel n → ℝ}
    {μc μp : Measure (ComplexModel n)} (c : ℝ)
    (hμc : IsBTLimit Ω (Function.update v i₀ fun z ↦ c + p z) μc)
    (hμp : IsBTLimit Ω (Function.update v i₀ p) μp) : μc = μp :=
  hμc.unique (hμp.update_const_add i₀ c)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
