/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledLocalizationAssembly

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.UniformHardyConstantHoist

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# S-2's second half: the Hardy constant absorbed above the domain binders

`exists_ruledHardySelection` reads

```lean
theorem exists_ruledHardySelection
    (d : ℕ) [NeZero d] {rho Rad s : ℝ}
    {U : Set (Vec d)} (hSandwich : HasBallSandwich U rho Rad)
    (hs : 0 < s) (hsHalf : s < 1 / 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (V : Set (Vec d)), … ≤ C * hsNormSq V s G
```

so its `∃ C` **already sits before `V` and `system`** — `C` is uniform over
domains at fixed `(d, ρ, Rad, s)`.  The obstruction to putting it in
`C₀ s₀ ρ Rad` is *not* the domain quantifier; it is that the theorem must be
*applied*, and applying it needs a witness domain `U` with a sandwich, which the
frozen clause only produces alongside the very `U` the constant must precede.

The repair is the Cdual module's F1 move: classical choice over the parameter
triple.  `exists_uniformParameterConstant` below is that move in the abstract,
and `exists_uniformHardyConstant` is its application — a single
`C : ℝ → ℝ → ℝ → ℝ≥0∞` fixed once and for all, whose value at `(s, ρ, Rad)`
serves every domain with that sandwich.

**What this does not do.**  It removes the quantifier-order defect only.  The
constant still depends on `(d, ρ, Rad, s)`, which is exactly `C₀ s₀ ρ Rad`'s
permitted dependence, so no further absorptions is needed — but the *composition* that
feeds it into the `hHardy` premise binder is one of the composed rows waiting
on the root interface.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- **The absorptions, abstractly.**  A parameterised family of existentials becomes a
single parameterised choice function.  This is the Cdual module's F1 move. -/
theorem exists_uniformParameterConstant {β : Type*} [Nonempty β]
    (P : ℝ → ℝ → ℝ → β → Prop) :
    ∃ f : ℝ → ℝ → ℝ → β,
      ∀ s rho Rad : ℝ, (∃ b, P s rho Rad b) → P s rho Rad (f s rho Rad) := by
  classical
  refine ⟨fun s rho Rad =>
    if h : ∃ b, P s rho Rad b then h.choose else Classical.arbitrary β, ?_⟩
  intro s rho Rad h
  simp only [dite_eq_left h]
  exact h.choose_spec

/-- **S-2b.**  One Hardy constant, fixed before every domain binder, serving
every witness with the given sandwich radii and order. -/
theorem exists_uniformHardyConstant (d : ℕ) [NeZero d] :
    ∃ C : ℝ → ℝ → ℝ → ℝ≥0∞,
      ∀ (s rho Rad : ℝ), 0 < s → s < 1 / 2 →
        ∀ (U : Set (Vec d)), HasBallSandwich U rho Rad →
          C s rho Rad ≠ ⊤ ∧
            ∀ (V : Set (Vec d)), IsOpenBoundedConvexDomain V →
              HasBallSandwich V rho Rad →
              ∀ (system : EnlargedMarginRuledTriadicWhitneySystem V rho Rad)
                (G : Vec d → Vec d),
                Integrable G (volume.restrict V) →
                  normalizedWhitneyRowEnergy system
                      (ruledPositiveWhitneyCellEnergy
                        system s G) ≤
                    C s rho Rad * hsNormSq V s G := by
  obtain ⟨f, hf⟩ :=
    exists_uniformParameterConstant
      (β := ℝ≥0∞)
      (fun s rho Rad C =>
        C ≠ ⊤ ∧
          ∀ (V : Set (Vec d)), IsOpenBoundedConvexDomain V →
            HasBallSandwich V rho Rad →
            ∀ (system : EnlargedMarginRuledTriadicWhitneySystem V rho Rad)
              (G : Vec d → Vec d),
              Integrable G (volume.restrict V) →
                normalizedWhitneyRowEnergy system
                    (ruledPositiveWhitneyCellEnergy
                      system s G) ≤
                  C * hsNormSq V s G)
  refine ⟨f, ?_⟩
  intro s rho Rad hs hsHalf U hSandwich
  exact hf s rho Rad
    (exists_ruledHardySelection d
      hSandwich hs hsHalf)

end

end RowSupply
end HighContrast
end HCPolySupport
