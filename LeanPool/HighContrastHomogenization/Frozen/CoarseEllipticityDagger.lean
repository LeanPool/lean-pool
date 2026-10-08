/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup

/-!
# High-contrast homogenization: Frozen.CoarseEllipticityDagger

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse ellipticity assumption `e.coarse.ellipticity`

The random-source coarse ellipticity assumption `e.coarse.ellipticity` at unit macroscopic
normalization: with exponent `g`, deterministic positive reference block `E`,
increasing gauge `Ψ` on `ℝ_+` with values in `[1, ∞)`, growth witness `K > 1`,
and nonnegative source scale `S`, the coarse block response of every standard
aligned cube whose center lies in `□_m` is dominated by the reference block with
the discount factor `3^{g(m-k)}`, almost surely on the event that the source has
burned at scale `m`.

The coefficient fields are uniformly elliptic almost everywhere, with ellipticity
constants belonging to the field and entering no estimate;
`e.qualitative.ellipticity` follows from this, and every quantitative object
of the development — `Π`, the gauge and its growth witness, `Θ_m`, and every
dimensional constant — is independent of them.
-/

/-- **The coarse ellipticity assumption `e.coarse.ellipticity`**, with exponent `g`,
deterministic positive reference block `E`, increasing gauge `Ψ` on `ℝ_+` with
values in `[1, ∞)`, growth witness `K > 1`, and nonnegative source scale `S`. -/
structure HCPoly.Frozen.CoarseEllipticityDagger {d : ℕ}
    (P : MeasureTheory.Measure (HCPolySupport.HighContrast.CoeffSpace d)) (g : ℝ)
    (E : HCPolySupport.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : HCPolySupport.HighContrast.CoeffSpace d → ℝ) : Prop where
  g_mem : g ∈ Set.Ico (0 : ℝ) 1
  refBlock_isSymm : HCPolySupport.IsSymmetricBlockMat E
  refBlock_posDef : HCPolySupport.Book.Ch02.BlockPosDef E
  gauge_admissible : HCPolySupport.IndependentSums.AdmissiblePsi Ψ
  one_lt_growthWitness : 1 < K
  gauge_growth : HCPolySupport.IndependentSums.HasPsiGrowth Ψ K
  source_measurable : Measurable S
  source_nonneg : ∀ a, 0 ≤ S a
  source_tail : ∀ t : ℝ, 0 < t →
    P.real (HCPolySupport.IndependentSums.upperTailEvent S t) ≤ (Ψ t)⁻¹
  coarse_bound : ∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m →
    ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      HCPolySupport.HighContrast.standardCellCenter k w ∈
        HCPolySupport.HighContrast.centeredCube d m →
      HCPolySupport.BlockMatLoewnerLE
        (HCPolySupport.HighContrast.coarseBlock
          (HCPolySupport.HighContrast.standardCell d k w) a)
        (HCPolySupport.HighContrast.blockScale
          ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E)

/-! ## The assumption under the project namespace

`HCPolySupport.HighContrast.CoarseEllipticityDagger` is `HCPoly.Frozen.CoarseEllipticityDagger`
itself, not a second
reading of it: the proofs of the paper's propositions are written in the project
namespace and use the frozen declaration through this name. -/
namespace HCPolySupport.HighContrast

export HCPoly.Frozen (CoarseEllipticityDagger)

end HCPolySupport.HighContrast
