/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.WitnessBlock
public import LeanPool.HighContrastHomogenization.Consistency.WitnessSigmaField
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger

/-!
# High-contrast homogenization: Annealed.Witness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The hypothesis set of the random-source theorems is satisfiable

`t.polynomial.entry` quantifies over laws that are stationary under integer
translations, have unit range of dependence, and satisfy the coarse ellipticity
condition `e.coarse.ellipticity`.  Nothing in those statements exhibits a law
that satisfies all three, so on their own they
leave open the possibility that the hypothesis set is empty and the conclusion
vacuous.  This file closes that possibility with an explicit law.

The witness is the Dirac law at the constant identity coefficient field, with
source scale identically zero, gauge `Ψ(t) = e^t`, growth witness `K = 2`,
reference block `(4d+1)` times the doubled identity, and discount exponent
`g = 0`.  Stationarity holds because the constant field is fixed by integer
translation; independence holds because under an atomic law every pair of
events is independent; the source tail is trivial because the upper tail events
of the zero source at positive levels are empty; and the coarse domination is
the scale-uniform bound of the constant field, which needs no discount factor.

The Dirac law also carries the measurability of the coarse response, which
`e.Theta.m` presupposes for `Θ_m`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The gauge -/

/-- The exponential is an admissible gauge: increasing on `ℝ_+` with values in
`[1, ∞)`. -/
theorem admissiblePsi_exp : IndependentSums.AdmissiblePsi Real.exp := by
  refine ⟨fun x _ y _ hxy => Real.exp_le_exp.2 hxy, fun t ht => ?_⟩
  have h := Real.add_one_le_exp t
  linarith only [h, ht]

/-- The exponential gauge has growth witness `2`: `t e^t ≤ e^{2t}` for
`t ≥ 1`. -/
theorem hasPsiGrowth_exp : IndependentSums.HasPsiGrowth Real.exp 2 := by
  intro t _
  have h1 : t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith only [h]
  have h2 : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [two_mul, Real.exp_add]
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le

/-! ## The witness law -/

/-- The witness law: the Dirac law at the constant identity coefficient field. -/
@[expose]
def witnessLaw (d : ℕ) : Measure (CoeffSpace d) :=
  Measure.dirac (constIdentity d)

instance instIsProbabilityMeasureWitnessLaw :
    IsProbabilityMeasure (witnessLaw d) := by
  rw [witnessLaw]
  infer_instance

/-- **The witness law is stationary**: the constant identity field is fixed by
every integer translation. -/
theorem isStationaryLaw_witnessLaw : HCPoly.Frozen.IsStationaryLaw (witnessLaw d) := by
  intro z
  rw [witnessLaw, Measure.map_dirac' (measurable_translateCoeff z), translateCoeff_constIdentity]

/-- **Every atomic law has unit range of dependence**: under a Dirac law the
indicator of an intersection is the product of the indicators, so any two
sigma-fields coarser than the global one are independent. -/
theorem isUnitRangeLaw_dirac (a : CoeffSpace d) :
    HCPoly.Frozen.IsUnitRangeLaw (Measure.dirac a) := by
  intro U V _ _ _
  rw [ProbabilityTheory.Indep_iff]
  intro t₁ t₂ ht₁ ht₂
  have h₁ := coeffSigma_le_global d U t₁ ht₁
  have h₂ := coeffSigma_le_global d V t₂ ht₂
  rw [Measure.dirac_apply' a (h₁.inter h₂), Measure.dirac_apply' a h₁,
    Measure.dirac_apply' a h₂]
  by_cases hA : a ∈ t₁ <;> by_cases hB : a ∈ t₂ <;> simp [hA, hB]

theorem isUnitRangeLaw_witnessLaw : HCPoly.Frozen.IsUnitRangeLaw (witnessLaw d) :=
  isUnitRangeLaw_dirac _

/-! ## The source scale -/

/-- At a positive level the upper tail event of the zero source is empty. -/
theorem upperTailEvent_zero {t : ℝ} (ht : 0 < t) :
    IndependentSums.upperTailEvent (fun _ : CoeffSpace d => (0 : ℝ)) t = ∅ := by
  ext a
  simp only [IndependentSums.upperTailEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_lt]
  exact ht.le

/-! ## The coarse ellipticity assumption -/

/-- At the exponent `g = 0` the discount factor `3^{g(m-k)}` is one. -/
theorem blockScale_discount_zero (E : BlockMat d) (m k : ℤ) :
    blockScale ((3 : ℝ) ^ ((0 : ℝ) * ((m : ℝ) - (k : ℝ)))) E = E := by
  rw [zero_mul, Real.rpow_zero]
  simp [blockScale]

/-- At a nonnegative exponent the discount factor `3^{g(m-k)}` is at least one on
the scales `k ≤ m` of `e.coarse.ellipticity`. -/
theorem one_le_discount {g : ℝ} (hg : 0 ≤ g) {m k : ℤ} (hkm : k ≤ m) :
    (1 : ℝ) ≤ (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) := by
  have hkm' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hexp : 0 ≤ g * ((m : ℝ) - (k : ℝ)) :=
    mul_nonneg hg (by linarith only [hkm'])
  calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 3).symm
    _ ≤ (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- **The witness law satisfies `e.coarse.ellipticity`** at every admissible
discount exponent, with the doubled-identity reference block, the exponential
gauge, growth witness `2`, and the zero source scale. -/
theorem coarseEllipticityDagger_witnessLaw_of_mem_Ico {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    HCPoly.Frozen.CoarseEllipticityDagger (witnessLaw d) g (witnessRefBlock d)
      Real.exp 2 (fun _ => 0) where
  g_mem := hg
  refBlock_isSymm := isSymmetricBlockMat_witnessRefBlock
  refBlock_posDef := blockPosDef_witnessRefBlock
  gauge_admissible := admissiblePsi_exp
  one_lt_growthWitness := by norm_num
  gauge_growth := hasPsiGrowth_exp
  source_measurable := measurable_const
  source_nonneg := fun _ => le_rfl
  source_tail := by
    intro t ht
    rw [upperTailEvent_zero ht, measureReal_empty]
    positivity
  coarse_bound := by
    have hpoint : ∀ m : ℤ, (0 : ℝ) ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) (constIdentity d))
          (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) (witnessRefBlock d)) := by
      intro m _ k hkm w _
      exact blockMatLoewnerLE_coarseBlock_constIdentity_blockScale
        (one_le_discount hg.1 hkm) k w
    rw [witnessLaw, _root_.Filter.Eventually, MeasureTheory.ae_dirac_eq]
    exact hpoint

/-- The witness law at the exponent `g = 0`, at which the discount factor is
one. -/
theorem coarseEllipticityDagger_witnessLaw :
    HCPoly.Frozen.CoarseEllipticityDagger (witnessLaw d) 0 (witnessRefBlock d)
      Real.exp 2 (fun _ => 0) :=
  coarseEllipticityDagger_witnessLaw_of_mem_Ico (Set.mem_Ico.2 ⟨le_rfl, one_pos⟩)

/-! ## The coarse response is measurable under an atomic law -/

/-- Under an atomic law every entry of the coarse response is almost surely
strongly measurable: the well-formedness that `e.Theta.m`
presupposes. -/
theorem hasMeasurableCoarseBlock_dirac (a : CoeffSpace d) (U : Set (Vec d)) :
    HasMeasurableCoarseBlock (Measure.dirac a) U :=
  fun _ _ => aestronglyMeasurable_const.congr (ae_eq_dirac _).symm

theorem hasMeasurableCoarseBlock_witnessLaw (U : Set (Vec d)) :
    HasMeasurableCoarseBlock (witnessLaw d) U := by
  rw [witnessLaw]
  exact hasMeasurableCoarseBlock_dirac _ U

/-! ## The hypothesis set is satisfiable -/

/-- **The law-side hypothesis set of `t.polynomial.entry` is
satisfiable**, in every dimension and with no further restriction: the Dirac law
at the constant identity field, with the doubled-identity reference block, the
exponential gauge, growth witness `2`, and the zero source scale, satisfies all
four hypotheses at the discount exponent `g = 0`. -/
theorem exists_law_satisfying_hypotheses (d : ℕ) :
    ∃ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P ∧
      HCPoly.Frozen.IsStationaryLaw P ∧
      HCPoly.Frozen.IsUnitRangeLaw P ∧
      HCPoly.Frozen.CoarseEllipticityDagger P 0 E Ψ K S :=
  ⟨witnessLaw d, witnessRefBlock d, Real.exp, 2, fun _ => 0,
    instIsProbabilityMeasureWitnessLaw, isStationaryLaw_witnessLaw,
    isUnitRangeLaw_witnessLaw, coarseEllipticityDagger_witnessLaw⟩

/-- **The hypothesis set is satisfiable at every admissible discount exponent**,
so no branch of the quantifier over `g` in
`t.polynomial.entry` is vacuous. -/
theorem exists_law_satisfying_hypotheses_of_mem_Ico (d : ℕ) {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P ∧
      HCPoly.Frozen.IsStationaryLaw P ∧
      HCPoly.Frozen.IsUnitRangeLaw P ∧
      HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S :=
  ⟨witnessLaw d, witnessRefBlock d, Real.exp, 2, fun _ => 0,
    instIsProbabilityMeasureWitnessLaw, isStationaryLaw_witnessLaw,
    isUnitRangeLaw_witnessLaw, coarseEllipticityDagger_witnessLaw_of_mem_Ico hg⟩

end

end HighContrast
end HCPolySupport
