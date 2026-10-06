/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.IdentityCells
public import LeanPool.HighContrastHomogenization.Provider.Transport.CellDomination

/-!
# High-contrast homogenization: Provider.Entry.StandardCellMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Euclidean cell bound at every generation and every center

The boundary layers of the comparison between adapted and Euclidean cubes are
unions of standard aligned cubes at generations running down to `-∞`, and they
sit wherever the target cell sits,
not at the origin.  The printed proof handles them with the ellipticity of
`e.coarse.ellipticity` and integer stationarity.  Both are needed together,
in the following form.

`e.coarse.ellipticity` discounts a cube by `3^{g(m-k)}` only when the cube's
center lies in the macroscopic cube `□_m` that the source has burned, so read
literally on a cube deep inside a large target it costs a factor of the target's
own generation.  Integer stationarity removes that cost: a standard aligned cube
of any generation is the *integer* translate of one whose center lies in the unit
cube — at a nonnegative generation the center is integral, at a negative one the
index reduces modulo `3^{-k}` — and a cube centered in the unit cube burns at the
macroscopic generation `max{1, k+l}`, where `3^l` brackets `3^{-k}S`.

The resulting mean bound `E[𝐀(z+□_k)] ≤ (1 + 9K_{Ψ_S}^23^{-k})^g𝐄` holds at every
generation `k ∈ ℤ` and every aligned center, which is exactly what the
geometric-series calculation of the comparison consumes.  Its only stochastic
input is the source mean `E[S] ≤ 2K_{Ψ_S}^2`, moved inside the concave power by
Jensen's inequality — the step the printed proof performs with Hölder.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Jensen's inequality at an affine argument -/

/-- **Jensen's inequality at an affine function of the source scale.**  The
concavity of `x ↦ x^g` on the nonnegative reals moves the mean of the source
inside the power; the printed proof performs this step with Hölder. -/
theorem integral_rpow_affine_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {A B : ℝ} (hA : 1 ≤ A)
    (hB : 0 ≤ B) :
    ∫ a, (A + B * S a) ^ g ∂P ≤ (A + B * ∫ a, S a ∂P) ^ g := by
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g ≤ 1 := le_of_lt hdag.g_mem.2
  have hS0 : ∀ a, 0 ≤ S a := hdag.source_nonneg
  have hone : ∀ a, (1 : ℝ) ≤ A + B * S a := fun a => by nlinarith only [hA, hB, hS0 a]
  have hfi : Integrable (fun a => A + B * S a) P :=
    (integrable_const A).add ((integrable_source hdag).const_mul B)
  have hmeas : AEStronglyMeasurable (fun a => (A + B * S a) ^ g) P :=
    ((measurable_const.add
      (hdag.source_measurable.const_mul B)).pow_const g).aestronglyMeasurable
  have hgi : Integrable (fun a => (A + B * S a) ^ g) P := by
    refine hfi.mono' hmeas (Filter.Eventually.of_forall fun a => ?_)
    have hpow : (A + B * S a) ^ g ≤ (A + B * S a) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (hone a) hg1
    rw [Real.rpow_one] at hpow
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith only [hone a]) g)]
    exact hpow
  have hjensen := (Real.concaveOn_rpow hg0 hg1).le_map_integral
    (f := fun a => A + B * S a)
    (fun x _ => (Real.continuousAt_rpow_const x g (Or.inr hg0)).continuousWithinAt)
    isClosed_Ici
    (Filter.Eventually.of_forall fun a => by
      have := hone a
      simp only [Set.mem_Ici]
      linarith only [this])
    hfi hgi
  have hsum : ∫ a, (A + B * S a) ∂P = A + B * ∫ a, S a ∂P := by
    rw [integral_add (integrable_const A) ((integrable_source hdag).const_mul B),
      integral_const, integral_const_mul, probReal_univ, smul_eq_mul, one_mul]
  rw [hsum] at hjensen
  exact hjensen

/-! ## The pathwise bound at a cell centered in the unit cube -/

/-- **The pathwise Euclidean cell bound.**  The random-source ellipticity of
`e.coarse.ellipticity` read at the macroscopic generation `max{1, k+l}`,
where `3^l` brackets `3^{-k}S`: a standard aligned cube whose center lies in the
unit cube is inside every macroscopic cube of generation at least one, so no
factor of the target's generation is produced. -/
theorem ae_coarseBlock_standardCell_le {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (k : ℤ) {v : Fin d → ℤ}
    (hv : ∀ i, |standardCellCenter k v i| < 1) :
    ∀ᵐ a ∂P, BlockMatLoewnerLE (coarseBlock (standardCell d k v) a)
      (blockScale ((3 * (3 : ℝ) ^ (-k) + 1 + 3 * ((3 : ℝ) ^ (-k) * S a)) ^ g) E) := by
  filter_upwards [hdag.coarse_bound] with a ha
  have hu0 : 0 ≤ (3 : ℝ) ^ (-k) * S a := by
    have hS := hdag.source_nonneg a
    positivity
  obtain ⟨l, hl1, hl2⟩ := exists_pow_three_bracket hu0
  set m : ℤ := max 1 (k + (l : ℤ)) with hmdef
  have hkm : k ≤ m := le_max_of_le_right (by omega)
  have hm1 : (1 : ℤ) ≤ m := le_max_left _ _
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hSle : S a ≤ (3 : ℝ) ^ m := by
    have hmul := mul_le_mul_of_nonneg_left hl1 h3k.le
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel,
      zpow_zero, one_mul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)] at hmul
    exact hmul.trans (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  have h3m : (3 : ℝ) ≤ (3 : ℝ) ^ m := by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hm1
    rwa [zpow_one] at this
  have hcenter : standardCellCenter k v ∈ centeredCube d m := by
    rw [Recurrence.mem_centeredCube_iff]
    intro i
    have hvi := hv i
    have h1 : |standardCellCenter k v i| < 1 := hvi
    rw [abs_lt] at h1
    constructor <;> linarith only [h1.1, h1.2, h3m]
  have hb := ha m hSle k hkm v hcenter
  refine Persistence.blockMatLoewnerLE_blockScale_mono (isSymmetricBlockMat_coarseBlock _ a)
    hdag.refBlock_isSymm hdag.refBlock_posDef ?_ hb
  have hexp : (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) = ((3 : ℝ) ^ (m - k)) ^ g := by
    rw [← Real.rpow_intCast (3 : ℝ) (m - k), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast
    ring_nf
  rw [hexp]
  refine Real.rpow_le_rpow (by positivity) ?_ hdag.g_mem.1
  have hsplit : (3 : ℝ) ^ (m - k) ≤ (3 : ℝ) ^ (1 - k) + (3 : ℝ) ^ ((l : ℕ) : ℤ) := by
    rcases max_cases (1 : ℤ) (k + (l : ℤ)) with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hmdef, hm]
      have : (0 : ℝ) < (3 : ℝ) ^ ((l : ℕ) : ℤ) := by positivity
      linarith only [this]
    · rw [hmdef, hm, show k + (l : ℤ) - k = ((l : ℕ) : ℤ) by ring]
      have : (0 : ℝ) < (3 : ℝ) ^ (1 - k) := by positivity
      linarith only [this]
  have hone : (3 : ℝ) ^ (1 - k) = 3 * (3 : ℝ) ^ (-k) := by
    rw [show (1 : ℤ) - k = 1 + -k by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  rw [hone] at hsplit
  linarith only [hsplit, hl2]

/-! ## Integrability and the mean bound -/

/-- The coarse response over a standard aligned cube is integrable over the law
at every generation and every aligned center. -/
theorem hasIntegrableCoarseBlock_standardCell {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (k : ℤ) {v : Fin d → ℤ} (hv : ∀ i, |standardCellCenter k v i| < 1) :
    HasIntegrableCoarseBlock P (standardCell d k v) := by
  set A : ℝ := 3 * (3 : ℝ) ^ (-k) + 1 with hA
  set B : ℝ := 3 * (3 : ℝ) ^ (-k) with hB
  have hA1 : (1 : ℝ) ≤ A := by
    have : (0 : ℝ) < (3 : ℝ) ^ (-k) := by positivity
    rw [hA]; linarith only [this]
  have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
  have hS0 : ∀ a, 0 ≤ S a := hdag.source_nonneg
  have hone : ∀ a, (1 : ℝ) ≤ A + B * S a := fun a => by nlinarith only [hA1, hB0, hS0 a]
  have hCE : (0 : ℝ) ≤ blockEntrySum E := blockEntrySum_nonneg E
  have hmeas : HasMeasurableCoarseBlock P (standardCell d k v) := by
    have h := Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P Matrix.PosDef.one k v
    rwa [adaptedCellAt_one] at h
  have hdom : Integrable (fun a => 2 * blockEntrySum E * (A + B * S a)) P :=
    (((integrable_const A).add ((integrable_source hdag).const_mul B)).const_mul
      (2 * blockEntrySum E))
  intro α β
  refine hdom.mono' (hmeas α β) ?_
  filter_upwards [ae_coarseBlock_standardCell_le hdag k hv] with a hle
  have hrw : (3 * (3 : ℝ) ^ (-k) + 1 + 3 * ((3 : ℝ) ^ (-k) * S a)) = A + B * S a := by
    rw [hA, hB]; ring
  rw [hrw] at hle
  have hentry := Transport.abs_blockMatEntry_coarseBlock_le_of_blockMatLoewnerLE hle α β
  have hpow0 : (0 : ℝ) ≤ (A + B * S a) ^ g := Real.rpow_nonneg (by linarith only [hone a]) g
  have hpow : (A + B * S a) ^ g ≤ A + B * S a := by
    have h := Real.rpow_le_rpow_of_exponent_le (hone a) (le_of_lt hdag.g_mem.2)
    rwa [Real.rpow_one] at h
  rw [Real.norm_eq_abs]
  refine hentry.trans ?_
  rw [abs_of_nonneg hpow0]
  nlinarith only [hpow, hCE, hpow0]

/-- **The Euclidean cell bound at every generation and every center.**  The mean
of the coarse response over a standard aligned cube of generation `k` lies below
`(1 + 9K_{Ψ_S}^23^{-k})𝐄` to the power `g`, uniformly in the aligned center: the
cube is an integer translate of one centered in the unit cube, and there the
random-source ellipticity applies with no macroscopic loss. -/
theorem annealedBlock_standardCell_le {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (k : ℤ) (w : Fin d → ℤ) :
    BlockMatLoewnerLE (annealedBlock P (standardCell d k w))
      (blockScale ((1 + 9 * K ^ 2 * (3 : ℝ) ^ (-k)) ^ g) E) := by
  obtain ⟨u, v, hcell, hv⟩ := exists_reduced_standardCell k w
  set A : ℝ := 3 * (3 : ℝ) ^ (-k) + 1 with hA
  set B : ℝ := 3 * (3 : ℝ) ^ (-k) with hB
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-k) := by positivity
  have hA1 : (1 : ℝ) ≤ A := by rw [hA]; linarith only [h3]
  have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
  have hS0 : ∀ a, 0 ≤ S a := hdag.source_nonneg
  have hone : ∀ a, (1 : ℝ) ≤ A + B * S a := fun a => by nlinarith only [hA1, hB0, hS0 a]
  have hint : HasIntegrableCoarseBlock P (standardCell d k v) :=
    hasIntegrableCoarseBlock_standardCell hdag k hv
  have hmeas : HasMeasurableCoarseBlock P (standardCell d k v) :=
    fun α β => (hint α β).aestronglyMeasurable
  have htrans : annealedBlock P (standardCell d k w) = annealedBlock P (standardCell d k v) := by
    rw [hcell]
    exact Recurrence.annealedBlock_translateSet hstat hmeas u
  have hgi : Integrable (fun a => (A + B * S a) ^ g) P := by
    have hfi : Integrable (fun a => A + B * S a) P :=
      (integrable_const A).add ((integrable_source hdag).const_mul B)
    refine hfi.mono' ((measurable_const.add
      (hdag.source_measurable.const_mul B)).pow_const g).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    have hpow : (A + B * S a) ^ g ≤ (A + B * S a) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (hone a) (le_of_lt hdag.g_mem.2)
    rw [Real.rpow_one] at hpow
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith only [hone a]) g)]
    exact hpow
  have haver : BlockMatLoewnerLE (annealedBlock P (standardCell d k v))
      (blockScale (∫ a, (A + B * S a) ^ g ∂P) E) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_annealedBlock hint, toFullBlockMat_blockScale,
      show (∫ a, (A + B * S a) ^ g ∂P) • toFullBlockMat E =
          ∫ a, ((A + B * S a) ^ g) • toFullBlockMat E ∂P by rw [integral_smul_const]]
    have hgiC : Integrable (fun a => ((A + B * S a) ^ g) • toFullBlockMat E) P := by
      have hgiC' : Integrable (fun a : CoeffSpace d => fun p q : BlockCoord d =>
          (A + B * S a) ^ g * toFullBlockMat E p q) P := by
        rw [integrable_pi_iff]
        intro p
        rw [integrable_pi_iff]
        intro q
        exact hgi.mul_const _
      exact hgiC'
    refine integral_mono' (integrable_toFullBlockMat hint) hgiC ?_
    filter_upwards [ae_coarseBlock_standardCell_le hdag k hv] with a ha
    have hrw : (3 * (3 : ℝ) ^ (-k) + 1 + 3 * ((3 : ℝ) ^ (-k) * S a)) = A + B * S a := by
      rw [hA, hB]; ring
    rw [hrw] at ha
    have h := le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock _ a)
      (isSymmetricBlockMat_blockScale _ hdag.refBlock_isSymm) ha
    rwa [toFullBlockMat_blockScale] at h
  rw [htrans]
  refine Persistence.blockMatLoewnerLE_blockScale_mono
    (isSymmetricBlockMat_annealedBlock P _) hdag.refBlock_isSymm
    hdag.refBlock_posDef ?_ haver
  refine le_trans (integral_rpow_affine_le hdag hA1 hB0) ?_
  have hmean0 : (0 : ℝ) ≤ ∫ a, S a ∂P := integral_nonneg fun a => hS0 a
  refine Real.rpow_le_rpow (by nlinarith only [hA1, hB0, hmean0]) ?_ hdag.g_mem.1
  have hmean := integral_source_le hdag
  have hK : (1 : ℝ) < K := hdag.one_lt_growthWitness
  have hstep : B * ∫ a, S a ∂P ≤ B * (2 * K ^ 2) := mul_le_mul_of_nonneg_left hmean hB0
  have hval : B * (2 * K ^ 2) = 6 * K ^ 2 * (3 : ℝ) ^ (-k) := by rw [hB]; ring
  rw [hval] at hstep
  have hK2 : (1 : ℝ) ≤ K ^ 2 := by nlinarith only [hK]
  have hthree : 3 * (3 : ℝ) ^ (-k) ≤ 3 * K ^ 2 * (3 : ℝ) ^ (-k) := by
    nlinarith only [hK2, h3]
  rw [hA, hB]
  linarith only [hstep, hthree, hB]

/-- The coarse response over a standard aligned cube is integrable over the law
at every generation and every aligned center: the finiteness at the reduced
center transports along the integer translation. -/
theorem hasIntegrableCoarseBlock_standardCell_of_stationary {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (k : ℤ) (w : Fin d → ℤ) :
    HasIntegrableCoarseBlock P (standardCell d k w) := by
  obtain ⟨u, v, hcell, hv⟩ := exists_reduced_standardCell k w
  rw [hcell]
  exact Recurrence.hasIntegrableCoarseBlock_translateSet hstat
    (hasIntegrableCoarseBlock_standardCell hdag k hv) u

end

end Entry
end HighContrast
end HCPolySupport
