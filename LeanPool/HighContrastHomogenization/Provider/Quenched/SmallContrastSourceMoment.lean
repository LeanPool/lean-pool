/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.StrongTailMoment
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSourceMoment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Source-scale moments from the Dagger tail

The normalized source scale `max 1 (S·3^{-s_K})`, with `3^{s_K}` above the
growth witness, has the strong `Ψ`-tail `t ↦ (t·Ψ(t))⁻¹`, hence bounded
moments of every integer order with the explicit `growthBar` constants; on
the tail event `{3^Δ < max 1 (S·3^{-s_K})}` any fixed moment of the
`Δ`-rescaled variable decays like `3^{-MΔ}`.  This is the printed
crude-moments display `𝔼[𝒮^{2γ}(𝒮 3^{-n})^{2(1-γ)}] ≤ C(K,Ψ) 3^{-2n}` in
the form the weak-norm caps consume — no window multiplier, no coupled
window, no portable history.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The growth hypothesis transfers to the growth bar. -/
private theorem hasPsiGrowth_growthBar {Ψ : ℝ → ℝ} {K : ℝ}
    (hadm : IndependentSums.AdmissiblePsi Ψ) (hK : 1 < K)
    (hgrow : IndependentSums.HasPsiGrowth Ψ K) :
    IndependentSums.HasPsiGrowth Ψ (growthBar K) := by
  intro t ht
  refine (hgrow ht).trans (hadm.1 ?_ ?_ ?_)
  · exact Set.mem_Ici.mpr (by nlinarith only [hK, ht])
  · exact Set.mem_Ici.mpr (by
      have h2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
      nlinarith only [h2, ht])
  · have hKB : K ≤ growthBar K := le_max_right _ _
    nlinarith only [hKB, ht]

/-- The normalized source scale. -/
@[expose]
def normalizedSourceScale (S : CoeffSpace d → ℝ) (sK : ℤ) :
    CoeffSpace d → ℝ :=
  fun a => max 1 (S a * (3 : ℝ) ^ (-sK))

theorem one_le_normalizedSourceScale (S : CoeffSpace d → ℝ) (sK : ℤ)
    (a : CoeffSpace d) : 1 ≤ normalizedSourceScale S sK a :=
  le_max_left _ _

/-- **The strong tail.**  Above the growth witness, the normalized source
scale has the strong `Ψ`-tail. -/
theorem measureReal_normalizedSourceScale_tail
    {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    ⦃t : ℝ⦄ (ht : 1 ≤ t) :
    P.real {a | t < normalizedSourceScale S sK a} ≤ (t * Ψ t)⁻¹ := by
  have h3sK : (0 : ℝ) < (3 : ℝ) ^ sK :=
    lt_of_lt_of_le (by norm_num) ((le_max_left 2 K).trans hsK)
  have hevent : {a | t < normalizedSourceScale S sK a} =
      IndependentSums.upperTailEvent S ((3 : ℝ) ^ sK * t) := by
    ext a
    simp only [IndependentSums.upperTailEvent, Set.mem_ofPred_eq,
      normalizedSourceScale, lt_max_iff]
    constructor
    · rintro (h1 | h2)
      · exact absurd h1 (not_lt.mpr ht)
      · calc
          (3 : ℝ) ^ sK * t = t * (3 : ℝ) ^ sK := by ring
          _ < S a * (3 : ℝ) ^ (-sK) * (3 : ℝ) ^ sK :=
            mul_lt_mul_of_pos_right h2 h3sK
          _ = S a := by
            rw [mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
            simp
    · intro h
      right
      have h1 : t * (3 : ℝ) ^ sK < S a := by
        calc
          t * (3 : ℝ) ^ sK = (3 : ℝ) ^ sK * t := by ring
          _ < S a := h
      calc
        t = t * (3 : ℝ) ^ sK * (3 : ℝ) ^ (-sK) := by
          rw [mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp
        _ < S a * (3 : ℝ) ^ (-sK) := by
          refine mul_lt_mul_of_pos_right h1 ?_
          positivity
    -- the tail event identification
  rw [hevent]
  have hpos : 0 < (3 : ℝ) ^ sK * t := mul_pos h3sK (by linarith only [ht])
  refine (hdag.source_tail _ hpos).trans ?_
  have hΨt : 1 ≤ Ψ t := hdag.gauge_admissible.2 (by linarith only [ht])
  have hmono : t * Ψ t ≤ Ψ ((3 : ℝ) ^ sK * t) := by
    refine (hdag.gauge_growth ht).trans (hdag.gauge_admissible.1 ?_ ?_ ?_)
    · exact Set.mem_Ici.mpr (by nlinarith only [hdag.one_lt_growthWitness, ht])
    · exact Set.mem_Ici.mpr (by positivity)
    · have hKsK : K ≤ (3 : ℝ) ^ sK := (le_max_right 2 K).trans hsK
      nlinarith only [hKsK, ht]
  refine inv_anti₀ ?_ hmono
  nlinarith only [ht, hΨt]

/-- **The moments.**  Every integer moment of the normalized source scale is
bounded by the explicit `growthBar` constant. -/
theorem lintegral_normalizedSourceScale_pow_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫⁻ a, ENNReal.ofReal (normalizedSourceScale S sK a ^ (N : ℝ)) ∂P ≤
      ENNReal.ofReal
        (1 + 2 * (N : ℝ) * (1 + Real.log (growthBar K)) *
          growthBar K ^ IndependentSums.natTriangular N) := by
  refine IndependentSums.lintegral_rpow_le_of_strongPsiTail N hN
    (le_max_left 2 K)
    (hasPsiGrowth_growthBar hdag.gauge_admissible
      hdag.one_lt_growthWitness hdag.gauge_growth)
    hdag.gauge_admissible ?_ (fun a => ?_) ?_
  · refine (Measurable.max measurable_const ?_).aemeasurable
    exact hdag.source_measurable.mul_const _
  · exact le_trans zero_le_one (one_le_normalizedSourceScale S sK a)
  · exact fun t ht => measureReal_normalizedSourceScale_tail hdag hsK ht

/-- **The decayed tail moment.**  On the tail event `{3^Δ < V}`, the `N`-th
moment of the `Δ`-rescaled normalized source scale decays like `3^{-MΔ}`,
for every reserve order `M`. -/
theorem setLintegral_normalizedSourceScale_pow_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (N M : ℕ) (hNM : 1 ≤ N + M) {Delta : ℤ} (hDelta : 0 ≤ Delta) :
    ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
        ENNReal.ofReal
          ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
            (N : ℝ)) ∂P ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-((M : ℝ) * (Delta : ℝ)))) *
        ENNReal.ofReal
          (1 + 2 * ((N + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
            growthBar K ^ IndependentSums.natTriangular (N + M)) := by
  have hmeasSet : MeasurableSet
      {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a} := by
    refine measurableSet_lt measurable_const ?_
    exact Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  have hdom : ∀ᵐ a ∂(P.restrict
      {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a}),
      ENNReal.ofReal
          ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
            (N : ℝ)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(((N + M : ℕ) : ℝ) * (Delta : ℝ)))) *
          ENNReal.ofReal
            (normalizedSourceScale S sK a ^ ((N + M : ℕ) : ℝ)) := by
    rw [ae_restrict_iff' hmeasSet]
    refine _root_.Filter.Eventually.of_forall fun a ha => ?_
    have hV1 : (1 : ℝ) ≤ normalizedSourceScale S sK a :=
      one_le_normalizedSourceScale S sK a
    have h3D : (0 : ℝ) < (3 : ℝ) ^ Delta := by positivity
    have hVD : (1 : ℝ) ≤ normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta) := by
      have h := Set.mem_ofPred_eq ▸ ha
      rw [show (1 : ℝ) = (3 : ℝ) ^ Delta * (3 : ℝ) ^ (-Delta) from by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; simp]
      exact mul_le_mul_of_nonneg_right (le_of_lt h) (by positivity)
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep1 : (normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
        (N : ℝ) ≤
        (normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
          ((N + M : ℕ) : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hVD ?_
      exact_mod_cast Nat.le_add_right N M
    refine hstep1.trans (le_of_eq ?_)
    rw [Real.mul_rpow (by linarith only [hV1]) (by positivity)]
    rw [← Real.rpow_intCast (3 : ℝ) (-Delta),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [show ((-Delta : ℤ) : ℝ) * ((N + M : ℕ) : ℝ) =
        -(((N + M : ℕ) : ℝ) * (Delta : ℝ)) from by push_cast; ring]
    ring
  calc
    ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
        ENNReal.ofReal
          ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
            (N : ℝ)) ∂P ≤
        ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(((N + M : ℕ) : ℝ) * (Delta : ℝ)))) *
            ENNReal.ofReal
              (normalizedSourceScale S sK a ^ ((N + M : ℕ) : ℝ)) ∂P :=
      lintegral_mono_ae hdom
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(((N + M : ℕ) : ℝ) * (Delta : ℝ)))) *
        ∫⁻ a, ENNReal.ofReal
          (normalizedSourceScale S sK a ^ ((N + M : ℕ) : ℝ)) ∂P := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-((M : ℝ) * (Delta : ℝ)))) *
        ENNReal.ofReal
          (1 + 2 * ((N + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
            growthBar K ^ IndependentSums.natTriangular (N + M)) := by
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
        (lintegral_normalizedSourceScale_pow_le hdag hsK (N + M) hNM)
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hD0 : (0 : ℝ) ≤ (Delta : ℝ) := by exact_mod_cast hDelta
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hcast : ((N + M : ℕ) : ℝ) = (N : ℝ) + (M : ℝ) := by push_cast; ring
      rw [hcast]
      nlinarith only [hD0, hN0]

end

end HCPolySupport.HighContrast.Quenched
