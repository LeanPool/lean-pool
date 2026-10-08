/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitSuccessorEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeFiniteRangeDatum
public import LeanPool.HighContrastHomogenization.Provider.Window.SuccessorTail
public import LeanPool.HighContrastHomogenization.Provider.Window.ScaleMeasurability

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnSplitSource

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse-ellipticity datum at the window's successor scale

The burn-split envelope is stated over the successor scale of a window, so the
moment estimates that consume it need a coarse-ellipticity datum carried by that
scale rather than by the original source.  The window's own tail
(`e.source.multiplier`) supplies it: above the window threshold the
successor scale has the source gauge dilated by that threshold, and below it the
gauge is flat, which is what an admissible gauge is allowed to be.

The datum is stated at the enlarged scale `max 𝒮 S_hat`, so the coarse bound of
`e.coarse.ellipticity` transfers by monotonicity and the tail is the union
of the two.  The dilation and the union factor both enter the growth witness,
that is, a scale threshold — which is where the printed account puts them.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory
open IndependentSums

noncomputable section

variable {d : ℕ}

/-- The enlarged source scale: the original source scale joined with the
window's successor scale. -/
@[expose]
def burnSplitSource (g : ℝ) (E : BlockMat d) (h : ℤ) (S : CoeffSpace d → ℝ) :
    CoeffSpace d → ℝ :=
  fun a => max (S a) (successorScale g E h a).toReal

/-- The window threshold above which the successor scale carries the source
gauge. -/
@[expose]
def burnSplitThreshold (d : ℕ) (K : ℝ) (jStar M : ℤ) : ℝ :=
  max ((3 : ℝ) ^ M)
    (growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ (M - jStar + 1))

/-- The dilated gauge, flat below the dilation. -/
@[expose]
def burnSplitGauge (Ψ : ℝ → ℝ) (B : ℝ) : ℝ → ℝ :=
  fun u => max 1 (Ψ (u / B) / (2 * Ψ 1))

theorem one_le_burnSplitGauge (Ψ : ℝ → ℝ) (B u : ℝ) :
    1 ≤ burnSplitGauge Ψ B u :=
  le_max_left _ _

theorem admissiblePsi_burnSplitGauge {Ψ : ℝ → ℝ}
    (hadm : AdmissiblePsi Ψ) {B : ℝ} (hB : 0 < B) :
    AdmissiblePsi (burnSplitGauge Ψ B) := by
  refine ⟨?_, fun t _ => one_le_burnSplitGauge Ψ B t⟩
  intro u hu v hv huv
  refine max_le_max le_rfl ?_
  have hc : 0 < 2 * Ψ 1 := by
    have h1 : (1 : ℝ) ≤ Ψ 1 := hadm.2 zero_le_one
    linarith only [h1]
  refine div_le_div_of_nonneg_right ?_ hc.le
  refine hadm.1 (Set.mem_Ici.mpr (div_nonneg (Set.mem_Ici.mp hu) hB.le))
    (Set.mem_Ici.mpr (div_nonneg (Set.mem_Ici.mp hv) hB.le))
    (div_le_div_of_nonneg_right huv hB.le)

/-- Iterating the growth condition above the growth witness. -/
private theorem pow_mul_psi_le {Ψ : ℝ → ℝ} {K : ℝ}
    (hadm : AdmissiblePsi Ψ) (hgrowth : HasPsiGrowth Ψ K) (hK : 1 < K) :
    ∀ (n : ℕ) {s : ℝ}, K ≤ s → K ^ n * Ψ s ≤ Ψ (K ^ n * s) := by
  intro n
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
      intro s hs
      have hK0 : (0 : ℝ) < K := by linarith only [hK]
      have hs1 : (1 : ℝ) ≤ s := by linarith only [hs, hK]
      have hKn1 : (1 : ℝ) ≤ K ^ n := one_le_pow₀ hK.le
      have hKns : (1 : ℝ) ≤ K ^ n * s := by nlinarith only [hKn1, hs1]
      have hstep : (K ^ n * s) * Ψ (K ^ n * s) ≤ Ψ (K * (K ^ n * s)) :=
        hgrowth hKns
      have hKle : K ≤ K ^ n * s := by nlinarith only [hKn1, hs, hK0]
      have hpsi0 : (0 : ℝ) ≤ Ψ (K ^ n * s) := by
        have := hadm.2 (by linarith only [hKns] : (0 : ℝ) ≤ K ^ n * s)
        linarith only [this]
      have hbase := ih hs
      calc
        K ^ (n + 1) * Ψ s = K * (K ^ n * Ψ s) := by ring
        _ ≤ K * Ψ (K ^ n * s) :=
          mul_le_mul_of_nonneg_left hbase hK0.le
        _ ≤ (K ^ n * s) * Ψ (K ^ n * s) :=
          mul_le_mul_of_nonneg_right hKle hpsi0
        _ ≤ Ψ (K * (K ^ n * s)) := hstep
        _ = Ψ (K ^ (n + 1) * s) := by ring_nf

theorem hasPsiGrowth_burnSplitGauge {Ψ : ℝ → ℝ} {K : ℝ}
    (hadm : AdmissiblePsi Ψ) (hgrowth : HasPsiGrowth Ψ K) (hK : 1 < K)
    {B : ℝ} (hB : 1 ≤ B) {n : ℕ} (hn : 2 * Ψ 1 ≤ K ^ n) :
    HasPsiGrowth (burnSplitGauge Ψ B) (B * K ^ (n + 1)) := by
  intro t ht
  have hK0 : (0 : ℝ) < K := by linarith only [hK]
  have hB0 : (0 : ℝ) < B := by linarith only [hB]
  have ht0 : (0 : ℝ) ≤ t := by linarith only [ht]
  have hPsi1 : (1 : ℝ) ≤ Ψ 1 := hadm.2 zero_le_one
  have hc : (0 : ℝ) < 2 * Ψ 1 := by linarith only [hPsi1]
  have hPsit : (1 : ℝ) ≤ Ψ t := hadm.2 ht0
  -- the gauge is below the original gauge
  have hle : burnSplitGauge Ψ B t ≤ Ψ t := by
    refine max_le hPsit ?_
    have hdiv : t / B ≤ t := by
      rw [div_le_iff₀ hB0]
      nlinarith only [ht0, hB]
    have hmono : Ψ (t / B) ≤ Ψ t :=
      hadm.1 (Set.mem_Ici.mpr (div_nonneg ht0 hB0.le))
        (Set.mem_Ici.mpr ht0) hdiv
    rw [div_le_iff₀ hc]
    nlinarith only [hmono, hPsit, hPsi1]
  -- one growth step of the original gauge
  have hstep : t * Ψ t ≤ Ψ (K * t) := hgrowth ht
  -- the iterated step absorbs the union factor
  have hs : K ≤ K * t := by nlinarith only [ht, hK0]
  have hiter := pow_mul_psi_le hadm hgrowth hK n hs
  have hpsiKt : (0 : ℝ) ≤ Ψ (K * t) := by
    have := hadm.2 (by nlinarith only [ht0, hK0] : (0 : ℝ) ≤ K * t)
    linarith only [this]
  have habs : 2 * Ψ 1 * Ψ (K * t) ≤ Ψ (K ^ n * (K * t)) := by
    calc
      2 * Ψ 1 * Ψ (K * t) ≤ K ^ n * Ψ (K * t) :=
        mul_le_mul_of_nonneg_right hn hpsiKt
      _ ≤ Ψ (K ^ n * (K * t)) := hiter
  have harg : B * K ^ (n + 1) * t / B = K ^ n * (K * t) := by
    field_simp
    ring
  calc
    t * burnSplitGauge Ψ B t ≤ t * Ψ t :=
      mul_le_mul_of_nonneg_left hle ht0
    _ ≤ Ψ (K * t) := hstep
    _ ≤ Ψ (K ^ n * (K * t)) / (2 * Ψ 1) := by
      rw [le_div_iff₀ hc]
      nlinarith only [habs]
    _ = Ψ (B * K ^ (n + 1) * t / B) / (2 * Ψ 1) := by rw [harg]
    _ ≤ burnSplitGauge Ψ B (B * K ^ (n + 1) * t) := le_max_right _ _

/-- The window threshold is at least one. -/
theorem one_le_burnSplitThreshold {K : ℝ} {jStar M : ℤ}
    (hjM : jStar + 1 ≤ M) : 1 ≤ burnSplitThreshold d K jStar M := by
  refine le_trans ?_ (le_max_right _ _)
  have h2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hpow : (1 : ℝ) ≤ growthBar K ^ (4 * (d + 1)) :=
    one_le_pow₀ (by linarith only [h2])
  have hz : (1 : ℝ) ≤ (3 : ℝ) ^ (M - jStar + 1) := by
    calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℤ) := by norm_num
      _ ≤ (3 : ℝ) ^ (M - jStar + 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
  nlinarith only [hpow, hz]

/-- **The tail of the enlarged source scale.**  The union of the source tail
and the window's successor tail, at the dilated gauge. -/
theorem measureReal_burnSplitSource_tail [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M) :
    ∀ u : ℝ, 0 < u →
      P.real (upperTailEvent (burnSplitSource g E (M - jStar) S) u) ≤
        (burnSplitGauge Ψ
          (burnSplitThreshold d K jStar M * K) u)⁻¹ := by
  intro u hu
  have hK1 : (1 : ℝ) < K := hdag.one_lt_growthWitness
  have hK0 : (0 : ℝ) < K := by linarith only [hK1]
  have hA1 : (1 : ℝ) ≤ burnSplitThreshold d K jStar M :=
    one_le_burnSplitThreshold hw.2.1
  set A : ℝ := burnSplitThreshold d K jStar M with hAdef
  have hAK1 : (1 : ℝ) ≤ A * K := by nlinarith only [hA1, hK1]
  have hAK0 : (0 : ℝ) < A * K := by linarith only [hAK1]
  have hPsi1 : (1 : ℝ) ≤ Ψ 1 := hdag.gauge_admissible.2 zero_le_one
  set s : ℝ := u / (A * K) with hsdef
  have hs0 : (0 : ℝ) ≤ s := by
    rw [hsdef]
    exact div_nonneg hu.le hAK0.le
  by_cases hcase : Ψ s / (2 * Ψ 1) ≤ 1
  · have hgauge : burnSplitGauge Ψ (A * K) u = 1 := by
      rw [burnSplitGauge, ← hsdef]
      exact max_eq_left hcase
    rw [hgauge, inv_one]
    exact measureReal_le_one
  · push Not at hcase
    have hPsis : 2 * Ψ 1 < Ψ s := by
      have hcpos : (0 : ℝ) < 2 * Ψ 1 := by linarith only [hPsi1]
      rw [lt_div_iff₀ hcpos] at hcase
      linarith only [hcase]
    -- the gauge is above one, so the argument is above one
    have hs1 : (1 : ℝ) ≤ s := by
      by_contra hlt
      push Not at hlt
      have := hdag.gauge_admissible.1 (Set.mem_Ici.mpr hs0)
        (Set.mem_Ici.mpr zero_le_one) hlt.le
      linarith only [this, hPsis, hPsi1]
    have hus : u = A * (K * s) := by
      rw [hsdef]
      field_simp
    have hKs1 : (1 : ℝ) ≤ K * s := by nlinarith only [hK1, hs1]
    have hPsis0 : (0 : ℝ) < Ψ s := by linarith only [hPsis, hPsi1]
    -- the two tails
    have hSpart : P.real (upperTailEvent S u) ≤ (Ψ s)⁻¹ := by
      refine (hdag.source_tail u hu).trans ?_
      have hsu : s ≤ u := by nlinarith only [hAK1, hs0, hus, hKs1, hA1, hK1]
      have hmono : Ψ s ≤ Ψ u :=
        hdag.gauge_admissible.1 (Set.mem_Ici.mpr hs0)
          (Set.mem_Ici.mpr hu.le) hsu
      exact (inv_le_inv₀ (by linarith only [hPsis0, hmono]) hPsis0).2 hmono
    have hShpart :
        P.real (upperTailEvent
          (fun a => (successorScale g E (M - jStar) a).toReal) u) ≤
          (Ψ s)⁻¹ := by
      have hsub : upperTailEvent
          (fun a => (successorScale g E (M - jStar) a).toReal) u ⊆
          {a : CoeffSpace d |
            ENNReal.ofReal
              (max ((3 : ℝ) ^ M)
                ((K * s) * growthBar K ^ (4 * (d + 1)) *
                  (3 : ℝ) ^ (M - jStar + 1))) <
              successorScale g E (M - jStar) a} := by
        intro a ha
        have haR : u < (successorScale g E (M - jStar) a).toReal := ha
        have hne : successorScale g E (M - jStar) a ≠ ⊤ := by
          intro htop
          rw [htop] at haR
          rw [ENNReal.toReal_top] at haR
          linarith only [haR, hu]
        have hlt : ENNReal.ofReal u < successorScale g E (M - jStar) a := by
          rw [← ENNReal.ofReal_toReal hne]
          exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le |>.2 haR
        refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hlt
        refine max_le ?_ ?_
        · rw [hus]
          have h1 : (3 : ℝ) ^ M ≤ A := le_max_left _ _
          nlinarith only [h1, hKs1, hA1]
        · rw [hus]
          have h2 : growthBar K ^ (4 * (d + 1)) *
              (3 : ℝ) ^ (M - jStar + 1) ≤ A := le_max_right _ _
          have hKs0 : (0 : ℝ) ≤ K * s := by linarith only [hKs1]
          nlinarith only [h2, hKs0]
      refine (measureReal_mono hsub).trans ?_
      refine (Window.measureReal_successorScale_tail hstat hdag hQ hw
        hKs1).trans ?_
      have hmono : Ψ s ≤ Ψ (K * s) :=
        hdag.gauge_admissible.1 (Set.mem_Ici.mpr hs0)
          (Set.mem_Ici.mpr (by linarith only [hKs1]))
          (by nlinarith only [hK1, hs1])
      exact (inv_le_inv₀ (by linarith only [hPsis0, hmono]) hPsis0).2 hmono
    -- the union
    have hsplit : upperTailEvent (burnSplitSource g E (M - jStar) S) u =
        upperTailEvent S u ∪
          upperTailEvent
            (fun a => (successorScale g E (M - jStar) a).toReal) u := by
      ext a
      simp only [upperTailEvent, burnSplitSource, Set.mem_ofPred_eq,
        Set.mem_union, lt_max_iff]
    have hgauge : burnSplitGauge Ψ (A * K) u = Ψ s / (2 * Ψ 1) := by
      rw [burnSplitGauge, ← hsdef]
      exact max_eq_right hcase.le
    rw [hgauge, hsplit]
    refine (measureReal_union_le _ _).trans ?_
    have hsum : (Ψ s)⁻¹ + (Ψ s)⁻¹ ≤ (Ψ s / (2 * Ψ 1))⁻¹ := by
      rw [inv_div, le_div_iff₀ hPsis0]
      have hinv : (Ψ s)⁻¹ * Ψ s = 1 := inv_mul_cancel₀ (ne_of_gt hPsis0)
      nlinarith only [hinv, hPsi1, hPsis0]
    linarith only [hSpart, hShpart, hsum]

/-- **The coarse-ellipticity datum at the enlarged source scale.**  Every
clause of `e.coarse.ellipticity` transfers: the coarse bound by
monotonicity of the scale, the tail from the window. -/
theorem coarseEllipticityDagger_burnSplitSource [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {n : ℕ} (hn : 2 * Ψ 1 ≤ K ^ n) :
    HCPoly.Frozen.CoarseEllipticityDagger P g E
      (burnSplitGauge Ψ (burnSplitThreshold d K jStar M * K))
      (burnSplitThreshold d K jStar M * K * K ^ (n + 1))
      (burnSplitSource g E (M - jStar) S) := by
  have hK1 : (1 : ℝ) < K := hdag.one_lt_growthWitness
  have hK0 : (0 : ℝ) < K := by linarith only [hK1]
  have hA1 : (1 : ℝ) ≤ burnSplitThreshold d K jStar M :=
    one_le_burnSplitThreshold hw.2.1
  have hAK1 : (1 : ℝ) ≤ burnSplitThreshold d K jStar M * K := by
    nlinarith only [hA1, hK1]
  have hpow : (1 : ℝ) < K ^ (n + 1) := one_lt_pow₀ hK1 (by omega)
  refine coarseEllipticityDagger_of_source_le hdag
    (fun a => le_max_left _ _) ?_ (fun a => ?_)
    (admissiblePsi_burnSplitGauge hdag.gauge_admissible
      (by linarith only [hAK1]))
    ?_
    (hasPsiGrowth_burnSplitGauge hdag.gauge_admissible hdag.gauge_growth hK1
      hAK1 hn)
    (measureReal_burnSplitSource_tail hstat hdag hQ hw)
  · exact hdag.source_measurable.max
      (Window.measurable_successorScale g E hdag.refBlock_isSymm
        hdag.refBlock_posDef (M - jStar)).ennreal_toReal
  · exact le_trans (hdag.source_nonneg a) (le_max_left _ _)
  · nlinarith only [hAK1, hpow]

/-- **The maximal envelope at the enlarged source scale.**  The burn-split
envelope re-read at the scale carrying the coarse-ellipticity datum. -/
theorem henvMax_burnsplit_at_burnSplitSource [NeZero d]
    (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {D : ℕ} (hdepth : M - jStar = ((2 * D : ℕ) : ℤ))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    (hD : boundaryConst Cd g nu ≤ (3 : ℝ) ^ D)
    {rho : ℝ} (hrho : g ≤ rho) (t : ℤ)
    (hgeom : ∀ k : ℤ, k ≤ t →
      ∀ w ∈ Response.alignedIndex (roundedGrid l nu) k t,
        adaptedCellAt (roundedGrid l nu) k w ⊆
          centeredCube d (t + (D : ℤ)))
    {cIso : ℝ} (hcIso : 0 ≤ cIso) :
    ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l nu) t
          (isotropyReference cIso E) a ≤
        ENNReal.ofReal
          (4 / (1 + cIso) *
            ((max 1
              (3 * burnSplitSource g E (M - jStar) S a *
                (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))))) ^ g / 2)) := by
  have hR0 : (0 : ℝ) ≤ 4 / (1 + cIso) :=
    div_nonneg (by norm_num) (by linarith only [hcIso])
  filter_upwards [henvMax_burnsplit_of_successorScale hd hstat hg hdag hQ hw
    hdepth hl hCd hnu hD hrho t hgeom hcIso] with a ha
  refine ha.trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_ hR0
  refine (div_le_div_iff_of_pos_right (by norm_num)).2 ?_
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hle : (successorScale g E (M - jStar) a).toReal ≤
      burnSplitSource g E (M - jStar) S a := le_max_right _ _
  have hstep : 3 * (successorScale g E (M - jStar) a).toReal *
      (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))) ≤
      3 * burnSplitSource g E (M - jStar) S a *
        (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hc0
    linarith only [hle]
  refine Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _))
    (max_le_max le_rfl hstep) hg.1

end

end HCPolySupport.HighContrast.Quenched
