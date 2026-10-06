/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledWitnessAssembly
public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeRowFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeTransport
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RowDecayAESummability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedWitness
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211Cost
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211CellRenormalization
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RebaseSourceHalf

/-!
# High-contrast homogenization: Provider.Quenched.EndpointRelativeEngineData

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Endpoint-relative coupled-engine data

The coefficient law is first read in the units of the annealed endpoint.
Growing recent windows then give a radius family with a uniform shifted tail,
while the same family controls the physical block row after pulling it back to
the original coefficient law.
-/

namespace HCPolySupport.HighContrast.Quenched

open _root_.Filter MeasureTheory

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

private theorem exists_endpoint_eta {alpha gap mu : ℝ} {A : ℕ}
    (halpha : 0 < alpha) (hgap : 0 < gap) (hmu : 0 < mu) (hA : 1 ≤ A) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ alpha ∧ eta ≤ mu ∧
      eta ≤ gap * (A : ℝ) := by
  let eta : ℝ := min (min alpha mu) (gap * (A : ℝ)) / 2
  have hApos : 0 < (A : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le hA
  have hmin : 0 < min (min alpha mu) (gap * (A : ℝ)) := by
    exact lt_min (lt_min halpha hmu) (mul_pos hgap hApos)
  refine ⟨eta, by dsimp only [eta]; positivity, ?_, ?_, ?_⟩
  · dsimp only [eta]
    exact (div_le_self hmin.le (by norm_num)).trans
      ((min_le_left _ _).trans (min_le_left _ _))
  · dsimp only [eta]
    exact (div_le_self hmin.le (by norm_num)).trans
      ((min_le_left _ _).trans (min_le_right _ _))
  · dsimp only [eta]
    exact (div_le_self hmin.le (by norm_num)).trans (min_le_right _ _)

private theorem twelve_mul_triadic_le_endpoint_burn
    {gap : ℝ} {A q Q : ℕ}
    (hgapA : 1 ≤ gap * (A : ℝ)) (hq : 1 ≤ q) (hQ : 4 ≤ Q) :
    12 * (3 : ℝ) ^ q ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ (gap * ((A * (Q * q) : ℕ) : ℝ)) := by
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hQR : 4 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hexp : (4 : ℝ) * (q : ℝ) ≤
      gap * ((A * (Q * q) : ℕ) : ℝ) := by
    push_cast
    have hmul := mul_le_mul hgapA hQR (by norm_num : (0 : ℝ) ≤ 4)
      (by positivity : 0 ≤ gap * (A : ℝ))
    nlinarith only [hmul, hqR]
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 3) hexp
  have hthreeq : (27 : ℝ) ≤ (3 : ℝ) ^ (3 * (q : ℝ)) := by
    have he : (3 : ℝ) ≤ 3 * (q : ℝ) := by nlinarith only [hqR]
    simpa only [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) by norm_num] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) he
  have hsplit : (3 : ℝ) ^ ((4 : ℝ) * (q : ℝ)) =
      (3 : ℝ) ^ (q : ℝ) * (3 : ℝ) ^ (3 * (q : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [← Real.rpow_natCast] at ⊢
  calc
    12 * (3 : ℝ) ^ (q : ℝ) ≤
        (1 / 2 : ℝ) * (3 : ℝ) ^ ((4 : ℝ) * (q : ℝ)) := by
      rw [hsplit]
      have hp : 0 ≤ (3 : ℝ) ^ (q : ℝ) := by positivity
      nlinarith only [hthreeq, hp]
    _ ≤ (1 / 2 : ℝ) *
        (3 : ℝ) ^ (gap * ((A * (Q * q) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)

private theorem exists_nat_mul_ge_one {theta : ℝ} (htheta : 0 < theta) :
    ∃ R : ℕ, 1 ≤ R ∧ 1 ≤ theta * (R : ℝ) := by
  obtain ⟨R, hR⟩ := exists_nat_ge (1 / theta)
  have hmul : 1 ≤ theta * (R : ℝ) := by
    have := (div_le_iff₀ htheta).1 hR
    simpa only [one_div, inv_mul_cancel₀ htheta.ne', mul_comm] using this
  exact ⟨max 1 R, le_max_left _ _, hmul.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast le_max_right 1 R) htheta.le)⟩

private theorem endpoint_fixed_normalizer_cost {base Bconst : ℝ}
    (hbase : 3 ≤ base) (hB : 1 ≤ Bconst) :
    Bconst ≤ base ^ Real.logb 3 Bconst :=
  fixed_le_rpow_of_three_le hB hbase

private theorem endpoint_fallback_scalar_bound
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {base geomG Cblk delta theta x : ℝ} {q R qfb : ℕ}
    (hbaseEq : base = 2 + aspectRatio E * K)
    (hqBase : base ≤ (3 : ℝ) ^ q) (hqfb : qfb = R * q)
    (hgeomG : 0 ≤ geomG) (hCblkFallback : 48 * geomG ≤ Cblk)
    (hdelta : delta = 1 / 2) (hthetaR : 1 ≤ theta * (R : ℝ))
    (hx : x ≤ 4 * kappaRef E * geomG) :
    x ≤ Cblk * delta * (3 : ℝ) ^ (theta * (qfb : ℝ)) := by
  have hkappa := Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
  have haspectBase : aspectRatio E ≤ base := by
    have hK1 : 1 ≤ K := le_of_lt hdag.one_lt_growthWitness
    have ha0 : 0 ≤ aspectRatio E := zero_le_one.trans
      (one_le_aspectRatio_of_coarseEllipticityDagger hdag)
    rw [hbaseEq]
    nlinarith only [hK1, ha0]
  have hleft : 4 * kappaRef E * geomG ≤ 24 * (3 : ℝ) ^ q * geomG := by
    have hk := hkappa.trans (mul_le_mul_of_nonneg_left
      (haspectBase.trans hqBase) (by norm_num))
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hk]) hgeomG
  have hexp : (q : ℝ) ≤ theta * (qfb : ℝ) := by
    rw [hqfb]
    push_cast
    have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith only [hthetaR, hq0]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  have hp' : (3 : ℝ) ^ q ≤ (3 : ℝ) ^ (theta * (qfb : ℝ)) := by
    simpa only [Real.rpow_natCast] using hp
  calc
    x ≤ 4 * kappaRef E * geomG := hx
    _ ≤ 24 * (3 : ℝ) ^ q * geomG := hleft
    _ = (24 * geomG) * (3 : ℝ) ^ q := by ring
    _ ≤ (Cblk * delta) * (3 : ℝ) ^ (theta * (qfb : ℝ)) := by
      have hc : 24 * geomG ≤ Cblk * delta := by
        rw [hdelta]
        linarith only [hCblkFallback]
      have hCblk0 : 0 ≤ Cblk :=
        (mul_nonneg (by norm_num) hgeomG).trans hCblkFallback
      exact mul_le_mul hc hp' (by positivity)
        (mul_nonneg hCblk0 (by rw [hdelta]; norm_num))

private theorem endpoint_initial_burn
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g gamma : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} {base : ℝ} {A Q q : ℕ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hbaseEq : base = 2 + aspectRatio E * K)
    (hqBase : base ≤ (3 : ℝ) ^ q)
    (hgapA : 1 ≤ (gamma - g) * (A : ℝ)) (hq : 1 ≤ q) (hQ : 4 ≤ Q) :
    2 * kappaRef E ≤ (1 / 2 : ℝ) *
      (3 : ℝ) ^ ((gamma - g) * ((A * (Q * q) : ℕ) : ℝ)) := by
  have hkappa := Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
  have haspectBase : aspectRatio E ≤ base := by
    have hK1 : 1 ≤ K := le_of_lt hdag.one_lt_growthWitness
    have ha0 : 0 ≤ aspectRatio E := zero_le_one.trans
      (one_le_aspectRatio_of_coarseEllipticityDagger hdag)
    rw [hbaseEq]
    nlinarith only [hK1, ha0]
  have hkbase : kappaRef E ≤ 6 * base :=
    hkappa.trans (mul_le_mul_of_nonneg_left haspectBase (by norm_num))
  have hraw : 2 * kappaRef E ≤ 12 * (3 : ℝ) ^ q := by
    nlinarith only [hkbase, hqBase]
  exact hraw.trans (twelve_mul_triadic_le_endpoint_burn hgapA hq hQ)

private theorem nonempty_coupledWitnessEngineData_of_fields
    {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ} {Abar : BlockMat d}
    {Nann : ℕ} {rho theta deltaOut Cmix mu : ℝ}
    {nstar qfb b N0 : ℕ} {radius F Brow : ℕ → CoeffSpace d → ℝ}
    {Cblk Bconst C1 C2 C3 Cstop Cround : ℝ}
    (hrhoEq : rho = (1 + 3 * g) / 4)
    (hBrowEq : Brow = fun m a => quenched_block_row rho Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m)
    (hmuEq : mu = (d : ℝ) / 2 - g) (hmu : 0 < mu)
    (hradiusTail : ∀ n q : ℕ, nstar ≤ n →
      P.real {a : CoeffSpace d | (3 : ℝ) ^ (n + q + b) < radius n a} ≤
        Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (q : ℝ)))))
    (hCblk : 0 < Cblk) (hFmeas : ∀ n, Measurable (F n))
    (hrowDecay : ∀ᵐ a ∂P, ∀ m : ℕ, nstar ≤ m →
      Brow m a ≤
        Cblk * deltaOut * (3 : ℝ) ^ (-theta *
          ((m : ℝ) - (stoppingGeneration nstar qfb radius m a : ℝ) - (nstar : ℝ))))
    (hrowNonnegative : ∀ m a, 0 ≤ Brow m a)
    (hFsum : ∀ᵐ a ∂P, ∀ k : ℕ, HasSum (fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * (j : ℝ)) *
        Brow (k + j) a) (F k a))
    (hN0star : nstar ≤ N0) (hBconst : 1 ≤ Bconst)
    (hthresholdLow : (qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk ≤
      (N0 : ℝ) - (nstar : ℝ))
    (hthresholdGain : Real.log 2 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)) * ((3 : ℝ) ^ (mu / 2) - 1))
    (hthresholdAbs : 2 * Real.log 4 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)))
    (hnormalizerRel : (3 : ℝ) ^ (2 * mu *
      ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ))) ≤
        frGaugeConst d / 2 * Bconst ^ (2 * mu))
    (hbase1 : 1 ≤ 2 + aspectRatio E * K)
    (hbase3 : (3 : ℝ) ≤ (2 + aspectRatio E * K) ^ C3)
    (hgenCost : (3 : ℝ) ^ N0 ≤ (2 + aspectRatio E * K) ^ C1)
    (hnormCost : Bconst ≤ (2 + aspectRatio E * K) ^ C2)
    (hrawCost : C1 + C2 + C3 ≤ Cstop)
    (hroundCost : (3 : ℝ) ≤ (2 + aspectRatio E * K) ^ Cround)
    (hfinalCost : Cround + Cstop ≤ Cmix) :
    Nonempty (CoupledWitnessEngineData P g E Psi K S Abar Nann theta deltaOut Cmix) := by
  subst rho
  subst Brow
  exact ⟨{
    mu := mu
    nstar := nstar
    qfb := qfb
    b := b
    N0 := N0
    radius := radius
    F := F
    Cblk := Cblk
    Bconst := Bconst
    C1 := C1
    C2 := C2
    C3 := C3
    Cstop := Cstop
    Cround := Cround
    mu_eq := hmuEq
    mu_pos := hmu
    radius_tail := hradiusTail
    Cblk_pos := hCblk
    F_measurable := hFmeas
    row_decay := hrowDecay
    row_nonnegative := hrowNonnegative
    row_hasSum := hFsum
    nstar_le_N0 := hN0star
    one_le_Bconst := hBconst
    threshold_low := hthresholdLow
    threshold_gain := hthresholdGain
    threshold_absolute := hthresholdAbs
    normalizer_relation := hnormalizerRel
    one_le_base := hbase1
    three_le_base_pow := hbase3
    generation_cost := hgenCost
    normalizer_cost := hnormCost
    raw_cost := hrawCost
    rounding_cost := hroundCost
    final_cost := hfinalCost
  }⟩

private theorem endpoint_window_certificate
    {d : ℕ} {g gamma delta eta alpha : ℝ} {E Abar : BlockMat d}
    {S : CoeffSpace d → ℝ} {Ahat : ℕ → BlockMat d}
    {a : CoeffSpace d} {nstar q0 A D L : ℕ}
    (hfin : ∀ n, nstar ≤ n →
      renormScale S (Ahat n) (endpointTolerance delta eta q0 L n)
        gamma (endpointWindowLength A L n) n a ≠ ⊤)
    (hpos : ∀ n, nstar ≤ n → Book.Ch02.BlockPosDef (Ahat n))
    (href : ∀ n, nstar ≤ n →
      BlockMatLoewnerLE E (blockScale (2 * kappaRef E) (Ahat n)))
    (hupper : ∀ n, nstar ≤ n →
      BlockMatLoewnerLE (Ahat n)
        (blockScale (1 + 6 * (3 : ℝ) ^
          (-alpha * ((n - endpointReferenceOffset A D L n : ℕ) : ℝ))) Abar))
    (herr : ∀ n, nstar ≤ n →
      6 * (3 : ℝ) ^
          (-alpha * ((n - endpointReferenceOffset A D L n : ℕ) : ℝ)) ≤
        endpointTolerance delta eta q0 L n)
    (hburn : ∀ n, nstar ≤ n →
      2 * kappaRef E ≤ endpointTolerance delta eta q0 L n *
        (3 : ℝ) ^ ((gamma - g) * (endpointWindowLength A L n : ℝ)))
    (hAbar : Book.Ch02.BlockPosDef Abar) :
    ∀ n, nstar ≤ n → ∃ h : ℕ,
      h = endpointWindowLength A L n ∧
      renormScale S (Ahat n) (endpointTolerance delta eta q0 L n) gamma h n a ≠ ⊤ ∧
      Book.Ch02.BlockPosDef (Ahat n) ∧
      BlockMatLoewnerLE E (blockScale (2 * kappaRef E) (Ahat n)) ∧
      BlockMatLoewnerLE (Ahat n)
        (blockScale (1 + endpointTolerance delta eta q0 L n) Abar) ∧
      2 * kappaRef E ≤ endpointTolerance delta eta q0 L n *
        (3 : ℝ) ^ ((gamma - g) * (h : ℝ)) := by
  intro n hn
  have hscale : BlockMatLoewnerLE
      (blockScale (1 + 6 * (3 : ℝ) ^
        (-alpha * ((n - endpointReferenceOffset A D L n : ℕ) : ℝ))) Abar)
      (blockScale (1 + endpointTolerance delta eta q0 L n) Abar) := by
    apply blockMatLoewnerLE_blockScale_mono
    · simpa only [add_comm] using add_le_add_left (herr n hn) 1
    · exact hAbar
  exact ⟨endpointWindowLength A L n, rfl, hfin n hn, hpos n hn,
    href n hn, (hupper n hn).trans hscale, hburn n hn⟩


private theorem endpoint_reference_integrability (d : ℕ)
    [NeZero d] {g : ℝ}
    {A D Qraw q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    {Nann : ℕ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hL : 0 < (A + D + 1))
    (hQpos : 1 ≤ (Qraw + 4))
    (hdagBase : HCPoly.Frozen.CoarseEllipticityDagger (triadicRebasedLaw Nann P) g E
      (triadicRebasedGauge Nann Psi) K (triadicRebasedSource Nann S))
        (hqLow : (2 + aspectRatio E * K) ^ 2 ≤ (3 : ℝ) ^ (q : ℤ))
    : (((triadicRebasedGauge Nann Psi) ((3 : ℝ) ^ ((q : ℤ) - (0 : ℤ))))⁻¹ ≤ 1 / 2) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      ((Qraw + 4) * q) ≤ endpointWindowIndex (A + D + 1) n) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      q ≤ n - endpointReferenceOffset A D (A + D + 1) n) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      ((triadicRebasedGauge Nann Psi) ((3 : ℝ) ^
        ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ))))⁻¹ ≤
          1 / 2) ∧
    (∀ n : ℕ, IsSymmetricBlockMat ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      Book.Ch02.BlockPosDef ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)) := by
  classical
  let L : ℕ := A + D + 1
  let Q : ℕ := Qraw + 4
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  let Pbase : Measure (CoeffSpace d) := triadicRebasedLaw Nann P
  let Sbase : CoeffSpace d → ℝ := triadicRebasedSource Nann S
  let Psibase : ℝ → ℝ := triadicRebasedGauge Nann Psi
  let Ahat : ℕ → BlockMat d := fun n =>
    annealedBlock Pbase
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)))
  have hhalf0 : (Psibase ((3 : ℝ) ^ ((q : ℤ) - (0 : ℤ))))⁻¹ ≤ 1 / 2 := by
    have h := inv_gauge_at_entry_add_bracket_le_half
      (mEnt := Nann) hdag hqLow
    dsimp only [Psibase, triadicRebasedGauge]
    simp only [sub_zero]
    rw [show (3 : ℝ) ^ Nann * (3 : ℝ) ^ (q : ℤ) =
      (3 : ℝ) ^ ((Nann + q : ℕ) : ℤ) by
        rw [← zpow_natCast (3 : ℝ) Nann, ← zpow_add₀ (by norm_num)]
        congr 1]
    exact h
  have hqIndex : ∀ n : ℕ, nstar ≤ n →
      q0 ≤ endpointWindowIndex L n := by
    intro n hn
    exact endpointWindowIndex_mono hL (by simpa only [nstar] using hn)
  have hinnerQ : ∀ n : ℕ, nstar ≤ n →
      q ≤ n - endpointReferenceOffset A D L n := by
    intro n hn
    have hqq0 : q ≤ q0 := by
      dsimp only [q0]
      have hm := Nat.mul_le_mul_right q hQpos
      simpa only [one_mul] using hm
    exact hqq0.trans ((hqIndex n hn).trans
      (endpoint_reference_generation_ge_index (A := A) (D := D)
        (L := L) (n := n) (by rfl)))
  have hhalf : ∀ n : ℕ, nstar ≤ n →
      (Psibase ((3 : ℝ) ^
        ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ))))⁻¹ ≤
          1 / 2 := by
    intro n hn
    let inner : ℕ := n - endpointReferenceOffset A D L n
    have hpq : (0 : ℝ) < Psibase ((3 : ℝ) ^ (q : ℤ)) :=
      zero_lt_one.trans_le (hdagBase.gauge_admissible.2 (by positivity))
    have harg : (3 : ℝ) ^ (q : ℤ) ≤
        (3 : ℝ) ^ ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by
        have hoff := endpointReferenceOffset_le
          (A := A) (D := D) (L := L) (n := n) rfl
        exact_mod_cast hinnerQ n hn)
    have hpsi := hdagBase.gauge_admissible.1
      (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (by positivity)) harg
    have hinv := inv_anti₀ hpq hpsi
    exact hinv.trans hhalf0
  have hAhatSymm : ∀ n : ℕ, IsSymmetricBlockMat (Ahat n) := by
    intro n
    dsimp only [Ahat]
    exact isSymmetricBlockMat_annealedBlock Pbase _
  have hAhatPos : ∀ n : ℕ, nstar ≤ n →
      Book.Ch02.BlockPosDef (Ahat n) := by
    intro n hn
    dsimp only [Ahat]
    exact blockPosDef_annealedBlock_of_frozen hdagBase
      ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)) (hhalf n hn)
  exact ⟨hhalf0, hqIndex, hinnerQ, hhalf, hAhatSymm, hAhatPos⟩

private theorem endpoint_radius_base_thresholds (d : ℕ)
    [NeZero d] {g eta T : ℝ}
    {A D B Qraw q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    {Nann : ℕ}
    (hT : 1 ≤ T)
    (hTthr : Real.log 2 ≤ frGaugeConst d * T ^ 2 *
      ((3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g)) - 1))
    (hB : 1 ≤ B)
    (hBbase : (2 * (A : ℝ) + (d : ℝ) * (A : ℝ) * Real.log 3) /
      frGaugeConst d + 1 ≤ (3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) * (B : ℝ)))
    (hmu : 0 < ((d : ℝ) / 2 - g))
    (hdeltaOut : (1 / 2) ∈ Set.Ioo (0 : ℝ) 1)
    (hL : 0 < (A + D + 1))
    (hstatBase : HCPoly.Frozen.IsStationaryLaw (triadicRebasedLaw Nann P))
    (hunitBase : HCPoly.Frozen.IsUnitRangeLaw (triadicRebasedLaw Nann P))
    (hdagBase : HCPoly.Frozen.CoarseEllipticityDagger (triadicRebasedLaw Nann P) g E
      (triadicRebasedGauge Nann Psi) K (triadicRebasedSource Nann S))
    (hq0 : 1 ≤ ((Qraw + 4) * q))
    (hGain : 0 < renormGain d g E)
    (hbaseInitial : T ≤
      renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g) (1 / 2) (renormGain d g E) (D * ((Qraw + 4) *
        q)) 0)
    (honeBaseInitial : 1 ≤
      renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g) (1 / 2) (renormGain d g E) (D * ((Qraw + 4) *
        q)) 0)
    (hnet : 1 ≤ ((d : ℝ) / 2 - g) * (D : ℝ) - eta)
    (hetaD : eta ≤ ((d : ℝ) / 2 - g) * (D : ℝ))
    (hqIndex : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      ((Qraw + 4) * q) ≤ endpointWindowIndex (A + D + 1) n)
    (hhalf : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      ((triadicRebasedGauge Nann Psi) ((3 : ℝ) ^
        ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ))))⁻¹ ≤
          1 / 2)
        (hA : 1 ≤ A)
    : (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      T ≤ renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
        (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n)) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      1 ≤ renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
        (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n)) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      Real.log 2 ≤ frGaugeConst d *
        renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
          (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
          (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n) ^ 2 *
            ((3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g)) - 1)) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      HasCellRenormalization (triadicRebasedLaw Nann P) (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n) g ((d : ℝ) /
        2)
        (renormGain d g E) n (endpointReferenceOffset A D (A + D + 1) n)
          (endpointWindowLength A (A + D + 1) n)) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      (3 : ℝ) ^ ((endpointWindowIndex (A + D + 1) n - ((Qraw + 4) * q) : ℕ) : ℝ) ≤
        renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
          (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
          (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n)) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      Real.log (2 * renormCellCount d (endpointWindowLength A (A + D + 1) n)) ≤
        frGaugeConst d *
          (renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
              (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
              (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n) ^
                2 *
            (3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) * ((B * ((Qraw + 4) * q)) : ℝ)) - 1)) := by
  classical
  let mu : ℝ := (d : ℝ) / 2 - g
  let deltaOut : ℝ := 1 / 2
  let L : ℕ := A + D + 1
  let Q : ℕ := Qraw + 4
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  let b : ℕ := B * q0
  let Pbase : Measure (CoeffSpace d) := triadicRebasedLaw Nann P
  let Sbase : CoeffSpace d → ℝ := triadicRebasedSource Nann S
  let Psibase : ℝ → ℝ := triadicRebasedGauge Nann Psi
  let Ahat : ℕ → BlockMat d := fun n =>
    annealedBlock Pbase
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)))
  have hbaseN : ∀ n : ℕ, nstar ≤ n →
      T ≤ renormBase g ((d : ℝ) / 2) mu
        (endpointTolerance deltaOut eta q0 L n) (renormGain d g E)
        (endpointReferenceOffset A D L n) (endpointWindowLength A L n) := by
    intro n hn
    exact hbaseInitial.trans (renormBase_endpointTolerance_mono
      hdeltaOut.1.le hGain hetaD hL (by simpa only [nstar] using hn))
  have honeBaseN : ∀ n : ℕ, nstar ≤ n →
      1 ≤ renormBase g ((d : ℝ) / 2) mu
        (endpointTolerance deltaOut eta q0 L n) (renormGain d g E)
        (endpointReferenceOffset A D L n) (endpointWindowLength A L n) :=
    fun n hn => hT.trans (hbaseN n hn)
  have hthrN : ∀ n : ℕ, nstar ≤ n →
      Real.log 2 ≤ frGaugeConst d *
        renormBase g ((d : ℝ) / 2) mu
          (endpointTolerance deltaOut eta q0 L n) (renormGain d g E)
          (endpointReferenceOffset A D L n) (endpointWindowLength A L n) ^ 2 *
            ((3 : ℝ) ^ (2 * mu) - 1) := by
    intro n hn
    have hbaseSq : T ^ 2 ≤
        renormBase g ((d : ℝ) / 2) mu
          (endpointTolerance deltaOut eta q0 L n) (renormGain d g E)
          (endpointReferenceOffset A D L n) (endpointWindowLength A L n) ^ 2 := by
      exact (sq_le_sq₀ (zero_le_one.trans hT)
        (zero_le_one.trans (hT.trans (hbaseN n hn)))).2 (hbaseN n hn)
    have hfac : 0 ≤ frGaugeConst d * ((3 : ℝ) ^ (2 * mu) - 1) := by
      have hp : 1 ≤ (3 : ℝ) ^ (2 * mu) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      exact mul_nonneg (frGaugeConst_pos d).le (sub_nonneg.mpr hp)
    have hm := mul_le_mul_of_nonneg_right hbaseSq hfac
    nlinarith only [hTthr, hm]
  have hcellN : ∀ n : ℕ, nstar ≤ n →
      HasCellRenormalization Pbase Sbase (Ahat n) g ((d : ℝ) / 2)
        (renormGain d g E) n (endpointReferenceOffset A D L n)
          (endpointWindowLength A L n) := by
    intro n hn
    rw [renormGain, ← unitRangeCellGain_eq_publicGain]
    dsimp only [Ahat]
    exact hasCellRenormalization_unitRangeCellGain_of_frozen
      (P := Pbase) (g := g) (E := E) (Psi := Psibase) (K := K) (S := Sbase)
      (n := n) (l0 := endpointReferenceOffset A D L n)
      (h := endpointWindowLength A L n) hstatBase hunitBase hdagBase
      (by
        have hoff := endpointReferenceOffset_le
          (A := A) (D := D) (L := L) (n := n) rfl
        omega)
      (by
        have hw := endpointWindowLength_le_referenceOffset A D L n
        omega)
      (hhalf n hn)
  have hgrowthN : ∀ n : ℕ, nstar ≤ n →
      (3 : ℝ) ^ ((endpointWindowIndex L n - q0 : ℕ) : ℝ) ≤
        renormBase g ((d : ℝ) / 2) mu
          (endpointTolerance deltaOut eta q0 L n) (renormGain d g E)
          (endpointReferenceOffset A D L n) (endpointWindowLength A L n) := by
    intro n hn
    exact rpow_index_growth_le_renormBase_endpoint hnet hL
      (by simpa only [nstar] using hn) honeBaseInitial
  have hbufN : ∀ n : ℕ, nstar ≤ n →
      Real.log (2 * renormCellCount d (endpointWindowLength A L n)) ≤
        frGaugeConst d *
          (renormBase g ((d : ℝ) / 2) mu
              (endpointTolerance deltaOut eta q0 L n) (renormGain d g E)
              (endpointReferenceOffset A D L n) (endpointWindowLength A L n) ^ 2 *
            (3 : ℝ) ^ (2 * mu * (b : ℝ)) - 1) := by
    intro n hn
    have hidx := hqIndex n hn
    have hgrowth := hgrowthN n hn
    rw [Nat.cast_sub hidx] at hgrowth
    have hbuf' := endpoint_varying_radius_buffer (d := d) (A := A) (B := B)
      (q0 := q0) (q := endpointWindowIndex L n) (mu := mu)
      (baseNow := renormBase g ((d : ℝ) / 2) mu
        (endpointTolerance deltaOut eta q0 L n) (renormGain d g E)
        (endpointReferenceOffset A D L n) (endpointWindowLength A L n))
      hA hq0 hidx hmu hB hBbase hgrowth
    simpa only [endpointWindowLength, b] using hbuf'
  exact ⟨hbaseN, honeBaseN, hthrN, hcellN, hgrowthN, hbufN⟩

private theorem endpoint_physical_radius_certificates (d : ℕ)
    [NeZero d] {g eta : ℝ}
    {A D B Qraw q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    {Nann : ℕ}
    (hmu : 0 < ((d : ℝ) / 2 - g))
    (hgn : g ≤ (d : ℝ) / 2)
    (hgr : g ≤ ((g + ((1 + 3 * g) / 4)) / 2))
    (hdeltaOut : (1 / 2) ∈ Set.Ioo (0 : ℝ) 1)
    (hdagBase : HCPoly.Frozen.CoarseEllipticityDagger (triadicRebasedLaw Nann P) g E
      (triadicRebasedGauge Nann Psi) K (triadicRebasedSource Nann S))
    (hq0 : 1 ≤ ((Qraw + 4) * q))
    (hGain : 0 < renormGain d g E)
    (hqIndex : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      ((Qraw + 4) * q) ≤ endpointWindowIndex (A + D + 1) n)
    (hAhatSymm : ∀ n : ℕ, IsSymmetricBlockMat ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n))
    (hAhatPos : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      Book.Ch02.BlockPosDef ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n))
    (honeBaseN : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      1 ≤ renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
        (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n))
    (hthrN : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      Real.log 2 ≤ frGaugeConst d *
        renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
          (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
          (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n) ^ 2 *
            ((3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g)) - 1))
    (hcellN : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      HasCellRenormalization (triadicRebasedLaw Nann P) (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n) g ((d : ℝ) /
        2)
        (renormGain d g E) n (endpointReferenceOffset A D (A + D + 1) n)
          (endpointWindowLength A (A + D + 1) n))
    (hbufN : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      Real.log (2 * renormCellCount d (endpointWindowLength A (A + D + 1) n)) ≤
        frGaugeConst d *
          (renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g)
              (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) (renormGain d g E)
              (endpointReferenceOffset A D (A + D + 1) n) (endpointWindowLength A (A + D + 1) n) ^
                2 *
            (3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) * ((B * ((Qraw + 4) * q)) : ℝ)) - 1))
    : (∀ n r : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      P.real {a : CoeffSpace d | (3 : ℝ) ^ (n + r + (B * ((Qraw + 4) * q))) < (fun n a =>
    (fun n =>
    renormRadius (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n)
      ((g + ((1 + 3 * g) / 4)) / 2) (endpointWindowLength A (A + D + 1) n) n) n
        (physical_scale_coeff Nann a)) n a} ≤
        Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) * (r : ℝ))))) ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      ∀ᵐ a ∂P, renormScale (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n) ((g + ((1 + 3 * g) / 4)) / 2)
        (endpointWindowLength A (A + D + 1) n) n (physical_scale_coeff Nann a) ≠ ⊤) ∧
    (∀ᵐ a ∂P, ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      renormScale (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n)
        ((g + ((1 + 3 * g) / 4)) / 2) (endpointWindowLength A (A + D + 1) n) n
          (physical_scale_coeff Nann a) ≠ ⊤) ∧
    (∀ᵐ a ∂P,
      ∀ M : ℤ, (triadicRebasedSource Nann S) (physical_scale_coeff Nann a) ≤ (3 : ℝ) ^ M →
        ∀ k : ℤ, k ≤ M → ∀ w : Fin d → ℤ,
          standardCellCenter k w ∈ centeredCube d M →
          BlockMatLoewnerLE
            (coarseBlock (standardCell d k w) (physical_scale_coeff Nann a))
            (blockScale ((3 : ℝ) ^ (g * ((M : ℝ) - (k : ℝ)))) E)) := by
  classical
  let rho : ℝ := (1 + 3 * g) / 4
  let gamma : ℝ := (g + rho) / 2
  let mu : ℝ := (d : ℝ) / 2 - g
  let deltaOut : ℝ := 1 / 2
  let L : ℕ := A + D + 1
  let Q : ℕ := Qraw + 4
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  let b : ℕ := B * q0
  let Pbase : Measure (CoeffSpace d) := triadicRebasedLaw Nann P
  let Sbase : CoeffSpace d → ℝ := triadicRebasedSource Nann S
  let Psibase : ℝ → ℝ := triadicRebasedGauge Nann Psi
  let Ahat : ℕ → BlockMat d := fun n =>
    annealedBlock Pbase
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)))
  let radiusBase : ℕ → CoeffSpace d → ℝ := fun n =>
    renormRadius Sbase (Ahat n) (endpointTolerance deltaOut eta q0 L n)
      gamma (endpointWindowLength A L n) n
  let radius : ℕ → CoeffSpace d → ℝ := fun n a =>
    radiusBase n (physical_scale_coeff Nann a)
  have hradiusTail : ∀ n r : ℕ, nstar ≤ n →
      P.real {a : CoeffSpace d | (3 : ℝ) ^ (n + r + b) < radius n a} ≤
        Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (r : ℝ)))) := by
    intro n r hn
    have hdeltaN : 0 ≤ endpointTolerance deltaOut eta q0 L n :=
      (endpointTolerance_pos (eta := eta) hdeltaOut.1).le
    have htail := measureReal_renormRadius_gt_le_varying
      (P := Pbase) (S := Sbase) (Ahat := Ahat n)
      (gamma := g) (nu := (d : ℝ) / 2) (mu := mu) (rho := gamma)
      (delta := endpointTolerance deltaOut eta q0 L n)
      (Gain := renormGain d g E) (n := n)
      (l0 := endpointReferenceOffset A D L n)
      (h := endpointWindowLength A L n) (b := b)
      (hAhatPos n hn) hGain hdeltaN (by dsimp only [mu]) hmu
      hgn hgr
      (honeBaseN n hn) (hthrN n hn) (hcellN n hn)
      (by
        dsimp only [b]
        exact Nat.mul_pos (by omega) (Nat.zero_lt_one.trans_le hq0))
      (by
        dsimp only [endpointWindowLength]
        exact Nat.mul_pos (by omega)
          (hq0.trans (hqIndex n hn)))
      (hbufN n hn) r
    have hmeas : Measurable (radiusBase n) := by
      dsimp only [radiusBase]
      exact measurable_renormRadius hdagBase.source_measurable (hAhatSymm n)
        (hAhatPos n hn) hdeltaN _ _
    rw [← measureReal_triadicRebasedLaw_upperTailEvent Nann hmeas
      ((3 : ℝ) ^ (n + r + b))]
    simpa only [Pbase, radius, radiusBase] using htail
  have hfinPhysical : ∀ n : ℕ, nstar ≤ n →
      ∀ᵐ a ∂P, renormScale Sbase (Ahat n)
        (endpointTolerance deltaOut eta q0 L n) gamma
        (endpointWindowLength A L n) n (physical_scale_coeff Nann a) ≠ ⊤ := by
    intro n hn
    have hbaseAE := ae_renormScale_ne_top (P := Pbase) (S := Sbase)
      (Ahat := Ahat n) (gamma := g) (nu := (d : ℝ) / 2) (mu := mu)
      (rho := gamma) (delta := endpointTolerance deltaOut eta q0 L n)
      (Gain := renormGain d g E) (n := n)
      (l0 := endpointReferenceOffset A D L n)
      (h := endpointWindowLength A L n)
      (hAhatPos n hn) hGain
      (endpointTolerance_pos (eta := eta) hdeltaOut.1).le
      (by dsimp only [mu]) hmu
      hgn hgr
      (honeBaseN n hn) (hthrN n hn) (hcellN n hn)
    have hpull :=
      ((CoeffSpace.triadicDilationMeasurableEquiv Nann).measurableEmbedding.ae_map_iff).1
        (by simpa only [Pbase] using! hbaseAE)
    simpa only [physical_scale_coeff_eq_triadicDilation] using! hpull
  have hfinAll : ∀ᵐ a ∂P, ∀ n : ℕ, nstar ≤ n →
      renormScale Sbase (Ahat n) (endpointTolerance deltaOut eta q0 L n)
        gamma (endpointWindowLength A L n) n (physical_scale_coeff Nann a) ≠ ⊤ := by
    rw [ae_all_iff]
    intro n
    by_cases hn : nstar ≤ n
    · exact (hfinPhysical n hn).mono fun _ ha _ => ha
    · exact _root_.Filter.Eventually.of_forall fun _ h => (hn h).elim
  have hcoarsePhysical : ∀ᵐ a ∂P,
      ∀ M : ℤ, Sbase (physical_scale_coeff Nann a) ≤ (3 : ℝ) ^ M →
        ∀ k : ℤ, k ≤ M → ∀ w : Fin d → ℤ,
          standardCellCenter k w ∈ centeredCube d M →
          BlockMatLoewnerLE
            (coarseBlock (standardCell d k w) (physical_scale_coeff Nann a))
            (blockScale ((3 : ℝ) ^ (g * ((M : ℝ) - (k : ℝ)))) E) := by
    have hpull :=
      ((CoeffSpace.triadicDilationMeasurableEquiv Nann).measurableEmbedding.ae_map_iff).1
        (by simpa only [Pbase] using! hdagBase.coarse_bound)
    simpa only [physical_scale_coeff_eq_triadicDilation] using! hpull
  exact ⟨hradiusTail, hfinPhysical, hfinAll, hcoarsePhysical⟩

private theorem endpoint_physical_stopped_row_bound (d : ℕ)
    [NeZero d] {g alpha eta : ℝ}
    {A D Qraw R q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E Abar : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    {Nann : ℕ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hAbar : IsSymmetricBlockMat Abar) (hAbarPos : Book.Ch02.BlockPosDef Abar)
    (hsandwich : ∀ j : ℕ,
      BlockMatLoewnerLE Abar (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ))) ∧
      BlockMatLoewnerLE (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ)))
        (blockScale (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) Abar))
    (heta : 0 < eta) (hetaAlpha : eta ≤ alpha)
    (hthetaR : 1 ≤ (eta / ((A + D + 1 : ℕ) : ℝ)) * (R : ℝ))
    (hqLow : (2 + aspectRatio E * K) ^ 2 ≤ (3 : ℝ) ^ (q : ℤ))
    (hg0 : 0 ≤ g)
    (hrhoGap : 0 < ((1 + 3 * g) / 4) - g)
    (hgammaRho : ((g + ((1 + 3 * g) / 4)) / 2) < ((1 + 3 * g) / 4))
    (hgamma0 : 0 ≤ ((g + ((1 + 3 * g) / 4)) / 2))
    (hgr : g ≤ ((g + ((1 + 3 * g) / 4)) / 2))
    (hdeltaOut : (1 / 2) ∈ Set.Ioo (0 : ℝ) 1)
    (hL : 0 < (A + D + 1))
    (hgeomG : 0 ≤ ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹))
    (hCblk : 0 < (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1
      - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)))
    (hCblkMain : 4 * (3 : ℝ) ^ eta * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) /
      4)) / 2))))⁻¹) ≤ (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta
      * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)))
    (hCblkFallback : 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) ≤ (1 + 48 * ((1 - (3 : ℝ)
      ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) -
      ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)))
    (hbase : 3 ≤ (2 + aspectRatio E * K))
    (hdagBase : HCPoly.Frozen.CoarseEllipticityDagger (triadicRebasedLaw Nann P) g E
      (triadicRebasedGauge Nann Psi) K (triadicRebasedSource Nann S))
    (hburnN : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      2 * kappaRef E ≤ endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n *
        (3 : ℝ) ^ ((((g + ((1 + 3 * g) / 4)) / 2) - g) * (endpointWindowLength A (A + D + 1) n :
          ℝ)))
    (hstartAnnealed : 6 * (3 : ℝ) ^ (-alpha * (((Qraw + 4) * q) : ℝ)) ≤ (1 / 2))
    (hhalf : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      ((triadicRebasedGauge Nann Psi) ((3 : ℝ) ^
        ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ))))⁻¹ ≤
          1 / 2)
    (hAhatPos : ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      Book.Ch02.BlockPosDef ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n))
    (hfinAll : ∀ᵐ a ∂P, ∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      renormScale (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n)
        ((g + ((1 + 3 * g) / 4)) / 2) (endpointWindowLength A (A + D + 1) n) n
          (physical_scale_coeff Nann a) ≠ ⊤)
    (hcoarsePhysical : ∀ᵐ a ∂P,
      ∀ M : ℤ, (triadicRebasedSource Nann S) (physical_scale_coeff Nann a) ≤ (3 : ℝ) ^ M →
        ∀ k : ℤ, k ≤ M → ∀ w : Fin d → ℤ,
          standardCellCenter k w ∈ centeredCube d M →
          BlockMatLoewnerLE
            (coarseBlock (standardCell d k w) (physical_scale_coeff Nann a))
            (blockScale ((3 : ℝ) ^ (g * ((M : ℝ) - (k : ℝ)))) E))
    : (∀ᵐ a ∂P, ∀ m : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ m → (fun m a =>
    quenched_block_row ((1 + 3 * g) / 4) Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m) m a ≤
        (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1 - (3 :
          ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)) * (1 / 2) *
          (3 : ℝ) ^ (-(eta / ((A + D + 1) : ℝ)) *
            ((m : ℝ) - (stoppingGeneration ((A + D + 1) * ((Qraw + 4) * q)) (R * q) (fun n a =>
    (fun n =>
    renormRadius (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n)
      ((g + ((1 + 3 * g) / 4)) / 2) (endpointWindowLength A (A + D + 1) n) n) n
        (physical_scale_coeff Nann a)) m a : ℝ) -
              (((A + D + 1) * ((Qraw + 4) * q)) : ℝ)))) := by
  classical
  let rho : ℝ := (1 + 3 * g) / 4
  let gamma : ℝ := (g + rho) / 2
  let deltaOut : ℝ := 1 / 2
  let L : ℕ := A + D + 1
  let theta : ℝ := eta / (L : ℝ)
  let Q : ℕ := Qraw + 4
  let geomG : ℝ := (1 - (3 : ℝ) ^ (-(rho - g)))⁻¹
  let geomGamma : ℝ := (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹
  let Cblk : ℝ := 1 + 48 * geomG + 4 * (3 : ℝ) ^ eta * geomGamma
  let base : ℝ := 2 + aspectRatio E * K
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  let qfb : ℕ := R * q
  let Pbase : Measure (CoeffSpace d) := triadicRebasedLaw Nann P
  let Sbase : CoeffSpace d → ℝ := triadicRebasedSource Nann S
  let Psibase : ℝ → ℝ := triadicRebasedGauge Nann Psi
  let Ahat : ℕ → BlockMat d := fun n =>
    annealedBlock Pbase
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)))
  let radiusBase : ℕ → CoeffSpace d → ℝ := fun n =>
    renormRadius Sbase (Ahat n) (endpointTolerance deltaOut eta q0 L n)
      gamma (endpointWindowLength A L n) n
  let radius : ℕ → CoeffSpace d → ℝ := fun n a =>
    radiusBase n (physical_scale_coeff Nann a)
  let Brow : ℕ → CoeffSpace d → ℝ := fun m a =>
    quenched_block_row rho Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m
  have hrowDecay : ∀ᵐ a ∂P, ∀ m : ℕ, nstar ≤ m → Brow m a ≤
        Cblk * deltaOut *
          (3 : ℝ) ^ (-theta *
            ((m : ℝ) - (stoppingGeneration nstar qfb radius m a : ℝ) -
              (nstar : ℝ))) := by
    filter_upwards [hfinAll, hcoarsePhysical] with a hfin hcoarse
    intro m hm
    change quenched_block_row rho Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m ≤ _
    rw [quenched_block_row_max_one_source]
    have hsourceEq : Sbase (physical_scale_coeff Nann a) =
        S a / (3 : ℝ) ^ Nann :=
      triadicRebasedSource_physical_scale_coeff Nann S a
    rw [← hsourceEq]
    apply quenched_block_row_le_stoppingGeneration_of_endpoint_family
      (g := g) (gamma := gamma) (rho := rho) (delta := deltaOut)
      (eta := eta) (Cblk := Cblk) (E := E) (Abar := Abar)
      (S := Sbase) (Ahat := Ahat) (radius := radiusBase)
      (nstar := nstar) (qfb := qfb) (q0 := q0) (A := A) (L := L)
      (a := physical_scale_coeff Nann a) rfl hgamma0
      hgr hgammaRho hdeltaOut.1 heta hL
      hAbar hAbarPos hcoarse (fun _ _ => rfl) ?_ hdeltaOut.2.le hCblk
      (by simpa only [geomGamma] using hCblkMain) ?_ m hm
    · apply endpoint_window_certificate (D := D) (alpha := alpha)
        (a := physical_scale_coeff Nann a) hfin hAhatPos
      · intro n hn
        simpa only [Ahat] using
          blockMatLoewnerLE_blockScale_annealedBlock_reference hdagBase
            ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ))
            (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdagBase _) (hhalf n hn)
      · intro n hn
        let inner : ℕ := n - endpointReferenceOffset A D L n
        have hsand := (hsandwich inner).2
        have hcov : Ahat n = annealedBlock P
            (centeredCube d ((Nann + inner : ℕ) : ℤ)) := by
          have hoff := endpointReferenceOffset_le
            (A := A) (D := D) (L := L) (n := n) rfl
          dsimp only [Ahat, Pbase, inner]
          rw [annealedBlock_triadicRebasedLaw]
          congr 2
          push_cast
          rw [Nat.cast_sub hoff]
        rwa [← hcov] at hsand
      · intro n hn
        exact annealed_error_le_endpointTolerance
          (q0 := q0) (A := A) (D := D) (L := L) (n := n)
          hdeltaOut.1.le heta.le hetaAlpha (show L = A + D + 1 by rfl)
          (by simpa only [nstar] using hn) hstartAnnealed
      · exact hburnN
      · exact hAbarPos
    · intro m' hm' hsource
      let inner : ℕ := nstar - endpointReferenceOffset A D L nstar
      have href := blockMatLoewnerLE_blockScale_annealedBlock_reference hdagBase
        ((nstar : ℤ) - (endpointReferenceOffset A D L nstar : ℤ))
        (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdagBase _)
        (hhalf nstar le_rfl)
      have hcomp0 : BlockMatLoewnerLE (Ahat nstar)
          (blockScale (1 + deltaOut) Abar) := by
        have herr := annealed_error_le_endpointTolerance
          (q0 := q0) (A := A) (D := D) (L := L) (n := nstar)
          hdeltaOut.1.le heta.le hetaAlpha (show L = A + D + 1 by rfl) le_rfl ?_
        · have hsand := (hsandwich inner).2
          have htol : endpointTolerance deltaOut eta q0 L nstar = deltaOut := by
            simp only [endpointTolerance, nstar, endpointWindowIndex_mul_stride L q0 hL,
              Nat.sub_self, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
          rw [htol] at herr
          have hcov : Ahat nstar = annealedBlock P
              (centeredCube d ((Nann + inner : ℕ) : ℤ)) := by
            have hoff := endpointReferenceOffset_le
              (A := A) (D := D) (L := L) (n := nstar) rfl
            dsimp only [Ahat, Pbase, inner]
            rw [annealedBlock_triadicRebasedLaw]
            congr 2
            push_cast
            rw [Nat.cast_sub hoff]
          rw [← hcov] at hsand
          have hscale : BlockMatLoewnerLE
              (blockScale (1 + 6 * (3 : ℝ) ^
                (-alpha * ((nstar - endpointReferenceOffset A D L nstar : ℕ) : ℝ))) Abar)
              (blockScale (1 + deltaOut) Abar) := by
            apply blockMatLoewnerLE_blockScale_mono
            · simpa only [add_comm] using add_le_add_left herr 1
            · exact hAbarPos
          exact hsand.trans hscale
        · exact hstartAnnealed
      have hfb := quenched_block_row_le_fallback
        (g := g) (rho := rho) (eps := deltaOut) (E := E)
        (Ahat := Ahat nstar) (Abar := Abar) (S := Sbase)
        (a := physical_scale_coeff Nann a) (m := m') hg0
        (by linarith only [hrhoGap])
        (⟨hdeltaOut.1.le, hdeltaOut.2.le⟩ : deltaOut ∈ Set.Icc (0 : ℝ) 1)
        hAbar hAbarPos
        (zero_le_one.trans (Initialization.one_le_kappaRef hdag.refBlock_isSymm
          hdag.refBlock_posDef (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)))
        (by simpa only [Ahat] using href) hcomp0 hcoarse hsource
      have hbaseq : base ≤ (3 : ℝ) ^ q := by
        have hbSq : base ≤ base ^ 2 := by
          have hb1 : 1 ≤ base := (by norm_num : (1 : ℝ) ≤ 3).trans hbase
          nlinarith only [hb1]
        simpa only [zpow_natCast] using hbSq.trans hqLow
      apply endpoint_fallback_scalar_bound hdag (base := base) (geomG := geomG)
        (Cblk := Cblk) (delta := deltaOut) (theta := theta)
        (q := q) (R := R) (qfb := qfb)
      · rfl
      · exact hbaseq
      · rfl
      · exact hgeomG
      · exact hCblkFallback
      · rfl
      · exact hthetaR
      · simpa only [geomG] using hfb
  exact hrowDecay

private theorem endpoint_initial_renormalization_base (d : ℕ)
    [NeZero d] {g T : ℝ}
    {D Qraw q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hT : 1 ≤ T)
    (hDcoef : 0 ≤ ((d : ℝ) / 2 - g) * (D : ℝ) - ((d : ℝ) / 2 - g) - 1)
    (hDbase : (192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
      (1 + renormShift d)) * T / (1 / 2 : ℝ) ≤
      (3 : ℝ) ^ (((d : ℝ) / 2 - g) * (D : ℝ) - ((d : ℝ) / 2 - g) - 1))
    (hmu : 0 < ((d : ℝ) / 2 - g))
    (hdeltaOut : (1 / 2) ∈ Set.Ioo (0 : ℝ) 1)
    (hbase : 3 ≤ (2 + aspectRatio E * K))
    (hq0 : 1 ≤ ((Qraw + 4) * q))
    (hqBase : (2 + aspectRatio E * K) ≤ (3 : ℝ) ^ (((Qraw + 4) * q) : ℕ))
    (hGain : 0 < renormGain d g E)
    : (renormGain d g E ≤ (192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
    (1 + renormShift d)) * (2 + aspectRatio E * K)) ∧
    ((192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
    (1 + renormShift d)) * T / (1 / 2) * (2 + aspectRatio E * K) ≤
      (3 : ℝ) ^ (((d : ℝ) / 2 - g) * ((D * ((Qraw + 4) * q) : ℕ) : ℝ) - ((d : ℝ) / 2 - g))) ∧
    (T ≤
      renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g) (1 / 2) (renormGain d g E) (D * ((Qraw + 4) *
        q)) 0) ∧
    (1 ≤
      renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g) (1 / 2) (renormGain d g E) (D * ((Qraw + 4) *
        q)) 0) := by
  classical
  let mu : ℝ := (d : ℝ) / 2 - g
  let deltaOut : ℝ := 1 / 2
  let G0 : ℝ := 192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
    (1 + renormShift d)
  let Q : ℕ := Qraw + 4
  let base : ℝ := 2 + aspectRatio E * K
  let q0 : ℕ := Q * q
  have hGainBound : renormGain d g E ≤ G0 * base := by
    have hkappa := Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
    have hK1 : 1 ≤ K := le_of_lt hdag.one_lt_growthWitness
    have haspect0 : 0 ≤ aspectRatio E := zero_le_one.trans
      (one_le_aspectRatio_of_coarseEllipticityDagger hdag)
    have haspectBase : aspectRatio E ≤ base := by
      dsimp only [base]
      nlinarith only [hK1, haspect0]
    have hkbase : kappaRef E ≤ 6 * base :=
      hkappa.trans (mul_le_mul_of_nonneg_left haspectBase (by norm_num))
    have hfactor : 0 ≤ 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g *
        frThreshold d * (1 + renormShift d) := by
      have hshift : 0 ≤ renormShift d := renormShift_nonneg d
      have hfr : 0 ≤ frThreshold d := (frThreshold_pos d).le
      positivity
    rw [renormGain]
    dsimp only [G0]
    have hm := mul_le_mul_of_nonneg_left hkbase hfactor
    nlinarith only [hm]
  have hDpow : G0 * T / deltaOut * base ≤
      (3 : ℝ) ^ (mu * ((D * q0 : ℕ) : ℝ) - mu) := by
    apply mul_base_le_rpow_mul_index hmu hq0 hDcoef hDbase
      (le_trans zero_le_one (le_trans (by norm_num) hbase))
    exact hqBase
  have hbaseInitial : T ≤
      renormBase g ((d : ℝ) / 2) mu deltaOut (renormGain d g E) (D * q0) 0 := by
    apply T_le_renormBase_of_gain_bound hT hdeltaOut.1 hGain hGainBound hDpow
    dsimp only [mu]
    push_cast
    ring
  have honeBaseInitial : 1 ≤
      renormBase g ((d : ℝ) / 2) mu deltaOut (renormGain d g E) (D * q0) 0 :=
    hT.trans hbaseInitial
  exact ⟨hGainBound, hDpow, hbaseInitial, honeBaseInitial⟩

private theorem endpoint_initial_window_error_bounds (d : ℕ)
    [NeZero d] {g alpha eta : ℝ}
     (halpha : 0 < alpha)
    {A D Qraw q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hAcoef : 0 ≤ (((g + (1 + 3 * g) / 4) / 2) - g) * (A : ℝ) - 1)
    (hq : 1 ≤ q) (hqLow : (2 + aspectRatio E * K) ^ 2 ≤ (3 : ℝ) ^ (q : ℤ))
    (hetaGapA : eta ≤ (((g + (1 + 3 * g) / 4) / 2) - g) * (A : ℝ))
    (hdeltaOut : (1 / 2) ∈ Set.Ioo (0 : ℝ) 1)
    (hL : 0 < (A + D + 1))
    (hQ : 4 ≤ (Qraw + 4))
    (hQannealed : 12 ≤ (3 : ℝ) ^ (alpha * ((Qraw + 4) : ℝ)))
    (hbase : 3 ≤ (2 + aspectRatio E * K))
    : (2 * kappaRef E ≤
      (1 / 2) * (3 : ℝ) ^ ((((g + ((1 + 3 * g) / 4)) / 2) - g) * ((A * ((Qraw + 4) * q) : ℕ) : ℝ)))
        ∧
    (∀ n : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      2 * kappaRef E ≤ endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n *
        (3 : ℝ) ^ ((((g + ((1 + 3 * g) / 4)) / 2) - g) * (endpointWindowLength A (A + D + 1) n :
          ℝ))) ∧
    (12 ≤ (3 : ℝ) ^ (alpha * (((Qraw + 4) * q) : ℝ))) ∧
    (6 * (3 : ℝ) ^ (-alpha * (((Qraw + 4) * q) : ℝ)) ≤ (1 / 2)) := by
  classical
  let rho : ℝ := (1 + 3 * g) / 4
  let gamma : ℝ := (g + rho) / 2
  let deltaOut : ℝ := 1 / 2
  let L : ℕ := A + D + 1
  let Q : ℕ := Qraw + 4
  let base : ℝ := 2 + aspectRatio E * K
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  have hburnStart : 2 * kappaRef E ≤
      deltaOut * (3 : ℝ) ^ ((gamma - g) * ((A * q0 : ℕ) : ℝ)) := by
    have hbaseq : base ≤ (3 : ℝ) ^ q := by
      have hbSq : base ≤ base ^ 2 := by
        have hb1 : 1 ≤ base := (by norm_num : (1 : ℝ) ≤ 3).trans hbase
        nlinarith only [hb1]
      simpa only [zpow_natCast] using hbSq.trans hqLow
    have hgapA1 : 1 ≤ (gamma - g) * (A : ℝ) := by
      linarith only [hAcoef]
    simpa only [deltaOut, q0] using endpoint_initial_burn hdag rfl hbaseq
      hgapA1 hq hQ
  have hburnN : ∀ n : ℕ, nstar ≤ n →
      2 * kappaRef E ≤ endpointTolerance deltaOut eta q0 L n *
        (3 : ℝ) ^ ((gamma - g) * (endpointWindowLength A L n : ℝ)) := by
    intro n hn
    exact old_cell_burn_le_endpointTolerance hdeltaOut.1.le hetaGapA hL
      (by simpa only [nstar] using hn) hburnStart
  have hQalpha : 12 ≤ (3 : ℝ) ^ (alpha * (q0 : ℝ)) := by
    have hq0Q : (Q : ℝ) ≤ (q0 : ℝ) := by
      dsimp only [q0]
      push_cast
      nlinarith only [(show (1 : ℝ) ≤ q by exact_mod_cast hq)]
    exact hQannealed.trans (Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3)
      (mul_le_mul_of_nonneg_left hq0Q halpha.le))
  have hstartAnnealed : 6 * (3 : ℝ) ^ (-alpha * (q0 : ℝ)) ≤ deltaOut := by
    have hp : 0 < (3 : ℝ) ^ (alpha * (q0 : ℝ)) := by positivity
    rw [show (3 : ℝ) ^ (-alpha * (q0 : ℝ)) =
      ((3 : ℝ) ^ (alpha * (q0 : ℝ)))⁻¹ by
        rw [show -alpha * (q0 : ℝ) = -(alpha * (q0 : ℝ)) by ring,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]]
    dsimp only [deltaOut]
    exact (div_le_iff₀ hp).2 (by nlinarith only [hQalpha])
  exact ⟨hburnStart, hburnN, hQalpha, hstartAnnealed⟩

private theorem endpoint_row_summability_and_measurability (d : ℕ)
    [NeZero d] {g eta : ℝ}
    {A D B Qraw R q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E Abar : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    {Nann : ℕ}
    (hAbar : IsSymmetricBlockMat Abar) (hAbarPos : Book.Ch02.BlockPosDef Abar)
    (hg0 : 0 ≤ g)
    (hrhoGap : 0 < ((1 + 3 * g) / 4) - g)
    (hmu : 0 < ((d : ℝ) / 2 - g))
    (hdeltaOut : (1 / 2) ∈ Set.Ioo (0 : ℝ) 1)
    (htheta : 0 < (eta / ((A + D + 1) : ℝ)))
    (hCblk : 0 < (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1
      - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)))
    (hdagBase : HCPoly.Frozen.CoarseEllipticityDagger (triadicRebasedLaw Nann P) g E
      (triadicRebasedGauge Nann Psi) K (triadicRebasedSource Nann S))
    (hrowDecay : ∀ᵐ a ∂P, ∀ m : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ m → (fun m a =>
    quenched_block_row ((1 + 3 * g) / 4) Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m) m a ≤
        (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1 - (3 :
          ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)) * (1 / 2) *
          (3 : ℝ) ^ (-(eta / ((A + D + 1) : ℝ)) *
            ((m : ℝ) - (stoppingGeneration ((A + D + 1) * ((Qraw + 4) * q)) (R * q) (fun n a =>
    (fun n =>
    renormRadius (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n)
      ((g + ((1 + 3 * g) / 4)) / 2) (endpointWindowLength A (A + D + 1) n) n) n
        (physical_scale_coeff Nann a)) m a : ℝ) -
              (((A + D + 1) * ((Qraw + 4) * q)) : ℝ))))
    (hradiusTail : ∀ n r : ℕ, ((A + D + 1) * ((Qraw + 4) * q)) ≤ n →
      P.real {a : CoeffSpace d | (3 : ℝ) ^ (n + r + (B * ((Qraw + 4) * q))) < (fun n a =>
    (fun n =>
    renormRadius (triadicRebasedSource Nann S) ((fun n =>
    annealedBlock (triadicRebasedLaw Nann P)
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D (A + D + 1) n : ℤ)))) n)
        (endpointTolerance (1 / 2) eta ((Qraw + 4) * q) (A + D + 1) n)
      ((g + ((1 + 3 * g) / 4)) / 2) (endpointWindowLength A (A + D + 1) n) n) n
        (physical_scale_coeff Nann a)) n a} ≤
        Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) * (r : ℝ)))))
    : (∀ m a, 0 ≤ (fun m a =>
    quenched_block_row ((1 + 3 * g) / 4) Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m) m a) ∧
    (∀ᵐ a ∂P, ∀ k : ℕ, Summable fun j : ℕ =>
      (3 : ℝ) ^ ((eta / ((A + D + 1) : ℝ)) / 2 * (j : ℝ)) * (fun m a =>
    quenched_block_row ((1 + 3 * g) / 4) Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m) (k + j) a) ∧
    (∀ m, Measurable ((fun m a =>
    quenched_block_row ((1 + 3 * g) / 4) Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m) m)) := by
  classical
  let rho : ℝ := (1 + 3 * g) / 4
  let gamma : ℝ := (g + rho) / 2
  let mu : ℝ := (d : ℝ) / 2 - g
  let deltaOut : ℝ := 1 / 2
  let L : ℕ := A + D + 1
  let theta : ℝ := eta / (L : ℝ)
  let Q : ℕ := Qraw + 4
  let geomG : ℝ := (1 - (3 : ℝ) ^ (-(rho - g)))⁻¹
  let geomGamma : ℝ := (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹
  let Cblk : ℝ := 1 + 48 * geomG + 4 * (3 : ℝ) ^ eta * geomGamma
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  let qfb : ℕ := R * q
  let b : ℕ := B * q0
  let Pbase : Measure (CoeffSpace d) := triadicRebasedLaw Nann P
  let Sbase : CoeffSpace d → ℝ := triadicRebasedSource Nann S
  let Psibase : ℝ → ℝ := triadicRebasedGauge Nann Psi
  let Ahat : ℕ → BlockMat d := fun n =>
    annealedBlock Pbase
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)))
  let radiusBase : ℕ → CoeffSpace d → ℝ := fun n =>
    renormRadius Sbase (Ahat n) (endpointTolerance deltaOut eta q0 L n)
      gamma (endpointWindowLength A L n) n
  let radius : ℕ → CoeffSpace d → ℝ := fun n a =>
    radiusBase n (physical_scale_coeff Nann a)
  let Brow : ℕ → CoeffSpace d → ℝ := fun m a =>
    quenched_block_row rho Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m
  have hrowNonnegative : ∀ m a, 0 ≤ Brow m a := fun m a => by
    change 0 ≤ quenched_block_row rho Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m
    exact quenched_block_row_nonneg (rho := rho)
      (sourceScale := max 1 (S a / (3 : ℝ) ^ Nann))
      (a := physical_scale_coeff Nann a) hAbar hAbarPos m
  have hsummable : ∀ᵐ a ∂P, ∀ k : ℕ, Summable fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * Brow (k + j) a :=
    ae_summable_weighted_row_of_stoppingGeneration
      (P := P) (nstar := nstar) (qfb := qfb) (b := b) (R := radius)
      (B := Brow)
      (theta := theta) (mu := mu) (cd := frGaugeConst d)
      (delta := deltaOut) (Cblk := Cblk)
      htheta hmu (frGaugeConst_pos d) hdeltaOut.1 hCblk hradiusTail hrowDecay
        hrowNonnegative
  have hBmeas : ∀ m, Measurable (Brow m) := by
    intro m
    have hbaseMeas : Measurable (fun a => quenched_block_row rho Abar
        (max 1 (Sbase a)) a m) :=
      measurable_quenched_block_row (rho := rho)
        (sourceScale := fun a => max 1 (Sbase a)) hAbar hAbarPos
        (measurable_const.max hdagBase.source_measurable)
        (by linarith only [hrhoGap, hg0]) m
    have hpull := hbaseMeas.comp (measurable_physical_scale_coeff Nann)
    change Measurable (fun a => quenched_block_row rho Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m)
    change Measurable (fun a => quenched_block_row rho Abar
      (max 1 (Sbase (physical_scale_coeff Nann a)))
        (physical_scale_coeff Nann a) m) at hpull
    convert hpull using 1
    funext a
    rw [show Sbase (physical_scale_coeff Nann a) = S a / (3 : ℝ) ^ Nann by
      exact triadicRebasedSource_physical_scale_coeff Nann S a]
  exact ⟨hrowNonnegative, hsummable, hBmeas⟩

private theorem endpoint_geometric_row_constants
    {g eta : ℝ}
    (hrhoGap : 0 < ((1 + 3 * g) / 4) - g)
    (hgammaRho : ((g + ((1 + 3 * g) / 4)) / 2) < ((1 + 3 * g) / 4))
    : (0 ≤ ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹)) ∧
    (0 ≤ ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)) ∧
    (0 < (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1 - (3 :
      ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹))) ∧
    (4 * (3 : ℝ) ^ eta * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹)
      ≤ (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1 - (3 :
      ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3 * g) / 4)) / 2))))⁻¹))) ∧
    (48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - g)))⁻¹) ≤ (1 + 48 * ((1 - (3 : ℝ) ^ (-(((1 + 3 *
      g) / 4) - g)))⁻¹) + 4 * (3 : ℝ) ^ eta * ((1 - (3 : ℝ) ^ (-(((1 + 3 * g) / 4) - ((g + ((1 + 3
      * g) / 4)) / 2))))⁻¹))) := by
  classical
  let rho : ℝ := (1 + 3 * g) / 4
  let gamma : ℝ := (g + rho) / 2
  let geomG : ℝ := (1 - (3 : ℝ) ^ (-(rho - g)))⁻¹
  let geomGamma : ℝ := (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹
  have hgeomG : 0 ≤ geomG := by
    dsimp only [geomG]
    apply inv_nonneg.2
    have hp : (3 : ℝ) ^ (-(rho - g)) < 1 := by
      rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
      exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith only [hrhoGap])
    linarith only [hp]
  have hgeomGamma : 0 ≤ geomGamma := by
    dsimp only [geomGamma]
    apply inv_nonneg.2
    have hp : (3 : ℝ) ^ (-(rho - gamma)) < 1 := by
      rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
      exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith only [hgammaRho])
    linarith only [hp]
  let Cblk : ℝ := 1 + 48 * geomG + 4 * (3 : ℝ) ^ eta * geomGamma
  have hCblk : 0 < Cblk := by
    dsimp only [Cblk]
    positivity
  have hCblkMain : 4 * (3 : ℝ) ^ eta * geomGamma ≤ Cblk := by
    dsimp only [Cblk]
    nlinarith only [hgeomG]
  have hCblkFallback : 48 * geomG ≤ Cblk := by
    dsimp only [Cblk]
    have hp : 0 ≤ (3 : ℝ) ^ eta := by positivity
    nlinarith only [hgeomGamma, hp, mul_nonneg hp hgeomGamma]
  exact ⟨hgeomG, hgeomGamma, hCblk, hCblkMain, hCblkFallback⟩

private theorem endpoint_threshold_and_polynomial_costs (d : ℕ)
    [NeZero d] {g eta Bconst : ℝ}
    {A D B Qraw R Nfix q : ℕ}
    {E : BlockMat d} {K : ℝ}
    {theta mu Cblk : ℝ}
    (hBconst : 1 ≤ Bconst)
    (hlowFix : (0 : ℝ) + 0 + 1 + rowSplitOffset theta Cblk ≤ (Nfix : ℝ) - 0)
    (hgainFix : Real.log 2 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * mu * ((Nfix : ℝ) - 0 - badTailOffset theta Cblk 0 0)) *
        ((3 : ℝ) ^ (mu / 2) - 1))
    (habsFix : 2 * Real.log 4 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * mu * ((Nfix : ℝ) - 0 - badTailOffset theta Cblk 0 0)))
    (hrelFix : (3 : ℝ) ^ (2 * mu * (0 + badTailOffset theta Cblk 0 0 - (Nfix : ℝ))) ≤
      frGaugeConst d / 2 * Bconst ^ (2 * mu))
    (hqCost : (3 : ℝ) ^ q ≤ (2 + aspectRatio E * K) ^ (4 : ℝ))
    (hbase : 3 ≤ (2 + aspectRatio E * K))
    : (((R * q) : ℝ) + ((B * ((Qraw + 4) * q)) : ℝ) + 1 +
      rowSplitOffset (eta / ((A + D + 1) : ℝ)) Cblk ≤ ((((A + D + 1) * ((Qraw + 4) * q)) + (R * q)
        + (B * ((Qraw + 4) * q)) + Nfix) : ℝ) - (((A + D + 1) * ((Qraw + 4) * q)) : ℝ)) ∧
    (Real.log 2 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) * (((((A + D + 1) * ((Qraw + 4) * q)) + (R * q) + (B *
        ((Qraw + 4) * q)) + Nfix) : ℝ) - (((A + D + 1) * ((Qraw + 4) * q)) : ℝ) -
        badTailOffset (eta / ((A + D + 1) : ℝ)) Cblk (R * q) (B * ((Qraw + 4) * q)))) * ((3 : ℝ) ^
          (((d : ℝ) / 2 - g) / 2) - 1)) ∧
    (2 * Real.log 4 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) * (((((A + D + 1) * ((Qraw + 4) * q)) + (R * q) + (B *
        ((Qraw + 4) * q)) + Nfix) : ℝ) - (((A + D + 1) * ((Qraw + 4) * q)) : ℝ) -
        badTailOffset (eta / ((A + D + 1) : ℝ)) Cblk (R * q) (B * ((Qraw + 4) * q))))) ∧
    ((3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g) *
      ((((A + D + 1) * ((Qraw + 4) * q)) : ℝ) + badTailOffset (eta / ((A + D + 1) : ℝ)) Cblk (R *
        q) (B * ((Qraw + 4) * q)) - ((((A + D + 1) * ((Qraw + 4) * q)) + (R * q) + (B * ((Qraw + 4)
        * q)) + Nfix) : ℝ))) ≤
      frGaugeConst d / 2 * Bconst ^ (2 * ((d : ℝ) / 2 - g))) ∧
    ((((A + D + 1) * ((Qraw + 4) * q)) + (R * q) + (B * ((Qraw + 4) * q)) + Nfix) = ((A + D + 1) *
      (Qraw + 4) + R + B * (Qraw + 4)) * q + Nfix) ∧
    ((3 : ℝ) ^ (((A + D + 1) * ((Qraw + 4) * q)) + (R * q) + (B * ((Qraw + 4) * q)) + Nfix) ≤ (2 +
      aspectRatio E * K) ^ ((4 * ((A + D + 1) * (Qraw + 4) + R + B * (Qraw + 4)) + Nfix : ℕ))) ∧
    (Bconst ≤ (2 + aspectRatio E * K) ^ (Real.logb 3 Bconst)) := by
  classical
  let mu : ℝ := (d : ℝ) / 2 - g
  let L : ℕ := A + D + 1
  let theta : ℝ := eta / (L : ℝ)
  let Q : ℕ := Qraw + 4
  let Ccoeff : ℕ := L * Q + R + B * Q
  let C1 : ℝ := (4 * Ccoeff + Nfix : ℕ)
  let C2 : ℝ := Real.logb 3 Bconst
  let base : ℝ := 2 + aspectRatio E * K
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  let qfb : ℕ := R * q
  let b : ℕ := B * q0
  let N0 : ℕ := nstar + qfb + b + Nfix
  have hthresholdLow : (qfb : ℝ) + (b : ℝ) + 1 +
      rowSplitOffset theta Cblk ≤ (N0 : ℝ) - (nstar : ℝ) := by
    have hlow := hlowFix
    norm_num at hlow
    dsimp only [N0]
    push_cast
    linarith only [hlow]
  have hthresholdGain : Real.log 2 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)) * ((3 : ℝ) ^ (mu / 2) - 1) := by
    convert hgainFix using 1
    all_goals simp only [N0, badTailOffset, Nat.cast_add, Nat.cast_zero]
    all_goals ring_nf
  have hthresholdAbs : 2 * Real.log 4 ≤ frGaugeConst d *
      (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)) := by
    convert habsFix using 1
    all_goals simp only [N0, badTailOffset, Nat.cast_add, Nat.cast_zero]
    all_goals ring_nf
  have hnormalizerRel : (3 : ℝ) ^ (2 * mu *
      ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ))) ≤
      frGaugeConst d / 2 * Bconst ^ (2 * mu) := by
    convert hrelFix using 1
    all_goals simp only [N0, badTailOffset, Nat.cast_add, Nat.cast_zero, zero_add]
    all_goals ring_nf
  have hN0eq : N0 = Ccoeff * q + Nfix := by
    dsimp only [N0, nstar, qfb, b, q0, Ccoeff, L]
    ring
  have hgenCost : (3 : ℝ) ^ N0 ≤ base ^ C1 := by
    rw [hN0eq]
    simpa only [C1] using three_pow_affine_index_le hbase hqCost
  have hnormCost : Bconst ≤ base ^ C2 := by
    exact endpoint_fixed_normalizer_cost hbase hBconst
  exact ⟨hthresholdLow, hthresholdGain, hthresholdAbs, hnormalizerRel, hN0eq, hgenCost, hnormCost⟩

private theorem endpoint_bracket_and_gain_bounds (d : ℕ)
    [NeZero d] {g : ℝ}
    {Qraw q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hqLow : (2 + aspectRatio E * K) ^ 2 ≤ (3 : ℝ) ^ (q : ℤ))
    (hQpos : 1 ≤ (Qraw + 4))
    (hbase : 3 ≤ (2 + aspectRatio E * K))
        (hq : 1 ≤ q)
    : (1 ≤ ((Qraw + 4) * q)) ∧
    ((2 + aspectRatio E * K) ≤ (3 : ℝ) ^ (((Qraw + 4) * q) : ℕ)) ∧
    (0 < renormGain d g E) := by
  classical
  let Q : ℕ := Qraw + 4
  let base : ℝ := 2 + aspectRatio E * K
  let q0 : ℕ := Q * q
  have hq0 : 1 ≤ q0 := by
    dsimp only [q0]
    exact Nat.mul_pos (by omega) (by omega)
  have hqBase : base ≤ (3 : ℝ) ^ (q0 : ℕ) := by
    have hbaseSq : base ≤ base ^ 2 := by
      have hb1 : 1 ≤ base := le_trans (by norm_num) hbase
      nlinarith only [hb1]
    have hbq : base ≤ (3 : ℝ) ^ q := by
      simpa only [zpow_natCast] using hbaseSq.trans hqLow
    have hqq0 : q ≤ q0 := by
      dsimp only [q0]
      have := Nat.mul_le_mul_right q hQpos
      simpa only [one_mul] using this
    exact hbq.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hqq0)
  have hGain : 0 < renormGain d g E :=
    renormGain_pos hdag.refBlock_isSymm hdag.refBlock_posDef
      (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
  exact ⟨hq0, hqBase, hGain⟩
/-- The endpoint-relative renormalization family supplies the complete datum
consumed by the coupled witness assembly. -/
theorem exists_coupledWitnessEngineData_of_endpoint (d : ℕ) (hd : 2 ≤ d) :
    ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ alpha : ℝ, 0 < alpha →
      ∃ Cmix theta deltaOut : ℝ,
        0 < Cmix ∧ 0 < theta ∧ deltaOut ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
          (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
          (Abar : BlockMat d) (Nann : ℕ),
          IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
          HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
          IsSymmetricBlockMat Abar →
          Book.Ch02.BlockPosDef Abar →
          (∀ j : ℕ, annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
            (3 : ℝ) ^ (-alpha * (j : ℝ))) →
          (∀ j : ℕ,
            BlockMatLoewnerLE Abar
                (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ))) ∧
              BlockMatLoewnerLE
                (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ)))
                (blockScale (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) Abar)) →
          Nonempty (CoupledWitnessEngineData P g E Psi K S Abar Nann
            theta deltaOut Cmix) := by
  let : NeZero d := ⟨by omega⟩
  intro g hg alpha halpha
  let rho : ℝ := (1 + 3 * g) / 4
  let gamma : ℝ := (g + rho) / 2
  let mu : ℝ := (d : ℝ) / 2 - g
  let deltaOut : ℝ := 1 / 2
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hrhoGap : 0 < rho - g := by
    dsimp only [rho]
    linarith only [hg1]
  have hgammaGap : 0 < gamma - g := by
    dsimp only [gamma]
    linarith only [hrhoGap]
  have hgammaRho : gamma < rho := by
    dsimp only [gamma]
    linarith only [hrhoGap]
  have hgamma0 : 0 ≤ gamma := by
    dsimp only [gamma, rho]
    linarith only [hg0]
  have hmu : 0 < mu := by
    dsimp only [mu]
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR, hg1]
  have hgn : g ≤ (d : ℝ) / 2 := by
    dsimp only [mu] at hmu
    linarith only [hmu]
  have hgr : g ≤ gamma := by linarith only [hgammaGap]
  have hdeltaOut : deltaOut ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp only [deltaOut]
    norm_num
  let G0 : ℝ := 192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
    (1 + renormShift d)
  have hG0 : 0 < G0 := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hshift : 0 ≤ renormShift d := renormShift_nonneg d
    have hfr : 0 < frThreshold d := frThreshold_pos d
    dsimp only [G0]
    positivity
  obtain ⟨T, A, D, B, hT, hTthr, hA, hAcoef, hAbase,
      hD, hDcoef, hDbase, hB, hBbase⟩ :=
    exists_renormalization_parameters d hgammaGap hmu hdeltaOut.1
      hdeltaOut.2 hG0
  obtain ⟨eta, heta, hetaAlpha, hetaMu, hetaGapA⟩ :=
    exists_endpoint_eta halpha hgammaGap hmu hA
  let L : ℕ := A + D + 1
  have hL : 0 < L := by dsimp only [L]; omega
  let theta : ℝ := eta / (L : ℝ)
  have htheta : 0 < theta := by
    dsimp only [theta]
    positivity
  obtain ⟨Qraw, hQraw⟩ := exists_shift_of_pos halpha (by norm_num : (0 : ℝ) < 12)
  let Q : ℕ := Qraw + 4
  have hQ : 4 ≤ Q := by dsimp only [Q]; omega
  have hQpos : 1 ≤ Q := le_trans (by omega) hQ
  have hQannealed : 12 ≤ (3 : ℝ) ^ (alpha * (Q : ℝ)) := by
    have hmono : (3 : ℝ) ^ (alpha * (Qraw : ℝ)) ≤
        (3 : ℝ) ^ (alpha * (Q : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      have hcast : (Qraw : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show Qraw ≤ Q by simp [Q])
      exact mul_le_mul_of_nonneg_left hcast halpha.le
    exact hQraw.trans hmono
  obtain ⟨R, hR, hthetaR⟩ := exists_nat_mul_ge_one htheta
  let geomG : ℝ := (1 - (3 : ℝ) ^ (-(rho - g)))⁻¹
  let geomGamma : ℝ := (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹
  let Cblk : ℝ := 1 + 48 * geomG + 4 * (3 : ℝ) ^ eta * geomGamma
  obtain ⟨hgeomG, hgeomGamma, hCblk, hCblkMain, hCblkFallback⟩ :=
    endpoint_geometric_row_constants hrhoGap hgammaRho
  obtain ⟨Nfix, Bconst, hNfix, hBconst, hlowFix, hgainFix, habsFix,
      hrelFix, -, hBconstEq⟩ := exists_admissible_thresholds_bounded
    (nstar := 0) (qfb := 0) (b := 0) (theta := theta) (mu := mu)
      (cd := frGaugeConst d) (Cblk := Cblk) hmu (frGaugeConst_pos d)
  let Ccoeff : ℕ := L * Q + R + B * Q
  let C1 : ℝ := (4 * Ccoeff + Nfix : ℕ)
  let C2 : ℝ := Real.logb 3 Bconst
  let C3 : ℝ := 1
  let Cstop : ℝ := C1 + C2 + C3
  let Cround : ℝ := 1
  let Cmix : ℝ := Cround + Cstop
  have hC2 : 0 ≤ C2 := by
    dsimp only [C2]
    exact Real.logb_nonneg (by norm_num) hBconst
  have hCmix : 0 < Cmix := by
    dsimp only [Cmix, Cround, Cstop, C1, C3]
    positivity
  refine ⟨Cmix, theta, deltaOut, hCmix, htheta, hdeltaOut, ?_⟩
  intro P E Psi K S Abar Nann hP hstat hunit hdag hAbar hAbarPos
    _hcontrast hsandwich
  let : IsProbabilityMeasure P := hP
  let base : ℝ := 2 + aspectRatio E * K
  have hbase : 3 ≤ base := by
    simpa only [base] using three_le_rebaseBase hdag
  obtain ⟨q, hqLow, hqHigh⟩ := Entry.exists_pow_three_bracket (sq_nonneg base)
  obtain ⟨hq, hqCost⟩ := pow_three_bracket_sq_le_four hbase hqLow hqHigh
  let q0 : ℕ := Q * q
  let nstar : ℕ := L * q0
  let qfb : ℕ := R * q
  let b : ℕ := B * q0
  let N0 : ℕ := nstar + qfb + b + Nfix
  let Pbase : Measure (CoeffSpace d) := triadicRebasedLaw Nann P
  let : IsProbabilityMeasure Pbase := isProbabilityMeasure_triadicRebasedLaw Nann P
  let Sbase : CoeffSpace d → ℝ := triadicRebasedSource Nann S
  let Psibase : ℝ → ℝ := triadicRebasedGauge Nann Psi
  have hstatBase : HCPoly.Frozen.IsStationaryLaw Pbase :=
    stationaryLaw_triadicRebasedLaw hstat Nann
  have hunitBase : HCPoly.Frozen.IsUnitRangeLaw Pbase :=
    unitRangeLaw_triadicRebasedLaw hunit Nann
  have hdagBase : HCPoly.Frozen.CoarseEllipticityDagger Pbase g E Psibase K Sbase := by
    simpa only [Pbase, Psibase, Sbase] using hdag.triadicRebased Nann
  let Ahat : ℕ → BlockMat d := fun n =>
    annealedBlock Pbase
      (centeredCube d ((n : ℤ) - (endpointReferenceOffset A D L n : ℤ)))
  let radiusBase : ℕ → CoeffSpace d → ℝ := fun n =>
    renormRadius Sbase (Ahat n) (endpointTolerance deltaOut eta q0 L n)
      gamma (endpointWindowLength A L n) n
  let radius : ℕ → CoeffSpace d → ℝ := fun n a =>
    radiusBase n (physical_scale_coeff Nann a)
  obtain ⟨hq0, hqBase, hGain⟩ :=
    endpoint_bracket_and_gain_bounds d hdag hqLow hQpos hbase hq
  obtain ⟨hGainBound, hDpow, hbaseInitial, honeBaseInitial⟩ :=
    endpoint_initial_renormalization_base d hdag hT hDcoef hDbase hmu hdeltaOut hbase
      hq0 hqBase hGain
  have hnet : 1 ≤ mu * (D : ℝ) - eta := by
    linarith only [hDcoef, hetaMu]
  obtain ⟨hhalf0, hqIndex, hinnerQ, hhalf, hAhatSymm, hAhatPos⟩ :=
    endpoint_reference_integrability d hdag hL hQpos hdagBase hqLow
  have hetaD : eta ≤ mu * (D : ℝ) := by
    have hDreal : 1 ≤ (D : ℝ) := by exact_mod_cast hD
    have hm := mul_le_mul_of_nonneg_left hDreal hmu.le
    linarith only [hetaMu, hm]
  obtain ⟨hbaseN, honeBaseN, hthrN, hcellN, hgrowthN, hbufN⟩ :=
    endpoint_radius_base_thresholds d hT
      hTthr hB hBbase hmu hdeltaOut hL hstatBase hunitBase hdagBase hq0 hGain hbaseInitial
      honeBaseInitial hnet hetaD hqIndex hhalf hA
  obtain ⟨hradiusTail, hfinPhysical, hfinAll, hcoarsePhysical⟩ :=
    endpoint_physical_radius_certificates d hmu
      hgn hgr hdeltaOut hdagBase hq0 hGain hqIndex hAhatSymm hAhatPos honeBaseN hthrN hcellN hbufN
  obtain ⟨hburnStart, hburnN, hQalpha, hstartAnnealed⟩ :=
    endpoint_initial_window_error_bounds d halpha hdag hAcoef
      hq hqLow hetaGapA hdeltaOut hL hQ hQannealed hbase
  let Brow : ℕ → CoeffSpace d → ℝ := fun m a =>
    quenched_block_row rho Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m
  have hrowDecay :=
    endpoint_physical_stopped_row_bound d hdag hAbar hAbarPos hsandwich heta hetaAlpha hthetaR
      hqLow hg0
      hrhoGap hgammaRho hgamma0 hgr hdeltaOut hL hgeomG hCblk hCblkMain hCblkFallback hbase hdagBase
      hburnN hstartAnnealed hhalf hAhatPos hfinAll hcoarsePhysical
  obtain ⟨hrowNonnegative, hsummable, hBmeas⟩ :=
    endpoint_row_summability_and_measurability d hAbar hAbarPos hg0 hrhoGap hmu hdeltaOut htheta
      hCblk hdagBase
      hrowDecay hradiusTail
  obtain ⟨F, hFmeas, hFsum⟩ := exists_measurable_weighted_rowTailSum
    (P := P) (B := Brow) (kappa := theta / 2) hBmeas hsummable
  have hN0star : nstar ≤ N0 := by dsimp only [N0]; omega
  obtain ⟨hthresholdLow, hthresholdGain, hthresholdAbs, hnormalizerRel, hN0eq, hgenCost, hnormCost⟩
    :=
    endpoint_threshold_and_polynomial_costs d hBconst hlowFix hgainFix habsFix hrelFix hqCost
      hbase
  apply nonempty_coupledWitnessEngineData_of_fields
    (P := P) (g := g) (E := E) (Psi := Psi) (K := K) (S := S)
    (Abar := Abar) (Nann := Nann) (theta := theta) (deltaOut := deltaOut)
    (Cmix := Cmix) (rho := rho) (mu := mu) (nstar := nstar)
    (qfb := qfb) (b := b) (N0 := N0)
    (radius := radius) (F := F) (Brow := Brow) (Cblk := Cblk) (Bconst := Bconst)
    (C1 := C1) (C2 := C2) (C3 := C3) (Cstop := Cstop) (Cround := Cround)
  · exact rfl
  · exact rfl
  · exact rfl
  · exact hmu
  · exact hradiusTail
  · exact hCblk
  · exact hFmeas
  · exact hrowDecay
  · exact hrowNonnegative
  · exact hFsum
  · exact hN0star
  · exact hBconst
  · exact hthresholdLow
  · exact hthresholdGain
  · exact hthresholdAbs
  · exact hnormalizerRel
  · simpa only [base] using ((by norm_num : (1 : ℝ) ≤ 3).trans hbase)
  · simpa only [C3, Real.rpow_one, base] using hbase
  · simpa only [base] using hgenCost
  · simpa only [base] using hnormCost
  · exact le_rfl
  · simpa only [Cround, Real.rpow_one, base] using hbase
  · exact le_rfl

end

end HCPolySupport.HighContrast.Quenched
