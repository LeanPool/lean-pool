/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeGridCount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedLimitBlock

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeRenormalizedBadEvent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bad generations of the renormalized ellipticity estimate

The renormalization of ellipticity replaces the reference block of a
coarse-ellipticity datum by the annealed block at a fixed inner generation, at
the cost of a random minimal scale.  A generation `m` is *bad* when, on the event
that the source has burnt in at `m`, some cell of some inner scale within a
window of height `h` below `m` exceeds the additive multiple
`1 + δ 3^(ρ(m-k))` of the reference block.

This file fixes that event, records the single-cell estimate the argument cites,
and performs the two union bounds of the printed proof: over the cells of a
scale, whose number is counted by `card_centredIndexFinset`, and over the scales
of the window.  The parameter of the single-cell estimate is the printed one, and
the two inequalities it must satisfy — that it is at least one, and that the
deviation it produces is below the target `δ 3^(ρ(m-k))` — are proved here.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Monotonicity of a scaled block -/

/-- Scaling a positive block by a larger factor gives a larger block. -/
theorem blockMatLoewnerLE_blockScale_mono {c c' : ℝ} (hcc : c ≤ c') {A : BlockMat d}
    (hA : Book.Ch02.BlockPosDef A) :
    BlockMatLoewnerLE (blockScale c A) (blockScale c' A) := by
  intro X
  rw [blockVecDot_blockMatVecMul_blockScale, blockVecDot_blockMatVecMul_blockScale]
  have hnn : 0 ≤ blockVecDot X (blockMatVecMul A X) := by
    rcases eq_or_ne X 0 with rfl | hX
    · simp [blockVecDot_blockMatVecMul_eq_sum, toFullBlockVec]
    · exact (hA X hX).le
  nlinarith only [hcc, hnn]

/-! ## The bad events -/

/-- The bad-cell event: on the event that the source has burnt in at generation
`m`, the coarse block of the scale-`k` cell of index `w` exceeds the additive
multiple of the reference block. -/
@[expose]
def renormBadCell (S : CoeffSpace d → ℝ) (Ahat : BlockMat d) (delta rho : ℝ)
    (m k : ℤ) (w : Fin d → ℤ) : Set (CoeffSpace d) :=
  {a | S a ≤ (3 : ℝ) ^ m ∧
    ¬ BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale (1 + delta * (3 : ℝ) ^ (rho * ((m : ℝ) - (k : ℝ)))) Ahat)}

/-- The bad-generation event: some cell of some scale in the window of height
`h` below `m`, centred in `□_m`, is bad. -/
@[expose]
def renormBadGeneration (S : CoeffSpace d → ℝ) (Ahat : BlockMat d) (delta rho : ℝ)
    (h : ℕ) (m : ℤ) : Set (CoeffSpace d) :=
  ⋃ k ∈ Finset.Icc (m - (h : ℤ) + 1) m, ⋃ w ∈ centredIndexFinset d k m,
    renormBadCell S Ahat delta rho m k w

/-! ## The parameter of the single-cell estimate -/

/-- The parameter of the single-cell estimate at generation `m` and scale `k`. -/
@[expose]
def renormParam (gamma nu mu rho delta Gain : ℝ) (n l0 : ℕ) (m k : ℤ) : ℝ :=
  Gain⁻¹ * delta * (3 : ℝ) ^ ((gamma - nu) +
    mu * ((k : ℝ) - ((n : ℝ) - (l0 : ℝ))) + (rho - gamma) * ((m : ℝ) - (k : ℝ)))

/-- The value the parameter is at least, over the whole window at generation
`m`. -/
@[expose]
def renormFloor (gamma nu mu delta Gain : ℝ) (n l0 h : ℕ) (m : ℤ) : ℝ :=
  Gain⁻¹ * delta * (3 : ℝ) ^ ((gamma - nu) + mu * ((l0 : ℝ) - (h : ℝ))) *
    (3 : ℝ) ^ (mu * ((m : ℝ) - (n : ℝ)))

/-- The number of cells the two union bounds of the printed proof cover. -/
@[expose]
def renormCellCount (d h : ℕ) : ℝ := (h : ℝ) * (3 : ℝ) ^ (d * h)

/-! ## The two inequalities the parameter satisfies -/

/-- **The deviation produced by the parameter is below the target.**  This is the
display `Θ 3^7 3^(γ(m-l)) 3^(-ν(k-l)) T ≤ δ 3^(ρ(m-k))` of the printed proof, at
the inner generation `l = n - l₀`. -/
theorem renorm_gain_le {gamma nu mu rho delta Gain : ℝ} (hGain : 0 < Gain)
    (hdelta : 0 ≤ delta) (hmu : mu = nu - gamma) (hgn : gamma ≤ nu)
    (n l0 : ℕ) (m k : ℤ) :
    Gain * (3 : ℝ) ^ (gamma * ((m : ℝ) - ((n : ℝ) - (l0 : ℝ)))) *
        (3 : ℝ) ^ (-nu * ((k : ℝ) - ((n : ℝ) - (l0 : ℝ)))) *
        renormParam gamma nu mu rho delta Gain n l0 m k
      ≤ delta * (3 : ℝ) ^ (rho * ((m : ℝ) - (k : ℝ))) := by
  have hcancel : Gain * Gain⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hGain)
  set E1 : ℝ := gamma * ((m : ℝ) - ((n : ℝ) - (l0 : ℝ))) with hE1
  set E2 : ℝ := -nu * ((k : ℝ) - ((n : ℝ) - (l0 : ℝ))) with hE2
  set E3 : ℝ := (gamma - nu) + mu * ((k : ℝ) - ((n : ℝ) - (l0 : ℝ))) +
    (rho - gamma) * ((m : ℝ) - (k : ℝ)) with hE3
  have hsum : E1 + E2 + E3 = rho * ((m : ℝ) - (k : ℝ)) + (gamma - nu) := by
    rw [hE1, hE2, hE3, hmu]
    ring
  calc Gain * (3 : ℝ) ^ E1 * (3 : ℝ) ^ E2 * (Gain⁻¹ * delta * (3 : ℝ) ^ E3)
      = Gain * Gain⁻¹ * (delta * ((3 : ℝ) ^ E1 * (3 : ℝ) ^ E2 * (3 : ℝ) ^ E3)) := by
        ring
    _ = delta * ((3 : ℝ) ^ E1 * (3 : ℝ) ^ E2 * (3 : ℝ) ^ E3) := by
        rw [hcancel, one_mul]
    _ = delta * (3 : ℝ) ^ (E1 + E2 + E3) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    _ ≤ delta * (3 : ℝ) ^ (rho * ((m : ℝ) - (k : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hdelta
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        rw [hsum]
        linarith only [hgn]

/-- **The parameter is at least its floor over the window.** -/
theorem renormFloor_le_renormParam {gamma nu mu rho delta Gain : ℝ}
    (hGain : 0 < Gain) (hdelta : 0 ≤ delta) (hmu : 0 < mu) (hrg : gamma ≤ rho)
    {n l0 h : ℕ} {m k : ℤ} (hkm : k ≤ m) (hwin : m - (h : ℤ) + 1 ≤ k) :
    renormFloor gamma nu mu delta Gain n l0 h m ≤
      renormParam gamma nu mu rho delta Gain n l0 m k := by
  have hcoef : (0 : ℝ) ≤ Gain⁻¹ * delta := mul_nonneg (inv_nonneg.2 hGain.le) hdelta
  have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hwinR : (m : ℝ) - (h : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hwin
  rw [renormFloor, renormParam, mul_assoc, ← Real.rpow_add (by norm_num)]
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hgap : (0 : ℝ) ≤ mu * ((k : ℝ) + (h : ℝ) - (m : ℝ)) :=
    mul_nonneg hmu.le (by linarith only [hwinR])
  have hgap2 : (0 : ℝ) ≤ (rho - gamma) * ((m : ℝ) - (k : ℝ)) :=
    mul_nonneg (by linarith only [hrg]) (by linarith only [hkmR])
  nlinarith only [hgap, hgap2]

/-- **The floor is at least one from the base generation on.**  The hypothesis is
the printed restriction on `l₀`. -/
theorem one_le_renormFloor {gamma nu mu delta Gain : ℝ} (hmu : 0 < mu)
    {n l0 h : ℕ} {m : ℤ} (hnm : (n : ℤ) ≤ m)
    (hl0 : 1 ≤ Gain⁻¹ * delta *
      (3 : ℝ) ^ ((gamma - nu) + mu * ((l0 : ℝ) - (h : ℝ)))) :
    1 ≤ renormFloor gamma nu mu delta Gain n l0 h m := by
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ (mu * ((m : ℝ) - (n : ℝ))) := by
    have hstep : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ (mu * ((m : ℝ) - (n : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_nonneg hmu.le (by linarith only [hnmR]))
    simpa using hstep
  rw [renormFloor]
  nlinarith only [hl0, hpow]

/-! ## The single-cell estimate -/

/-- **The single-cell renormalization estimate.**  This is what the printed proof
of the renormalization lemma cites: subadditivity of the coarse block, the
concentration estimate for sums of coarse blocks, and the comparison of the
reference block with the annealed one at the inner generation `l = n - l₀`,
combined into one statement about a single cell. -/
@[expose]
def HasCellRenormalization (P : Measure (CoeffSpace d)) (S : CoeffSpace d → ℝ)
    (Ahat : BlockMat d) (gamma nu Gain : ℝ) (n l0 h : ℕ) : Prop :=
  ∀ m k : ℤ, (n : ℤ) ≤ m → m - (h : ℤ) + 1 ≤ k → k ≤ m →
    ∀ T : ℝ, 1 ≤ T → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m →
        P.real {a : CoeffSpace d | S a ≤ (3 : ℝ) ^ m ∧
            ¬ BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
              (blockScale (1 + Gain *
                (3 : ℝ) ^ (gamma * ((m : ℝ) - ((n : ℝ) - (l0 : ℝ)))) *
                (3 : ℝ) ^ (-nu * ((k : ℝ) - ((n : ℝ) - (l0 : ℝ)))) * T) Ahat)}
          ≤ (frGauge d T)⁻¹

/-! ## The two union bounds -/

/-- The bad-cell event at the target multiple is contained in the bad-cell event
at the parameter's multiple. -/
theorem renormBadCell_subset {S : CoeffSpace d → ℝ}
    {Ahat : BlockMat d} {gamma nu mu rho delta Gain : ℝ} {n l0 : ℕ} {m k : ℤ}
    (hAhat : Book.Ch02.BlockPosDef Ahat) (hGain : 0 < Gain) (hdelta : 0 ≤ delta)
    (hmu : mu = nu - gamma) (hgn : gamma ≤ nu) (w : Fin d → ℤ) :
    renormBadCell S Ahat delta rho m k w ⊆
      {a : CoeffSpace d | S a ≤ (3 : ℝ) ^ m ∧
        ¬ BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale (1 + Gain *
            (3 : ℝ) ^ (gamma * ((m : ℝ) - ((n : ℝ) - (l0 : ℝ)))) *
            (3 : ℝ) ^ (-nu * ((k : ℝ) - ((n : ℝ) - (l0 : ℝ)))) *
            renormParam gamma nu mu rho delta Gain n l0 m k) Ahat)} := by
  intro a ha
  obtain ⟨hsrc, hbad⟩ := ha
  refine ⟨hsrc, fun hle => hbad ?_⟩
  refine hle.trans (blockMatLoewnerLE_blockScale_mono ?_ hAhat)
  have hgain := renorm_gain_le (rho := rho) hGain hdelta hmu hgn n l0 m k
  linarith only [hgain]


/-! ## The union bound over the window -/

/-- **The bad-generation estimate.**  Two union bounds — over the cells of a
scale, counted by `card_centredIndexFinset`, and over the scales of the window —
turn the single-cell estimate into a bound on the whole bad generation, at the
parameter's floor. -/
theorem measureReal_renormBadGeneration_le {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {S : CoeffSpace d → ℝ} {Ahat : BlockMat d}
    {gamma nu mu rho delta Gain : ℝ} {n l0 h : ℕ}
    (hAhat : Book.Ch02.BlockPosDef Ahat) (hGain : 0 < Gain) (hdelta : 0 ≤ delta)
    (hmu : mu = nu - gamma) (hmupos : 0 < mu) (hgn : gamma ≤ nu) (hrg : gamma ≤ rho)
    (hl0 : 1 ≤ Gain⁻¹ * delta *
      (3 : ℝ) ^ ((gamma - nu) + mu * ((l0 : ℝ) - (h : ℝ))))
    (hcell : HasCellRenormalization P S Ahat gamma nu Gain n l0 h)
    {m : ℤ} (hnm : (n : ℤ) ≤ m) :
    P.real (renormBadGeneration S Ahat delta rho h m) ≤
      renormCellCount d h *
        (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ := by
  have hG1 : 1 ≤ renormFloor gamma nu mu delta Gain n l0 h m :=
    one_le_renormFloor hmupos hnm hl0
  have hGpos : (0 : ℝ) ≤ renormFloor gamma nu mu delta Gain n l0 h m :=
    le_trans zero_le_one hG1
  have hinvnn : (0 : ℝ) ≤
      (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ :=
    (inv_pos.2 (frGauge_pos d _)).le
  have hscale : ∀ k ∈ Finset.Icc (m - (h : ℤ) + 1) m,
      P.real (⋃ w ∈ centredIndexFinset d k m, renormBadCell S Ahat delta rho m k w)
        ≤ (3 : ℝ) ^ (d * h) *
          (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hTge : renormFloor gamma nu mu delta Gain n l0 h m ≤
        renormParam gamma nu mu rho delta Gain n l0 m k :=
      renormFloor_le_renormParam hGain hdelta hmupos hrg hk2 hk1
    have hT1 : 1 ≤ renormParam gamma nu mu rho delta Gain n l0 m k := le_trans hG1 hTge
    have hgauge : (frGauge d (renormParam gamma nu mu rho delta Gain n l0 m k))⁻¹ ≤
        (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ :=
      inv_anti₀ (frGauge_pos d _)
        ((admissiblePsi_frGauge d).1 (Set.mem_Ici.2 hGpos)
          (Set.mem_Ici.2 (le_trans hGpos hTge)) hTge)
    have hcellbound : ∀ w ∈ centredIndexFinset d k m,
        P.real (renormBadCell S Ahat delta rho m k w) ≤
          (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ := by
      intro w hw
      have hcentre : standardCellCenter k w ∈ centeredCube d m :=
        (mem_centredIndexFinset_iff hk2).1 hw
      have hsub := renormBadCell_subset (S := S) (Ahat := Ahat) (rho := rho)
        (n := n) (l0 := l0) (m := m) (k := k) hAhat hGain hdelta hmu hgn w
      exact ((measureReal_mono hsub).trans
        (hcell m k hnm hk1 hk2 _ hT1 w hcentre)).trans hgauge
    have hcard : ((centredIndexFinset d k m).card : ℝ) ≤ (3 : ℝ) ^ (d * h) := by
      have hnat : (centredIndexFinset d k m).card = 3 ^ (d * (m - k).toNat) :=
        card_centredIndexFinset d k m
      have hexp : d * (m - k).toNat ≤ d * h := by
        have : (m - k).toNat ≤ h := by omega
        exact Nat.mul_le_mul_left d this
      have hmono : (3 : ℝ) ^ (d * (m - k).toNat) ≤ (3 : ℝ) ^ (d * h) :=
        pow_le_pow_right₀ (by norm_num) hexp
      rw [hnat]
      push_cast
      exact hmono
    calc P.real (⋃ w ∈ centredIndexFinset d k m, renormBadCell S Ahat delta rho m k w)
        ≤ ∑ w ∈ centredIndexFinset d k m,
            P.real (renormBadCell S Ahat delta rho m k w) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ centredIndexFinset d k m,
            (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ :=
          Finset.sum_le_sum hcellbound
      _ = ((centredIndexFinset d k m).card : ℝ) *
            (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 : ℝ) ^ (d * h) *
            (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard hinvnn
  have hcardIcc : (Finset.Icc (m - (h : ℤ) + 1) m).card = h := by
    rw [Int.card_Icc]
    omega
  calc P.real (renormBadGeneration S Ahat delta rho h m)
      ≤ ∑ k ∈ Finset.Icc (m - (h : ℤ) + 1) m,
          P.real (⋃ w ∈ centredIndexFinset d k m,
            renormBadCell S Ahat delta rho m k w) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (m - (h : ℤ) + 1) m, (3 : ℝ) ^ (d * h) *
          (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ :=
        Finset.sum_le_sum hscale
    _ = renormCellCount d h *
          (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ := by
        rw [Finset.sum_const, hcardIcc, nsmul_eq_mul, renormCellCount]
        ring

end

end Quenched
end HighContrast
end HCPolySupport
