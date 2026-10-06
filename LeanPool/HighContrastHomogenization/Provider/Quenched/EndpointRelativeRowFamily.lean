/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeParameters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RenormalizedRowDecay
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RenormalizedRadiusFamilyVarying

/-!
# High-contrast homogenization: Provider.Quenched.EndpointRelativeRowFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Endpoint-relative row decay from a growing radius family

The stopping generation selects one member of the growing renormalization
family.  The successful branch uses that member's radius; the fallback branch
uses the uniform coarse-ellipticity estimate.
-/

namespace HCPolySupport.HighContrast.Quenched

open _root_.Filter MeasureTheory

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- Pointwise assembly of the successful and fallback branches of the
endpoint-relative row estimate. -/
theorem quenched_block_row_le_stoppingGeneration_of_endpoint_family [NeZero d]
    {g gamma rho delta eta Cblk : ℝ} {E Abar : BlockMat d}
    {S : CoeffSpace d → ℝ} {Ahat : ℕ → BlockMat d}
    {radius : ℕ → CoeffSpace d → ℝ}
    {nstar qfb q0 A L : ℕ} {a : CoeffSpace d}
    (hnstar : nstar = L * q0)
    (hgamma0 : 0 ≤ gamma) (hgr : g ≤ gamma) (hgammaRho : gamma < rho)
    (hdelta : 0 < delta) (heta : 0 < eta) (hL : 0 < L)
    (hAbarSymm : IsSymmetricBlockMat Abar)
    (hAbar : Book.Ch02.BlockPosDef Abar)
    (hcoarse : ∀ M : ℤ, S a ≤ (3 : ℝ) ^ M →
      ∀ k : ℤ, k ≤ M → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d M →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale ((3 : ℝ) ^ (g * ((M : ℝ) - (k : ℝ)))) E))
    (hradius : ∀ n, nstar ≤ n → radius n a =
      renormRadius S (Ahat n) (endpointTolerance delta eta q0 L n)
        gamma (endpointWindowLength A L n) n a)
    (hwindow : ∀ n, nstar ≤ n →
      ∃ h : ℕ,
        h = endpointWindowLength A L n ∧
        renormScale S (Ahat n) (endpointTolerance delta eta q0 L n)
          gamma h n a ≠ ⊤ ∧
        Book.Ch02.BlockPosDef (Ahat n) ∧
        BlockMatLoewnerLE E (blockScale (2 * kappaRef E) (Ahat n)) ∧
        BlockMatLoewnerLE (Ahat n)
          (blockScale (1 + endpointTolerance delta eta q0 L n) Abar) ∧
        2 * kappaRef E ≤ endpointTolerance delta eta q0 L n *
          (3 : ℝ) ^ ((gamma - g) * (h : ℝ)))
    (hdeltaOne : delta ≤ 1)
    (hCblkPos : 0 < Cblk)
    (hCblk : 4 * (3 : ℝ) ^ eta *
        (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹ ≤ Cblk)
    (hfallback : ∀ m : ℕ, nstar ≤ m → S a ≤ (3 : ℝ) ^ m →
      quenched_block_row rho Abar (S a) a m ≤
        Cblk * delta * (3 : ℝ) ^ ((eta / (L : ℝ)) * (qfb : ℝ))) :
    ∀ m : ℕ, nstar ≤ m →
      quenched_block_row rho Abar (S a) a m ≤
        Cblk * delta *
          (3 : ℝ) ^ (-(eta / (L : ℝ)) *
            ((m : ℝ) -
              (stoppingGeneration nstar qfb radius m a : ℝ) -
              (nstar : ℝ))) := by
  intro m hm
  by_cases hsource : S a ≤ (3 : ℝ) ^ m
  · by_cases hcand : ∃ q, IsStoppingCandidate nstar radius m a q
    · let q : ℕ := Nat.find hcand
      let n : ℕ := m - q
      have hqspec := Nat.find_spec hcand
      have hq : q ≤ m - nstar := by
        change Nat.find hcand ≤ m - nstar
        exact hqspec.1
      have hn : nstar ≤ n := by dsimp only [n]; omega
      have hrad : radius n a ≤ (3 : ℝ) ^ m := by
        change radius (m - Nat.find hcand) a ≤ (3 : ℝ) ^ m
        exact hqspec.2
      obtain ⟨h, rfl, hfin, hAhatPos, href, hcomp, hburn⟩ := hwindow n hn
      have htolPos := endpointTolerance_pos (eta := eta)
        (q0 := q0) (L := L) (n := n) hdelta
      have htolLe : endpointTolerance delta eta q0 L n ≤ delta :=
        endpointTolerance_le_delta hdelta.le heta.le
      have htolIcc : endpointTolerance delta eta q0 L n ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨htolPos.le, htolLe.trans hdeltaOne⟩
      have hrad' : renormRadius S (Ahat n) (endpointTolerance delta eta q0 L n)
          gamma (endpointWindowLength A L n) n a ≤ (3 : ℝ) ^ m := by
        rw [← hradius n hn]
        exact hrad
      have hrow := quenched_block_row_le_of_renormRadius_le hgamma0 hgr
        hgammaRho htolIcc htolIcc hAhatPos hAbarSymm hAbar href hcomp hburn
        hcoarse hfin (by omega) hrad' hsource
      have htolDecay := endpointTolerance_le_generation_decay
        (n := n) (q0 := q0) (L := L) hdelta.le heta hL
        (by rw [← hnstar]; exact hn)
      have hgeom : 0 ≤ (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹ := by
        have hq : (3 : ℝ) ^ (-(rho - gamma)) < 1 := by
          rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
          exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2
            (by linarith only [hgammaRho])
        exact inv_nonneg.2 (sub_nonneg.mpr hq.le)
      have hsum : endpointTolerance delta eta q0 L n +
          endpointTolerance delta eta q0 L n ≤
          2 * ((3 : ℝ) ^ eta * delta *
            (3 : ℝ) ^ (-(eta / (L : ℝ)) *
              ((n : ℝ) - (nstar : ℝ)))) := by
        have ht := htolDecay
        rw [← hnstar] at ht
        linarith only [ht]
      have hmain : quenched_block_row rho Abar (S a) a m ≤
          Cblk * delta * (3 : ℝ) ^ (-(eta / (L : ℝ)) *
            ((n : ℝ) - (nstar : ℝ))) := by
        calc
          quenched_block_row rho Abar (S a) a m ≤
              2 * (endpointTolerance delta eta q0 L n +
                endpointTolerance delta eta q0 L n) *
                (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹ := hrow
          _ ≤ 4 * ((3 : ℝ) ^ eta * delta *
                (3 : ℝ) ^ (-(eta / (L : ℝ)) *
                  ((n : ℝ) - (nstar : ℝ)))) *
                (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹ := by
              have hs := mul_le_mul_of_nonneg_left hsum
                (by norm_num : (0 : ℝ) ≤ 2)
              have h2 : 2 * (endpointTolerance delta eta q0 L n +
                  endpointTolerance delta eta q0 L n) ≤
                  4 * ((3 : ℝ) ^ eta * delta *
                    (3 : ℝ) ^ (-(eta / (L : ℝ)) *
                      ((n : ℝ) - (nstar : ℝ)))) := by
                linarith only [hs]
              exact mul_le_mul_of_nonneg_right h2 hgeom
          _ = (4 * (3 : ℝ) ^ eta *
                (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹) * delta *
                (3 : ℝ) ^ (-(eta / (L : ℝ)) *
                  ((n : ℝ) - (nstar : ℝ))) := by ring
          _ ≤ Cblk * delta * (3 : ℝ) ^ (-(eta / (L : ℝ)) *
                ((n : ℝ) - (nstar : ℝ))) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hCblk hdelta.le)
                (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      rw [stoppingGeneration, dite_eq_left hcand]
      have hqm : q ≤ m := hq.trans (Nat.sub_le m nstar)
      simpa only [q, n, Nat.cast_sub hqm] using hmain
    · rw [stoppingGeneration, dite_eq_right hcand]
      have hfb := hfallback m hm hsource
      have hmstar : nstar ≤ m := hm
      have hcast : ((m - nstar + qfb : ℕ) : ℝ) =
          (m : ℝ) - (nstar : ℝ) + (qfb : ℝ) := by
        rw [Nat.cast_add, Nat.cast_sub hmstar]
      rw [hcast]
      convert hfb using 1
      congr 2
      ring
  · unfold quenched_block_row
    rw [ite_eq_right hsource]
    exact mul_nonneg (mul_nonneg hCblkPos.le hdelta.le)
      (Real.rpow_nonneg (by norm_num) _)

end

end HCPolySupport.HighContrast.Quenched
