/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Tail.ElementaryBound
public import LeanPool.DeciSigma1.Holes.Tail.LevelElementaryBound
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # A closed elementary bound on rejected tails

The logarithmic level envelope and the affine compression estimate give a double exponential
bound independent of the alphabet size.

## Main declarations

- `compressionLengthBoundIter_le_log`: compression preserves a logarithmic envelope.
- `tailLengthBound_le_double_exp2`: the closed bound on rejected tails.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open Arithmetic

/-- Compression multiplies a common logarithmic bound by at most `16 * (r + 1)`. -/
theorem compressionLengthBoundIter_le_log (k N D r E H : ℕ)
    (hH : 1 ≤ H) (hN : N ≤ exp2 H) (hfac : N.factorial ≤ exp2 H)
    (hhead : 2 ^ (k * (N - 1)) ≤ exp2 H) (hD : D ≤ exp2 H)
    (hr : r ≤ exp2 H) (hE : E ≤ exp2 H) :
    compressionLengthBoundIter k N D r E ≤ exp2 (16 * (r + 1) * H) := by
  have hnd : N * D ≤ exp2 (2 * H) := by
    calc
      _ ≤ exp2 H * exp2 H := Nat.mul_le_mul hN hD
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hdf : D * N.factorial ≤ exp2 (2 * H) := by
    calc
      _ ≤ exp2 H * exp2 H := Nat.mul_le_mul hD hfac
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hmarg : Periodic.fixedMargin N D + Periodic.statePeriodModulus N D ≤
      exp2 (6 * H) := by
    calc
      _ ≤ exp2 (2 * H + 4) := by
        unfold Periodic.fixedMargin Periodic.boundaryMargin Periodic.stateTransientLength
          Periodic.statePeriodModulus
        rw [exp2_add]
        change _ ≤ exp2 (2 * H) * 16
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hgap : Periodic.comparisonGap N D + Periodic.statePeriodModulus N D ≤
      exp2 (5 * H) := by
    calc
      _ ≤ exp2 (2 * H + 3) := by
        unfold Periodic.comparisonGap Periodic.boundaryMargin Periodic.stateTransientLength
          Periodic.statePeriodModulus
        rw [exp2_add]
        change _ ≤ exp2 (2 * H) * 8
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hslope : compressionSlope k N D ≤ exp2 (6 * H) := by
    calc
      _ ≤ exp2 H * exp2 (5 * H) := Nat.mul_le_mul hhead hgap
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have htwo : 2 * r + 1 ≤ exp2 (3 * H) := by
    have hpos : 1 ≤ exp2 H := Nat.two_pow_pos H
    calc
      _ ≤ exp2 (H + 2) := by
        rw [exp2_add]
        change _ ≤ exp2 H * 4
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hinter : compressionIntercept k N D r ≤ exp2 (10 * H) := by
    have hi : compressionIntercept k N D r ≤
        (Periodic.fixedMargin N D + Periodic.statePeriodModulus N D) +
          (2 * r + 1) * compressionSlope k N D := by
      unfold compressionIntercept compressionSlope
      calc
        _ ≤ _ + ((2 * r + 1) * 2 ^ (k * (N - 1))) *
            (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)) _
        _ = _ := by ring
    have hprod : (2 * r + 1) * compressionSlope k N D ≤ exp2 (9 * H) := by
      calc
        _ ≤ exp2 (3 * H) * exp2 (6 * H) := Nat.mul_le_mul htwo hslope
        _ = _ := by rw [← exp2_add]; congr 1; omega
    have hsmall : exp2 (6 * H) ≤ exp2 (9 * H) := exp2_mono (by omega)
    calc
      _ ≤ exp2 (9 * H + 1) := by
        rw [exp2_add]
        change _ ≤ exp2 (9 * H) * 2
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hbase : 1 + r * compressionSlope k N D ≤ exp2 (8 * H) := by
    have hprod : r * compressionSlope k N D ≤ exp2 (7 * H) := by
      calc
        _ ≤ exp2 H * exp2 (6 * H) := Nat.mul_le_mul hr hslope
        _ = _ := by rw [← exp2_add]; congr 1; omega
    have hpos : 1 ≤ exp2 (7 * H) := Nat.two_pow_pos _
    calc
      _ ≤ exp2 (7 * H + 1) := by
        rw [exp2_add]
        change _ ≤ exp2 (7 * H) * 2
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hinit : E + r * compressionIntercept k N D r ≤ exp2 (12 * H) := by
    have hprod : r * compressionIntercept k N D r ≤ exp2 (11 * H) := by
      calc
        _ ≤ exp2 H * exp2 (10 * H) := Nat.mul_le_mul hr hinter
        _ = _ := by rw [← exp2_add]; congr 1; omega
    have hsmall : exp2 H ≤ exp2 (11 * H) := exp2_mono (by omega)
    calc
      _ ≤ exp2 (11 * H + 1) := by
        rw [exp2_add]
        change _ ≤ exp2 (11 * H) * 2
        omega
      _ ≤ _ := exp2_mono (by omega)
  calc
    _ ≤ (1 + r * compressionSlope k N D) ^ r *
        (E + r * compressionIntercept k N D r) :=
      compressionLengthBoundIter_le_affine k N D r E
    _ ≤ exp2 (8 * H) ^ r * exp2 (12 * H) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase r) hinit
    _ = exp2 (8 * H * r + 12 * H) := by rw [← exp2_mul, ← exp2_add]
    _ ≤ _ := exp2_mono (by nlinarith)

private theorem uncoveredLengthBound_le_log (σ k N H : ℕ) (hH : 2 ≤ H)
    (hk : k ≤ exp2 H) (hQ : levelMultiplicity k N ≤ exp2 H)
    (hst : stateEnvelope H (levelState k N (levelCount k + 1))) :
    uncoveredLengthBound (levelBounds σ k N) ≤ exp2 (8 * H) := by
  let M := exp2 H
  have hM : 1 ≤ M := Nat.two_pow_pos H
  have hTt := hst.2.2.2.2
  rw [levelState_succ_uncoveredBound] at hTt
  have hTp : levelEscapeLength k N (levelCount k) ≤ M := by
    dsimp [M]
    nlinarith only [hTt]
  have hp : (levelState k N (levelCount k + 1)).periodBound ≤ M := hst.1
  have hu : (levelState k N (levelCount k + 1)).uncoveredBound ≤ M := hst.2.2.2.2
  have hpoly : uncoveredLengthBound (levelBounds σ k N) ≤
      M * (M + (M + 3) * (3 * M + 3) + (M + 3) * (2 * M)) := by
    unfold uncoveredLengthBound
    change k * ((levelState k N (levelCount k + 1)).uncoveredBound +
      (levelMultiplicity k N + 3) * (3 * levelEscapeLength k N (levelCount k) + 3) +
      (levelMultiplicity k N + 3) * (2 * (levelState k N (levelCount k + 1)).periodBound)) ≤ _
    gcongr
  have hpoly' : M * (M + (M + 3) * (3 * M + 3) + (M + 3) * (2 * M)) ≤
      64 * M ^ 3 := by
    have h1 : M ≤ M * M := by nlinarith
    have h2 : M * M ≤ M ^ 3 := by nlinarith
    nlinarith only [h1, h2]
  calc
    _ ≤ 64 * M ^ 3 := hpoly.trans hpoly'
    _ = exp2 (3 * H + 6) := by
      dsimp [M]
      rw [← exp2_mul]
      change exp2 6 * exp2 (H * 3) = _
      rw [← exp2_add]; congr 1; omega
    _ ≤ _ := exp2_mono (by omega)

private def initialLogBound (k N : ℕ) : ℕ :=
  let Q := levelMultiplicity k N
  k + N + Q + N * N + k * N + k * (Q + 3) + 20

private def levelLogSlope (k N : ℕ) : ℕ :=
  (k + N + 10) * (levelMultiplicity k N + N + 3) ^ k + 5

private theorem tailLengthBound_le_raw (σ k N : ℕ) :
    tailLengthBound σ k N ≤ exp2 (exp2
      (initialLogBound k N + levelLogSlope k N * (levelCount k + 1) +
        k * (levelMultiplicity k N + 3) + 7)) := by
  let Q := levelMultiplicity k N
  let r := k * (Q + 3)
  let A := initialLogBound k N
  let B := A + levelLogSlope k N * (levelCount k + 1)
  let H := exp2 B
  have hA : k + N + Q + N * N + 20 ≤ A := by dsimp [A, initialLogBound, Q]; omega
  have hAH : A ≤ H := (by dsimp [B]; omega : A ≤ B).trans (le_exp2 B)
  have hH : 2 ≤ H := by omega
  have hN : N ≤ H := by omega
  have hN2 : N * N ≤ H := by omega
  have hkN : k * N ≤ H := by
    have : k * N ≤ A := by dsimp [A, initialLogBound]; omega
    omega
  have hr : r ≤ H := by
    have : r ≤ A := by dsimp [r, Q, A, initialLogBound]; omega
    omega
  have hs := levelState_envelope k N A (levelCount k + 1) hA
  have hlog : exp2 (levelLogSlope k N * (levelCount k + 1)) * A ≤ H := by
    calc
      _ ≤ exp2 (levelLogSlope k N * (levelCount k + 1)) * exp2 A :=
        Nat.mul_le_mul_left _ (le_exp2 A)
      _ = H := by dsimp [H, B]; rw [← exp2_add]; congr 1; omega
  have hm := exp2_mono hlog
  have hst : stateEnvelope H (levelState k N (levelCount k + 1)) :=
    ⟨hs.1.trans hm, hs.2.1.trans hm, hs.2.2.1.trans hm,
      hs.2.2.2.1.trans hm, hs.2.2.2.2.trans hm⟩
  have hE := uncoveredLengthBound_le_log σ k N H hH
    ((by omega : k ≤ H).trans (le_exp2 H))
    ((by omega : Q ≤ H).trans (le_exp2 H)) hst
  have hH8 : H ≤ 8 * H := by omega
  have hmono := exp2_mono hH8
  have hc := compressionLengthBoundIter_le_log k N
    ((levelBounds σ k N).periodBound (levelCount k)) r
    (uncoveredLengthBound (levelBounds σ k N)) (8 * H) (by omega)
    ((hN.trans (le_exp2 H)).trans hmono)
    ((factorial_le_exp2_sq N).trans (exp2_mono (hN2.trans hH8)))
    (exp2_mono ((Nat.mul_le_mul_left k (Nat.sub_le N 1)).trans (hkN.trans hH8)))
    (hst.1.trans hmono) ((hr.trans (le_exp2 H)).trans hmono) hE
  change tailLengthBound σ k N ≤ _ at hc
  apply hc.trans (exp2_mono _)
  have hr' : r + 1 ≤ exp2 r := succ_le_exp2 r
  calc
    16 * (r + 1) * (8 * H) = 128 * (r + 1) * H := by ring
    _ ≤ 128 * exp2 r * H := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr')
    _ = exp2 (B + r + 7) := by
      change exp2 7 * exp2 r * exp2 B = _
      rw [← exp2_add, ← exp2_add]; congr 1; omega

private theorem rawExponent_le (k N : ℕ) :
    initialLogBound k N + levelLogSlope k N * (levelCount k + 1) +
      k * (levelMultiplicity k N + 3) + 7 ≤ (k + N + 20) ^ (2 * k + 5) := by
  let R := k + N + 20
  let Q := levelMultiplicity k N
  have hR : 20 ≤ R := by dsimp [R]; omega
  have hQ : Q ≤ 4 + 2 * k * N := by
    dsimp [Q, levelMultiplicity]
    gcongr <;> exact Nat.sub_le _ _
  have hQS : Q + N + 3 ≤ R ^ 2 := by
    dsimp [R]
    nlinarith only [hQ]
  have hQ' : Q ≤ R ^ 2 := by omega
  have hA : initialLogBound k N + k * (Q + 3) + 7 ≤ R ^ 4 := by
    calc
      _ ≤ k + N + R ^ 2 + N * N + k * N + 2 * k * (R ^ 2 + 3) + 27 := by
        dsimp [initialLogBound]
        change k + N + Q + N * N + k * N + k * (Q + 3) + 20 + k * (Q + 3) + 7 ≤ _
        have := Nat.mul_le_mul_left (2 * k) (Nat.add_le_add_right hQ' 3)
        nlinarith only [hQ', this]
      _ ≤ _ := by dsimp [R]; ring_nf; omega
  have hp : 1 ≤ (Q + N + 3) ^ k := Nat.one_le_pow _ _ (by omega)
  have hV : levelLogSlope k N ≤ R ^ (2 * k + 1) := by
    calc
      _ ≤ (k + N + 15) * (Q + N + 3) ^ k := by
        dsimp [levelLogSlope]
        change (k + N + 10) * (Q + N + 3) ^ k + 5 ≤ _
        nlinarith only [hp]
      _ ≤ R * (R ^ 2) ^ k :=
        Nat.mul_le_mul (by dsimp [R]; omega) (Nat.pow_le_pow_left hQS k)
      _ = _ := by rw [← pow_mul, pow_succ]; ring
  have hl : levelCount k + 1 ≤ R ^ 2 := by
    dsimp [levelCount, R]
    nlinarith
  have hprod : levelLogSlope k N * (levelCount k + 1) ≤ R ^ (2 * k + 3) := by
    calc
      _ ≤ R ^ (2 * k + 1) * R ^ 2 := Nat.mul_le_mul hV hl
      _ = _ := by rw [← pow_add]
  have h₁ : R ^ 4 ≤ R ^ (2 * k + 4) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h₂ : R ^ (2 * k + 3) ≤ R ^ (2 * k + 4) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  dsimp [Q] at hA
  calc
    _ ≤ 2 * R ^ (2 * k + 4) := by omega
    _ ≤ R * R ^ (2 * k + 4) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ]; ring

/-- The rejected-tail bound is at most a double exponential, uniformly in the alphabet size. -/
theorem tailLengthBound_le_double_exp2 (σ k N : ℕ) :
    tailLengthBound σ k N ≤ exp2 (exp2 ((k + N + 20) ^ (2 * k + 5))) :=
  (tailLengthBound_le_raw σ k N).trans (exp2_mono (exp2_mono (rawExponent_le k N)))

end DeciSigma1.Holes.Tail
