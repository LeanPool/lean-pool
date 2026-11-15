/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Trace.TraceAssemble

/-!
# Weierstrass avoidance along the per-disk reduction chains

The genericity hypothesis of `thm:omega-prime-global` clause (c) asks that no reduction step
of the per-disk pipeline hit a Weierstrass point. The condition is coprimality of the `u`-part
with `2·v`, and this file supplies it block by block for the two shapes the pipeline runs:

* a **pair** block needs both doubled `y`-values to be units. For the constant pair
  `(Q) + (ιP₀)` those are `y_Q` and `b` (`ChabautyColeman.isCoprime_pair_const`); on the
  residue disk the moving point contributes `b·η`, a unit because `η` has constant coefficient
  `1` (`ChabautyColeman.isCoprime_phiU₁`, `ChabautyColeman.isCoprime_phiU₃`).
* a **chart** block needs nothing beyond the centre's own Bézout certificate, and the `⊖τ`
  block is that certificate with the sign of `v` flipped
  (`ChabautyColeman.isCoprime_neg_map_C`).

`ChabautyColeman.isCoprime_phiPipeline` combines the blocks into avoidance for the pipeline
output. The consumer is `LeanPool.HyperellipticCurves.Log.Trace.TraceKz`, where these feed the
reduction-chain hypotheses of the generic chart capstone; `ChabautyColeman.isUnit_two_mul_map`
transports a doubled unit along a base change.

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B]

theorem isUnit_two_mul_map (φ : A →+* B) {x : A} (h : IsUnit (2 * x)) : IsUnit (2 * φ x) := by
  simpa [map_ofNat] using h.map φ

end BaseChange

section Pair

variable {O : Type*} [CommRing O] {f : O[X]} {a b xQ yQ m₀ : O} {m : O⟦X⟧}

/-- **Weierstrass avoidance for a constant pair block**: the divisor `(Q) + (ιP₀)` misses the
Weierstrass points exactly when `y_Q` and `b` are units. -/
theorem isCoprime_pair_const (hm₀ : m₀ * (a - xQ) = -b - yQ) (h2 : IsUnit (2 : O))
    (hb : IsUnit b) (hyQ : IsUnit yQ) :
    IsCoprime ((X - C xQ) * (X - C a)) (2 * pairV xQ yQ m₀) :=
  isCoprime_pairV hm₀ (h2.mul hyQ) (by rw [mul_neg]; exact (h2.mul hb).neg)

/-- **Weierstrass avoidance for the moving pair block on the residue disk.** The second point
is `ιQ`, so the condition is again that `y_Q` and `b` be units: the first point moves with the
disk parameter and its `y`-coordinate `b·η` is a unit because `η` has constant coefficient
`1`. -/
theorem isCoprime_phiU₁
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (h2 : IsUnit (2 : O)) (hb : IsUnit b) (hyQ : IsUnit yQ) :
    IsCoprime (phiU₁ a xQ) (2 * phiV₁ f a b m) := by
  have h₁ : IsUnit (2 * (PowerSeries.C b * diskSeriesGeneric f a)) := by
    refine PowerSeries.isUnit_iff_constantCoeff.mpr ?_
    rw [map_mul, map_mul, constantCoeff_diskSeriesGeneric, mul_one,
      PowerSeries.constantCoeff_C, map_ofNat]
    exact h2.mul hb
  have h₃ : IsUnit (2 * -yQ) := by rw [mul_neg]; exact (h2.mul hyQ).neg
  have h₂ : IsUnit (2 * PowerSeries.C (-yQ)) := isUnit_two_mul_map PowerSeries.C h₃
  rw [phiU₁, phiV₁]
  exact isCoprime_pairV hm h₁ h₂

theorem isCoprime_phiU₃ (hm₀ : m₀ * (a - xQ) = -b - yQ) (h2 : IsUnit (2 : O)) (hb : IsUnit b)
    (hyQ : IsUnit yQ) : IsCoprime (phiU₃ a xQ) (2 * phiV₃ xQ yQ m₀) := by
  rw [phiU₃, phiV₃]
  exact isCoprime_two_mul_map (isCoprime_pair_const hm₀ h2 hb hyQ) PowerSeries.C

end Pair

section Formal

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}
  {dτ : CantorCertData (MvPowerSeries (Fin n ⊕ Fin n) O)}

/-- Weierstrass avoidance for the `⊖τ` block: the centre's certificate with the sign of `v`
flipped. -/
theorem isCoprime_neg_map_C {σ : Type*} (hbez : c₁ * u + c₂ * (2 * v) = 1) :
    IsCoprime (u.map (MvPowerSeries.C : O →+* MvPowerSeries σ O))
      (2 * -(v.map MvPowerSeries.C)) := by
  have h := (isCoprime_two_mul_map ⟨c₁, c₂, hbez⟩
    (MvPowerSeries.C : O →+* MvPowerSeries σ O)).neg_right
  rwa [← mul_neg] at h

end Formal

section Disk

variable {O : Type*} [CommRing O] {f uτ vτ c₁ c₂ : O[X]}
  {a b xQ yQ m₀ : O} {m : O⟦X⟧} {d : CantorCertData O⟦X⟧}

/-- **Weierstrass avoidance of the per-disk pipeline output** is the second condition of the
avoidance bundle: nothing beyond the bundle is needed. -/
theorem isCoprime_phiPipeline
    (hav : IsPipelineAvoid (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d) :
    IsCoprime (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1
      (2 * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2) :=
  hav.hcop₂

end Disk

end ChabautyColeman

end
