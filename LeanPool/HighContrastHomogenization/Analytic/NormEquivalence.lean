/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.WeightedEnergy

/-!
# High-contrast homogenization: Analytic.NormEquivalence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Removing the coefficient field from the approximation conditions

`h1sNormSqOn b V u Du` is `‖u‖_{L¹(V)}² + ∫_V Du · σ Du`, the squared `H¹_s`
norm of `s.introduction` evaluated on a pair `(u, Du)`.  Only the second
summand sees the coefficient field, and where the field is uniformly elliptic
almost everywhere on `V` it is pinched between `lam` and `Lam` multiples of
`∫_V ‖Du‖²`, with the constants of `V`.  The whole quantity is therefore
two-sidedly comparable to an unweighted companion, and a sequence tends to `0` in
one exactly when it does in the other: every approximation condition of the
membership classes is a condition on the classical unweighted space, with the
rough coefficient field absent from it.

The ellipticity hypothesis is not removable, but it is a per-set hypothesis: what
the comparison needs on `V` is a pair of constants for `V`.  Both comparison
constants, `min 1 lam` and `max 1 Lam`, degenerate without it, and the
equivalence fails for a coefficient field whose symmetric part is not bounded
below on `V`.

The second section treats the skew part, which the comparison says nothing
about: on every bounded set, with that set's constants, the two inequalities
packaged in `IsEllipticMatrix` bound the whole matrix, hence its skew part, by
`Lam`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The norm-equivalence reduction

`h1sNormSqOn b V u Du = ‖u‖_{L¹(V)}² + ∫_V Du · s Du`.  Only the second summand
sees the coefficient field, and on every bounded set, with that set's constants,
it is pinched between `lam` and `Lam` multiples of `∫_V ‖Du‖²` by the two halves
already proved for the weighted energy.  Consequently the whole quantity is
two-sidedly comparable to the *unweighted* quantity below, and — the point of
this section — a sequence tends to `0` in the weighted quantity exactly when it
does in the unweighted one.  The rough coefficient field is therefore absent
from the residual density question, which becomes a citable classical fact
about the ordinary space `L¹(V) × L²(V)` rather than an open question about
weighted spaces. -/

/-- The unweighted companion of `h1sNormSqOn`: `‖u‖_{L¹(V)}² + ∫_V ‖Du‖²`. -/
@[expose]
def h1NormSqOnUnweighted (V : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    ℝ≥0∞ :=
  (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2 +
    ∫⁻ x in V, ENNReal.ofReal (vecNormSq (Du x)) ∂volume

/-- The lower half of the two-sided comparison.  The constant `min 1 lam` is the
worse of the two summandwise constants: `1` on the `L¹` term, which carries no
weight, and `lam` on the energy term. -/
theorem ofReal_min_mul_h1NormSqOnUnweighted_le_h1sNormSqOn_restrict
    {b : CoeffField d} {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x))
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    ENNReal.ofReal (min 1 lam) * h1NormSqOnUnweighted V u Du ≤
      h1sNormSqOn b V u Du := by
  have h1 : ENNReal.ofReal (min 1 lam) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have h2 : ENNReal.ofReal (min 1 lam) ≤ ENNReal.ofReal lam :=
    ENNReal.ofReal_le_ofReal (min_le_right _ _)
  simp only [h1NormSqOnUnweighted, h1sNormSqOn, mul_add]
  refine add_le_add ?_ ?_
  · calc ENNReal.ofReal (min 1 lam) *
          (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2
        ≤ 1 * (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2 :=
          mul_le_mul' h1 le_rfl
      _ = (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2 := one_mul _
  · calc ENNReal.ofReal (min 1 lam) *
          ∫⁻ x in V, ENNReal.ofReal (vecNormSq (Du x)) ∂volume
        ≤ ENNReal.ofReal lam *
            ∫⁻ x in V, ENNReal.ofReal (vecNormSq (Du x)) ∂volume :=
          mul_le_mul' h2 le_rfl
      _ ≤ sEnergyOn b V Du :=
          lintegral_ofReal_vecNormSq_le_sEnergyOn_restrict (Lam := Lam) hell Du

/-- The lower half of the two-sided comparison, with the pinching read on all of
`ℝ^d`. -/
theorem ofReal_min_mul_h1NormSqOnUnweighted_le_h1sNormSqOn {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) :
    ENNReal.ofReal (min 1 lam) * h1NormSqOnUnweighted V u Du ≤
      h1sNormSqOn b V u Du :=
  ofReal_min_mul_h1NormSqOnUnweighted_le_h1sNormSqOn_restrict (Lam := Lam)
    (ae_restrict_of_ae hell) u Du

/-- The upper half of the two-sided comparison, with constant `max 1 Lam` and the
pinching read on `V` alone. -/
theorem h1sNormSqOn_le_ofReal_max_mul_h1NormSqOnUnweighted_restrict
    {b : CoeffField d} {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x))
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    h1sNormSqOn b V u Du ≤
      ENNReal.ofReal (max 1 Lam) * h1NormSqOnUnweighted V u Du := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 Lam) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h2 : ENNReal.ofReal Lam ≤ ENNReal.ofReal (max 1 Lam) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  simp only [h1NormSqOnUnweighted, h1sNormSqOn, mul_add]
  refine add_le_add ?_ ?_
  · calc (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2
        = 1 * (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2 := (one_mul _).symm
      _ ≤ ENNReal.ofReal (max 1 Lam) *
            (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2 :=
          mul_le_mul' h1 le_rfl
  · exact (sEnergyOn_le_lintegral_ofReal_vecNormSq_restrict (lam := lam) hell Du).trans
      (mul_le_mul' h2 le_rfl)

/-- The upper half of the two-sided comparison, with constant `max 1 Lam`. -/
theorem h1sNormSqOn_le_ofReal_max_mul_h1NormSqOnUnweighted {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) :
    h1sNormSqOn b V u Du ≤
      ENNReal.ofReal (max 1 Lam) * h1NormSqOnUnweighted V u Du :=
  h1sNormSqOn_le_ofReal_max_mul_h1NormSqOnUnweighted_restrict (lam := lam)
    (ae_restrict_of_ae hell) u Du

/-- Domination transfers a limit `0` in `ℝ≥0∞`. -/
theorem tendsto_zero_of_le_of_tendsto_zero {ι : Type*} {l : Filter ι}
    {f g : ι → ℝ≥0∞} (hfg : ∀ n, f n ≤ g n)
    (hg : Filter.Tendsto g l (nhds 0)) : Filter.Tendsto f l (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hg ⊢
  intro ε hε
  filter_upwards [hg ε hε] with n hn using (hfg n).trans hn

/-- **The reduction.**  On every bounded set, with that set's constants,
convergence to `0` in the weighted `H¹_s` quantity is *equivalent* to convergence
to `0` in the unweighted quantity.  The coefficient field `b` has disappeared from the right
hand side: every remaining density question about the `H¹_s` part of `MemH1a`,
`MemH1a0` and `MemH1sLoc` is a question about the classical unweighted space. -/
theorem tendsto_h1sNormSqOn_zero_iff_restrict {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x)) {ι : Type*}
    {l : Filter ι} (u : ι → Vec d → ℝ) (Du : ι → Vec d → Vec d) :
    Filter.Tendsto (fun n => h1sNormSqOn b V (u n) (Du n)) l (nhds 0) ↔
      Filter.Tendsto (fun n => h1NormSqOnUnweighted V (u n) (Du n)) l
        (nhds 0) := by
  set k : ℝ≥0∞ := ENNReal.ofReal (min 1 lam) with hk
  have hk0 : k ≠ 0 := by
    rw [hk, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_min one_pos hlam
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro h
    have hmul : Filter.Tendsto (fun n => k * h1NormSqOnUnweighted V (u n) (Du n))
        l (nhds 0) :=
      tendsto_zero_of_le_of_tendsto_zero
        (fun n => ofReal_min_mul_h1NormSqOnUnweighted_le_h1sNormSqOn_restrict
          (Lam := Lam) hell _ _) h
    have hinv := ENNReal.Tendsto.const_mul hmul (Or.inr (ENNReal.inv_ne_top.mpr hk0))
    rw [mul_zero] at hinv
    refine hinv.congr fun n => ?_
    rw [← mul_assoc, ENNReal.inv_mul_cancel hk0 hktop, one_mul]
  · intro h
    have hM : Filter.Tendsto
        (fun n => ENNReal.ofReal (max 1 Lam) * h1NormSqOnUnweighted V (u n) (Du n))
        l (nhds 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (max 1 Lam)) h
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at hc
    exact tendsto_zero_of_le_of_tendsto_zero
      (fun n => h1sNormSqOn_le_ofReal_max_mul_h1NormSqOnUnweighted_restrict
        (lam := lam) hell _ _) hM

/-- **The reduction**, with the pinching read on all of `ℝ^d`. -/
theorem tendsto_h1sNormSqOn_zero_iff {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) {ι : Type*}
    {l : Filter ι} (u : ι → Vec d → ℝ) (Du : ι → Vec d → Vec d) :
    Filter.Tendsto (fun n => h1sNormSqOn b V (u n) (Du n)) l (nhds 0) ↔
      Filter.Tendsto (fun n => h1NormSqOnUnweighted V (u n) (Du n)) l
        (nhds 0) :=
  tendsto_h1sNormSqOn_zero_iff_restrict (Lam := Lam) hlam
    (ae_restrict_of_ae hell) u Du

/-- The reduction at the exact shape occurring in `MemH1a`, `MemH1a0` and
`MemH1sLoc`, with the pinching read on `V` alone: the `H¹_s` approximation
condition on a smooth approximating sequence is unweighted `H¹` approximation. -/
theorem tendsto_h1sNormSqOn_sub_zero_iff_restrict {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x))
    (u : Vec d → ℝ) (Du : Vec d → Vec d) (v : ℕ → Vec d → ℝ) :
    Filter.Tendsto
        (fun n => h1sNormSqOn b V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto
        (fun n => h1NormSqOnUnweighted V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) :=
  tendsto_h1sNormSqOn_zero_iff_restrict (Lam := Lam) hlam hell _ _

/-- The reduction at the exact shape occurring in `MemH1a`, `MemH1a0` and
`MemH1sLoc`: the `H¹_s` approximation condition on a smooth approximating
sequence is unweighted `H¹` approximation. -/
theorem tendsto_h1sNormSqOn_sub_zero_iff {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) (v : ℕ → Vec d → ℝ) :
    Filter.Tendsto
        (fun n => h1sNormSqOn b V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto
        (fun n => h1NormSqOnUnweighted V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) :=
  tendsto_h1sNormSqOn_sub_zero_iff_restrict (Lam := Lam) hlam
    (ae_restrict_of_ae hell) u Du _

/-! ## The skew flux is not a second obstruction

`MemH1a` carries a *third* clause beyond the `H¹_s` approximation, namely
`skewFluxDualNorm b V (∇vₙ - Du) → 0`, and the previous section says nothing
about it.  One might
fear that this clause is a genuinely separate density problem, with no ambient
bound on the skew part `k` available — that is what "high contrast" would
normally mean.

It is not.  On the class actually used here, `AEUniformlyEllipticField`, the two
inequalities packaged in `IsEllipticMatrix` (coercivity of `A` and coercivity of
`A⁻¹`) already bound the *whole* matrix on every bounded set, with that set's
constants, hence its skew part; the fact
is `vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix` in CoarseGraining.  The
three lemmas below are the pointwise ingredients of the resulting domination
`skewFluxDualNorm b V F ≲ Lam · lam^{-1/2} · ‖F‖_{L²(V)}`, which makes the third
clause a *consequence* of the second rather than an independent obligation.
Only the integrability bookkeeping of the `⊤` branch of `skewFluxPairing`
separates these ingredients from that statement. -/

/-- **The skew part is bounded on the coefficient class.**  The uniform
ellipticity that `AEUniformlyEllipticField` supplies on each bounded set bounds
the whole matrix there, hence its skew part, by `Lam`: the high-contrast
degeneracy does not reach the skew flux. -/
theorem ae_vecNormSq_matVecMul_skewPart_le {b : CoeffField d} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) :
    ∀ᵐ x ∂volume, ∀ ξ : Vec d,
      vecNormSq (matVecMul (skewPart (b x)) ξ) ≤ Lam ^ 2 * vecNormSq ξ := by
  filter_upwards [hell] with x hx
  exact fun ξ => vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix hx ξ

/-- Cauchy–Schwarz for the integrand of `skewFluxPairing`: it is bounded by
`Lam` times the product of the two Euclidean norms. -/
theorem sq_vecDot_matVecMul_skewPart_le {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (G F : Vec d) :
    vecDot G (matVecMul (skewPart A) F) ^ 2 ≤
      Lam ^ 2 * (vecNormSq G * vecNormSq F) := by
  calc vecDot G (matVecMul (skewPart A) F) ^ 2
      ≤ vecNormSq G * vecNormSq (matVecMul (skewPart A) F) :=
        sq_vecDot_le_vecNormSq_mul_vecNormSq G (matVecMul (skewPart A) F)
    _ ≤ vecNormSq G * (Lam ^ 2 * vecNormSq F) :=
        mul_le_mul_of_nonneg_left
          (vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix hA F)
          (vecNormSq_nonneg G)
    _ = Lam ^ 2 * (vecNormSq G * vecNormSq F) := by ring

/-- **The test class of `skewFluxDualNorm` is bounded in `L²`.**  A test of unit
weighted `H¹_s` norm has squared `L²` gradient at most `lam⁻¹`, so the supremum
defining the dual norm ranges over an `L²`-bounded family. -/
theorem lintegral_vecNormSq_le_of_h1sNormSqOn_le_one {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) {φ : Vec d → ℝ}
    (hφ : h1sNormSqOn b V φ (smoothGrad φ) ≤ 1) :
    (∫⁻ x in V, ENNReal.ofReal (vecNormSq (smoothGrad φ x)) ∂volume) ≤
      ENNReal.ofReal lam⁻¹ := by
  have hen : sEnergyOn b V (smoothGrad φ) ≤ 1 := by
    refine le_trans ?_ hφ
    simp only [h1sNormSqOn]
    exact le_add_self
  rw [ENNReal.ofReal_inv_of_pos hlam, ENNReal.le_inv_iff_mul_le]
  calc (∫⁻ x in V, ENNReal.ofReal (vecNormSq (smoothGrad φ x)) ∂volume) *
        ENNReal.ofReal lam
      = ENNReal.ofReal lam *
          ∫⁻ x in V, ENNReal.ofReal (vecNormSq (smoothGrad φ x)) ∂volume :=
        mul_comm _ _
    _ ≤ sEnergyOn b V (smoothGrad φ) :=
        lintegral_ofReal_vecNormSq_le_sEnergyOn hell (smoothGrad φ)
    _ ≤ 1 := hen

end

end HighContrast
end HCPolySupport
