/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Representation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Order.SuccPred.IntervalSucc

/-
Modified for Lean Pool: module names and imports adapted.

The adapted `phiFunctional` definition is from `MultilinearInterpolation/KMethod.lean`
at commit a351feafa218223404e53711861dd986822cd270.
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jim Potergies, Michael Rothgang, Lua Viana Reis
-/

/-!
# The discrete and the continuous K-method

For a bounded linear map `ι : Y → X`, `0 < θ` and `0 < q ≤ ∞`, the **continuous K-method**
measures `f ∈ X` by

`‖f‖_{K,θ,q} = (∫_0^∞ (t^(-θ) K(t, f))^q dt/t)^(1/q)`   (`ApproximationScheme.kMethodNorm`),

the essential supremum of `t^(-θ) K(t, f)` for `q = ∞`. The space `(X, Y)_{θ,q}` consists
of the `f` with `‖f‖_{K,θ,q} < ∞` (`ApproximationScheme.MemKMethod`). Bergh–Löfström,
Section 3.1, uses `0 < θ < 1` and `1 ≤ q ≤ ∞`, with `θ = 0, 1` also allowed when
`q = ∞`. The Lean definition admits all real `θ` and uses `eLpNorm`, which is zero for
`q = 0`. The main theorem (`ApproximationScheme.memInterp_iff_memKMethod`) extends the
two-sided comparison of their Lemma 3.1.3. For a bounded linear map, every one-sided grid
`t = 2^(-kρ)` with `ρ > 0` and the added ambient norm give the same space, with explicit
comparison constants
(`ApproximationScheme.kMethodNorm_le_interpNorm`, `ApproximationScheme.interpNorm_le_kMethodNorm`).
Hence the grid does not matter, and the representation theorem reads `A^s_q = (X, Y)_{s/r,q}`
for the continuous K-method (`ApproximationScheme.memApprox_iff_memKMethod`).

The proof passes through the grid `t = 2^(nρ)`, `n ∈ ℤ`, for every increasing
`φ : [0, ∞] → [0, ∞]` in place of `K(·, f)` (`ApproximationScheme.discretePhiSeq`).  On the
piece `[2^(nρ), 2^((n+1)ρ))`, whose measure for `dt/t` is `ρ log 2`, the integrand `t^(-θ) φ(t)`
lies between `2^(-ρθ)` times the `n`-th and `2^(ρθ)` times the `(n+1)`-th term of the sequence
`(2^(-nρθ) φ(2^(nρ)))_n`; the general comparison of an `L_q` norm with step functions on disjoint
pieces of equal measure is `MeasureTheory.eLpNorm_le_of_le_on_pieces` and
`MeasureTheory.le_eLpNorm_of_le_on_pieces`.  For `φ = K(·, f)`, the terms with `n ≤ 0` are the
sequence of `ApproximationScheme.interpNorm`, the term with `n = k + 1 > 0` is at most
`2^(-kρθ) ‖f‖`, and `‖f‖ ≤ max(1, ‖ι‖) K(1, f)`; the comparison of the two grids holds for every
`φ`, with an upper bound `M` of `φ` in place of `‖f‖`
(`ApproximationScheme.lqNorm_le_lqNorm_discretePhiSeq`,
`ApproximationScheme.lqNorm_discretePhiSeq_le`).  Under a change of scale,
`K(c t, f) ≤ max(1, c) K(t, f)` (`ApproximationScheme.kFunctional_mul_le`), and `‖f‖ ≤ K(t, f)`
for `t ≥ ‖ι‖` (`ApproximationScheme.enorm_le_kFunctional`).

The functional `ApproximationScheme.phiFunctional` is the formula of `EQuasinorm.phiFunctional`
in the project *MultilinearInterpolation* (Bonn; van Doorn, Portegies, Rothgang, Viana Reis;
Apache 2.0).  That project states the equivalence `discreteKMethod_equiv_kmethod`
for general quasi-normed couples on the grid `2^n`, `n ∈ ℤ`. The comparison below extends
Bergh–Löfström, Lemma 3.1.3, to a one-sided grid with arbitrary positive spacing, supplemented
by the ambient norm.  For `ρ = 1` and `θ ≥ 0`, the comparison of `phiFunctional` with its
discrete version
for increasing `φ` (`ApproximationScheme.phiFunctional_le_lqNorm_discretePhiSeq`,
`ApproximationScheme.lqNorm_discretePhiSeq_le_phiFunctional`) gives the two inequalities of that
equivalence for every couple whose K-functional is increasing in `t`.  This file applies it to
the couple given by a bounded linear map `ι`; `memInterp_iff_memKMethod` is its form with the
grid on `ℕ` and the term `‖f‖`.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ι : Y →L[ℝ] X}

/-! ### The K-functional across scales -/

/-- **The K-functional under a finite change of scale**: `K(c t, f) ≤ max(1, c) K(t, f)` for
`c < ∞`, since `‖f - ι y‖ + c t ‖y‖ ≤ max(1, c) (‖f - ι y‖ + t ‖y‖)` for every `y`. -/
theorem kFunctional_mul_le_of_ne_top {c : ℝ≥0∞} (hc : c ≠ ∞) (t : ℝ≥0∞) (f : X) :
    kFunctional ι (c * t) f ≤ max 1 c * kFunctional ι t f := by
  have hM0 : max 1 c ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  have hMt : max 1 c ≠ ∞ := max_ne_top ENNReal.one_ne_top hc
  rw [kFunctional, kFunctional, ENNReal.mul_iInf_of_ne hM0 hMt]
  refine iInf_mono fun y => ?_
  rw [mul_add, mul_assoc c]
  gcongr
  · exact le_mul_of_one_le_left' (le_max_left _ _)
  · exact le_max_right _ _

/-- **The K-functional at large scales bounds the norm**: `‖f‖ ≤ K(t, f)` for `t ≥ ‖ι‖`, since
`‖f‖ ≤ ‖f - ι y‖ + ‖ι‖ ‖y‖`. -/
theorem enorm_le_kFunctional {t : ℝ≥0∞} (ht : ‖ι‖ₑ ≤ t) (f : X) : ‖f‖ₑ ≤ kFunctional ι t f :=
  le_iInf fun y => calc
    ‖f‖ₑ = ‖(f - ι y) + ι y‖ₑ := by rw [sub_add_cancel]
    _ ≤ ‖f - ι y‖ₑ + ‖ι y‖ₑ := eNorm_add_le _ _
    _ ≤ ‖f - ι y‖ₑ + t * ‖y‖ₑ := by
        gcongr
        exact (ι.le_opENorm y).trans (by gcongr)

/-- **The norm by the K-functional at scale one**: `‖f‖ ≤ max(1, ‖ι‖) K(1, f)`. -/
theorem enorm_le_max_mul_kFunctional_one (f : X) : ‖f‖ₑ ≤ max 1 ‖ι‖ₑ * kFunctional ι 1 f := by
  have h := kFunctional_mul_le_of_ne_top (ι := ι) (eNorm_ne_top : ‖ι‖ₑ ≠ ∞) 1 f
  rw [mul_one] at h
  exact (enorm_le_kFunctional le_rfl f).trans h

/-- **The K-functional vanishes only at `0`**: if `K(t, f) = 0` for some `t > 0`, then `f = 0`.
With `s = min(t, 1)`, `‖f‖ ≤ K(‖ι‖, f) ≤ max(1, ‖ι‖/s) K(s, f) ≤ max(1, ‖ι‖/s) K(t, f)`. -/
theorem eq_zero_of_kFunctional_eq_zero {t : ℝ≥0∞} (ht : t ≠ 0) {f : X}
    (h : kFunctional ι t f = 0) : f = 0 := by
  have hs0 : min t 1 ≠ 0 := (lt_min (pos_iff_ne_zero.2 ht) zero_lt_one).ne'
  have hsT : min t 1 ≠ ∞ := (min_le_right t 1).trans_lt ENNReal.one_lt_top |>.ne
  have hc : ‖ι‖ₑ / min t 1 ≠ ∞ := ENNReal.div_ne_top eNorm_ne_top hs0
  have hf : ‖f‖ₑ ≤ 0 := calc
    ‖f‖ₑ ≤ kFunctional ι (‖ι‖ₑ / min t 1 * min t 1) f :=
        enorm_le_kFunctional (ENNReal.div_mul_cancel hs0 hsT).ge f
    _ ≤ max 1 (‖ι‖ₑ / min t 1) * kFunctional ι (min t 1) f :=
        kFunctional_mul_le_of_ne_top hc _ f
    _ ≤ max 1 (‖ι‖ₑ / min t 1) * kFunctional ι t f := by
        gcongr
        exact kFunctional_mono (min_le_left t 1) f
    _ = 0 := by rw [h, mul_zero]
  exact eNorm_eq_zero.1 (nonpos_iff_eq_zero.1 hf)

/-- **The K-functional under a change of scale**: `K(c t, f) ≤ max(1, c) K(t, f)` for every
`c, t ∈ [0, ∞]`.  For `c = ∞` and `t > 0` the right side is `∞` unless `K(t, f) = 0`, and then
`f = 0`. -/
theorem kFunctional_mul_le (c t : ℝ≥0∞) (f : X) :
    kFunctional ι (c * t) f ≤ max 1 c * kFunctional ι t f := by
  rcases ne_or_eq c ∞ with hc | rfl
  · exact kFunctional_mul_le_of_ne_top hc t f
  rcases eq_or_ne t 0 with rfl | ht
  · rw [mul_zero]
    exact le_mul_of_one_le_left' (le_max_left _ _)
  rcases eq_or_ne (kFunctional ι t f) 0 with h | h
  · rw [eq_zero_of_kFunctional_eq_zero ht h, kFunctional_zero_right]
    exact zero_le
  · rw [max_eq_right le_top, ENNReal.top_mul h]
    exact le_top

/-! ### The continuous K-method -/

/-- The measure `dt/t` on `(0, ∞)`, as a measure on `ℝ`: Lebesgue measure with density `1/t`,
restricted to `t > 0`. -/
noncomputable def kMethodMeasure : Measure ℝ :=
  (volume.withDensity (·.toNNReal⁻¹)).restrict (Ioi 0)

/-- The functional `Φ_{θ,q}(φ) = (∫_0^∞ (t^(-θ) φ(t))^q dt/t)^(1/q)` of a function
`φ : [0, ∞] → [0, ∞]` (the essential supremum of `t^(-θ) φ(t)` for `q = ∞`).  The formula is
that of `EQuasinorm.phiFunctional` in the project *MultilinearInterpolation* (Bonn, Apache 2.0). -/
noncomputable def phiFunctional (θ : ℝ) (q : ℝ≥0∞) (φ : ℝ≥0∞ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (fun (t : ℝ) ↦ t.toNNReal ^ (-θ) * φ t.toNNReal) q
    (volume.withDensity (·.toNNReal⁻¹) |>.restrict (Ioi 0))

/-- The integrand `t ↦ t^(-θ) φ(t)` of `Φ_{θ,q}(φ)`, for `t : ℝ`. -/
noncomputable def phiIntegrand (θ : ℝ) (φ : ℝ≥0∞ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal t ^ (-θ) * φ (ENNReal.ofReal t)

variable {θ ρ : ℝ} {q : ℝ≥0∞} {φ : ℝ≥0∞ → ℝ≥0∞}

/-- `Φ_{θ,q}(φ)` is the `L_q(dt/t)` norm of `t ↦ t^(-θ) φ(t)`. -/
theorem phiFunctional_eq (φ : ℝ≥0∞ → ℝ≥0∞) :
    phiFunctional θ q φ = eLpNorm (phiIntegrand θ φ) q kMethodMeasure := rfl

/-- For a measurable `φ`, the integrand `t ↦ t^(-θ) φ(t)` is measurable. -/
theorem measurable_phiIntegrand_of_measurable (hφ : Measurable φ) :
    Measurable (phiIntegrand θ φ) :=
  (ENNReal.measurable_ofReal.pow_const _).mul (hφ.comp ENNReal.measurable_ofReal)

/-- For an increasing `φ`, the integrand `t ↦ t^(-θ) φ(t)` is measurable. -/
theorem measurable_phiIntegrand (hφ : Monotone φ) : Measurable (phiIntegrand θ φ) :=
  measurable_phiIntegrand_of_measurable hφ.measurable

/-- `Φ_{θ,q}(φ)` depends only on the values of `φ` on `(0, ∞)`: if `φ t = ψ t` for every
`t ≠ 0, ∞`, then `Φ_{θ,q}(φ) = Φ_{θ,q}(ψ)`. -/
theorem phiFunctional_congr {ψ : ℝ≥0∞ → ℝ≥0∞} (h : ∀ t, t ≠ 0 → t ≠ ∞ → φ t = ψ t) :
    phiFunctional θ q φ = phiFunctional θ q ψ := by
  rw [phiFunctional_eq, phiFunctional_eq, kMethodMeasure]
  refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun t ht => ?_))
  rw [phiIntegrand, phiIntegrand, h _ (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top]

variable (ι) in
/-- The norm of the **continuous K-method**, `‖f‖_{K,θ,q} = Φ_{θ,q}(K(·, f))`, that is
`(∫_0^∞ (t^(-θ) K(t, f))^q dt/t)^(1/q)` for `0 < q < ∞`, the essential supremum of
`t^(-θ) K(t, f)` for `q = ∞`, and `0` for `q = 0` by the `eLpNorm` convention. This
extends the classical range of Bergh–Löfström, Section 3.1, described above. -/
noncomputable def kMethodNorm (θ : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  phiFunctional θ q fun t => kFunctional ι t f

variable (ι) in
/-- `f` belongs to the **real interpolation space** `(X, Y)_{θ,q}` of the continuous
K-method: `‖f‖_{K,θ,q} < ∞`. -/
def MemKMethod (θ : ℝ) (q : ℝ≥0∞) (f : X) : Prop := kMethodNorm ι θ q f < ∞

variable (ι) in
/-- The integrand `t ↦ t^(-θ) K(t, f)` of the continuous K-method, for `t : ℝ`. -/
noncomputable def kMethodIntegrand (θ : ℝ) (f : X) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal t ^ (-θ) * kFunctional ι (ENNReal.ofReal t) f

/-- The continuous K-norm is the `L_q(dt/t)` norm of `t ↦ t^(-θ) K(t, f)`. -/
theorem kMethodNorm_eq (f : X) :
    kMethodNorm ι θ q f = eLpNorm (kMethodIntegrand ι θ f) q kMethodMeasure := rfl

/-- The integrand of the continuous K-method is measurable (`K(·, f)` is monotone). -/
theorem measurable_kMethodIntegrand (f : X) : Measurable (kMethodIntegrand ι θ f) :=
  measurable_phiIntegrand (monotone_kFunctional f)

/-! ### The dyadic pieces of `(0, ∞)` -/

/-- The dyadic piece `[2^(nρ), 2^((n+1)ρ))` of `(0, ∞)`. -/
noncomputable def dyadicPiece (ρ : ℝ) (n : ℤ) : Set ℝ :=
  Ico ((2 : ℝ) ^ ((n : ℝ) * ρ)) ((2 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * ρ))

/-- The dyadic pieces are measurable. -/
theorem measurableSet_dyadicPiece (ρ : ℝ) (n : ℤ) : MeasurableSet (dyadicPiece ρ n) :=
  measurableSet_Ico

/-- The dyadic pieces lie in `(0, ∞)`. -/
theorem dyadicPiece_subset_Ioi (ρ : ℝ) (n : ℤ) : dyadicPiece ρ n ⊆ Ioi 0 :=
  fun _ ht => lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) ht.1

/-- A point `t` of the dyadic piece `[2^(nρ), 2^((n+1)ρ))` satisfies
`2^(nρ) ≤ t ≤ 2^((n+1)ρ)` as an element of `[0, ∞]`. -/
theorem ofReal_mem_Icc_of_mem_dyadicPiece {n : ℤ} {t : ℝ} (ht : t ∈ dyadicPiece ρ n) :
    ENNReal.ofReal t ∈
      Icc ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) ((2 : ℝ≥0∞) ^ (((n + 1 : ℤ) : ℝ) * ρ)) := by
  rw [← ENNReal.ofReal_two_rpow, ← ENNReal.ofReal_two_rpow]
  exact ⟨ENNReal.ofReal_le_ofReal ht.1, ENNReal.ofReal_le_ofReal ht.2.le⟩

/-- The dyadic pieces are pairwise disjoint for `ρ ≥ 0`. -/
theorem pairwise_disjoint_dyadicPiece (hρ : 0 ≤ ρ) : Pairwise (Disjoint on dyadicPiece ρ) := by
  have hmono : Monotone fun n : ℤ => (2 : ℝ) ^ ((n : ℝ) * ρ) := fun m n h =>
    Real.rpow_le_rpow_of_exponent_le one_le_two
      (mul_le_mul_of_nonneg_right (Int.cast_le.2 h) hρ)
  have h := Monotone.pairwise_disjoint_on_Ico_succ hmono
  simp only [Order.succ_eq_add_one] at h
  exact h

/-- For `ρ > 0` the dyadic pieces cover `(0, ∞)`. -/
theorem exists_mem_dyadicPiece (hρ : 0 < ρ) {t : ℝ} (ht : 0 < t) :
    ∃ n, t ∈ dyadicPiece ρ n := by
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow ht (Real.one_lt_rpow one_lt_two hρ)
  have h : ∀ m : ℤ, ((2 : ℝ) ^ ρ) ^ m = (2 : ℝ) ^ ((m : ℝ) * ρ) := fun m => by
    rw [← Real.rpow_intCast, ← Real.rpow_mul zero_le_two, mul_comm]
  rw [h, h] at hn
  exact ⟨n, hn⟩

/-- For `ρ > 0`, almost every point for `dt/t` lies in a dyadic piece. -/
theorem ae_mem_iUnion_dyadicPiece (hρ : 0 < ρ) :
    ∀ᵐ t ∂kMethodMeasure, t ∈ ⋃ n, dyadicPiece ρ n := by
  rw [kMethodMeasure]
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun t ht => mem_iUnion.2 (exists_mem_dyadicPiece hρ ht))

/-- **The measure `dt/t` of a dyadic piece** is `log 2^ρ = ρ log 2`, for `ρ ≥ 0`. -/
theorem kMethodMeasure_dyadicPiece (hρ : 0 ≤ ρ) (n : ℤ) :
    kMethodMeasure (dyadicPiece ρ n) = ENNReal.ofReal (ρ * Real.log 2) := by
  have ha : 0 < (2 : ℝ) ^ ((n : ℝ) * ρ) := Real.rpow_pos_of_pos two_pos _
  have hb : 0 < (2 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * ρ) := Real.rpow_pos_of_pos two_pos _
  have hab : (2 : ℝ) ^ ((n : ℝ) * ρ) ≤ (2 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * ρ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by push_cast; nlinarith)
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (dyadicPiece ρ n) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ico_subset_Icc_self
    exact continuousOn_inv₀.mono fun t ht => (ha.trans_le ht.1).ne'
  have hnn : 0 ≤ᵐ[volume.restrict (dyadicPiece ρ n)] fun t : ℝ => t⁻¹ :=
    (ae_restrict_iff' measurableSet_Ico).2
      (Filter.Eventually.of_forall fun t ht => inv_nonneg.2 (ha.le.trans ht.1))
  rw [kMethodMeasure, Measure.restrict_apply (measurableSet_dyadicPiece ρ n),
    inter_eq_left.2 (dyadicPiece_subset_Ioi ρ n),
    withDensity_apply _ (measurableSet_dyadicPiece ρ n)]
  calc ∫⁻ t in dyadicPiece ρ n, ((t.toNNReal : ℝ≥0∞))⁻¹
      = ∫⁻ t in dyadicPiece ρ n, ENNReal.ofReal t⁻¹ :=
        setLIntegral_congr_fun (measurableSet_dyadicPiece ρ n) fun t ht =>
          (ENNReal.ofReal_inv_of_pos (ha.trans_le ht.1)).symm
    _ = ENNReal.ofReal (∫ t in dyadicPiece ρ n, t⁻¹) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (ρ * Real.log 2) := by
        rw [dyadicPiece, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          integral_inv_of_pos ha hb, ← Real.rpow_sub two_pos, Real.log_rpow two_pos]
        congr 2
        push_cast
        ring

/-- The measure `ρ log 2` of a dyadic piece is nonzero for `ρ > 0`. -/
theorem ofReal_mul_log_two_ne_zero (hρ : 0 < ρ) : ENNReal.ofReal (ρ * Real.log 2) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (mul_pos hρ (Real.log_pos one_lt_two))).ne'

/-! ### The discrete functional on the grid `2^(nρ)`, `n ∈ ℤ` -/

/-- The sequence `(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}`: the function `φ` sampled on the grid
`t = 2^(nρ)` with the weight `t^(-θ)`.  For `ρ = 1` its `ℓ_q` norm is the formula of
`EQuasinorm.discretePhiFunctional θ q (n ↦ φ(2^n))` in the project *MultilinearInterpolation*. -/
noncomputable def discretePhiSeq (θ ρ : ℝ) (φ : ℝ≥0∞ → ℝ≥0∞) (n : ℤ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (-((n : ℝ) * ρ * θ)) * φ ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ))

/-- **Upper bound on a piece**: for an increasing `φ`, `θ ≥ 0` and
`t ∈ [2^(nρ), 2^((n+1)ρ))`, `t^(-θ) φ(t) ≤ 2^(ρθ) · 2^(-(n+1)ρθ) φ(2^((n+1)ρ))`. -/
theorem phiIntegrand_le_discretePhiSeq (hφ : Monotone φ) (hθ : 0 ≤ θ) {n : ℤ} {t : ℝ}
    (ht : t ∈ dyadicPiece ρ n) :
    phiIntegrand θ φ t ≤ 2 ^ (ρ * θ) * discretePhiSeq θ ρ φ (n + 1) := by
  have h := ofReal_mem_Icc_of_mem_dyadicPiece ht
  have hw : ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) ^ (-θ) =
      2 ^ (ρ * θ) * 2 ^ (-(((n + 1 : ℤ) : ℝ) * ρ * θ)) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    congr 1
    push_cast
    ring
  calc phiIntegrand θ φ t
      ≤ ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) ^ (-θ) * φ ((2 : ℝ≥0∞) ^ (((n + 1 : ℤ) : ℝ) * ρ)) :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_nonpos h.1 (neg_nonpos.2 hθ)) (hφ h.2)
    _ = 2 ^ (ρ * θ) * discretePhiSeq θ ρ φ (n + 1) := by
        rw [hw, discretePhiSeq, mul_assoc]

/-- **Lower bound on a piece**: for an increasing `φ`, `θ ≥ 0` and
`t ∈ [2^(nρ), 2^((n+1)ρ))`, `2^(-ρθ) · 2^(-nρθ) φ(2^(nρ)) ≤ t^(-θ) φ(t)`. -/
theorem discretePhiSeq_le_phiIntegrand (hφ : Monotone φ) (hθ : 0 ≤ θ) {n : ℤ} {t : ℝ}
    (ht : t ∈ dyadicPiece ρ n) :
    2 ^ (-(ρ * θ)) * discretePhiSeq θ ρ φ n ≤ phiIntegrand θ φ t := by
  have h := ofReal_mem_Icc_of_mem_dyadicPiece ht
  have hw : 2 ^ (-(ρ * θ)) * (2 : ℝ≥0∞) ^ (-((n : ℝ) * ρ * θ)) =
      ((2 : ℝ≥0∞) ^ (((n + 1 : ℤ) : ℝ) * ρ)) ^ (-θ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    congr 1
    push_cast
    ring
  calc 2 ^ (-(ρ * θ)) * discretePhiSeq θ ρ φ n
      = ((2 : ℝ≥0∞) ^ (((n + 1 : ℤ) : ℝ) * ρ)) ^ (-θ) * φ ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) := by
        rw [discretePhiSeq, ← mul_assoc, hw]
    _ ≤ phiIntegrand θ φ t :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_nonpos h.2 (neg_nonpos.2 hθ)) (hφ h.1)

/-- **The functional `Φ_{θ,q}` by its discrete version**: for an increasing `φ`, `θ ≥ 0` and
`ρ > 0`, `Φ_{θ,q}(φ) ≤ (ρ log 2)^(1/q) 2^(ρθ) ‖(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}‖_{ℓ_q}`. -/
theorem phiFunctional_le_lqNorm_discretePhiSeq (hφ : Monotone φ) (hθ : 0 ≤ θ) (hρ : 0 < ρ) :
    phiFunctional θ q φ ≤ ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
      (2 ^ (ρ * θ) * lqNorm q (discretePhiSeq θ ρ φ)) := by
  rw [phiFunctional_eq, ← ENNReal.lqNorm_comp_equiv (Equiv.addRight (1 : ℤ)),
    ← ENNReal.lqNorm_const_mul]
  exact eLpNorm_le_of_le_on_pieces (measurable_phiIntegrand hφ).aestronglyMeasurable
    (measurableSet_dyadicPiece ρ) (pairwise_disjoint_dyadicPiece hρ.le)
    (ae_mem_iUnion_dyadicPiece hρ) (kMethodMeasure_dyadicPiece hρ.le)
    fun _ _ ht => phiIntegrand_le_discretePhiSeq hφ hθ ht

/-- **The discrete version of `Φ_{θ,q}` by the functional**: for an increasing `φ`, `θ ≥ 0`
and `ρ > 0`, `(ρ log 2)^(1/q) 2^(-ρθ) ‖(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}‖_{ℓ_q} ≤ Φ_{θ,q}(φ)`. -/
theorem lqNorm_discretePhiSeq_le_phiFunctional (hφ : Monotone φ) (hθ : 0 ≤ θ) (hρ : 0 < ρ) :
    ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
      (2 ^ (-(ρ * θ)) * lqNorm q (discretePhiSeq θ ρ φ)) ≤ phiFunctional θ q φ := by
  rw [phiFunctional_eq, ← ENNReal.lqNorm_const_mul]
  exact le_eLpNorm_of_le_on_pieces (measurableSet_dyadicPiece ρ)
    (pairwise_disjoint_dyadicPiece hρ.le) (kMethodMeasure_dyadicPiece hρ.le)
    (ofReal_mul_log_two_ne_zero hρ) fun _ _ ht => discretePhiSeq_le_phiIntegrand hφ hθ ht

/-! ### The discrete K-method on the grid `2^(nρ)`, `n ∈ ℤ` -/

variable (ι) in
/-- The sequence `(2^(-nρθ) K(2^(nρ), f))_{n ∈ ℤ}` of the discrete K-method on the grid
`t = 2^(nρ)`: `discretePhiSeq θ ρ` for `φ = K(·, f)`. -/
noncomputable def discreteKSeq (θ ρ : ℝ) (f : X) (n : ℤ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (-((n : ℝ) * ρ * θ)) * kFunctional ι ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) f

variable (ι) in
/-- The norm of the **discrete K-method** on the grid `t = 2^(nρ)`, `n ∈ ℤ`:
`‖(2^(-nρθ) K(2^(nρ), f))_{n ∈ ℤ}‖_{ℓ_q}`.  For `ρ = 1` this is the formula of
`discreteKMethod` in the project *MultilinearInterpolation*. -/
noncomputable def discreteKMethodNorm (θ ρ : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  lqNorm q (discreteKSeq ι θ ρ f)

/-- The discrete K-norm on `ℤ` is the `ℓ_q` norm of `discretePhiSeq θ ρ` for `φ = K(·, f)`. -/
theorem discreteKMethodNorm_eq (f : X) : discreteKMethodNorm ι θ ρ q f =
    lqNorm q (discretePhiSeq θ ρ fun t => kFunctional ι t f) := rfl

/-- **Upper bound on a piece**: for `t ∈ [2^(nρ), 2^((n+1)ρ))` and `θ ≥ 0`,
`t^(-θ) K(t, f) ≤ 2^(ρθ) · 2^(-(n+1)ρθ) K(2^((n+1)ρ), f)`. -/
theorem kMethodIntegrand_le_discreteKSeq (hθ : 0 ≤ θ) {n : ℤ} {t : ℝ}
    (ht : t ∈ dyadicPiece ρ n) (f : X) :
    kMethodIntegrand ι θ f t ≤ 2 ^ (ρ * θ) * discreteKSeq ι θ ρ f (n + 1) :=
  phiIntegrand_le_discretePhiSeq (monotone_kFunctional f) hθ ht

/-- **Lower bound on a piece**: for `t ∈ [2^(nρ), 2^((n+1)ρ))` and `θ ≥ 0`,
`2^(-ρθ) · 2^(-nρθ) K(2^(nρ), f) ≤ t^(-θ) K(t, f)`. -/
theorem discreteKSeq_le_kMethodIntegrand (hθ : 0 ≤ θ) {n : ℤ} {t : ℝ}
    (ht : t ∈ dyadicPiece ρ n) (f : X) :
    2 ^ (-(ρ * θ)) * discreteKSeq ι θ ρ f n ≤ kMethodIntegrand ι θ f t :=
  discretePhiSeq_le_phiIntegrand (monotone_kFunctional f) hθ ht

/-- **The continuous K-norm by the discrete one on `ℤ`**: for `θ ≥ 0` and `ρ > 0`,
`‖f‖_{K,θ,q} ≤ (ρ log 2)^(1/q) 2^(ρθ) ‖(2^(-nρθ) K(2^(nρ), f))_{n ∈ ℤ}‖_{ℓ_q}`. -/
theorem kMethodNorm_le_discreteKMethodNorm (hθ : 0 ≤ θ) (hρ : 0 < ρ) (f : X) :
    kMethodNorm ι θ q f ≤ ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
      (2 ^ (ρ * θ) * discreteKMethodNorm ι θ ρ q f) := by
  rw [discreteKMethodNorm_eq]
  exact phiFunctional_le_lqNorm_discretePhiSeq (monotone_kFunctional f) hθ hρ

/-- **The discrete K-norm on `ℤ` by the continuous one**: for `θ ≥ 0` and `ρ > 0`,
`(ρ log 2)^(1/q) 2^(-ρθ) ‖(2^(-nρθ) K(2^(nρ), f))_{n ∈ ℤ}‖_{ℓ_q} ≤ ‖f‖_{K,θ,q}`. -/
theorem discreteKMethodNorm_le_kMethodNorm (hθ : 0 ≤ θ) (hρ : 0 < ρ) (f : X) :
    ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
      (2 ^ (-(ρ * θ)) * discreteKMethodNorm ι θ ρ q f) ≤ kMethodNorm ι θ q f := by
  rw [discreteKMethodNorm_eq]
  exact lqNorm_discretePhiSeq_le_phiFunctional (monotone_kFunctional f) hθ hρ

/-! ### The grid on `ℤ` and the grid on `ℕ` -/

/-- The map `k ↦ -k` from `ℕ` to `ℤ` is injective. -/
theorem injective_neg_natCast : Injective fun k : ℕ => -(k : ℤ) :=
  neg_injective.comp Nat.cast_injective

/-- The map `k ↦ k + 1` from `ℕ` to `ℤ` is injective. -/
theorem injective_natCast_add_one : Injective fun k : ℕ => (k : ℤ) + 1 :=
  (add_left_injective 1).comp Nat.cast_injective

/-- The terms of `(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}` with `n = -k ≤ 0` are `2^(kρθ) φ(2^(-kρ))`. -/
theorem discretePhiSeq_neg_natCast (φ : ℝ≥0∞ → ℝ≥0∞) (k : ℕ) :
    discretePhiSeq θ ρ φ (-k) = dyadicWeight (ρ * θ) k * φ (dyadicWeight (-ρ) k) := by
  have h1 : -(((-(k : ℤ) : ℤ) : ℝ) * ρ * θ) = (k : ℝ) * (ρ * θ) := by push_cast; ring
  have h2 : ((-(k : ℤ) : ℤ) : ℝ) * ρ = (k : ℝ) * -ρ := by push_cast; ring
  rw [discretePhiSeq, ENNReal.dyadicWeight, ENNReal.dyadicWeight, h1, h2]

/-- The term of `(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}` with `n = 0` is `φ(1)`. -/
theorem discretePhiSeq_zero (φ : ℝ≥0∞ → ℝ≥0∞) : discretePhiSeq θ ρ φ 0 = φ 1 := by
  simp [discretePhiSeq]

/-- If `φ ≤ M`, the terms of `(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}` with `n = k + 1 > 0` are at most
`2^(-kρθ) M`, for `ρθ ≥ 0`. -/
theorem discretePhiSeq_natCast_add_one_le {M : ℝ≥0∞} (hρθ : 0 ≤ ρ * θ) (hM : ∀ t, φ t ≤ M)
    (k : ℕ) : discretePhiSeq θ ρ φ ((k : ℤ) + 1) ≤ M * dyadicWeight (-(ρ * θ)) k := by
  rw [discretePhiSeq, mul_comm M, ENNReal.dyadicWeight]
  refine mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_) (hM _)
  push_cast
  nlinarith

/-- **Splitting the grid on `ℤ`**: if `φ ≤ M` and `ρθ ≥ 0`, the sequence
`(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}` is at most the sequence `2^(kρθ) φ(2^(-kρ))` placed at
`n = -k ≤ 0` plus the sequence `2^(-kρθ) M` placed at `n = k + 1 > 0`. -/
theorem discretePhiSeq_le_extend {M : ℝ≥0∞} (hρθ : 0 ≤ ρ * θ) (hM : ∀ t, φ t ≤ M) (n : ℤ) :
    discretePhiSeq θ ρ φ n ≤
      extend (fun k : ℕ => -(k : ℤ)) (fun k => dyadicWeight (ρ * θ) k * φ (dyadicWeight (-ρ) k))
          0 n +
        extend (fun k : ℕ => (k : ℤ) + 1) (fun k => M * dyadicWeight (-(ρ * θ)) k) 0 n := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rcases k with _ | k
    · have h0 : ((0 : ℕ) : ℤ) = -((0 : ℕ) : ℤ) := by simp
      rw [h0, injective_neg_natCast.extend_apply, discretePhiSeq_neg_natCast]
      exact le_self_add
    · have h1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [h1, injective_natCast_add_one.extend_apply]
      exact (discretePhiSeq_natCast_add_one_le hρθ hM k).trans le_add_self
  · rw [injective_neg_natCast.extend_apply, discretePhiSeq_neg_natCast]
    exact le_self_add

/-- **The grid on `ℤ` by the grid on `ℕ`**: if `φ ≤ M` and `ρθ ≥ 0`, then
`‖(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}‖_{ℓ_q} ≤ C_q γ (M + ‖(2^(kρθ) φ(2^(-kρ)))_{k ∈ ℕ}‖_{ℓ_q})` with
`γ = dyadicGeomConst (ρθ) q`, where `C_q` is Mathlib's constant `LpAddConst q` of the
quasi-triangle inequality (`1` for `q ≥ 1`). -/
theorem lqNorm_discretePhiSeq_le {M : ℝ≥0∞} (hρθ : 0 ≤ ρ * θ) (hM : ∀ t, φ t ≤ M) :
    lqNorm q (discretePhiSeq θ ρ φ) ≤ LpAddConst q * dyadicGeomConst (ρ * θ) q *
      (M + lqNorm q fun k : ℕ => dyadicWeight (ρ * θ) k * φ (dyadicWeight (-ρ) k)) := by
  set a : ℕ → ℝ≥0∞ := fun k => dyadicWeight (ρ * θ) k * φ (dyadicWeight (-ρ) k)
  calc lqNorm q (discretePhiSeq θ ρ φ)
      ≤ lqNorm q (fun n => extend (fun k : ℕ => -(k : ℤ)) a 0 n +
          extend (fun k : ℕ => (k : ℤ) + 1) (fun k => M * dyadicWeight (-(ρ * θ)) k) 0 n) :=
        ENNReal.lqNorm_mono (discretePhiSeq_le_extend hρθ hM)
    _ ≤ LpAddConst q * (lqNorm q (extend (fun k : ℕ => -(k : ℤ)) a 0) +
          lqNorm q (extend (fun k : ℕ => (k : ℤ) + 1)
            (fun k => M * dyadicWeight (-(ρ * θ)) k) 0)) :=
        ENNReal.lqNorm_add_le' q _ _
    _ ≤ LpAddConst q * (lqNorm q a + M * dyadicGeomConst (ρ * θ) q) := by
        rw [ENNReal.lqNorm_extend_zero injective_neg_natCast,
          ENNReal.lqNorm_extend_zero injective_natCast_add_one, ENNReal.lqNorm_const_mul]
        gcongr
        exact ENNReal.lqNorm_dyadicWeight_neg_le_dyadicGeomConst hρθ
    _ ≤ LpAddConst q * dyadicGeomConst (ρ * θ) q * (M + lqNorm q a) := by
        rw [mul_assoc]
        gcongr
        calc lqNorm q a + M * dyadicGeomConst (ρ * θ) q
            ≤ dyadicGeomConst (ρ * θ) q * lqNorm q a + M * dyadicGeomConst (ρ * θ) q := by
              gcongr
              exact le_mul_of_one_le_left' (ENNReal.one_le_dyadicGeomConst _ _)
          _ = dyadicGeomConst (ρ * θ) q * (M + lqNorm q a) := by ring

/-- **The grid on `ℕ` is part of the grid on `ℤ`**:
`‖(2^(kρθ) φ(2^(-kρ)))_{k ∈ ℕ}‖_{ℓ_q} ≤ ‖(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}‖_{ℓ_q}`. -/
theorem lqNorm_le_lqNorm_discretePhiSeq :
    lqNorm q (fun k : ℕ => dyadicWeight (ρ * θ) k * φ (dyadicWeight (-ρ) k)) ≤
      lqNorm q (discretePhiSeq θ ρ φ) := by
  have h : (fun k : ℕ => dyadicWeight (ρ * θ) k * φ (dyadicWeight (-ρ) k)) =
      discretePhiSeq θ ρ φ ∘ fun k : ℕ => -(k : ℤ) :=
    funext fun k => (discretePhiSeq_neg_natCast φ k).symm
  rw [h]
  exact ENNReal.lqNorm_comp_le_of_injective injective_neg_natCast _

/-- The terms with `n = -k ≤ 0` are the sequence of the interpolation norm:
`2^(kρθ) K(2^(-kρ), f)`. -/
theorem discreteKSeq_neg_natCast (f : X) (k : ℕ) :
    discreteKSeq ι θ ρ f (-k) = interpSeq ι θ ρ f k :=
  discretePhiSeq_neg_natCast (fun t => kFunctional ι t f) k

/-- The term with `n = 0` is `K(1, f)`. -/
theorem discreteKSeq_zero (f : X) : discreteKSeq ι θ ρ f 0 = kFunctional ι 1 f :=
  discretePhiSeq_zero (fun t => kFunctional ι t f)

/-- The terms with `n = k + 1 > 0` are at most `2^(-kρθ) ‖f‖`, for `ρθ ≥ 0`. -/
theorem discreteKSeq_natCast_add_one_le (hρθ : 0 ≤ ρ * θ) (f : X) (k : ℕ) :
    discreteKSeq ι θ ρ f ((k : ℤ) + 1) ≤ ‖f‖ₑ * dyadicWeight (-(ρ * θ)) k :=
  discretePhiSeq_natCast_add_one_le (φ := fun t => kFunctional ι t f) hρθ
    (fun _ => kFunctional_le_enorm f) k

/-- **Splitting the grid on `ℤ`**: the sequence on `ℤ` is at most the interpolation sequence
placed at `n = -k ≤ 0` plus the sequence `2^(-kρθ) ‖f‖` placed at `n = k + 1 > 0`. -/
theorem discreteKSeq_le_extend (hρθ : 0 ≤ ρ * θ) (f : X) (n : ℤ) :
    discreteKSeq ι θ ρ f n ≤
      extend (fun k : ℕ => -(k : ℤ)) (interpSeq ι θ ρ f) 0 n +
        extend (fun k : ℕ => (k : ℤ) + 1) (fun k => ‖f‖ₑ * dyadicWeight (-(ρ * θ)) k) 0 n :=
  discretePhiSeq_le_extend (φ := fun t => kFunctional ι t f) hρθ (fun _ => kFunctional_le_enorm f) n

/-- **The discrete K-norm on `ℤ` by the interpolation norm**: for `ρθ ≥ 0`,
`‖(2^(-nρθ) K(2^(nρ), f))_{n ∈ ℤ}‖_{ℓ_q} ≤ C_q γ ‖f‖_{θ,q}` with
`γ = dyadicGeomConst (ρθ) q`, where `C_q` is Mathlib's constant `LpAddConst q` of the
quasi-triangle inequality (`1` for `q ≥ 1`). -/
theorem discreteKMethodNorm_le_interpNorm (hρθ : 0 ≤ ρ * θ) (f : X) :
    discreteKMethodNorm ι θ ρ q f ≤
      LpAddConst q * dyadicGeomConst (ρ * θ) q * interpNorm ι θ ρ q f :=
  lqNorm_discretePhiSeq_le (φ := fun t => kFunctional ι t f) hρθ fun _ => kFunctional_le_enorm f

/-- **The interpolation norm by the discrete K-norm on `ℤ`**: for `q ≠ 0`,
`‖f‖_{θ,q} ≤ (1 + max(1, ‖ι‖)) ‖(2^(-nρθ) K(2^(nρ), f))_{n ∈ ℤ}‖_{ℓ_q}`; the term `‖f‖` is
controlled by `‖f‖ ≤ max(1, ‖ι‖) K(1, f)`. -/
theorem interpNorm_le_discreteKMethodNorm (hq : q ≠ 0) (f : X) :
    interpNorm ι θ ρ q f ≤ (1 + max 1 ‖ι‖ₑ) * discreteKMethodNorm ι θ ρ q f := by
  have h1 : ‖f‖ₑ ≤ max 1 ‖ι‖ₑ * discreteKMethodNorm ι θ ρ q f := by
    refine (enorm_le_max_mul_kFunctional_one (ι := ι) f).trans ?_
    gcongr
    rw [← discreteKSeq_zero (θ := θ) (ρ := ρ)]
    exact ENNReal.le_lqNorm hq _ 0
  have h2 : lqNorm q (interpSeq ι θ ρ f) ≤ discreteKMethodNorm ι θ ρ q f :=
    lqNorm_le_lqNorm_discretePhiSeq (φ := fun t => kFunctional ι t f)
  calc interpNorm ι θ ρ q f = ‖f‖ₑ + lqNorm q (interpSeq ι θ ρ f) := rfl
    _ ≤ max 1 ‖ι‖ₑ * discreteKMethodNorm ι θ ρ q f + discreteKMethodNorm ι θ ρ q f :=
        add_le_add h1 h2
    _ = (1 + max 1 ‖ι‖ₑ) * discreteKMethodNorm ι θ ρ q f := by ring

/-! ### The discrete and the continuous K-method agree -/

/-- The constant `(ρ log 2)^(1/q) 2^(ρθ) C_q γ`, with `γ = dyadicGeomConst (ρθ) q`, of the bound
of the continuous K-norm by the discrete one on the grid `2^(-kρ)`. -/
noncomputable def kMethodUpperConst (θ ρ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) * 2 ^ (ρ * θ) *
    (LpAddConst q * dyadicGeomConst (ρ * θ) q)

/-- The constant `kMethodUpperConst θ ρ q` is finite for `θ, ρ > 0`. -/
theorem kMethodUpperConst_ne_top (hθ : 0 < θ) (hρ : 0 < ρ) (q : ℝ≥0∞) :
    kMethodUpperConst θ ρ q ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    (ENNReal.two_rpow_ne_top _))
    (ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q).ne
      (ENNReal.dyadicGeomConst_ne_top (mul_pos hρ hθ) q))

/-- **The continuous K-norm by the one-sided discrete norm**. For `θ ≥ 0` and `ρ > 0`,
`‖f‖_{K,θ,q} ≤ kMethodUpperConst θ ρ q · ‖f‖_{θ,q}`, where `‖f‖_{θ,q}` is the
discrete K-method on the grid `2^(-kρ)`.  The constant is finite for `θ > 0`
(`kMethodUpperConst_ne_top`). -/
theorem kMethodNorm_le_interpNorm (hθ : 0 ≤ θ) (hρ : 0 < ρ) (f : X) :
    kMethodNorm ι θ q f ≤ kMethodUpperConst θ ρ q * interpNorm ι θ ρ q f := by
  calc kMethodNorm ι θ q f
      ≤ ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
          (2 ^ (ρ * θ) * discreteKMethodNorm ι θ ρ q f) :=
        kMethodNorm_le_discreteKMethodNorm hθ hρ f
    _ ≤ ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) * (2 ^ (ρ * θ) *
          (LpAddConst q * dyadicGeomConst (ρ * θ) q * interpNorm ι θ ρ q f)) := by
        gcongr
        exact discreteKMethodNorm_le_interpNorm (mul_nonneg hρ.le hθ) f
    _ = kMethodUpperConst θ ρ q * interpNorm ι θ ρ q f := by
        rw [kMethodUpperConst]
        ring

variable (ι) in
/-- The constant `(1 + max(1, ‖ι‖)) 2^(ρθ) (ρ log 2)^(-1/q)` of the bound of the discrete
K-norm on the grid `2^(-kρ)` by the continuous one. -/
noncomputable def kMethodLowerConst (θ ρ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  (1 + max 1 ‖ι‖ₑ) * (2 ^ (ρ * θ) * (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal))⁻¹)

/-- The factor `(ρ log 2)^(1/q)` is nonzero for `ρ > 0`. -/
theorem ofReal_mul_log_two_rpow_ne_zero (hρ : 0 < ρ) (q : ℝ≥0∞) :
    ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) ≠ 0 :=
  (ENNReal.rpow_pos (pos_iff_ne_zero.2 (ofReal_mul_log_two_ne_zero hρ))
    ENNReal.ofReal_ne_top).ne'

/-- The factor `(log 2)^(1/q)` is nonzero: the case `ρ = 1` of
`ofReal_mul_log_two_rpow_ne_zero`. -/
theorem ofReal_log_two_rpow_ne_zero (q : ℝ≥0∞) :
    ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) ≠ 0 := by
  have h := ofReal_mul_log_two_rpow_ne_zero (ρ := 1) one_pos q
  rwa [one_mul] at h

/-- **The discrete version of `Φ_{θ,q}` by the functional, solved for the sequence**: for an
increasing `φ`, `θ ≥ 0` and `ρ > 0`,
`‖(2^(-nρθ) φ(2^(nρ)))_{n ∈ ℤ}‖_{ℓ_q} ≤ ((ρ log 2)^(1/q) 2^(-ρθ))⁻¹ Φ_{θ,q}(φ)`
(`lqNorm_discretePhiSeq_le_phiFunctional`). -/
theorem lqNorm_discretePhiSeq_le_inv_mul_phiFunctional {φ : ℝ≥0∞ → ℝ≥0∞} (hφ : Monotone φ)
    (hθ : 0 ≤ θ) (hρ : 0 < ρ) :
    lqNorm q (discretePhiSeq θ ρ φ) ≤
      (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(ρ * θ)))⁻¹ *
        phiFunctional θ q φ := by
  refine (ENNReal.mul_le_iff_le_inv (mul_ne_zero (ofReal_mul_log_two_rpow_ne_zero hρ q)
      (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne')
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      (ENNReal.two_rpow_ne_top _))).1 ?_
  rw [mul_assoc]
  exact lqNorm_discretePhiSeq_le_phiFunctional hφ hθ hρ

/-- The factor `((log 2)^(1/q) 2^(-θ))⁻¹` of `InterpCouple.discreteKMethodNorm_le_mul_kMethodNorm`
is finite. -/
theorem inv_log_two_rpow_mul_two_rpow_ne_top (θ : ℝ) (q : ℝ≥0∞) :
    (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-θ))⁻¹ ≠ ∞ :=
  ENNReal.inv_ne_top.2 (mul_ne_zero (ofReal_log_two_rpow_ne_zero q)
    (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne')

/-- The factor `(log 2)^(1/q) 2^θ` of `InterpCouple.kMethodNorm_le_mul_discreteKMethodNorm` is
finite. -/
theorem log_two_rpow_mul_two_rpow_ne_top (θ : ℝ) (q : ℝ≥0∞) :
    ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ θ ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    (ENNReal.two_rpow_ne_top θ)

/-- The constant `kMethodLowerConst ι θ ρ q` is finite for `ρ > 0`. -/
theorem kMethodLowerConst_ne_top (hρ : 0 < ρ) (q : ℝ≥0∞) : kMethodLowerConst ι θ ρ q ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    max_ne_top ENNReal.one_ne_top eNorm_ne_top⟩)
    (ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _)
      (ENNReal.inv_ne_top.2 (ofReal_mul_log_two_rpow_ne_zero hρ q)))

/-- **The one-sided discrete K-norm by the continuous norm**. For `θ ≥ 0`, `ρ > 0` and `q ≠ 0`,
`‖f‖_{θ,q} ≤ kMethodLowerConst ι θ ρ q · ‖f‖_{K,θ,q}`, where `‖f‖_{θ,q}`
is the discrete K-method on the grid `2^(-kρ)`. -/
theorem interpNorm_le_kMethodNorm (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hq : q ≠ 0) (f : X) :
    interpNorm ι θ ρ q f ≤ kMethodLowerConst ι θ ρ q * kMethodNorm ι θ q f := by
  have hc0 := ofReal_mul_log_two_rpow_ne_zero hρ q
  have hct : ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hD : discreteKMethodNorm ι θ ρ q f ≤ 2 ^ (ρ * θ) *
      (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal))⁻¹ * kMethodNorm ι θ q f := by
    rw [discreteKMethodNorm_eq, kMethodNorm]
    refine (lqNorm_discretePhiSeq_le_inv_mul_phiFunctional (monotone_kFunctional f) hθ
      hρ).trans_eq ?_
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), ENNReal.rpow_neg, inv_inv,
      mul_comm _ (2 ^ (ρ * θ))]
  calc interpNorm ι θ ρ q f ≤ (1 + max 1 ‖ι‖ₑ) * discreteKMethodNorm ι θ ρ q f :=
        interpNorm_le_discreteKMethodNorm hq f
    _ ≤ (1 + max 1 ‖ι‖ₑ) * (2 ^ (ρ * θ) *
          (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal))⁻¹ * kMethodNorm ι θ q f) := by
        gcongr
    _ = kMethodLowerConst ι θ ρ q * kMethodNorm ι θ q f := by
        rw [kMethodLowerConst]
        ring

/-- For the degenerate exponent `q = 0` every `f` lies in both spaces: `‖f‖_{θ,0} = ‖f‖` and
`‖f‖_{K,θ,0} = 0`. -/
theorem memInterp_zero_and_memKMethod_zero (f : X) :
    MemInterp ι θ ρ 0 f ∧ MemKMethod ι θ 0 f := by
  refine ⟨?_, ?_⟩
  · simp [MemInterp, interpNorm, ENNReal.lqNorm_zero_left]
  · simp [MemKMethod, kMethodNorm_eq,
      eLpNorm_exponent_zero (measurable_kMethodIntegrand (ι := ι) (θ := θ) f).aestronglyMeasurable]

/-- **The one-sided discrete and continuous K-methods agree**, extending the two-sided
comparison of Bergh–Löfström, Lemma 3.1.3, for a bounded linear map. For
`θ > 0`, `ρ > 0` and every `q`, including the zero-exponent convention, `f` lies in the
interpolation space of the discrete K-method on
the grid `t = 2^(-kρ)` if and only if `‖f‖_{K,θ,q} < ∞`, that is
`∫_0^∞ (t^(-θ) K(t, f))^q dt/t < ∞` for `0 < q < ∞` and `t^(-θ) K(t, f)` essentially bounded
for `q = ∞`.  This is, for the couple given by a bounded linear map `ι`, the analogue of the
equivalence `discreteKMethod_equiv_kmethod` stated in the project *MultilinearInterpolation*,
with the grid on `ℕ` and the term `‖f‖`. -/
theorem memInterp_iff_memKMethod (hθ : 0 < θ) (hρ : 0 < ρ) {f : X} :
    MemInterp ι θ ρ q f ↔ MemKMethod ι θ q f := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact iff_of_true (memInterp_zero_and_memKMethod_zero f).1
      (memInterp_zero_and_memKMethod_zero (ρ := ρ) f).2
  exact ⟨fun h => (kMethodNorm_le_interpNorm hθ.le hρ f).trans_lt
      (ENNReal.mul_lt_top (kMethodUpperConst_ne_top hθ hρ q).lt_top h),
    fun h => (interpNorm_le_kMethodNorm hθ.le hρ hq f).trans_lt
      (ENNReal.mul_lt_top (kMethodLowerConst_ne_top hρ q).lt_top h)⟩

/-- **The grid does not matter**: for `θ > 0` and every `q`, the discrete K-methods on the grids
`t = 2^(-kρ)` and `t = 2^(-kρ')`, `ρ, ρ' > 0`, give the same space. -/
theorem memInterp_iff_memInterp_of_pos {ρ' : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ) (hρ' : 0 < ρ')
    {f : X} : MemInterp ι θ ρ q f ↔ MemInterp ι θ ρ' q f :=
  (memInterp_iff_memKMethod hθ hρ).trans (memInterp_iff_memKMethod hθ hρ').symm

/-- **The representation theorem for the continuous K-method**: under Jackson's and Bernstein's
inequalities of order `r` and for `0 < s < r`, `1 ≤ q ≤ ∞`, `A^s_q = (X, Y)_{s/r,q}`, where
`(X, Y)_{s/r,q}` consists of the `f` with `‖f‖_{K,s/r,q} < ∞` (the integral
`∫_0^∞ (t^(-s/r) K(t, f))^q dt/t` for `q < ∞`, the essential supremum of `t^(-s/r) K(t, f)` for
`q = ∞`). -/
theorem memApprox_iff_memKMethod {A : ApproximationScheme X} {r s C₁ C₂ : ℝ}
    (hJ : JacksonBound ι A r C₁) (hC₁ : 0 ≤ C₁) (hB : LiftBound ι A r C₂) (hC₂ : 0 ≤ C₂)
    (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q) {f : X} :
    A.MemApprox s q f ↔ MemKMethod ι (s / r) q f :=
  (memApprox_iff_memInterp hJ hC₁ hB hC₂ hs hsr hq).trans
    (memInterp_iff_memKMethod (div_pos hs (hs.trans hsr)) (hs.trans hsr))

/-- **The representation theorem for a smoothness space** `W` of order `r` and the continuous
K-method: for `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q = (X, W)_{s/r,q}`. -/
theorem SmoothnessSpace.memApprox_iff_memKMethod {A : ApproximationScheme X} {s : ℝ}
    (W : SmoothnessSpace A Y) (hs : 0 < s) (hsr : s < W.order) (hq : 1 ≤ q) {f : X} :
    A.MemApprox s q f ↔ MemKMethod W.incl (s / W.order) q f :=
  ApproximationScheme.memApprox_iff_memKMethod W.jackson W.jacksonConst_nonneg W.bernstein
    W.bernsteinConst_nonneg hs hsr hq

end ApproximationScheme
