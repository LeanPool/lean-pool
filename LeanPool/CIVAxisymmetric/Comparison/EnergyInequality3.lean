/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Barrier
public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality
public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality2
public import LeanPool.CIVAxisymmetric.Comparison.MollifiedEquation
public import LeanPool.CIVAxisymmetric.Analysis.KatoRegularization
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The comparison energy inequality: a spatial truncation for the Kato regularization

`CIV.Comparison.EnergyInequality` proves the support/integrability facts about
`comparisonEnergy` and the Grönwall step of `lem:aniso:comparison`, but takes the integrated
energy inequality `eq:aniso:comparison:positive:energy` as a hypothesis
(`hineq` of `comparisonEnergy_le_exp_mul_integral_sq`). `CIV.Comparison.EnergyInequality2`
proves that this integrated inequality follows once the mollified equation
`eq:aniso:comparison:mollified` (`mollified_equation`) is upgraded from a distributional
identity in time into a fundamental-theorem-of-calculus statement, and records that the
natural closed form for the Kato regularization, `Φ_κ(g) = (g + √(g² + κ²)) / 2 − κ / 2`, does
**not** tend to `0` as `g → -∞`: it tends to `-κ / 2`. Composing `Φ_κ` with the excess
`g = q_ε − Ψ_σ` directly (unbounded below away from the compact support of `v_ε = g₊`) therefore
gives an energy `∫ Φ_κ(g)²` that diverges over all of `Vec m`, for every fixed `κ > 0`, since the
integrand tends to the nonzero constant `κ² / 4` over infinite measure. A `κ`-independent spatial
truncation is needed before the Kato step, not a regularization of the unbounded difference `g` on
the whole space.

## Main results

* **The truncation.** `mollifierCutoff m R` is a smooth cutoff on `Vec m`, built as a product of
  one-dimensional profiles `kappaBump1D R` (one per coordinate, using `Vec m`'s sup norm): it is
  `1` on `closedBall 0 R`, supported in `closedBall 0 (2 * R)`, and valued in `[0, 1]`
  (`contDiff_mollifierCutoff`, `mollifierCutoff_eq_one`, `hasCompactSupport_mollifierCutoff`,
  `mollifierCutoff_nonneg`, `mollifierCutoff_le_one`). Once `R` is fixed at or above the support
  radius `Minf / σ` of `BarrierSupport.posPart_mollifySlice_sub_barrier_eq_zero`, multiplying
  `comparisonPosPart` by the cutoff does not change it **at all**, for every `x`
  (`comparisonPosPart_mul_mollifierCutoff_eq_self`): this is an exact pointwise identity, not a
  limit, and its squared form shows the truncated energy equals `comparisonEnergy` exactly
  (`integral_sq_mul_mollifierCutoff_eq_comparisonEnergy`). **Consequently no limit `R → ∞` is
  needed anywhere below: `R` is fixed once, at any value `≥ Minf / σ`.** The Kato regularization
  of the excess, multiplied by the cutoff, is smooth and compactly supported for every `κ > 0`
  (`contDiff_kappaProfile_mul_mollifierCutoff`,
  `hasCompactSupport_kappaProfile_mul_mollifierCutoff`)
  — the divergence described above is exactly what the cutoff repairs.

* **The Kato profile as a real-variable function.** `katoSmooth`'s second argument has type
  `ℝ → ℝ`, so the spatial composition needs `kappaProfile kap := katoSmooth kap id : ℝ → ℝ`
  applied to the excess `g x`, not `katoSmooth` itself applied to a function of `Vec m`.
  `kappaProfile kap` is smooth, its derivative has the closed form
  `(1 + t / √(t² + κ²)) / 2 ∈ [0, 1]`, and it is globally `1`-Lipschitz
  (`hasDerivAt_kappaProfile`, `lipschitzWith_kappaProfile`).

* **A fundamental theorem of calculus for the squared Kato profile of a primitive.** If `F`
  satisfies `F τ = F τ₀ + ∫ h` on an open set, `(kappaProfile kap ∘ F)²` obeys the same kind of
  identity, with right side the chain-rule derivative `2 Φ_κ(F) Φ_κ'(F) h`
  (`sq_kappaProfile_eq_add_intervalIntegral`). The proof shows `F` is absolutely continuous (a
  primitive of an interval-integrable function), transports absolute continuity through the
  globally-Lipschitz `kappaProfile kap` (`LipschitzWith.comp_absolutelyContinuousOnInterval`),
  computes the a.e. derivative of the square by the chain rule, and applies the fundamental
  theorem of calculus for absolutely continuous functions
  (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`).

* **The pointwise-in-`x` upgrade of the mollified equation.** Applying
  `CIV.eq_add_intervalIntegral_of_pairing_eq` to `mollified_equation`'s tested
  identity (with no adapter: the two shapes match exactly) shows that, for a fixed spatial point
  `x`, `mollifySlice m ε q (x, ·)` is literally the primitive of the right side of
  `eq:aniso:comparison:mollified` (`mollifySlice_eq_add_intervalIntegral`). Since the barrier is
  affine in `τ` with the constant rate `σ * K`, the excess `g = q_ε − Ψ_σ` obeys the same kind of
  primitive identity, with the constant `σ * K` subtracted from the right side
  (`excess_eq_add_intervalIntegral`) — this part needs no calculus at all, only the closed form of
  `barrier`.

* **Their combination**: the per-`x`, per-`κ` truncated energy-density identity
  (`truncatedKatoSq_eq_add_intervalIntegral`), obtained by feeding the excess's primitive identity
  into the fundamental theorem of calculus for the squared Kato profile and multiplying through by
  the (`τ`-independent) constant `mollifierCutoff m R x`.

## Hypotheses `hCont` and `hLoc`

Invoking `eq_add_intervalIntegral_of_pairing_eq` at a fixed spatial point `x` requires
`ContinuousOn (fun τ => mollifySlice m ε q (x, τ)) I` and local integrability on `I` of the right
side of `eq:aniso:comparison:mollified` at `x`. These enter `mollifySlice_eq_add_intervalIntegral`,
`excess_eq_add_intervalIntegral` and `truncatedKatoSq_eq_add_intervalIntegral` as the explicit
hypotheses `hCont` and `hLoc`. `CIV.mollifySlice_ae_ae_sub_eq_intervalIntegral` proves the
corresponding identity, almost everywhere in time, without them.

## Use

The per-`x` identity is integrated over `Vec m` in `CIV.Comparison.EnergySpatialIntegration`,
where the Green identity for the truncated Laplacian is available in both directions
(`integral_partialLaplacian_mul_eq_neg_integral_gradPair_mul`, integrating by parts off the
differentiated factor, and `integral_mul_lapD_eq`, off the test factor). They combine into
`integral_partialLaplacian_mul_comm_of_hasCompactSupport`, the form needed when the differentiated
factor is smooth but not compactly supported, as `mollifySlice` is. The spatial integration of the
Laplacian term is `integral_kappaTestFn_mul_partialLaplacian_eq`, and the `κ ↓ 0` interchange with
the outer time integral is `tendsto_intervalIntegral_integral_sq_kappaProfile_mul_mollifierCutoff`;
both use `mollifierCutoff` and `kappaProfile` from this file.

`Vec m`'s ambient norm is the sup norm (the default `Pi` structure on `Fin m → ℝ`), so the cutoff
is built as a literal product of one-dimensional profiles rather than through
`ContDiffBump (0 : Vec m)`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

/-! ## Part 1: the spatial cutoff -/

/-- A smooth product of finitely many smooth real functions, composed with coordinate
projections, is smooth. -/
theorem contDiff_finset_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [DecidableEq ι] {n : WithTop ℕ∞} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contDiff_const
  | @insert a s ha ih =>
    have hfa : ContDiff ℝ n (f a) := hf a (Finset.mem_insert_self a s)
    have hrest : ContDiff ℝ n (fun x => ∏ i ∈ s, f i x) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x => ∏ i ∈ insert a s, f i x) = fun x => f a x * ∏ i ∈ s, f i x := by
      funext x; rw [Finset.prod_insert ha]
    rw [heq]
    exact hfa.mul hrest

/-- The one-dimensional smooth cutoff of scale `R`: equal to `1` on `closedBall 0 R`,
supported in `ball 0 (2 * R)`, ranging in `[0, 1]`. The junk value off `0 < R` is `0`. -/
@[expose] def kappaBump1D (R : ℝ) : ℝ → ℝ :=
  fun t => if h : 0 < R then (⟨R, 2 * R, h, by linarith only [h]⟩ : ContDiffBump (0 : ℝ)) t else 0

theorem kappaBump1D_eq (R : ℝ) (hR : 0 < R) (t : ℝ) :
    kappaBump1D R t = (⟨R, 2 * R, hR, by linarith only [hR]⟩ : ContDiffBump (0 : ℝ)) t := by
  simp only [kappaBump1D, dite_eq_left hR]

theorem contDiff_kappaBump1D (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (kappaBump1D R) := by
  have heq : kappaBump1D R = (⟨R, 2 * R, hR, by linarith only [hR]⟩ : ContDiffBump (0 : ℝ)) := by
    funext t; exact kappaBump1D_eq R hR t
  rw [heq]
  exact (⟨R, 2 * R, hR, by linarith only [hR]⟩ : ContDiffBump (0 : ℝ)).contDiff

theorem kappaBump1D_nonneg (R : ℝ) (hR : 0 < R) (t : ℝ) : 0 ≤ kappaBump1D R t := by
  rw [kappaBump1D_eq R hR t]
  exact (⟨R, 2 * R, hR, by linarith only [hR]⟩ : ContDiffBump (0 : ℝ)).nonneg

theorem kappaBump1D_le_one (R : ℝ) (hR : 0 < R) (t : ℝ) : kappaBump1D R t ≤ 1 := by
  rw [kappaBump1D_eq R hR t]
  exact (⟨R, 2 * R, hR, by linarith only [hR]⟩ : ContDiffBump (0 : ℝ)).le_one

theorem kappaBump1D_eq_one (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : |t| ≤ R) :
    kappaBump1D R t = 1 := by
  rw [kappaBump1D_eq R hR t]
  refine (⟨R, 2 * R, hR, by linarith only [hR]⟩ : ContDiffBump (0 : ℝ)).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact ht

theorem kappaBump1D_eq_zero (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : 2 * R ≤ |t|) :
    kappaBump1D R t = 0 := by
  rw [kappaBump1D_eq R hR t]
  refine (⟨R, 2 * R, hR, by linarith only [hR]⟩ : ContDiffBump (0 : ℝ)).zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero]
  exact ht

/-- The spatial cutoff of scale `R` on `Vec m`: the product of the one-dimensional cutoffs
`kappaBump1D R` applied to each coordinate. Equal to `1` on `closedBall 0 R`, supported in
`closedBall 0 (2 * R)`, ranging in `[0, 1]`. Built as a literal product over coordinates because
`Vec m`'s ambient norm is the `Pi` sup norm, for which `closedBall 0 R` is exactly the box
`{x | ∀ i, |x i| ≤ R}`. -/
@[expose] def mollifierCutoff (m : ℕ) (R : ℝ) (x : Vec m) : ℝ := ∏ i : Fin m, kappaBump1D R (x i)

/-- A finite product of real numbers each lying in `[0, 1]` itself lies in `[0, 1]`. -/
theorem finset_prod_le_one_of_forall_mem_Icc {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha' := hf a (Finset.mem_insert_self a s)
    have hs' : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod_nonneg : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => (hs' i hi).1
    have hprod_le : ∏ i ∈ s, f i ≤ 1 := ih hs'
    nlinarith only [ha'.1, ha'.2, hprod_nonneg, hprod_le]

theorem contDiff_mollifierCutoff (m : ℕ) (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifierCutoff m R) := by
  refine contDiff_finset_prod Finset.univ
    (f := fun (i : Fin m) (x : Vec m) => kappaBump1D R (x i)) ?_
  intro i _
  exact (contDiff_kappaBump1D R hR).comp (contDiff_apply ℝ ℝ i)

theorem mollifierCutoff_nonneg (m : ℕ) (R : ℝ) (hR : 0 < R) (x : Vec m) :
    0 ≤ mollifierCutoff m R x :=
  Finset.prod_nonneg fun i _ => kappaBump1D_nonneg R hR (x i)

theorem mollifierCutoff_le_one (m : ℕ) (R : ℝ) (hR : 0 < R) (x : Vec m) :
    mollifierCutoff m R x ≤ 1 :=
  finset_prod_le_one_of_forall_mem_Icc Finset.univ
    (fun i _ => ⟨kappaBump1D_nonneg R hR (x i), kappaBump1D_le_one R hR (x i)⟩)

theorem mollifierCutoff_eq_one (m : ℕ) (R : ℝ) (hR : 0 < R) {x : Vec m}
    (hx : x ∈ Metric.closedBall (0 : Vec m) R) : mollifierCutoff m R x = 1 := by
  have hxi : ∀ i : Fin m, |x i| ≤ R := by
    intro i
    have h := (pi_norm_le_iff_of_nonneg hR.le (x := x)).mp ?_ i
    · simpa [Real.norm_eq_abs] using h
    · rwa [Metric.mem_closedBall, dist_zero_right] at hx
  have hone : ∀ i ∈ (Finset.univ : Finset (Fin m)), kappaBump1D R (x i) = 1 :=
    fun i _ => kappaBump1D_eq_one R hR (hxi i)
  exact Finset.prod_congr rfl hone |>.trans Finset.prod_const_one

theorem mollifierCutoff_eq_zero (m : ℕ) (R : ℝ) (hR : 0 < R) {x : Vec m}
    (hx : x ∉ Metric.closedBall (0 : Vec m) (2 * R)) : mollifierCutoff m R x = 0 := by
  have hnot : ¬ ∀ i, |x i| ≤ 2 * R := by
    intro hall
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by linarith only [hR]) (x := x)).mpr ?_
    intro i
    simpa [Real.norm_eq_abs] using hall i
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  rw [not_le] at hi
  have hzero : kappaBump1D R (x i) = 0 := kappaBump1D_eq_zero R hR hi.le
  exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

theorem hasCompactSupport_mollifierCutoff (m : ℕ) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (mollifierCutoff m R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Vec m) (2 * R))
    (fun _x hx => mollifierCutoff_eq_zero m R hR hx)

/-! ## Part 2: the truncation is exact once `R ≥ Minf / σ` — no `R → ∞` limit -/

/-- **Stage (1) of the truncation.** Once `R` dominates the support radius `Minf / σ` of
`BarrierSupport.posPart_mollifySlice_sub_barrier_eq_zero`, the cutoff `mollifierCutoff m R` is
identically `1` on the excess `comparisonPosPart`, for every `x` — not merely in a limit as
`R → ∞`. Multiplying by the cutoff therefore does not change `comparisonPosPart` at all. -/
theorem comparisonPosPart_mul_mollifierCutoff_eq_self {m : ℕ} {ε M σ K τ₀ τ Minf R : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) (hR : 0 < R)
    (hRM : Minf / σ ≤ R) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) (x : Vec m) :
    comparisonPosPart m ε M σ K τ₀ q (x, τ) * mollifierCutoff m R x
      = comparisonPosPart m ε M σ K τ₀ q (x, τ) := by
  by_cases hx : x ∈ Metric.closedBall (0 : Vec m) R
  · rw [mollifierCutoff_eq_one m R hR hx, mul_one]
  · have hnorm : R ≤ ‖x‖ := le_norm_of_notMem_closedBall hx
    have hnorm' : Minf / σ ≤ ‖x‖ := le_trans hRM hnorm
    rw [comparisonPosPart_eq_zero_of_norm_ge hε hσ hK hM hτ hmeas hbdd x hnorm', zero_mul]

/-- The squared form of `comparisonPosPart_mul_mollifierCutoff_eq_self`: the truncated energy
density equals the untruncated one, exactly, for the fixed `R ≥ Minf / σ`. -/
theorem sq_comparisonPosPart_mul_mollifierCutoff_eq_self {m : ℕ} {ε M σ K τ₀ τ Minf R : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) (hR : 0 < R)
    (hRM : Minf / σ ≤ R) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) (x : Vec m) :
    (comparisonPosPart m ε M σ K τ₀ q (x, τ) * mollifierCutoff m R x) ^ 2
      = comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2 := by
  rw [comparisonPosPart_mul_mollifierCutoff_eq_self hε hσ hK hM hτ hR hRM hmeas hbdd x]

/-- The truncated energy equals `comparisonEnergy` exactly, for every `R ≥ Minf / σ`: no limit
`R → ∞` is needed once `R` is fixed at or above the support radius of `comparisonPosPart`. -/
theorem integral_sq_mul_mollifierCutoff_eq_comparisonEnergy {m : ℕ} {ε M σ K τ₀ τ Minf R : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) (hR : 0 < R)
    (hRM : Minf / σ ≤ R) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) :
    ∫ x, (comparisonPosPart m ε M σ K τ₀ q (x, τ) * mollifierCutoff m R x) ^ 2
      = comparisonEnergy m ε M σ K τ₀ q τ := by
  unfold comparisonEnergy
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact sq_comparisonPosPart_mul_mollifierCutoff_eq_self hε hσ hK hM hτ hR hRM hmeas hbdd x

/-! ## Part 3: the real-variable Kato profile -/

/-- The real-variable Kato profile `Φ_κ(t) = (t + √(t² + κ²)) / 2 − κ / 2`: `katoSmooth kap`
applied to the identity, so that spatial compositions `x ↦ Φ_κ(g x)` (for `g : Vec m → ℝ`) can be
written `kappaProfile kap (g x)` — `katoSmooth` itself only accepts a function of `ℝ`. -/
@[expose] def kappaProfile (kap : ℝ) : ℝ → ℝ := katoSmooth kap id

theorem kappaProfile_eq (kap t : ℝ) :
    kappaProfile kap t = (t + Real.sqrt (t ^ 2 + kap ^ 2)) / 2 - kap / 2 := by
  unfold kappaProfile katoSmooth
  simp

theorem contDiff_kappaProfile (kap : ℝ) (hkap : 0 < kap) :
    ContDiff ℝ (⊤ : ℕ∞) (kappaProfile kap) :=
  contDiff_katoSmooth kap hkap contDiff_id

/-- The derivative of the Kato profile in closed form. -/
theorem hasDerivAt_kappaProfile (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    HasDerivAt (kappaProfile kap) ((1 + t / Real.sqrt (t ^ 2 + kap ^ 2)) / 2) t := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 + kap ^ 2) (2 * t) t := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t ^ 1) t := hasDerivAt_pow 2 t
    simpa using h1.add_const (kap ^ 2)
  have hne : t ^ 2 + kap ^ 2 ≠ 0 := radicand_ne_zero kap id t hkap
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + kap ^ 2))
      ((2 * t) / (2 * Real.sqrt (t ^ 2 + kap ^ 2))) t := hsq.sqrt hne
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hadd : HasDerivAt (fun s : ℝ => s + Real.sqrt (s ^ 2 + kap ^ 2))
      (1 + (2 * t) / (2 * Real.sqrt (t ^ 2 + kap ^ 2))) t := hid.add hsqrt
  have hdiv : HasDerivAt (fun s : ℝ => (s + Real.sqrt (s ^ 2 + kap ^ 2)) / 2)
      ((1 + (2 * t) / (2 * Real.sqrt (t ^ 2 + kap ^ 2))) / 2) t := hadd.div_const 2
  have hsub : HasDerivAt (fun s : ℝ => (s + Real.sqrt (s ^ 2 + kap ^ 2)) / 2 - kap / 2)
      ((1 + (2 * t) / (2 * Real.sqrt (t ^ 2 + kap ^ 2))) / 2) t := hdiv.sub_const (kap / 2)
  have heqf : (fun s : ℝ => (s + Real.sqrt (s ^ 2 + kap ^ 2)) / 2 - kap / 2)
      = kappaProfile kap := by
    funext s; rw [kappaProfile_eq]
  rw [heqf] at hsub
  have hsqrtpos : 0 < Real.sqrt (t ^ 2 + kap ^ 2) := Real.sqrt_pos.mpr (lt_of_le_of_ne
    (by positivity) (Ne.symm hne))
  have heqderiv : (1 + (2 * t) / (2 * Real.sqrt (t ^ 2 + kap ^ 2))) / 2
      = (1 + t / Real.sqrt (t ^ 2 + kap ^ 2)) / 2 := by
    have hne' : Real.sqrt (t ^ 2 + kap ^ 2) ≠ 0 := hsqrtpos.ne'
    field_simp
  rwa [heqderiv] at hsub

theorem deriv_kappaProfile (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    deriv (kappaProfile kap) t = (1 + t / Real.sqrt (t ^ 2 + kap ^ 2)) / 2 :=
  (hasDerivAt_kappaProfile kap hkap t).deriv

/-- The derivative of the Kato profile lies in `[0, 1]`. -/
theorem deriv_kappaProfile_mem_Icc (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    0 ≤ deriv (kappaProfile kap) t ∧ deriv (kappaProfile kap) t ≤ 1 := by
  rw [deriv_kappaProfile kap hkap t]
  have hsqrtpos : 0 < Real.sqrt (t ^ 2 + kap ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith only [sq_nonneg t, hkap, mul_pos hkap hkap])
  have hlt : |t| < Real.sqrt (t ^ 2 + kap ^ 2) := by
    have h1 : |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    rw [h1]
    refine Real.sqrt_lt_sqrt (sq_nonneg t) ?_
    nlinarith only [hkap]
  have hle1 : t / Real.sqrt (t ^ 2 + kap ^ 2) ≤ 1 := by
    rw [div_le_one hsqrtpos]
    exact le_trans (le_abs_self t) hlt.le
  have hge : -1 ≤ t / Real.sqrt (t ^ 2 + kap ^ 2) := by
    rw [le_div_iff₀ hsqrtpos]
    nlinarith only [neg_abs_le t, hlt.le]
  exact ⟨by linarith only [hge], by linarith only [hle1]⟩

/-- The Kato profile is globally `1`-Lipschitz. -/
theorem lipschitzWith_kappaProfile (kap : ℝ) (hkap : 0 < kap) :
    LipschitzWith 1 (kappaProfile kap) := by
  rw [← lipschitzOnWith_univ]
  refine convex_univ.lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (hasDerivAt_kappaProfile kap hkap x).differentiableAt) ?_
  intro x _
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (deriv_kappaProfile_mem_Icc kap hkap x).1]
  simpa using (deriv_kappaProfile_mem_Icc kap hkap x).2

/-! ## Part 4: the fundamental theorem of calculus for the squared Kato profile -/

/-- If `F` obeys the primitive identity `F τ = F τ₀ + ∫ s in τ₀..τ, h s` throughout an open set
`I`, and `[a, b] ⊆ I` with `τ₀ ∈ [a, b]`, then the squared Kato regularization
`(kappaProfile kap ∘ F)²` obeys the same kind of identity on `[a, b]`, with right side the
chain-rule derivative `2 · kappaProfile kap (F s) · deriv (kappaProfile kap) (F s) · h s`. -/
theorem sq_kappaProfile_eq_add_intervalIntegral {kap : ℝ} (hkap : 0 < kap)
    {I : Set ℝ} (hI : IsOpen I) {F h : ℝ → ℝ} {τ₀ : ℝ}
    (hF : ∀ τ ∈ I, F τ = F τ₀ + ∫ s in τ₀..τ, h s)
    {a b : ℝ} (hab : a ≤ b) (habI : Icc a b ⊆ I) (hτ₀ab : τ₀ ∈ Icc a b)
    (hh : IntervalIntegrable h volume a b) :
    (kappaProfile kap (F b)) ^ 2 = (kappaProfile kap (F a)) ^ 2
      + ∫ s in a..b, 2 * kappaProfile kap (F s) * deriv (kappaProfile kap) (F s) * h s := by
  set G : ℝ → ℝ := fun τ => F τ₀ + ∫ s in τ₀..τ, h s with hGdef
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hτ₀' : τ₀ ∈ uIcc a b := by rwa [huIcc]
  have hGac : AbsolutelyContinuousOnInterval G a b := by
    have hprim : AbsolutelyContinuousOnInterval (fun τ => ∫ s in τ₀..τ, h s) a b :=
      hh.absolutelyContinuousOnInterval_intervalIntegral hτ₀'
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => F τ₀) a b := by
      have hLip : LipschitzOnWith 0 (fun _ : ℝ => F τ₀) (uIcc a b) := fun x _ y _ => by simp
      exact hLip.absolutelyContinuousOnInterval
    exact hconst.add hprim
  have hFeqG : EqOn F G (uIcc a b) := by
    rw [huIcc]
    intro τ hτ
    exact hF τ (habI hτ)
  have hFac : AbsolutelyContinuousOnInterval F a b := hGac.congr hFeqG.symm
  have hKac : AbsolutelyContinuousOnInterval (kappaProfile kap ∘ F) a b :=
    (lipschitzWith_kappaProfile kap hkap).comp_absolutelyContinuousOnInterval hFac
  have hSqac : AbsolutelyContinuousOnInterval
      (kappaProfile kap ∘ F * (kappaProfile kap ∘ F)) a b := hKac.mul hKac
  have hFTC := hSqac.integral_deriv_eq_sub
  have hderivFa : ∀ᵐ s, s ∈ uIcc a b → HasDerivAt F (h s) s := by
    filter_upwards [hh.ae_hasDerivAt_integral] with s hs hsmem
    have hderivG : HasDerivAt G (h s) s := (hs hsmem τ₀ hτ₀').const_add (F τ₀)
    have hnbhd : I ∈ 𝓝 s := hI.mem_nhds (habI (huIcc ▸ hsmem))
    have hEq : F =ᶠ[𝓝 s] G := by filter_upwards [hnbhd] with y hy; exact hF y hy
    exact hderivG.congr_of_eventuallyEq hEq
  have hderivSq : ∀ᵐ s, s ∈ uIcc a b →
      HasDerivAt (kappaProfile kap ∘ F * (kappaProfile kap ∘ F))
        (2 * kappaProfile kap (F s) * deriv (kappaProfile kap) (F s) * h s) s := by
    filter_upwards [hderivFa] with s hs
    intro hsmem
    have hFs := hs hsmem
    have hKs' : HasDerivAt (kappaProfile kap ∘ F)
        ((1 + F s / Real.sqrt (F s ^ 2 + kap ^ 2)) / 2 * h s) s :=
      (hasDerivAt_kappaProfile kap hkap (F s)).comp s hFs
    have hKs : HasDerivAt (kappaProfile kap ∘ F) (deriv (kappaProfile kap) (F s) * h s) s := by
      rwa [deriv_kappaProfile kap hkap (F s)]
    have hprod := hKs.mul hKs
    have heqderiv : deriv (kappaProfile kap) (F s) * h s * (kappaProfile kap ∘ F) s
        + (kappaProfile kap ∘ F) s * (deriv (kappaProfile kap) (F s) * h s)
        = 2 * kappaProfile kap (F s) * deriv (kappaProfile kap) (F s) * h s := by
      simp only [Function.comp_apply]
      ring
    rwa [heqderiv] at hprod
  have hcongr : ∫ s in a..b, deriv (kappaProfile kap ∘ F * (kappaProfile kap ∘ F)) s
      = ∫ s in a..b, 2 * kappaProfile kap (F s) * deriv (kappaProfile kap) (F s) * h s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderivSq] with s hs hsmem
    exact (hs (uIoc_subset_uIcc hsmem)).deriv
  rw [hcongr] at hFTC
  have hval : (kappaProfile kap ∘ F * (kappaProfile kap ∘ F)) b
      - (kappaProfile kap ∘ F * (kappaProfile kap ∘ F)) a
      = (kappaProfile kap (F b)) ^ 2 - (kappaProfile kap (F a)) ^ 2 := by
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  rw [hval] at hFTC
  linarith only [hFTC]

/-! ## Part 5: the pointwise-in-`x` upgrade of the mollified equation -/

/-- **The mollified slice is a primitive in time, under the hypotheses `hCont` and `hLoc`.**
For a fixed spatial point `x`, the mollified slice `mollifySlice m ε q (x, ·)` is literally the
primitive, based at any `τ₀ ∈ I`, of the right side of `eq:aniso:comparison:mollified` — this
upgrades `mollified_equation`'s tested (distributional) identity into an equality of real
numbers, via the general distributional fundamental theorem of calculus
`eq_add_intervalIntegral_of_pairing_eq`. The two shapes match with no adapter. -/
theorem mollifySlice_eq_add_intervalIntegral {m d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} {q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε) (x : Vec m)
    (hCont : ContinuousOn (fun τ => mollifySlice m ε q (x, τ)) I)
    (hLoc : LocallyIntegrableOn (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
        - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
        + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
            (fun y => q (y, τ)) x) I volume)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) {τ : ℝ} (hτ : τ ∈ I) :
    mollifySlice m ε q (x, τ) = mollifySlice m ε q (x, τ₀)
      + ∫ s in τ₀..τ, (partialLaplacian m d (mollifySlice m ε q) (x, s)
          - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
          + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
              (fun y => q (y, s)) x) := by
  refine eq_add_intervalIntegral_of_pairing_eq hI hIoc hCont hLoc ?_ hτ₀ hτ
  intro χ hχ hχc hχI
  exact mollified_equation m d I hI B divB q hB hq heq hε x χ hχ hχc hχI

/-- The excess `g = q_ε − Ψ_σ` over the barrier, as a function of `τ` at the fixed spatial
point `x`, obeys the same kind of primitive identity as `mollifySlice`: the barrier is affine in
`τ` with the constant rate `σ * K` (`Barrier.barrier`, unfolded directly — no calculus is needed
for this part). -/
theorem excess_eq_add_intervalIntegral {m d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} {q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    (M σ K : ℝ) (x : Vec m)
    (hCont : ContinuousOn (fun τ => mollifySlice m ε q (x, τ)) I)
    (hLoc : LocallyIntegrableOn (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
        - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
        + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
            (fun y => q (y, τ)) x) I volume)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) {τ : ℝ} (hτ : τ ∈ I) :
    (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ))
      = (mollifySlice m ε q (x, τ₀) - barrier m M σ K τ₀ (x, τ₀))
        + ∫ s in τ₀..τ, ((partialLaplacian m d (mollifySlice m ε q) (x, s)
            - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
            + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
                (fun y => q (y, s)) x) - σ * K) := by
  have hM := mollifySlice_eq_add_intervalIntegral hI hIoc hB hq heq hε x hCont hLoc hτ₀ hτ
  have hUIcc : uIcc τ₀ τ ⊆ I := hIoc.uIcc_subset hτ₀ hτ
  have hhIcc : IntegrableOn (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
      - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
      + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
          (fun y => q (y, τ)) x) (uIcc τ₀ τ) volume :=
    hLoc.integrableOn_compact_subset hUIcc isCompact_uIcc
  have hhInterval : IntervalIntegrable (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
      - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
      + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
          (fun y => q (y, τ)) x) volume τ₀ τ :=
    intervalIntegrable_iff.mpr (hhIcc.mono_set uIoc_subset_uIcc)
  have hconstInterval : IntervalIntegrable (fun _ : ℝ => σ * K) volume τ₀ τ :=
    intervalIntegrable_const
  have hBar : barrier m M σ K τ₀ (x, τ) - barrier m M σ K τ₀ (x, τ₀) = ∫ s in τ₀..τ, σ * K := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    unfold barrier
    ring
  have hsplit : (∫ s in τ₀..τ, ((partialLaplacian m d (mollifySlice m ε q) (x, s)
      - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
      + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
          (fun y => q (y, s)) x) - σ * K))
      = (∫ s in τ₀..τ, (partialLaplacian m d (mollifySlice m ε q) (x, s)
          - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
          + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
              (fun y => q (y, s)) x))
        - ∫ s in τ₀..τ, σ * K :=
    intervalIntegral.integral_sub hhInterval hconstInterval
  rw [hsplit, ← hBar]
  linarith only [hM]

/-! ## Part 6: the per-`x`, per-`κ` truncated energy-density identity -/

/-- Combines `excess_eq_add_intervalIntegral` (the excess is its own primitive) with
`sq_kappaProfile_eq_add_intervalIntegral` (the chain rule/fundamental theorem of calculus for its
squared Kato regularization) and multiplies through by the constant `mollifierCutoff m R x`: the
per-`x`, per-`κ` identity that the energy computation integrates spatially
(`integral_kappaTestFn_mul_partialLaplacian_eq`). -/
theorem truncatedKatoSq_eq_add_intervalIntegral {m d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} {q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    (M σ K : ℝ) (x : Vec m) (R kap : ℝ) (hkap : 0 < kap)
    (hCont : ContinuousOn (fun τ => mollifySlice m ε q (x, τ)) I)
    (hLoc : LocallyIntegrableOn (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
        - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
        + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
            (fun y => q (y, τ)) x) I volume)
    {τ₀ τ : ℝ} (hτ₀ : τ₀ ∈ I) (hτ : τ ∈ I) (hτord : τ₀ ≤ τ) :
    (kappaProfile kap (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ))
        * mollifierCutoff m R x) ^ 2
      = (kappaProfile kap (mollifySlice m ε q (x, τ₀) - barrier m M σ K τ₀ (x, τ₀))
          * mollifierCutoff m R x) ^ 2
        + ∫ s in τ₀..τ, (2 * kappaProfile kap (mollifySlice m ε q (x, s)
              - barrier m M σ K τ₀ (x, s))
            * deriv (kappaProfile kap) (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s))
            * ((partialLaplacian m d (mollifySlice m ε q) (x, s)
                - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
                + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
                    (fun y => q (y, s)) x) - σ * K)) * mollifierCutoff m R x ^ 2 := by
  set F : ℝ → ℝ := fun τ' => mollifySlice m ε q (x, τ') - barrier m M σ K τ₀ (x, τ') with hFdef
  set h : ℝ → ℝ := fun s => (partialLaplacian m d (mollifySlice m ε q) (x, s)
      - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
      + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
          (fun y => q (y, s)) x) - σ * K with hhdef
  have hFeq : ∀ τ' ∈ I, F τ' = F τ₀ + ∫ s in τ₀..τ', h s :=
    fun τ' hτ' => excess_eq_add_intervalIntegral hI hIoc hB hq heq hε M σ K x hCont hLoc hτ₀ hτ'
  have hIccI : Icc τ₀ τ ⊆ I := hIoc.out hτ₀ hτ
  have hτ₀mem : τ₀ ∈ Icc τ₀ τ := ⟨le_refl τ₀, hτord⟩
  have hUIcc : uIcc τ₀ τ ⊆ I := hIoc.uIcc_subset hτ₀ hτ
  have hhIcc : IntegrableOn (fun s => partialLaplacian m d (mollifySlice m ε q) (x, s)
      - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
      + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
          (fun y => q (y, s)) x) (uIcc τ₀ τ) volume :=
    hLoc.integrableOn_compact_subset hUIcc isCompact_uIcc
  have hhInterval : IntervalIntegrable h volume τ₀ τ := by
    have hbase : IntervalIntegrable (fun s => partialLaplacian m d (mollifySlice m ε q) (x, s)
        - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
        + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
            (fun y => q (y, s)) x) volume τ₀ τ :=
      intervalIntegrable_iff.mpr (hhIcc.mono_set uIoc_subset_uIcc)
    exact hbase.sub intervalIntegrable_const
  have hcombine := sq_kappaProfile_eq_add_intervalIntegral hkap hI hFeq hτord hIccI hτ₀mem
    hhInterval
  have hmul : (kappaProfile kap (F τ)) ^ 2 * mollifierCutoff m R x ^ 2
      = (kappaProfile kap (F τ₀)) ^ 2 * mollifierCutoff m R x ^ 2
        + (∫ s in τ₀..τ, 2 * kappaProfile kap (F s) * deriv (kappaProfile kap) (F s) * h s)
          * mollifierCutoff m R x ^ 2 := by
    rw [← add_mul, ← hcombine]
  rw [← mul_pow, ← mul_pow, ← intervalIntegral.integral_mul_const] at hmul
  exact hmul

/-! ## Part 7: the truncated Kato test function is smooth and compactly supported -/

/-- **The culmination of stage (1).** For every `κ > 0`, the Kato regularization of the excess,
multiplied by the spatial cutoff, is compactly supported — the divergent, uncut `Φ_κ(g)` alone is
not, since `Φ_κ(g) → -κ / 2` (not `0`) away from the compact support of `v_ε`. -/
theorem hasCompactSupport_kappaProfile_mul_mollifierCutoff {m : ℕ} {ε M σ K τ₀ τ R kap : ℝ}
    (hR : 0 < R) {q : Vec m × ℝ → ℝ} :
    HasCompactSupport (fun x : Vec m =>
      kappaProfile kap (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ))
        * mollifierCutoff m R x) := by
  have hf' : HasCompactSupport (mollifierCutoff m R) := hasCompactSupport_mollifierCutoff m R hR
  exact hf'.mul_left

theorem contDiff_kappaProfile_mul_mollifierCutoff {m : ℕ} {ε M σ K τ₀ τ R kap : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hkap : 0 < kap) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m =>
      kappaProfile kap (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ))
        * mollifierCutoff m R x) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x' : Vec m =>
      mollifySlice m ε q (x', τ) - barrier m M σ K τ₀ (x', τ)) :=
    (contDiff_mollifySlice hε τ q M hmeas hbdd).sub
      ((contDiff_barrier M σ K τ₀).comp (contDiff_id.prodMk contDiff_const))
  exact ((contDiff_kappaProfile kap hkap).comp hg).mul (contDiff_mollifierCutoff m R hR)

end CIV
