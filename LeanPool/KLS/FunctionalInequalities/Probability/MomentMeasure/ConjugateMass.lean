/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.AffineMaximum
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Upper semicontinuity of conjugate mass (CEK Lemma 17, (56b))

`limsup_mass_legendre_le`: let `K` be open and convex with `0 ∈ K`, let potentials `φ j` converge to
`ψ` at every point of
`K`, where `ψ` is finite, and let `ψ` be radially closed and `⊤` off `closure K`. Then for every
additive Haar measure `dx`
on a finite-dimensional space, dimension zero included, `∫ exp(-ψ*) dx` is finite and is at least
`limsup_j ∫ exp(-(φ j)*) dx` (Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1, Lemma
17, (56b)).
No convergence of the conjugates, finiteness of initial dual masses or integrability is assumed: the
pointwise step is
`limsup_density_legendre_le`, and the common integrable dominator
`exists_integrable_exponential_domination` is built from
finitely many vertices (`Analysis/Convex/Legendre/AffineMaximum.lean`) and
`integrable_exp_sub_norm`, the Haar integrability of
`exp(M - c‖y‖)` for `c > 0`.

Real normalization (`real_legendre_normalization`): if the conjugate `φ*` has a real representative
`ψ` and conjugate mass
`1`, then `exp(−ψ)` is Bochner integrable with integral `1` and `weightedMeasure dx ψ` is a
probability measure; finiteness of
the lower integral is established before the real conversion.
-/

@[expose] public section

section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace FunctionalInequalities.Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual exponential norm decay is Haar-integrable in every finite dimension.
The nontrivial case uses polar integration; the zero-dimensional case is compact. -/
theorem integrable_exp_sub_norm [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (dx : Measure E) [dx.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun y : E => Real.exp (M - c * ‖y‖)) dx := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    have : CompactSpace E := inferInstance
    have : IsFiniteMeasure dx := inferInstance
    have heq : (fun y : E => Real.exp (M - c * ‖y‖)) = fun _ : E => Real.exp M := by
      funext y
      rw [Subsingleton.elim y 0]
      simp
    rw [heq]
    exact integrable_const _
  · let := hE
    have hi : Integrable (fun y : E => Real.exp (-c * ‖y‖)) dx := by
      apply (integrable_fun_norm_addHaar dx (f := fun t : ℝ => Real.exp (-c * t))).mpr
      simpa only [smul_eq_mul, Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) (p :=
          1) (by have hsn := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E - 1); linarith)
          (by norm_num) hc)
    convert hi.const_mul (Real.exp M) using 1
    funext y
    rw [← Real.exp_add]
    congr 1
    ring

namespace MomentMeasure

open FunctionalInequalities.Analysis

/-- Pointwise conjugate-density limsup control from actual interior convergence.
No convergence of the conjugates is assumed. Infinite conjugates and density zero
are retained through the EReal exponential order isomorphism. -/
theorem limsup_density_legendre_le
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hsup : ∀ y, legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x)
    (y : E) :
    limsup (fun j => density (legendre (φ j)) y) atTop ≤ density (legendre ψ) y := by
  let L := limsup (fun j => density (legendre (φ j)) y) atTop
  have hbound : legendre ψ y ≤ -ENNReal.log L := by
    rw [hsup y]
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have hneg : Tendsto (fun j => -( (inner ℝ x y : EReal) - φ j x)) atTop
        (𝓝 (-((inner ℝ x y : EReal) - ψ x))) := by
      have hc := (EReal.continuousAt_add (p := (-(inner ℝ x y : EReal), ψ x))
        (.inl (by simp)) (.inl (by simp))).tendsto.comp
          (tendsto_const_nhds.prodMk_nhds (hlim x hx))
      simpa only [EReal.neg_sub (.inl (EReal.coe_ne_bot _))
        (.inl (EReal.coe_ne_top _)), Function.comp_def] using hc
    have hexp := (EReal.expOrderIso.continuous.tendsto _).comp hneg
    have hL : L ≤ EReal.exp (-((inner ℝ x y : EReal) - ψ x)) := by
      calc
        L ≤ limsup (fun j => EReal.exp (-((inner ℝ x y : EReal) - φ j x))) atTop :=
          limsup_le_limsup (Eventually.of_forall fun j =>
            EReal.exp_monotone (EReal.neg_le_neg_iff.mpr
              (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ j z) x)))
        _ = _ := hexp.limsup_eq
    have hlog : ENNReal.log L ≤ -((inner ℝ x y : EReal) - ψ x) := by
      simpa only [ENNReal.logOrderIso_apply, EReal.log_exp] using ENNReal.logOrderIso.monotone hL
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hlog
  have hn : ENNReal.log L ≤ -legendre ψ y := by
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hbound
  simpa only [ENNReal.exp_log, L, density] using EReal.exp_monotone hn

omit [InnerProductSpace ℝ E] in
private theorem density_le_exp_of_lower (ψ : E → EReal) (y : E) (c M : ℝ)
    (hlower : ((c * ‖y‖ - M : ℝ) : EReal) ≤ ψ y) :
    density ψ y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖)) := by
  have h := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hlower)
  simpa only [density, ← EReal.coe_neg, EReal.exp_coe, neg_sub] using h

section FiniteDimensional

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The original open-neighborhood geometry and vertex convergence produce the
actual common exponential dominator. Finiteness is proved rather than supplied.
No condition on initial dual masses is used, and zero-dimensional Haar is included. -/
theorem exists_integrable_exponential_domination
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x))) :
    ∃ (c M : ℝ) (N : ℕ), 0 < c ∧
      (∫⁻ y, ENNReal.ofReal (Real.exp (M - c * ‖y‖)) ∂dx) ≠ ⊤ ∧
      (∀ y, density (legendre ψ) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖))) ∧
      ∀ j, N ≤ j → ∀ y,
        density (legendre (φ j)) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖)) := by
  classical
  obtain ⟨s, hs, hsK, hs0⟩ := exists_finite_hull_neighborhood hK h0
  obtain ⟨c, hc, hcoerc⟩ := affineMaximum_coercive s hs hs0
  let M : ℝ := s.sup' hs (fun x => (ψ x).toReal)
  have hMs : ∀ x ∈ s, (ψ x).toReal ≤ M := fun x hx => Finset.le_sup' (fun x => (ψ x).toReal) hx
  have hA : ∀ y, c * ‖y‖ - M ≤ affineMaximum s hs (fun x => (ψ x).toReal) y :=
    hcoerc _ M hMs
  have hfs : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥ := fun x hx => hfin x (hsK hx)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_affineMaximum_sub_le_legendre φ ψ s hs hfs
      (fun x hx => hlim x (hsK hx)) (by norm_num : (0 : ℝ) < 1))
  refine ⟨c, M + 1, N, hc, ?_, ?_, ?_⟩
  · exact (lintegral_ofReal_ne_top_iff_integrable
      (integrable_exp_sub_norm dx hc (M + 1)).aestronglyMeasurable
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr
        (integrable_exp_sub_norm dx hc (M + 1))
  · intro y
    apply density_le_exp_of_lower _ y c (M + 1)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hA y])).trans
      (affineMaximum_le_legendre ψ s hs hfs y)
  · intro j hj y
    apply density_le_exp_of_lower _ y c (M + 1)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hA y])).trans (hN j hj y)

/-- CEK Lemma 17 (56b) for the actual limit already delivered by (56a).
Only the original interior convergence and actual radial extension are inputs;
the finite affine comparison, domination and mass finiteness are all proved. -/
theorem limsup_mass_legendre_le
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) :
    mass dx (legendre ψ) ≠ ⊤ ∧
      limsup (fun j => mass dx (legendre (φ j))) atTop ≤ mass dx (legendre ψ) := by
  obtain ⟨c, M, N, _hc, hfinite, hψbound, hφbound⟩ :=
    exists_integrable_exponential_domination dx φ ψ hK h0 hfin hlim
  have hpoint : ∀ y, limsup (fun j => density (legendre (φ j)) y) atTop ≤
      density (legendre ψ) y :=
    limsup_density_legendre_le φ ψ hlim (legendre_eq_interior_sup hK hKconv h0 ψ hrad hoff)
  refine ⟨ne_top_of_le_ne_top hfinite (lintegral_mono hψbound), ?_⟩
  have htail := limsup_lintegral_le
    (fun y => ENNReal.ofReal (Real.exp (M - c * ‖y‖)))
    (fun j => measurable_density_legendre (φ (j + N)))
    (fun j => Eventually.of_forall (hφbound (j + N) (Nat.le_add_left _ _))) hfinite
  change limsup (fun j => mass dx (legendre (φ (j + N)))) atTop ≤ _ at htail
  rw [limsup_nat_add (fun j => mass dx (legendre (φ j))) N] at htail
  calc
    limsup (fun j => mass dx (legendre (φ j))) atTop
        ≤ ∫⁻ y, limsup (fun j => density (legendre (φ (j + N))) y) atTop ∂dx := htail
    _ = ∫⁻ y, limsup (fun j => density (legendre (φ j)) y) atTop ∂dx := by
      apply lintegral_congr
      intro y
      exact limsup_nat_add (fun j => density (legendre (φ j)) y) N
    _ ≤ mass dx (legendre ψ) := lintegral_mono hpoint

end FiniteDimensional

end MomentMeasure

end FunctionalInequalities.Probability

/-! ### CEK Proposition 12: logarithmic comparison from integral limits -/

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section
-- A logarithmic lower bound from limits of integrals.

open Filter
open scoped ENNReal Topology
/-- CEK Proposition12 limit assembly: the actual extended logarithm and real
integral limits produce the functional comparison. Neither positive finite
sequence mass nor log convergence nor the final comparison is assumed.
Zero/infinite masses at a finite prefix remain allowed. This is an assembly
helper for the two actual Lemma17 inequalities, not an attainment theorem. -/
theorem log_sub_ge_of_integral_limits
    (a : ℕ → ℝ≥0∞) (m : ℕ → ℝ) (Z : ℝ≥0∞) (r S M : ℝ)
    (hnn : ∀ j, 0 ≤ m j)
    (hF : Tendsto (fun j => ENNReal.log (a j) - (m j : EReal)) atTop (𝓝 (S : EReal)))
    (hm : Tendsto m atTop (𝓝 M))
    (hfirst : ENNReal.ofReal r ≤ liminf (fun j => ENNReal.ofReal (m j)) atTop)
    (hsecond : limsup a atTop ≤ Z) :
    0 < Z ∧ (S : EReal) ≤ ENNReal.log Z - (r : EReal) := by
  have hmE : Tendsto (fun j => (m j : EReal)) atTop (𝓝 (M : EReal)) :=
    EReal.tendsto_coe.mpr hm
  have hlog : Tendsto (fun j => ENNReal.log (a j)) atTop (𝓝 ((S + M : ℝ) : EReal)) := by
    have h := (EReal.continuousAt_add_coe_coe S M).tendsto.comp (hF.prodMk_nhds hmE)
    simpa only [Function.comp_def, EReal.sub_add_cancel, ← EReal.coe_add] using h
  have ha : Tendsto a atTop (𝓝 (ENNReal.ofReal (Real.exp (S + M)))) := by
    have h := (ENNReal.continuous_exp.tendsto ((S + M : ℝ) : EReal)).comp hlog
    simpa only [Function.comp_def, ENNReal.exp_log, EReal.exp_coe] using h
  have hZ : ENNReal.ofReal (Real.exp (S + M)) ≤ Z := by
    simpa only [ha.limsup_eq] using hsecond
  have hmR : Tendsto (fun j => ENNReal.ofReal (m j)) atTop (𝓝 (ENNReal.ofReal M)) :=
    (ENNReal.continuous_ofReal.tendsto M).comp hm
  have hM : 0 ≤ M := ge_of_tendsto hm (Eventually.of_forall hnn)
  have hrM : r ≤ M := (ENNReal.ofReal_le_ofReal_iff hM).mp (by
    simpa only [hmR.liminf_eq] using hfirst)
  have hl : ((S + M : ℝ) : EReal) ≤ ENNReal.log Z := by
    have h := ENNReal.log_le_log hZ
    simpa only [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] using h
  refine ⟨(ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le hZ, ?_⟩
  calc
    (S : EReal) ≤ ((S + M - r : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
    _ = ((S + M : ℝ) : EReal) - (r : EReal) := EReal.coe_sub _ _
    _ ≤ _ := EReal.sub_le_sub hl le_rfl

end

end FunctionalInequalities.Probability.MomentMeasure

namespace FunctionalInequalities.Probability.MomentMeasure

section RealNormalization

open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace

open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- Actual conjugate mass one gives genuine Bochner integrability and a
probability measure for its finite real representative. Integral finiteness
is established before using the ENNReal-to-real integrability bridge. -/
theorem real_legendre_normalization
    (dx : Measure E) (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, legendre q x = (ψ x : EReal))
    (hmass : mass dx (legendre q) = 1) :
    Integrable (fun x => Real.exp (-ψ x)) dx ∧
    (∫ x, Real.exp (-ψ x) ∂dx) = 1 ∧
    IsProbabilityMeasure (weightedMeasure dx (fun x => (ψ x : EReal))) := by
  have hd : density (legendre q) =
      (fun x => ENNReal.ofReal (Real.exp (-ψ x))) := by
    funext x
    simp only [density, hψ x, ← EReal.coe_neg, EReal.exp_coe]
  have hmassfinite : (∫⁻ x, density (legendre q) x ∂dx) ≠ ∞ := by
    change mass dx (legendre q) ≠ ∞
    rw [hmass]
    exact ENNReal.one_ne_top
  have hi : Integrable (fun x => (density (legendre q) x).toReal) dx :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top
      (measurable_density_legendre q).aemeasurable hmassfinite
  have hreal : (fun x => (density (legendre q) x).toReal) =
      (fun x => Real.exp (-ψ x)) := by
    funext x
    rw [hd, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [hreal] at hi
  have hmass' : (∫⁻ x, ENNReal.ofReal (Real.exp (-ψ x)) ∂dx) = 1 := by
    simpa only [mass, hd] using hmass
  have hnonneg : ∀ᵐ x ∂dx, 0 ≤ Real.exp (-ψ x) :=
    Filter.Eventually.of_forall (fun x => Real.exp_nonneg (-ψ x))
  have hpotential : (fun x : E => (ψ x : EReal)) = legendre q :=
    funext (fun x => (hψ x).symm)
  refine ⟨hi, ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae hnonneg hi.aestronglyMeasurable,
      hmass', ENNReal.toReal_one]
  · constructor
    change (dx.withDensity (density (fun x => (ψ x : EReal)))) univ = 1
    rw [hpotential, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact hmass

end RealNormalization

end FunctionalInequalities.Probability.MomentMeasure
