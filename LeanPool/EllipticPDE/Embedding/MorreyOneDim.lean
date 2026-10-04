/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.WeakGradient
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.HolderNorm


/-!
# Morrey's inequality on a one-dimensional ball

The `d = 1` warm-up for the Morrey embedding: a function with an `L²` weak derivative on
an interval has a `1/2`-Hölder representative. The singular kernel of the general-dimension
argument degenerates to the constant `1` here, so the whole content is the one-dimensional
weak fundamental theorem of calculus (recovering `u` a.e. from its weak derivative) followed
by Cauchy-Schwarz.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

section CoordTransport

/-- The measurable equivalence identifying `EuclideanSpace ℝ (Fin 1)` with `ℝ` via the single
coordinate. -/
def coordEquiv : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- `coordEquiv` sends a point to its single coordinate. -/
@[simp] lemma coordEquiv_apply (x : EuclideanSpace ℝ (Fin 1)) : coordEquiv x = x 0 := rfl

/-- The single coordinate of `coordEquiv.symm t` is `t`. -/
lemma coordEquiv_symm_coord (t : ℝ) :
    (coordEquiv.symm t : EuclideanSpace ℝ (Fin 1)) 0 = t := by
  conv_rhs => rw [← coordEquiv.apply_symm_apply t]
  rw [coordEquiv_apply]

/-- `coordEquiv.symm t` is the one-dimensional Euclidean point `!₂[t]`. -/
@[simp] lemma coordEquiv_symm_eq (t : ℝ) :
    (coordEquiv.symm t : EuclideanSpace ℝ (Fin 1)) = !₂[t] := by
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rw [coordEquiv_symm_coord]
  rfl

/-- `coordEquiv` is volume preserving between the Euclidean line and `ℝ`. -/
lemma coordEquiv_measurePreserving : MeasurePreserving coordEquiv volume volume := by
  have h1 : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm) volume volume :=
    MeasurePreserving.symm _ (PiLp.volume_preserving_toLp (Fin 1))
  have h2 : MeasurePreserving (⇑(MeasurableEquiv.funUnique (Fin 1) ℝ)) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  exact h2.comp h1

/-- `EuclideanSpace ℝ (Fin 1)` distance collapses to the distance of the single coordinate. -/
lemma dist_eq_coord (x y : EuclideanSpace ℝ (Fin 1)) : dist x y = |x 0 - y 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]

/-- The ball `Metric.ball c r` corresponds, under `coordEquiv`, to the coordinate interval
`Ioo (c 0 - r) (c 0 + r)`. -/
lemma coordEquiv_symm_preimage_ball (c : EuclideanSpace ℝ (Fin 1)) (r : ℝ) :
    coordEquiv.symm ⁻¹' (Metric.ball c r) = Set.Ioo (c 0 - r) (c 0 + r) := by
  ext t
  simp only [Set.mem_preimage, Metric.mem_ball, coordEquiv_symm_eq, dist_eq_coord,
    Matrix.cons_val_zero, Set.mem_Ioo, abs_sub_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- Transport a set integral over a `1`-D ball into an interval integral over the corresponding
coordinate interval. -/
lemma ball_setIntegral_eq_intervalIntegral {c : EuclideanSpace ℝ (Fin 1)} {r : ℝ} (hr : 0 < r)
    (F : EuclideanSpace ℝ (Fin 1) → ℝ) :
    ∫ x in Metric.ball c r, F x = ∫ t in (c 0 - r)..(c 0 + r), F (!₂[t]) := by
  have hab : c 0 - r ≤ c 0 + r := by linarith
  have hmp : MeasurePreserving (⇑coordEquiv.symm) volume volume :=
    MeasurePreserving.symm coordEquiv coordEquiv_measurePreserving
  have htr := hmp.setIntegral_preimage_emb coordEquiv.symm.measurableEmbedding F (Metric.ball c r)
  rw [coordEquiv_symm_preimage_ball] at htr
  simp only [coordEquiv_symm_eq] at htr
  rw [← htr, intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The ball corresponds, under `coordEquiv`, to the coordinate interval, in the forward
direction. -/
lemma coordEquiv_preimage_Ioo (c : EuclideanSpace ℝ (Fin 1)) (r : ℝ) :
    coordEquiv ⁻¹' (Set.Ioo (c 0 - r) (c 0 + r)) = Metric.ball c r := by
  rw [← coordEquiv_symm_preimage_ball]
  ext x
  simp only [Set.mem_preimage]
  constructor
  · intro hx
    have : coordEquiv.symm (coordEquiv x) = x := coordEquiv.symm_apply_apply x
    rwa [← this]
  · intro hx
    rwa [coordEquiv.symm_apply_apply]

end CoordTransport

section CoordLift

/-- The classical partial derivative of a lifted `1`-D test function is the classical
derivative of the interval function, at the corresponding coordinate. -/
lemma partialD_coord_comp {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ)
    (x : EuclideanSpace ℝ (Fin 1)) :
    partialD 0 (fun y : EuclideanSpace ℝ (Fin 1) => ψ (y 0)) x = deriv ψ (x 0) := by
  have hproj : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => y 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt
  have hcomp := ((hψ (x 0)).hasFDerivAt).comp x hproj
  have hfd : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 1) => ψ (y 0)) x
      = (fderiv ℝ ψ (x 0)).comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) := hcomp.fderiv
  change fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 1) => ψ (y 0)) x
      (EuclideanSpace.single 0 (1 : ℝ)) = deriv ψ (x 0)
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply]
  have hone : (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) (EuclideanSpace.single 0 (1 : ℝ)) = 1 := by
    simp
  rw [hone]
  rfl

/-- The coordinate projection agrees with `coordEquiv` as a bare function. -/
lemma proj_eq_coordEquiv :
    (⇑(EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) : EuclideanSpace ℝ (Fin 1) → ℝ) = ⇑coordEquiv :=
  rfl

/-- Lifting a smooth interval test function compactly supported in `Ioo a b` to
`EuclideanSpace ℝ (Fin 1)` is a smooth test function compactly supported in the ball. -/
lemma contDiff_lift {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin 1) => φ (x 0)) :=
  hφ.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff

/-- The support of a lifted test function is the coordinate preimage of the original support. -/
lemma support_lift (φ : ℝ → ℝ) :
    Function.support (fun x : EuclideanSpace ℝ (Fin 1) => φ (x 0))
      = coordEquiv ⁻¹' (Function.support φ) := by
  ext x
  simp [Function.mem_support, Set.mem_preimage, coordEquiv_apply]

/-- The topological support of a lifted test function is contained in the coordinate preimage
of the original topological support. -/
lemma tsupport_lift_subset (φ : ℝ → ℝ) :
    tsupport (fun x : EuclideanSpace ℝ (Fin 1) => φ (x 0)) ⊆ coordEquiv ⁻¹' (tsupport φ) := by
  rw [tsupport, support_lift, ← proj_eq_coordEquiv]
  apply closure_minimal (Set.preimage_mono (subset_tsupport φ))
  exact (isClosed_tsupport φ).preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous

/-- A lifted test function whose original is compactly supported in `(a, b)` has compact support
contained in the ball `Metric.ball c r`. -/
lemma hasCompactSupport_and_tsupport_lift {φ : ℝ → ℝ} {c : EuclideanSpace ℝ (Fin 1)} {r : ℝ}
    (hsub : tsupport φ ⊆ Set.Ioo (c 0 - r) (c 0 + r)) :
    HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 1) => φ (x 0)) ∧
      tsupport (fun x : EuclideanSpace ℝ (Fin 1) => φ (x 0)) ⊆ Metric.ball c r := by
  have hsub' : tsupport (fun x : EuclideanSpace ℝ (Fin 1) => φ (x 0)) ⊆ Metric.ball c r := by
    apply (tsupport_lift_subset φ).trans
    rw [← coordEquiv_preimage_Ioo]
    exact Set.preimage_mono hsub
  refine ⟨HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) ?_, hsub'⟩
  exact subset_tsupport _ |>.trans (hsub'.trans Metric.ball_subset_closedBall)

end CoordLift

section DuBoisReymond

variable {p q : ℝ}

/-- A mean-zero smooth function compactly supported in an open interval is the derivative,
everywhere, of a smooth function compactly supported in the same interval. -/
private lemma exists_contDiff_hasDerivAt_of_integral_eq_zero {ψ₀ : ℝ → ℝ}
    (hψ₀ : ContDiff ℝ (⊤ : ℕ∞) ψ₀) (hsupp : HasCompactSupport ψ₀)
    (hsub : tsupport ψ₀ ⊆ Set.Ioo p q) (hmean : ∫ t in p..q, ψ₀ t = 0) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ Set.Ioo p q ∧
      ∀ x, HasDerivAt Φ (ψ₀ x) x := by
  classical
  set Φ : ℝ → ℝ := fun x => ∫ t in p..x, ψ₀ t with hΦdef
  have hcont : Continuous ψ₀ := hψ₀.continuous
  have hderiv : ∀ x, HasDerivAt Φ (ψ₀ x) x :=
    fun x => (hcont.integral_hasStrictDerivAt p x).hasDerivAt
  have hderivΦ : deriv Φ = ψ₀ := funext fun x => (hderiv x).deriv
  have hdiff : Differentiable ℝ Φ := fun x => (hderiv x).differentiableAt
  have hΦsmooth : ContDiff ℝ (⊤ : ℕ∞) Φ :=
    contDiff_infty_iff_deriv.mpr ⟨hdiff, hderivΦ ▸ hψ₀⟩
  rcases eq_empty_or_nonempty (tsupport ψ₀) with hempty | hne
  · -- `ψ₀` is identically zero, so `Φ` is identically zero too.
    have hψ₀0 : ψ₀ = 0 := by
      funext x
      apply image_eq_zero_of_notMem_tsupport
      rw [hempty]; exact notMem_empty x
    have hΦ0 : Φ = 0 := by
      funext x
      simp [hΦdef, hψ₀0]
    refine ⟨Φ, hΦsmooth, ?_, ?_, hderiv⟩
    · rw [hΦ0]
      apply HasCompactSupport.of_support_subset_isCompact isCompact_empty
      simp
    · rw [hΦ0]; simp
  · -- `ψ₀` is supported in `[p', q'] ⊆ (p, q)`, the extremes of its (compact) support.
    have hcpt : IsCompact (tsupport ψ₀) := hsupp
    set p' := sInf (tsupport ψ₀) with hp'def
    set q' := sSup (tsupport ψ₀) with hq'def
    have hp'mem : p' ∈ tsupport ψ₀ := hcpt.sInf_mem hne
    have hq'mem : q' ∈ tsupport ψ₀ := hcpt.sSup_mem hne
    have hp'q : p < p' := (hsub hp'mem).1
    have hq'q : q' < q := (hsub hq'mem).2
    have hp'q' : p' ≤ q' := csInf_le_csSup hne hcpt.bddBelow hcpt.bddAbove
    -- `ψ₀` vanishes strictly outside `[p', q']`, hence (by continuity) also at `p'` and `q'`.
    have hzero_lt : ∀ x, x < p' → ψ₀ x = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport
        (fun hmem => absurd (csInf_le hcpt.bddBelow hmem) (not_le.mpr hx))
    have hzero_gt : ∀ x, q' < x → ψ₀ x = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport
        (fun hmem => absurd (le_csSup hcpt.bddAbove hmem) (not_le.mpr hx))
    have hψ₀p' : ψ₀ p' = 0 := by
      have h1 : Filter.Tendsto ψ₀ (nhdsWithin p' (Set.Iio p')) (nhds (ψ₀ p')) :=
        hcont.continuousAt.continuousWithinAt
      have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhdsWithin p' (Set.Iio p')] ψ₀ := by
        filter_upwards [self_mem_nhdsWithin] with x hx using (hzero_lt x hx).symm
      exact tendsto_nhds_unique h1 (Filter.Tendsto.congr' heq tendsto_const_nhds)
    have hψ₀q' : ψ₀ q' = 0 := by
      have h1 : Filter.Tendsto ψ₀ (nhdsWithin q' (Set.Ioi q')) (nhds (ψ₀ q')) :=
        hcont.continuousAt.continuousWithinAt
      have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhdsWithin q' (Set.Ioi q')] ψ₀ := by
        filter_upwards [self_mem_nhdsWithin] with x hx using (hzero_gt x hx).symm
      exact tendsto_nhds_unique h1 (Filter.Tendsto.congr' heq tendsto_const_nhds)
    have hzero_le : ∀ x, x ≤ p' → ψ₀ x = 0 := by
      intro x hx
      rcases hx.lt_or_eq with h | h
      · exact hzero_lt x h
      · exact h ▸ hψ₀p'
    have hzero_ge : ∀ x, q' ≤ x → ψ₀ x = 0 := by
      intro x hx
      rcases hx.lt_or_eq with h | h
      · exact hzero_gt x h
      · exact h.symm ▸ hψ₀q'
    have hzero_int_le : ∀ x, x ≤ p' → ∫ t in p..x, ψ₀ t = 0 := by
      intro x hx
      have heqOn : Set.EqOn ψ₀ 0 (Set.uIcc p x) := by
        intro t ht
        rcases Set.mem_uIcc.mp ht with ⟨_, ht2⟩ | ⟨_, ht2⟩
        · exact hzero_le t (ht2.trans hx)
        · exact hzero_le t (ht2.trans hp'q.le)
      rw [intervalIntegral.integral_congr heqOn]
      simp
    have hzero_int_ge : ∀ x, q' ≤ x → ∫ t in q'..x, ψ₀ t = 0 := by
      intro x hx
      have heqOn : Set.EqOn ψ₀ 0 (Set.uIcc q' x) := by
        intro t ht
        rcases Set.mem_uIcc.mp ht with ⟨ht1, _⟩ | ⟨ht1, _⟩
        · exact hzero_ge t ht1
        · exact hzero_ge t (hx.trans ht1)
      rw [intervalIntegral.integral_congr heqOn]
      simp
    have hΦ_le : ∀ x, x ≤ p' → Φ x = 0 := fun x hx => hzero_int_le x hx
    have hΦ_ge : ∀ x, q' ≤ x → Φ x = 0 := by
      intro x hx
      have h1 : Φ x = (∫ t in p..q', ψ₀ t) + ∫ t in q'..x, ψ₀ t := by
        have hadj : (∫ t in p..q', ψ₀ t) + ∫ t in q'..x, ψ₀ t = ∫ t in p..x, ψ₀ t :=
          intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable p q') (hcont.intervalIntegrable q' x)
        change ∫ t in p..x, ψ₀ t = _
        rw [← hadj]
      have h2 : ∫ t in p..q', ψ₀ t = 0 := by
        have hadj : (∫ t in p..q', ψ₀ t) + ∫ t in q'..q, ψ₀ t = ∫ t in p..q, ψ₀ t :=
          intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable p q') (hcont.intervalIntegrable q' q)
        have h3 : ∫ t in q'..q, ψ₀ t = 0 := hzero_int_ge q hq'q.le
        rw [h3, add_zero] at hadj
        rw [← hadj] at hmean
        exact hmean
      rw [h1, h2, zero_add]
      exact hzero_int_ge x hx
    refine ⟨Φ, hΦsmooth, ?_, ?_, hderiv⟩
    · apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := p') (b := q'))
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hxmem
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxmem
      rcases hxmem with h | h
      · exact hx (hΦ_le x h.le)
      · exact hx (hΦ_ge x h.le)
    · calc tsupport Φ ⊆ Set.Icc p' q' := by
            apply closure_minimal _ isClosed_Icc
            intro x hx
            rw [Function.mem_support] at hx
            by_contra hxmem
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxmem
            rcases hxmem with h | h
            · exact hx (hΦ_le x h.le)
            · exact hx (hΦ_ge x h.le)
        _ ⊆ Set.Ioo p q := fun x hx => ⟨lt_of_lt_of_le hp'q hx.1, lt_of_le_of_lt hx.2 hq'q⟩

/-- A whole-line Bochner integral of a function supported in `(p, q)` collapses to the
interval integral. -/
private lemma integral_eq_intervalIntegral_of_tsupport_subset {F : ℝ → ℝ}
    (hpq : p ≤ q) (hsupp : tsupport F ⊆ Set.Ioo p q) :
    ∫ x, F x ∂volume = ∫ t in p..q, F t := by
  have h1 : ∫ x, F x ∂volume = ∫ x in Set.Ioo p q, F x ∂volume := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsupp hmem))
  rw [h1, intervalIntegral.integral_of_le hpq, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- A smooth bump, compactly supported in `(p, q)`, with total interval integral `1`. -/
private lemma exists_bump_integral_one (hpq : p < q) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Set.Ioo p q ∧
      ∫ t in p..q, χ t = 1 := by
  set c₀ : ℝ := (p + q) / 2 with hc₀def
  set rOut : ℝ := (q - p) / 4 with hrOutdef
  set rIn : ℝ := (q - p) / 8 with hrIndef
  let hbump : ContDiffBump c₀ := ⟨rIn, rOut, by rw [hrIndef]; linarith, by
    rw [hrIndef, hrOutdef]; linarith⟩
  have htsupp : tsupport (hbump.normed volume) ⊆ Set.Ioo p q := by
    rw [hbump.tsupport_normed_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    have hxle : -rOut ≤ x - c₀ ∧ x - c₀ ≤ rOut := hx
    constructor <;> [linarith [hxle.1]; linarith [hxle.2]]
  refine ⟨hbump.normed volume, hbump.contDiff_normed, hbump.hasCompactSupport_normed,
    htsupp, ?_⟩
  rw [← integral_eq_intervalIntegral_of_tsupport_subset hpq.le htsupp]
  exact hbump.integral_normed

/-- **One-dimensional du Bois-Reymond lemma.** If `v` is locally integrable on `(p, q)` and
its weak derivative vanishes there (tested against every smooth compactly supported bump), then
`v` agrees a.e. on `(p, q)` with a constant. This is the key step recovering a
representative of `u` from a weak derivative: applied to `v = u - (\text{primitive of } g)`, it
supplies the constant of integration. -/
private lemma ae_eq_const_of_forall_integral_mul_deriv_eq_zero {v : ℝ → ℝ} (hpq : p < q)
    (hv : IntegrableOn v (Set.Ioo p q) volume)
    (hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo p q → ∫ t in p..q, v t * deriv φ t = 0) :
    ∃ C : ℝ, v =ᵐ[volume.restrict (Set.Ioo p q)] fun _ => C := by
  obtain ⟨χ, hχsmooth, hχsupp, hχtsupp, hχint⟩ := exists_bump_integral_one hpq
  set C : ℝ := ∫ t in p..q, v t * χ t with hCdef
  refine ⟨C, ?_⟩
  have hvI : IntervalIntegrable v volume p q :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hpq.le).mpr hv
  have hχI : IntervalIntegrable χ volume p q := hχsmooth.continuous.intervalIntegrable p q
  have hmain : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo p q → ∫ x, ψ x • (v x - C) ∂volume = 0 := by
    intro ψ hψsmooth hψsupp hψtsupp
    have hψI : IntervalIntegrable ψ volume p q := hψsmooth.continuous.intervalIntegrable p q
    set m : ℝ := ∫ t in p..q, ψ t with hmdef
    set ψ₀ : ℝ → ℝ := fun t => ψ t - m * χ t with hψ₀def
    have hψ₀smooth : ContDiff ℝ (⊤ : ℕ∞) ψ₀ := hψsmooth.sub (contDiff_const.mul hχsmooth)
    have hunion_compact : IsCompact (tsupport ψ ∪ tsupport χ) := hψsupp.union hχsupp
    have hunion_subset : tsupport ψ ∪ tsupport χ ⊆ Set.Ioo p q :=
      Set.union_subset hψtsupp hχtsupp
    have hψ₀supp_sub : Function.support ψ₀ ⊆ tsupport ψ ∪ tsupport χ := by
      intro x hx
      simp only [hψ₀def, Function.mem_support, ne_eq, sub_eq_zero] at hx
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      exact hx (by rw [image_eq_zero_of_notMem_tsupport hcon.1,
        image_eq_zero_of_notMem_tsupport hcon.2, mul_zero])
    have hψ₀supp : HasCompactSupport ψ₀ :=
      HasCompactSupport.of_support_subset_isCompact hunion_compact hψ₀supp_sub
    have hψ₀tsupp : tsupport ψ₀ ⊆ Set.Ioo p q :=
      (closure_minimal hψ₀supp_sub hunion_compact.isClosed).trans hunion_subset
    have hψ₀mean : ∫ t in p..q, ψ₀ t = 0 := by
      have hexp : ∫ t in p..q, ψ₀ t = (∫ t in p..q, ψ t) - m * ∫ t in p..q, χ t := by
        simp only [hψ₀def]
        rw [intervalIntegral.integral_sub hψI (hχI.const_mul m),
          intervalIntegral.integral_const_mul]
      rw [hexp, hχint, mul_one, ← hmdef, sub_self]
    obtain ⟨Φ, hΦsmooth, hΦsupp, hΦtsupp, hΦderiv⟩ :=
      exists_contDiff_hasDerivAt_of_integral_eq_zero hψ₀smooth hψ₀supp hψ₀tsupp hψ₀mean
    have hΦderiv' : deriv Φ = ψ₀ := funext fun x => (hΦderiv x).deriv
    have hkey : ∫ t in p..q, v t * ψ₀ t = 0 := by
      have := hzero Φ hΦsmooth hΦsupp hΦtsupp
      rwa [hΦderiv'] at this
    have hexpand : ∫ t in p..q, v t * ψ₀ t
        = (∫ t in p..q, v t * ψ t) - m * ∫ t in p..q, v t * χ t := by
      have heq : ∀ t, v t * ψ₀ t = v t * ψ t - m * (v t * χ t) := by
        intro t; simp only [hψ₀def]; ring
      simp_rw [heq]
      rw [intervalIntegral.integral_sub (hvI.mul_continuousOn hψsmooth.continuous.continuousOn)
        ((hvI.mul_continuousOn hχsmooth.continuous.continuousOn).const_mul m),
        intervalIntegral.integral_const_mul]
    rw [hkey] at hexpand
    have hvψ : ∫ t in p..q, v t * ψ t = m * C := by
      rw [hCdef]; linarith [hexpand]
    have hFsupp : tsupport (fun x => v x * ψ x - C * ψ x) ⊆ Set.Ioo p q :=
      calc tsupport (fun x => v x * ψ x - C * ψ x)
          ⊆ closure (Function.support (fun x => v x * ψ x)
              ∪ Function.support (fun x => C * ψ x)) := closure_mono (Function.support_sub _ _)
        _ = tsupport (fun x => v x * ψ x) ∪ tsupport (fun x => C * ψ x) := closure_union
        _ ⊆ Set.Ioo p q := Set.union_subset
            ((closure_mono (Function.support_mul_subset_right v ψ)).trans hψtsupp)
            ((closure_mono (Function.support_mul_subset_right (fun _ => C) ψ)).trans hψtsupp)
    have hrhs : ∫ x, (v x * ψ x - C * ψ x) ∂volume
        = (∫ t in p..q, v t * ψ t) - C * m := by
      rw [integral_eq_intervalIntegral_of_tsupport_subset hpq.le hFsupp,
        intervalIntegral.integral_sub (hvI.mul_continuousOn hψsmooth.continuous.continuousOn)
          (hψI.const_mul C), intervalIntegral.integral_const_mul]
    have hlhs : (fun x => ψ x • (v x - C)) = fun x => v x * ψ x - C * ψ x := by
      funext x; rw [smul_eq_mul]; ring
    rw [hlhs, hrhs, hvψ]
    ring
  have hvsubC : IntegrableOn (v - fun _ => C) (Set.Ioo p q) volume := by
    have hconst : IntegrableOn (fun _ : ℝ => C) (Set.Ioo p q) volume :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact hv.sub hconst
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo
    hvsubC.locallyIntegrableOn hmain
  apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hae] with x hx hxmem
  have := hx hxmem
  simp only [Pi.sub_apply] at this
  linarith

end DuBoisReymond

/-- A globally smooth function is absolutely continuous on every interval: its derivative is
continuous, hence bounded on the compact `uIcc a b`, giving a Lipschitz (hence AC) bound there. -/
private lemma absolutelyContinuousOnInterval_of_contDiff {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a b : ℝ) : AbsolutelyContinuousOnInterval φ a b := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hderivφcont : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (f := deriv φ) (s := Set.uIcc a b) hderivφcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC a Set.left_mem_uIcc)
  have hCbound : ∀ x ∈ Set.uIcc a b, ‖deriv φ x‖₊ ≤ C.toNNReal := by
    intro x hx
    rw [← Real.toNNReal_coe (r := ‖deriv φ x‖₊)]
    exact Real.toNNReal_le_toNNReal (hC x hx)
  exact ((convex_uIcc a b).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => hdiff.differentiableAt) hCbound).absolutelyContinuousOnInterval

/-- For a real-valued `L²` function, the square of the `eLpNorm` equals `ENNReal.ofReal` of the
integral of the square. -/
private lemma eLpNorm_two_sq_eq_ofReal_integral_sq {f : ℝ → ℝ} {μ : Measure ℝ}
    (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ x, (f x) ^ 2 ∂μ) := by
  have hstep : ∀ x, ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((f x) ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (f x)) (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
      hf.aestronglyMeasurable,
    show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
  simp_rw [hstep]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    ← ENNReal.rpow_natCast (ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
  norm_num

private lemma integral_weak_deriv_minus_primitive : ∀ (c : EuclideanSpace ℝ (Fin 1)) {r : ℝ} (_ :
  0 < r) (u g : EuclideanSpace ℝ (Fin 1) → ℝ)
  (_ : IntegrableOn u (ball c r) volume) (_ : HasWeakGradOn (ball c r) u fun _ => g),
  let a := c.ofLp 0 - r;
  ∀ (_ : a = c.ofLp 0 - r),
    let b := c.ofLp 0 + r;
    ∀ (_ : b = c.ofLp 0 + r) (_ : a < b),
      let g' := fun t => g !₂[t];
      let u'' := fun t => u !₂[t];
      ∀ (_ : (fun t => u !₂[t]) = u ∘ ⇑coordEquiv.symm)
        (_ : MeasurePreserving (⇑coordEquiv.symm) (volume.restrict (Ioo a b)) (volume.restrict
          (ball c r))),
        let G := fun x => ∫ (t : ℝ) in a..x, g' t;
        ∀ (_ : AbsolutelyContinuousOnInterval G a b) (_ : ∀ᵐ (x : ℝ), x ∈ uIcc a b →
          HasDerivAt G (g' x) x)
          (φ : ℝ → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ →
            HasCompactSupport φ → tsupport φ ⊆ Ioo a b → ∫ (t : ℝ) in a..b, (u'' t - G t) * deriv
              φ t = 0 := by
  classical
  intro c r hr u g hu hwg a hadef b hbdef hab g' u'' hcoordsymm' hmpr G hGac hGaeDeriv
  have hu''def : u'' = fun t => u !₂[t] := rfl
  intro φ hφsmooth hφsupp hφtsupp
  have hφtsupp' : tsupport φ ⊆ Set.Ioo (c 0 - r) (c 0 + r) := by
    rw [← hadef, ← hbdef]; exact hφtsupp
  set Φ : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => φ (x 0) with hΦdef
  have hΦsmooth : ContDiff ℝ (⊤ : ℕ∞) Φ := contDiff_lift hφsmooth
  obtain ⟨hΦsupp, hΦtsupp⟩ := hasCompactSupport_and_tsupport_lift hφtsupp'
  have hwgΦ := hwg Φ hΦsmooth hΦsupp hΦtsupp 0
  have hφdiff : Differentiable ℝ φ := hφsmooth.differentiable (by norm_num)
  have hpartialD : ∀ x, partialD 0 Φ x = deriv φ (x 0) := fun x => partialD_coord_comp hφdiff x
  have hlift1 : (fun x : EuclideanSpace ℝ (Fin 1) => u x * partialD 0 Φ x)
      = fun x => u x * deriv φ (x 0) := by funext x; rw [hpartialD]
  rw [hlift1] at hwgΦ
  rw [show (fun x : EuclideanSpace ℝ (Fin 1) => g x * Φ x) = fun x => g x * φ (x 0) from rfl]
    at hwgΦ
  rw [ball_setIntegral_eq_intervalIntegral hr (fun x => u x * deriv φ (x 0)),
      ball_setIntegral_eq_intervalIntegral hr (fun x => g x * φ (x 0))] at hwgΦ
  rw [← hadef, ← hbdef] at hwgΦ
  -- `hwgΦ : ∫ t in a..b, u'' t * deriv φ t = -∫ t in a..b, g' t * φ t`
  have hφAC : AbsolutelyContinuousOnInterval φ a b :=
    absolutelyContinuousOnInterval_of_contDiff hφsmooth a b
  have hφa : φ a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem => lt_irrefl a (hφtsupp hmem).1)
  have hφb : φ b = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem => lt_irrefl b (hφtsupp hmem).2)
  have hIBP := hφAC.integral_mul_deriv_eq_deriv_mul hGac
  rw [hφa, hφb] at hIBP
  simp only [zero_mul, sub_zero, zero_sub] at hIBP
  have hderivφcont : Continuous (deriv φ) := hφsmooth.continuous_deriv (by norm_num)
  have hcongr : ∫ t in a..b, φ t * deriv G t = ∫ t in a..b, φ t * g' t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hGaeDeriv] with x hx hxioc
    rw [(hx (Set.uIoc_subset_uIcc hxioc)).deriv]
  rw [hcongr] at hIBP
  -- `hIBP : ∫ t in a..b, φ t * g' t = -∫ t in a..b, deriv φ t * G t`
  have heq1 : ∫ t in a..b, u'' t * deriv φ t = -∫ t in a..b, g' t * φ t := hwgΦ
  have heq2 : ∫ t in a..b, G t * deriv φ t = -∫ t in a..b, g' t * φ t := by
    have e1 : ∫ t in a..b, G t * deriv φ t = ∫ t in a..b, deriv φ t * G t :=
      intervalIntegral.integral_congr (fun t _ => mul_comm _ _)
    have e2 : ∫ t in a..b, φ t * g' t = ∫ t in a..b, g' t * φ t :=
      intervalIntegral.integral_congr (fun t _ => mul_comm _ _)
    rw [e1]
    linarith [hIBP, e2]
  have hu''IntegrableOn : IntegrableOn u'' (Set.Ioo a b) volume := by
    rw [hu''def, hcoordsymm']
    exact hmpr.integrable_comp_of_integrable hu
  have hu''II : IntervalIntegrable u'' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hu''IntegrableOn
  have hGcont : ContinuousOn G (Set.uIcc a b) := hGac.continuousOn
  have hGII : IntervalIntegrable G volume a b := hGcont.intervalIntegrable
  have hsub : ∫ t in a..b, (u'' t - G t) * deriv φ t
      = (∫ t in a..b, u'' t * deriv φ t) - ∫ t in a..b, G t * deriv φ t := by
    have heq : ∀ t, (u'' t - G t) * deriv φ t = u'' t * deriv φ t - G t * deriv φ t := by
      intro t; ring
    simp_rw [heq]
    exact intervalIntegral.integral_sub (hu''II.mul_continuousOn hderivφcont.continuousOn)
      (hGII.mul_continuousOn hderivφcont.continuousOn)
  rw [hsub, heq1, heq2, sub_self]

/-- **Morrey on an interval.** A function with an `L²` weak derivative on a `1`-D ball has
a `C^{0,1/2}` representative, with Hölder constant linear in the `L²` norm of its
derivative.

Terminal result of the library, the one-dimensional endpoint of the Morrey chain.
Nothing else consumes it. -/
theorem morrey_ball_oneDim (c : EuclideanSpace ℝ (Fin 1)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin 1) → ℝ) (g : EuclideanSpace ℝ (Fin 1) → ℝ),
      IntegrableOn u (Metric.ball c r) volume →
      MemLp g 2 (volume.restrict (Metric.ball c r)) →
      HasWeakGradOn (Metric.ball c r) u (fun _ => g) →
      ∃ u' : EuclideanSpace ℝ (Fin 1) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)] u ∧
        HolderOnWith
          (C * (eLpNorm g 2 (volume.restrict (Metric.ball c r))).toNNReal)
          (morreyExponent 1 2) u' (Metric.ball c r) := by
  refine ⟨1, fun u g hu hg hwg => ?_⟩
  set a : ℝ := c 0 - r with hadef
  set b : ℝ := c 0 + r with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  set g' : ℝ → ℝ := fun t => g (!₂[t]) with hg'def
  set u'' : ℝ → ℝ := fun t => u (!₂[t]) with hu''def
  have hcoordsymm : (fun t : ℝ => g (!₂[t])) = g ∘ (coordEquiv.symm) := by
    funext t; rw [Function.comp_apply, coordEquiv_symm_eq]
  have hcoordsymm' : (fun t : ℝ => u (!₂[t])) = u ∘ (coordEquiv.symm) := by
    funext t; rw [Function.comp_apply, coordEquiv_symm_eq]
  have hmpr : MeasurePreserving (⇑coordEquiv.symm)
      (volume.restrict (Set.Ioo a b)) (volume.restrict (Metric.ball c r)) := by
    have h := (MeasurePreserving.symm coordEquiv coordEquiv_measurePreserving).restrict_preimage_emb
      coordEquiv.symm.measurableEmbedding (Metric.ball c r)
    rwa [coordEquiv_symm_preimage_ball] at h
  -- `g'` is `L²` (hence `L¹`) on `Ioo a b`, so interval integrable on `[a, b]`.
  have hg'MemLp : MemLp g' 2 (volume.restrict (Set.Ioo a b)) := by
    rw [hg'def, hcoordsymm]
    exact hg.comp_measurePreserving hmpr
  have hIooFinite : volume (Set.Ioo a b) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hIooFinite.lt_top⟩
  have hg'Integrable : Integrable g' (volume.restrict (Set.Ioo a b)) :=
    hg'MemLp.integrable (by norm_num)
  have hg'IntegrableOn : IntegrableOn g' (Set.Ioo a b) volume := hg'Integrable
  have hg'II : IntervalIntegrable g' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hg'IntegrableOn
  set G : ℝ → ℝ := fun x => ∫ t in a..x, g' t with hGdef
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    hg'II.absolutelyContinuousOnInterval_intervalIntegral (a := a) (b := b) (c := a)
      Set.left_mem_uIcc
  have hGaeDeriv : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt G (g' x) x := by
    filter_upwards [hg'II.ae_hasDerivAt_integral] with x hx
    intro hxmem
    exact hx hxmem a Set.left_mem_uIcc
  -- The weak-FTC step: `u'' - G` has weak derivative zero, tested against every bump on `(a, b)`.
  have hFTC : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo a b → ∫ t in a..b, (u'' t - G t) * deriv φ t = 0 := by
    exact integral_weak_deriv_minus_primitive c hr u g hu hwg hadef hbdef hab hcoordsymm' hmpr
      hGac hGaeDeriv
  -- Apply the du Bois-Reymond lemma to recover `u'' - G` as a constant a.e. on `(a, b)`.
  have hu''IntegrableOn : IntegrableOn u'' (Set.Ioo a b) volume := by
    rw [hu''def, hcoordsymm']
    exact hmpr.integrable_comp_of_integrable hu
  have hGcontOn : ContinuousOn G (Set.uIcc a b) := hGac.continuousOn
  have hGIntegrableOn : IntegrableOn G (Set.Ioo a b) volume := by
    apply (hGcontOn.mono ?_).integrableOn_compact isCompact_Icc |>.mono_set Set.Ioo_subset_Icc_self
    rw [Set.uIcc_of_le hab.le]
  obtain ⟨κ, hκ⟩ := ae_eq_const_of_forall_integral_mul_deriv_eq_zero hab
    (hu''IntegrableOn.sub hGIntegrableOn) hFTC
  set u' : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => G (x 0) + κ with hu'def
  refine ⟨u', ?_, ?_⟩
  · -- `u' =ᵐ u` on the ball.
    have hround : ∀ x : EuclideanSpace ℝ (Fin 1), (!₂[x 0] : EuclideanSpace ℝ (Fin 1)) = x := by
      intro x
      rw [← coordEquiv_symm_eq, ← coordEquiv_apply, coordEquiv.symm_apply_apply]
    have hmpr2 : MeasurePreserving (⇑coordEquiv) (volume.restrict (Metric.ball c r))
        (volume.restrict (Set.Ioo a b)) := MeasurePreserving.symm coordEquiv.symm hmpr
    have hcomp := hmpr2.quasiMeasurePreserving.ae_eq_comp hκ
    filter_upwards [hcomp] with x hx
    simp only [Function.comp_apply, Pi.sub_apply, coordEquiv_apply] at hx
    change G (x 0) + κ = u x
    have huround : u'' (x 0) = u x := by
      simp only [hu''def]
      rw [hround x]
    rw [huround] at hx
    linarith [hx]
  · -- Hölder continuity of the representative via Cauchy-Schwarz on the interval.
    set M : ℝ := (eLpNorm g 2 (volume.restrict (Metric.ball c r))).toReal with hMdef
    have hMnonneg : 0 ≤ M := ENNReal.toReal_nonneg
    have heLpfin : eLpNorm g 2 (volume.restrict (Metric.ball c r)) ≠ ⊤ := hg.eLpNorm_ne_top
    have heLp : eLpNorm g' 2 (volume.restrict (Set.Ioo a b))
        = eLpNorm g 2 (volume.restrict (Metric.ball c r)) := by
      rw [hg'def, hcoordsymm]
      exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hmpr
    -- `M² = ∫_{Ioo a b} (g')²`.
    have hM2 : M ^ 2 = ∫ t in Set.Ioo a b, (g' t) ^ 2 := by
      rw [hMdef, ← heLp, ← ENNReal.toReal_pow, eLpNorm_two_sq_eq_ofReal_integral_sq hg'MemLp,
        ENNReal.toReal_ofReal (integral_nonneg (fun t => sq_nonneg _))]
    -- Membership of `x 0` in the coordinate interval for `x ∈ ball c r`.
    have hmemcoord : ∀ z : EuclideanSpace ℝ (Fin 1), z ∈ Metric.ball c r → z 0 ∈ Set.Ioo a b := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_coord, abs_sub_lt_iff] at hz
      rw [hadef, hbdef, Set.mem_Ioo]
      constructor <;> [linarith [hz.2]; linarith [hz.1]]
    -- The pointwise Cauchy-Schwarz estimate.
    have hg'sq_int : IntegrableOn (fun t => (g' t) ^ 2) (Set.Ioo a b) volume :=
      hg'MemLp.integrable_sq
    have hnormsq : ∀ t : ℝ, ‖g' t‖ ^ (2 : ℝ) = (g' t) ^ 2 := by
      intro t
      rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        sq_abs]
    have hkey : ∀ x ∈ Metric.ball c r, ∀ y ∈ Metric.ball c r,
        |G (x 0) - G (y 0)| ≤ M * |x 0 - y 0| ^ (1 / 2 : ℝ) := by
      intro x hx y hy
      set p₀ : ℝ := y 0 with hp₀
      set q₀ : ℝ := x 0 with hq₀
      have hp₀mem : p₀ ∈ Set.Ioo a b := hmemcoord y hy
      have hq₀mem : q₀ ∈ Set.Ioo a b := hmemcoord x hx
      have hΙsub : Set.uIoc p₀ q₀ ⊆ Set.Ioo a b := by
        rw [Set.uIoc_eq_union]
        apply Set.union_subset
        · exact fun z hz => ⟨lt_trans hp₀mem.1 hz.1, lt_of_le_of_lt hz.2 hq₀mem.2⟩
        · exact fun z hz => ⟨lt_trans hq₀mem.1 hz.1, lt_of_le_of_lt hz.2 hp₀mem.2⟩
      have huicc_qp : Set.uIcc q₀ p₀ ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab.le]
        exact Set.uIcc_subset_Icc ⟨hq₀mem.1.le, hq₀mem.2.le⟩ ⟨hp₀mem.1.le, hp₀mem.2.le⟩
      have huicc_aq : Set.uIcc a q₀ ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab.le]
        exact Set.uIcc_subset_Icc ⟨le_rfl, hab.le⟩ ⟨hq₀mem.1.le, hq₀mem.2.le⟩
      have huicc_ap : Set.uIcc a p₀ ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab.le]
        exact Set.uIcc_subset_Icc ⟨le_rfl, hab.le⟩ ⟨hp₀mem.1.le, hp₀mem.2.le⟩
      have hII_aq : IntervalIntegrable g' volume a q₀ := hg'II.mono_set huicc_aq
      have hII_ap : IntervalIntegrable g' volume a p₀ := hg'II.mono_set huicc_ap
      -- Telescoping: `G q₀ - G p₀ = ∫ t in p₀..q₀, g' t`.
      have hGdiff : G q₀ - G p₀ = ∫ t in p₀..q₀, g' t := by
        change (∫ t in a..q₀, g' t) - (∫ t in a..p₀, g' t) = _
        exact intervalIntegral.integral_interval_sub_left hII_aq hII_ap
      -- Finite-measure instance on the sub-interval.
      have : IsFiniteMeasure (volume.restrict (Set.uIoc p₀ q₀)) :=
        ⟨by rw [Measure.restrict_apply_univ, Real.volume_uIoc]; exact ENNReal.ofReal_lt_top⟩
      -- Cauchy-Schwarz: `∫_{Ι} ‖g'‖ ≤ (∫_{Ι} (g')²)^½ · |q₀ - p₀|^½`.
      have hg'memΙ : MemLp g' (ENNReal.ofReal 2) (volume.restrict (Set.uIoc p₀ q₀)) := by
        rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) from by norm_num]
        exact hg'MemLp.mono_measure (Measure.restrict_mono hΙsub le_rfl)
      have hconstmemΙ : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2)
          (volume.restrict (Set.uIoc p₀ q₀)) := memLp_const 1
      have hCS := integral_mul_norm_le_Lp_mul_Lq
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hg'memΙ hconstmemΙ
      -- `∫_{Ι} ‖g'‖·‖1‖ = ∫_{Ι} ‖g'‖`, `∫_{Ι} ‖g'‖² = ∫_{Ι} (g')²`, `∫_{Ι} ‖1‖² = |q₀ - p₀|`.
      have e1 : ∫ a in Set.uIoc p₀ q₀, ‖g' a‖ * ‖(1 : ℝ)‖ = ∫ a in Set.uIoc p₀ q₀, ‖g' a‖ := by
        simp
      have e2 : ∫ a in Set.uIoc p₀ q₀, ‖g' a‖ ^ (2 : ℝ)
          = ∫ a in Set.uIoc p₀ q₀, (g' a) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t using hnormsq t
      have e3 : ∫ _a in Set.uIoc p₀ q₀, ‖(1 : ℝ)‖ ^ (2 : ℝ) = |q₀ - p₀| := by
        simp only [norm_one, Real.one_rpow]
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
          Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg _)]
      rw [e1, e2, e3] at hCS
      -- `∫_{Ι} (g')² ≤ ∫_{Ioo} (g')² = M²`.
      have hsubint : ∫ t in Set.uIoc p₀ q₀, (g' t) ^ 2 ≤ ∫ t in Set.Ioo a b, (g' t) ^ 2 := by
        apply setIntegral_mono_set hg'sq_int
          (Filter.Eventually.of_forall (fun t => sq_nonneg _))
        exact Filter.Eventually.of_forall hΙsub
      have hI1le : (∫ t in Set.uIoc p₀ q₀, (g' t) ^ 2) ^ (1 / 2 : ℝ) ≤ M := by
        calc (∫ t in Set.uIoc p₀ q₀, (g' t) ^ 2) ^ (1 / 2 : ℝ)
            ≤ (∫ t in Set.Ioo a b, (g' t) ^ 2) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (integral_nonneg (fun t => sq_nonneg _)) hsubint (by norm_num)
          _ = ((M ^ 2) ^ (1 / 2 : ℝ) : ℝ) := by rw [hM2]
          _ = M := by
              rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hMnonneg]
              norm_num
      -- Assemble.
      calc |G (x 0) - G (y 0)| = ‖∫ t in p₀..q₀, g' t‖ := by
              rw [hq₀, hp₀, hGdiff, Real.norm_eq_abs]
        _ ≤ ∫ t in Set.uIoc p₀ q₀, ‖g' t‖ :=
              intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ (∫ t in Set.uIoc p₀ q₀, (g' t) ^ 2) ^ (1 / 2 : ℝ) * |q₀ - p₀| ^ (1 / 2 : ℝ) := hCS
        _ ≤ M * |x 0 - y 0| ^ (1 / 2 : ℝ) := by
              have hpq_eq : |q₀ - p₀| = |x 0 - y 0| := by rw [hq₀, hp₀]
              rw [hpq_eq]
              exact mul_le_mul_of_nonneg_right hI1le (Real.rpow_nonneg (abs_nonneg _) _)
    -- Package into `HolderOnWith`.
    intro x hx y hy
    have hγ : ((morreyExponent 1 2 : ℝ≥0) : ℝ) = 1 / 2 := by
      rw [coe_morreyExponent (by norm_num) (by norm_num)]; norm_num
    have hkxy := hkey x hx y hy
    have hCcoe : ((1 * (eLpNorm g 2 (volume.restrict (Metric.ball c r))).toNNReal : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal M := by
      rw [one_mul, hMdef, ENNReal.ofReal_toReal heLpfin, ENNReal.coe_toNNReal heLpfin]
    have hu'diff : dist (u' x) (u' y) = |G (x 0) - G (y 0)| := by
      simp only [hu'def, Real.dist_eq]
      congr 1
      ring
    rw [edist_dist, edist_dist, hγ, hCcoe, hu'diff, dist_eq_coord,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2),
      ← ENNReal.ofReal_mul hMnonneg]
    exact ENNReal.ofReal_le_ofReal hkxy

end EllipticPdes.Embedding
