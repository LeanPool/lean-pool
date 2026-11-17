/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Mollification
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.SmoothBall
public import LeanPool.KLS.FunctionalInequalities.L2.Pairing

/-! # Weak products and compact local L2 data

Weak product rules: for globally `L²` factors (`HasWeakDerivAlong.mul_of_memLp_two`), bounded
factors with compact-local `L²` derivatives (`HasWeakDerivAlong.mul_of_locally_memLp_two`) and
locally essentially bounded factors (`HasWeakDerivAlong.mul_of_locally_bounded`); finite linear
combinations and Leibniz products; and multiplication by a compactly supported `C¹` cutoff
(`HasWeakDerivAlong.compact_mul_data`). It also provides the compact-local `L²` and local
integrability helpers shared with the other weak-calculus modules.

Supporting weak calculus for Letwin arXiv:2607.24164v1 and the
local elliptic estimates of Gilbarg--Trudinger (2001). Each declaration
retains its own support, integrability and dimensional hypotheses.
-/

@[expose] public section

section
open MeasureTheory
open scoped ContDiff

section WeakProducts

open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis


/-- Scalar weak product rule: global L2 factors and directional derivatives
produce a locally integrable product and its actual weak derivative. -/
theorem HasWeakDerivAlong.mul_of_memLp_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f df g dg : E → ℝ} {v : E} (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf2 : MemLp f 2 (volume : Measure E)) (hdf2 : MemLp df 2 (volume : Measure E))
    (hg2 : MemLp g 2 (volume : Measure E)) (hdg2 : MemLp dg 2 (volume : Measure E)) :
    HasWeakDerivAlong (fun x => f x * g x) (fun x => df x * g x + f x * dg x) v := by
  let φ : ℕ → ContDiffBump (0 : E) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hr : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let gm : ℕ → E → ℝ := fun m => (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  let dgm : ℕ → E → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] dg
  have hgm2 (m : ℕ) : MemLp (gm m) 2 (volume : Measure E) :=
    Mollification.memLp_convolution (φ m) hg2
  have hdgm2 (m : ℕ) : MemLp (dgm m) 2 (volume : Measure E) :=
    Mollification.memLp_convolution (φ m) hdg2
  have hgmconv : Tendsto (fun m => eLpNorm (gm m - g) 2 volume) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφ hg2
  have hdgmconv : Tendsto (fun m => eLpNorm (dgm m - dg) 2 volume) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφ hdg2
  have hgmC (m : ℕ) : ContDiff ℝ 1 (gm m) :=
    ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((φ m).contDiff_normed (n := 1)) hg.1
  have hgmder (m : ℕ) (x : E) : fderiv ℝ (gm m) x v = dgm m x :=
    fderiv_convolution_eq_of_hasWeakDerivAlong hg (φ m) x
  refine
    ⟨(hf2.integrable_mul hg2).locallyIntegrable,
      ((hdf2.integrable_mul hg2).add (hf2.integrable_mul hdg2)).locallyIntegrable, ?_⟩
  intro ψ hψ hψc
  have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
    change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have hψtop : MemLp ψ (⊤ : ℝ≥0∞) (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hψdtop : MemLp (fun x => fderiv ℝ ψ x v) (⊤ : ℝ≥0∞) (volume : Measure E) :=
    hψd.memLp_of_hasCompactSupport hψdc
  let a : E → ℝ := fun x => f x * fderiv ℝ ψ x v
  let b : E → ℝ := fun x => df x * ψ x
  let c : E → ℝ := fun x => f x * ψ x
  have ha : MemLp a 2 (volume : Measure E) := hf2.fun_mul hψdtop
  have hb : MemLp b 2 (volume : Measure E) := hdf2.fun_mul hψtop
  have hc : MemLp c 2 (volume : Measure E) := hf2.fun_mul hψtop
  have hid (m : ℕ) : (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) = -(∫ x, b x * gm m x) := by
    have hder (x : E) :
      fderiv ℝ (fun y => ψ y * gm m y) x v = ψ x * dgm m x + gm m x * fderiv ℝ ψ x v := by
      change (fderiv ℝ (ψ * gm m) x) v = _
      rw [fderiv_mul ((hψ.differentiable one_ne_zero).differentiableAt)
          (((hgmC m).differentiable one_ne_zero).differentiableAt)]
      simp only [add_apply, smul_apply, smul_eq_mul, hgmder]
    have hw := hf.2.2 (fun x => ψ x * gm m x) (hψ.mul (hgmC m)) hψc.mul_right
    calc
      (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) = ∫ x, a x * gm m x + c x * dgm m x :=
        (integral_add (ha.integrable_mul (hgm2 m)) (hc.integrable_mul (hdgm2 m))).symm
      _ = ∫ x, f x * fderiv ℝ (fun y => ψ y * gm m y) x v := by
        apply integral_congr_ae
        exact
          Filter.Eventually.of_forall fun x => by
            change a x * gm m x + c x * dgm m x = f x * fderiv ℝ (fun y => ψ y * gm m y) x v
            rw [hder]
            dsimp only [a, c]
            ring
      _ = -(∫ x, df x * (ψ x * gm m x)) := hw
      _ = -(∫ x, b x * gm m x) := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        exact
          Filter.Eventually.of_forall fun x => by
            dsimp only [b]
            ring
  have hA := FunctionalInequalities.L2.tendsto_integral_mul_of_eLpNorm_sub ha hg2 hgm2 hgmconv
  have hB := FunctionalInequalities.L2.tendsto_integral_mul_of_eLpNorm_sub hb hg2 hgm2 hgmconv
  have hC :=
    FunctionalInequalities.L2.tendsto_integral_mul_of_eLpNorm_sub hc hdg2 hdgm2 hdgmconv
  have hlim : (∫ x, a x * g x) + (∫ x, c x * dg x) = -(∫ x, b x * g x) :=
    tendsto_nhds_unique (hA.add hC) (Filter.Tendsto.congr (fun m => (hid m).symm) hB.neg)
  have hleft : (∫ x, (f x * g x) * fderiv ℝ ψ x v) = ∫ x, a x * g x := by
    apply integral_congr_ae
    exact
      Filter.Eventually.of_forall fun x => by
        dsimp only [a]
        ring
  have hright : (∫ x, (df x * g x + f x * dg x) * ψ x) = (∫ x, b x * g x) + (∫ x, c x * dg x) := by
    calc
      (∫ x, (df x * g x + f x * dg x) * ψ x) = ∫ x, b x * g x + c x * dg x := by
        apply integral_congr_ae
        exact
          Filter.Eventually.of_forall fun x => by
            dsimp only [b, c]
            ring
      _ = (∫ x, b x * g x) + (∫ x, c x * dg x) :=
        integral_add (hb.integrable_mul hg2) (hc.integrable_mul hdg2)
  rw [hleft, hright]
  linarith



/--
A continuous compactly supported cutoff times a function that is L2 on every compact set is globally
L2. -/
theorem memLp_mul_of_hasCompactSupport {n : ℕ} {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact S → MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    MemLp (fun x => χ x * f x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hKm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hind :
    MemLp ((tsupport χ).indicator f) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hKm.nullMeasurableSet).mpr (hf (tsupport χ) hχc)
  have hχlp : MemLp χ (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.memLp_of_hasCompactSupport hχc
  have hm :
    MemLp (fun x => χ x * ((tsupport χ).indicator f) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχlp.fun_mul hind
  convert hm using 1
  funext x
  by_cases hx : x ∈ tsupport χ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- Bounded weak factors with compact-local L2 derivatives have the actual
weak product derivative, which is itself L2 on every compact set. -/
theorem HasWeakDerivAlong.mul_of_locally_memLp_two {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf_top : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg_top : MemLp g (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hlocal :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => df x * g x + f x * dg x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    have hfirst : MemLp (fun x => df x * g x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      simpa only [mul_comm] using (hg_top.restrict S).fun_mul (hdf2 S hS)
    exact hfirst.add ((hf_top.restrict S).fun_mul (hdg2 S hS))
  have hproduct : MemLp (fun x => f x * g x) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hf_top.fun_mul hg_top
  have hdensity : LocallyIntegrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hlocal S hS).integrable (by norm_num)
  refine ⟨⟨hproduct.locallyIntegrable le_top, hdensity, ?_⟩, hlocal⟩
  intro ψ hψ hψc
  obtain ⟨R, hR⟩ := hψc.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := max R 0 + 1
      rOut := max R 0 + 2
      rIn_pos := by
        have hnonneg := le_max_right R 0
        linarith
      rIn_lt_rOut := by linarith }
  have hχ : ContDiff ℝ 1 (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.contDiff
  have hχc : HasCompactSupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.hasCompactSupport
  have hχon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v = 0 := by
    have hradius : R ≤ χ.rIn := by
      change R ≤ max R 0 + 1
      have hle := le_max_left R 0
      linarith
    have he := χ.eventuallyEq_one_of_mem_ball
      ((ball_subset_ball hradius) (hR hx))
    refine ⟨he.eq_of_nhds, ?_⟩
    simp [he.fderiv_eq]
  have hχ2 : MemLp (χ : EuclideanSpace ℝ (Fin n) → ℝ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.continuous.memLp_of_hasCompactSupport hχc
  have hχd : Continuous
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχdc : HasCompactSupport
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    hχc.fderiv_apply ℝ v
  have hχd2 : MemLp
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχd.memLp_of_hasCompactSupport hχdc
  have hχf2 : MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ2.fun_mul hf_top
  have hχg2 : MemLp (fun x => χ x * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ2.fun_mul hg_top
  have hχdf2 : MemLp
      (fun x => χ x * df x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdf2).add (hχd2.fun_mul hf_top)
  have hχdg2 : MemLp
      (fun x => χ x * dg x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdg2).add (hχd2.fun_mul hg_top)
  have hw := (hf.mul_contDiff hχ hχc).mul_of_memLp_two
    (hg.mul_contDiff hχ hχc) hχf2 hχdf2 hχg2 hχdg2
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (f x * g x) * fderiv ℝ ψ x v =
        ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v
      by_cases hx : x ∈ tsupport ψ
      · rw [(hχon x hx).1]
        simp only [one_mul]
      · rw [fderiv_of_notMem_tsupport ℝ hx]
        simp only [zero_apply, mul_zero]
  have hright :
      (∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) =
        ∫ x, (df x * g x + f x * dg x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x =
        (df x * g x + f x * dg x) * ψ x
      by_cases hx : x ∈ tsupport ψ
      · obtain ⟨hone, hzero⟩ := hχon x hx
        rw [hone, hzero]
        simp only [one_mul, zero_mul, add_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp only [mul_zero]
  calc
    (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := hleft
    _ = -(∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) :=
      hw.2.2 ψ hψ hψc
    _ = -(∫ x, (df x * g x + f x * dg x) * ψ x) :=
      congrArg Neg.neg hright


end FunctionalInequalities.Analysis

end WeakProducts

section WeakFinitePolynomials

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- Finite real linear combinations preserve the exact directional weak
derivative and its L2 membership on compact sets. -/
theorem hasWeakDerivAlong_finsetSum_mul {n : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℝ)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∑ i ∈ s, c i * f i x)
      (fun x => ∑ i ∈ s, c i * df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, c i * df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  have hcf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * f i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).1.smul (c i)
  have hcdf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * df i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).2.1.smul (c i)
  refine ⟨?_, ?_⟩
  · refine ⟨locallyIntegrable_finsetSum s hcf,
      locallyIntegrable_finsetSum s hcdf, ?_⟩
    intro ψ hψ hψc
    have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
      exact (hψc.fderiv ℝ).comp_left (by simp)
    have iF : ∀ i ∈ s,
        Integrable (fun x => (c i * f i x) * fderiv ℝ ψ x v)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcf i hi).integrable_smul_left_of_hasCompactSupport hψd hψdc
    have iG : ∀ i ∈ s,
        Integrable (fun x => (c i * df i x) * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcdf i hi).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    calc
      (∫ x, (∑ i ∈ s, c i * f i x) * fderiv ℝ ψ x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ i ∈ s, ∫ x, (c i * f i x) * fderiv ℝ ψ x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iF
      _ = ∑ i ∈ s, -(∫ x, (c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mul_assoc, integral_const_mul,
          (hf i hi).2.2 ψ hψ hψc, mul_neg]
      _ = -(∫ x, (∑ i ∈ s, c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        symm
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iG
  · intro S hS
    exact memLp_finsetSum s (fun i hi => (hdf2 i hi S hS).const_mul (c i))


/-- Finite bounded weak factors with compact-local L2 directional derivatives
have the Leibniz weak derivative, including the empty product. -/
theorem hasWeakDerivAlong_finsetProd_of_locally_memLp_two {n : ℕ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hbound : ∀ i ∈ s, MemLp (f i) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∏ i ∈ s, f i x)
      (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  revert hf hbound hdf2
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      simp only [Finset.prod_empty, Finset.sum_empty]
      constructor
      · simpa using
          (hasWeakDerivAlong_of_contDiff
            (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
            contDiff_const v)
      · intro S _
        exact MemLp.zero
  | @insert i t hi ih =>
      intro hf hbound hdf2
      have hrest := ih
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hbound j (Finset.mem_insert_of_mem hj))
        (fun j hj => hdf2 j (Finset.mem_insert_of_mem hj))
      have hrest_top :
          MemLp (fun x => ∏ j ∈ t, f j x) (⊤ : ENNReal)
            (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simpa only [ENNReal.inv_top, Finset.sum_const_zero, ENNReal.inv_zero] using
          (MemLp.fun_prod (p := fun _ : ι => (⊤ : ENNReal))
            (fun j hj => hbound j (Finset.mem_insert_of_mem hj)))
      have hbinary :=
        (hf i (Finset.mem_insert_self i t)).mul_of_locally_memLp_two
          hrest.1
          (hbound i (Finset.mem_insert_self i t))
          hrest_top
          (hdf2 i (Finset.mem_insert_self i t))
          hrest.2
      have hprod :
          (fun x => ∏ j ∈ insert i t, f j x) =
            (fun x => f i x * ∏ j ∈ t, f j x) := by
        funext x
        exact Finset.prod_insert hi
      have hsum :
          (fun x => ∑ j ∈ insert i t, df j x * ∏ k ∈ (insert i t).erase j, f k x) =
            (fun x => df i x * (∏ j ∈ t, f j x) +
              f i x * ∑ j ∈ t, df j x * ∏ k ∈ t.erase j, f k x) := by
        funext x
        rw [Finset.sum_insert hi, Finset.erase_insert hi, Finset.mul_sum]
        apply congrArg (fun r : ℝ => df i x * (∏ j ∈ t, f j x) + r)
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := by
          intro h
          subst j
          exact hi hj
        have hiErase : i ∉ t.erase j := by
          intro h
          exact hi (Finset.mem_of_mem_erase h)
        rw [Finset.erase_insert_of_ne hij, Finset.prod_insert hiErase]
        exact mul_left_comm _ _ _
      rw [hprod, hsum]
      exact hbinary


end FunctionalInequalities.Analysis

end WeakFinitePolynomials

section WeakLocalBoundedProducts
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

/-- Locally essentially bounded weak factors have their actual directional
product derivative, locally L2. No global bound or C1/C2 regularity is assumed. -/
theorem HasWeakDerivAlong.mul_of_locally_bounded {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf_top : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg_top : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hf2 :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf_top S hS).mono_exponent le_top
  have hg2 :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hg_top S hS).mono_exponent le_top
  have hlocal :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => df x * g x + f x * dg x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    have hfirst : MemLp (fun x => df x * g x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      simpa only [mul_comm] using (hg_top S hS).fun_mul (hdf2 S hS)
    exact hfirst.add ((hf_top S hS).fun_mul (hdg2 S hS))
  have hproduct : LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    have hp : MemLp (fun x => f x * g x) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      (hf_top S hS).fun_mul (hg_top S hS)
    exact hp.integrable le_top
  have hdensity : LocallyIntegrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hlocal S hS).integrable (by norm_num)
  refine ⟨⟨hproduct, hdensity, ?_⟩, hlocal⟩
  intro ψ hψ hψc
  obtain ⟨χ, hχ, hχc, hχnear⟩ := exists_compact_contDiff_eq_one_near hψc
  have hχon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ χ x v = 0 := by
    have he := hχnear x hx
    refine ⟨he.eq_of_nhds, ?_⟩
    rw [he.fderiv_eq]
    simp
  have hcut_top
      (a : EuclideanSpace ℝ (Fin n) → ℝ)
      (ha : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp a (⊤ : ENNReal)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
      MemLp (fun x => χ x * a x) (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    classical
    have hKm : MeasurableSet (tsupport χ) :=
      (isClosed_tsupport χ).measurableSet
    have hind : MemLp ((tsupport χ).indicator a) (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (memLp_indicator_iff_restrict hKm.nullMeasurableSet).mpr (ha (tsupport χ) hχc)
    have hχlp : MemLp χ (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hχ.continuous.memLp_of_hasCompactSupport hχc
    have hm : MemLp (fun x => χ x * ((tsupport χ).indicator a) x)
        (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hχlp.fun_mul hind
    convert hm using 1
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
        zero_mul, zero_mul]
  have hχd : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => fderiv ℝ χ x v) :=
    hχc.fderiv_apply ℝ v
  have hχdf2 : MemLp
      (fun x => χ x * df x + fderiv ℝ χ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdf2).add
      (memLp_mul_of_hasCompactSupport hχd hχdc hf2)
  have hχdg2 : MemLp
      (fun x => χ x * dg x + fderiv ℝ χ x v * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdg2).add
      (memLp_mul_of_hasCompactSupport hχd hχdc hg2)
  have hw := (hf.mul_contDiff hχ hχc).mul_of_locally_memLp_two
    (hg.mul_contDiff hχ hχc) (hcut_top f hf_top) (hcut_top g hg_top)
    (fun S _ => hχdf2.restrict S) (fun S _ => hχdg2.restrict S)
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (f x * g x) * fderiv ℝ ψ x v =
        ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v
      by_cases hx : x ∈ tsupport ψ
      · rw [(hχon x hx).1]
        simp only [one_mul]
      · rw [fderiv_of_notMem_tsupport ℝ hx, zero_apply]
        simp only [mul_zero]
  have hright :
      (∫ x, ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x) =
        ∫ x, (df x * g x + f x * dg x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x =
        (df x * g x + f x * dg x) * ψ x
      by_cases hx : x ∈ tsupport ψ
      · obtain ⟨hone, hzero⟩ := hχon x hx
        rw [hone, hzero]
        simp only [one_mul, zero_mul, add_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp only [mul_zero]
  calc
    (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := hleft
    _ = -(∫ x, ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x) :=
      hw.1.2.2 ψ hψ hψc
    _ = -(∫ x, (df x * g x + f x * dg x) * ψ x) :=
      congrArg Neg.neg hright
end FunctionalInequalities.Analysis
end WeakLocalBoundedProducts

section SharedCompactLocalTools

open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis

/-- A continuous function is essentially bounded on every compact set. -/
theorem memLp_top_restrict_of_continuous {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx

/-- The product of two functions that are L2 on every compact set is locally integrable. -/
theorem locallyIntegrable_mul_of_compact_L2 {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  exact (hf S hS).integrable_mul (hg S hS)

/-- A function that is L2 on every compact set is locally integrable. -/
theorem locallyIntegrable_of_compact_local_memLp_two {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (hf S hS).integrable (by norm_num)

/--
Multiplying a weak derivative pair `(f, df)` along `v` by a compactly supported C1 function `ψ`,
with `df` L2 and
`f` essentially bounded on compact sets, gives the weak derivative of `ψ f`, compact supports and a
globally L2 derivative. -/
theorem HasWeakDerivAlong.compact_mul_data {n : ℕ} {f df : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)} (h : HasWeakDerivAlong f df v)
    (hdf :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact S → MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact S →
          MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    HasWeakDerivAlong (fun x => ψ x * f x) (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) v ∧
      HasCompactSupport (fun x => ψ x * f x) ∧
        HasCompactSupport (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) ∧
          MemLp (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := hψc.fderiv_apply ℝ v
  have hf2 :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S → MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf S hS).mono_exponent le_top
  refine ⟨h.mul_contDiff hψ hψc, hψc.mul_right, ?_, ?_⟩
  · exact hψc.mul_right.add hdψc.mul_right
  · exact
      (memLp_mul_of_hasCompactSupport hψ.continuous hψc hdf).add
        (memLp_mul_of_hasCompactSupport hdψ hdψc hf2)

end FunctionalInequalities.Analysis

end SharedCompactLocalTools
