/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.CDFactorGrad
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedFinal
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitEigenFrame

/-! # `CDFactor`, part 2: the generator commutes with `π`, and `CD(ρ)` on the level

Under the factorization hypothesis `μ.map Φ = ν ⊗ μ'` (`hfact`, proved by workstream `measure`),
integration by parts on `M` and on `N` with test functions `χ(s) · g(π)` shows
`𝓛_M (v' ∘ π) = (𝓛_N v') ∘ π`; together with `Γ_M(u'∘π, w'∘π) = Γ_N(u',w')∘π` this transfers
`CD(ρ)` from `M` to `N`.  No comparison of the Levi-Civita connections is needed.
-/

@[expose] public section

open Bundle MeasureTheory Set Filter Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

open CutoffRigidity CutoffRigidity.Riemann

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] [MeasurableSpace M] [BorelSpace M]
  {k : ℕ} (fr : Frame F M k)

omit [MeasurableSpace F] [BorelSpace F] in
/-- The factorization of integrals of `χ(s) h(π)` through `μ.map Φ = ν ⊗ μ'`. -/
theorem integral_sv_mul_toLevel {μ : Measure M} {ν : Measure (Rd k)}
    [SFinite ν] {μ' : Measure fr.Level} [SFinite μ']
    (hfact : μ.map fr.splitEquiv = ν.prod μ')
    {χ : Rd k → ℝ} (hχ : Continuous χ)
    {h : fr.Level → ℝ} (hh : Continuous h) :
    ∫ x, χ (fr.sv x) * h (fr.toLevel x) ∂μ = (∫ t, χ t ∂ν) * ∫ y, h y ∂μ' := by
  have hΦ : Measurable fr.splitEquiv :=
    (fr.contMDiff_sv.continuous.measurable).prodMk fr.contMDiff_toLevel.continuous.measurable
  have hG : Measurable (fun p : Rd k × fr.Level => χ p.1 * h p.2) :=
    (hχ.measurable.comp measurable_fst).mul (hh.measurable.comp measurable_snd)
  have h1 : ∫ x, χ (fr.sv x) * h (fr.toLevel x) ∂μ =
      ∫ p, χ p.1 * h p.2 ∂(μ.map fr.splitEquiv) := by
    rw [integral_map hΦ.aemeasurable hG.aestronglyMeasurable]
    rfl
  rw [h1, hfact, integral_prod_mul]


omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M] in
theorem hasCompactSupport_sv_mul_toLevel {χ : Rd k → ℝ} {g : fr.Level → ℝ}
    (hχc : HasCompactSupport χ) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun x => χ (fr.sv x) * g (fr.toLevel x)) := by
  have hK : IsCompact (fr.splitEquiv.symm '' (tsupport χ ×ˢ tsupport g)) :=
    (hχc.isCompact.prod hgc.isCompact).image fr.splitEquiv.symm.continuous
  apply HasCompactSupport.intro hK
  intro x hx
  by_contra hne
  apply hx
  exact ⟨fr.splitEquiv x, ⟨subset_tsupport _ (left_ne_zero_of_mul hne),
    subset_tsupport _ (right_ne_zero_of_mul hne)⟩, fr.splitEquiv.symm_apply_apply x⟩

omit [MeasurableSpace F] [BorelSpace F] in
/-- A continuous function orthogonal (for `μ`) to all test functions `χ(s) g(π)` is `≤ 0`
at every point (positive part). -/
theorem nonpos_of_integral_test {μ : Measure M} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {D : M → ℝ} (hD : Continuous D)
    (h : ∀ (χ : Rd k → ℝ) (g : fr.Level → ℝ), ContDiff ℝ ∞ χ →
      HasCompactSupport χ →
      ContMDiff 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, ℝ) ∞ g → HasCompactSupport g →
      (∀ t, 0 ≤ χ t) → (∀ y, 0 ≤ g y) →
      ∫ x, χ (fr.sv x) * g (fr.toLevel x) * D x ∂μ = 0) (x₀ : M) : D x₀ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set Φ := fr.splitEquiv with hΦ
  have hU : IsOpen {x | 0 < D x} := isOpen_lt continuous_const hD
  have hW : (Φ.symm ⁻¹' {x | 0 < D x}) ∈ nhds (Φ x₀) := by
    apply Φ.symm.continuous.continuousAt.preimage_mem_nhds
    rw [Φ.symm_apply_apply]
    exact hU.mem_nhds hpos
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨f, -, hf⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, Rd k))
    (Φ x₀).1).mem_iff.mp hu
  obtain ⟨g, -, hg⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := 𝓘(ℝ, LevelModel F (Rd k))) (Φ x₀).2).mem_iff.mp hv
  have hχd : ContDiff ℝ ∞ (f : Rd k → ℝ) := contMDiff_iff_contDiff.mp
      f.contMDiff
  set φ : M → ℝ := fun x => f (fr.sv x) * g (fr.toLevel x) with hφ
  have hφc : Continuous φ :=
    (hχd.continuous.comp fr.contMDiff_sv.continuous).mul
      (g.contMDiff.continuous.comp fr.contMDiff_toLevel.continuous)
  have hΦx : ∀ x, Φ x = (fr.sv x, fr.toLevel x) := fun x => rfl
  have hφU : ∀ x, φ x ≠ 0 → 0 < D x := by
    intro x hx
    have h1 : f (fr.sv x) ≠ 0 := left_ne_zero_of_mul hx
    have h2 : g (fr.toLevel x) ≠ 0 := right_ne_zero_of_mul hx
    have h3 : fr.sv x ∈ u := hf (subset_tsupport _ h1)
    have h4 : fr.toLevel x ∈ v := hg (subset_tsupport _ h2)
    have h5 : Φ x ∈ Φ.symm ⁻¹' {x | 0 < D x} := huv ⟨by rw [hΦx]; exact h3, by rw [hΦx]; exact h4⟩
    simpa using h5
  have hφnn : ∀ x, 0 ≤ φ x := fun x => mul_nonneg f.nonneg g.nonneg
  have hnn : ∀ x, 0 ≤ φ x * D x := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    · exact mul_nonneg (hφnn x) (hφU x hx).le
  have hK : IsCompact (Φ.symm '' (tsupport f ×ˢ tsupport g)) :=
    (f.hasCompactSupport.isCompact.prod g.hasCompactSupport.isCompact).image Φ.symm.continuous
  have hφcs : HasCompactSupport φ := by
    apply HasCompactSupport.intro hK
    intro x hx
    by_contra hne
    apply hx
    refine ⟨Φ x, ⟨subset_tsupport _ (left_ne_zero_of_mul hne),
      subset_tsupport _ (right_ne_zero_of_mul hne)⟩, Φ.symm_apply_apply x⟩
  have hint := h f g hχd f.hasCompactSupport g.contMDiff g.hasCompactSupport
    (fun t => f.nonneg) (fun y => g.nonneg)
  have hpos2 : 0 < ∫ x, φ x * D x ∂μ := by
    refine (hφc.mul hD).integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := x₀)
      (hφcs.mul_right) hnn ?_
    have : φ x₀ = 1 := by
      simp only [hφ]
      have e1 : f (fr.sv x₀) = 1 := f.eq_one
      have e2 : g (fr.toLevel x₀) = 1 := g.eq_one
      rw [e1, e2, one_mul]
    rw [this, one_mul]
    exact hpos.ne'
  exact hpos2.ne' hint


/-- **(I2)** The generator commutes with `π`: `𝓛_M (v' ∘ π) = (𝓛_N v') ∘ π`, given the
factorization `μ.map Φ = ν ⊗ μ'` of the weighted measure. -/
theorem mgenerator_comp_toLevel {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
    [IsFiniteMeasure μ] (hμ : IsWeightedVolume F μ V)
    {ν : Measure (Rd k)} [SFinite ν]
    {μ' : Measure fr.Level} [IsFiniteMeasure μ']
    {V' : fr.Level → ℝ} (hV' : MSmooth (LevelModel F (Rd k)) V')
    (hμ' : IsWeightedVolume (LevelModel F (Rd k)) μ' V')
    (hfact : μ.map fr.splitEquiv = ν.prod μ')
    {v' : fr.Level → ℝ} (hv' : MSmooth (LevelModel F (Rd k)) v') (x : M) :
    mgenerator F V (fun z => v' (fr.toLevel z)) x =
      mgenerator (LevelModel F (Rd k)) V' v' (fr.toLevel x) := by
  have : μ.IsOpenPosMeasure :=
    ⟨fun U hU hne => (measure_pos_of_isWeightedVolume F hV hμ (continuousOn_chartVolumeDensity F)
      (fun x₀ z hz => chartVolumeDensity_pos F x₀ hz) hU hne).ne'⟩
  have hRM := weightedRegular (F := F) V hV
  have hRN := weightedRegular (F := LevelModel F (Rd k)) V' hV'
  have hu : MSmooth F (fun z => v' (fr.toLevel z)) := hv'.comp fr.contMDiff_toLevel
  have hA : Continuous (mgenerator F V (fun z => v' (fr.toLevel z))) := (hRM.2.1 _ hu).continuous
  have hB : Continuous (mgenerator (LevelModel F (Rd k)) V' v') :=
    (hRN.2.1 _ hv').continuous
  have hD : Continuous (fun x => mgenerator F V (fun z => v' (fr.toLevel z)) x -
      mgenerator (LevelModel F (Rd k)) V' v' (fr.toLevel x)) :=
    hA.sub (hB.comp fr.contMDiff_toLevel.continuous)
  have htest : ∀ (χ : Rd k → ℝ) (g : fr.Level → ℝ), ContDiff ℝ ∞ χ →
      HasCompactSupport χ →
      ContMDiff 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, ℝ) ∞ g → HasCompactSupport g →
      ∫ x, χ (fr.sv x) * g (fr.toLevel x) * (mgenerator F V (fun z => v' (fr.toLevel z)) x -
      mgenerator (LevelModel F (Rd k)) V' v' (fr.toLevel x)) ∂μ = 0 := by
    intro χ g hχ hχc hg hgc
    set u : M → ℝ := fun z => v' (fr.toLevel z) with hu_def
    have ha : MSmooth F (fun z => χ (fr.sv z)) := hχ.contMDiff.comp fr.contMDiff_sv
    have hb : MSmooth F (fun z => g (fr.toLevel z)) := hg.comp fr.contMDiff_toLevel
    have hφs : MSmooth F ((fun z => χ (fr.sv z)) * (fun z => g (fr.toLevel z))) := ha.mul hb
    have hcs := fr.hasCompactSupport_sv_mul_toLevel hχc hgc
    have hIBP := weightedIBP_of_isWeightedVolume F hV hμ
      ((fun z => χ (fr.sv z)) * (fun z => g (fr.toLevel z))) u hφs hu hcs
    have hIBPN := weightedIBP_of_isWeightedVolume (LevelModel F (Rd k)) hV' hμ'
      g v' hg hv' hgc
    have hcar : ∀ x, carre F ((fun z => χ (fr.sv z)) * (fun z => g (fr.toLevel z))) u x =
        χ (fr.sv x) * carre (LevelModel F (Rd k)) g v' (fr.toLevel x) := by
      intro x
      rw [carre_mul_left F ha hb x, fr.carre_comp_toLevel hg hv' x,
        fr.carre_sv_comp_toLevel hv' hχ x]
      simp
    have hgc' : Continuous g := hg.continuous
    have hχc' : Continuous χ := hχ.continuous
    have hCN : Continuous (carre (LevelModel F (Rd k)) g v') :=
      (hRN.1 g v' hg hv').continuous
    have e1 : ∫ x, carre F ((fun z => χ (fr.sv z)) * (fun z => g (fr.toLevel z))) u x ∂μ =
        (∫ t, χ t ∂ν) * ∫ y, carre (LevelModel F (Rd k)) g v' y ∂μ' := by
      simp_rw [hcar]
      exact fr.integral_sv_mul_toLevel hfact hχc' hCN
    have e2 : ∫ x, χ (fr.sv x) * (g (fr.toLevel x) *
        mgenerator (LevelModel F (Rd k)) V' v' (fr.toLevel x)) ∂μ =
        (∫ t, χ t ∂ν) * ∫ y, g y * mgenerator (LevelModel F (Rd k)) V' v' y
            ∂μ' :=
      fr.integral_sv_mul_toLevel hfact hχc' (h := fun y => g y *
        mgenerator (LevelModel F (Rd k)) V' v' y) (hgc'.mul hB)
    have hint1 : Integrable (fun x => χ (fr.sv x) * g (fr.toLevel x) * mgenerator F V u x) μ := by
      refine Continuous.integrable_of_hasCompactSupport ?_ hcs.mul_right
      exact ((hχc'.comp fr.contMDiff_sv.continuous).mul
        (hgc'.comp fr.contMDiff_toLevel.continuous)).mul hA
    have hint2 : Integrable (fun x => χ (fr.sv x) * g (fr.toLevel x) *
        mgenerator (LevelModel F (Rd k)) V' v' (fr.toLevel x)) μ := by
      refine Continuous.integrable_of_hasCompactSupport ?_ hcs.mul_right
      exact ((hχc'.comp fr.contMDiff_sv.continuous).mul
        (hgc'.comp fr.contMDiff_toLevel.continuous)).mul
        (hB.comp fr.contMDiff_toLevel.continuous)
    simp_rw [mul_sub]
    rw [integral_sub hint1 hint2]
    have e3 : ∫ x, χ (fr.sv x) * g (fr.toLevel x) * mgenerator F V u x ∂μ =
        -∫ x, carre F ((fun z => χ (fr.sv z)) * (fun z => g (fr.toLevel z))) u x ∂μ := by
      rw [hIBP]; simp [Pi.mul_apply]
    have e4 : ∫ x, χ (fr.sv x) * g (fr.toLevel x) *
        mgenerator (LevelModel F (Rd k)) V' v' (fr.toLevel x) ∂μ =
        (∫ t, χ t ∂ν) * ∫ y, g y * mgenerator (LevelModel F (Rd k)) V' v' y
            ∂μ' := by
      rw [← e2]; simp_rw [mul_assoc]
    rw [e3, e4, e1, hIBPN]
    ring
  have hz : ∀ D : M → ℝ, Continuous D → (∀ χ g, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ContMDiff 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, ℝ) ∞ g → HasCompactSupport g →
      ∫ x, χ (fr.sv x) * g (fr.toLevel x) * D x ∂μ = 0) → ∀ x, D x = 0 := by
    intro D hDc hDt x
    refine le_antisymm (fr.nonpos_of_integral_test (μ := μ) hDc (fun χ g a b c d _ _ => hDt χ g a
        b c d) x) ?_
    have := fr.nonpos_of_integral_test (μ := μ) hDc.neg (fun χ g a b c d _ _ => by
      simp only [Pi.neg_apply, mul_neg, integral_neg, hDt χ g a b c d, neg_zero]) x
    have h2 : -D x ≤ 0 := this
    linarith
  have := hz _ hD htest x
  linarith


/-- **(S9)** `CD(ρ)` descends to the level `N = {s = 0}` with the potential `V'` and measure `μ'`
of the factorization `μ.map Φ = ν ⊗ μ'`. -/
theorem cd_level {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
    [IsFiniteMeasure μ] (hμ : IsWeightedVolume F μ V)
    {ν : Measure (Rd k)} [SFinite ν]
    {μ' : Measure fr.Level} [IsFiniteMeasure μ']
    {V' : fr.Level → ℝ} (hV' : MSmooth (LevelModel F (Rd k)) V')
    (hμ' : IsWeightedVolume (LevelModel F (Rd k)) μ' V')
    (hfact : μ.map fr.splitEquiv = ν.prod μ') {ρ : ℝ} (hCD : CD F ρ V) :
    CD (LevelModel F (Rd k)) ρ V' := by
  intro f' hf' y
  have hRN := weightedRegular (F := LevelModel F (Rd k)) V' hV'
  have hu : MSmooth F (fun z => f' (fr.toLevel z)) := hf'.comp fr.contMDiff_toLevel
  have h := hCD _ hu y.val
  have hπ : fr.toLevel y.val = y := fr.toLevel_val y
  have hc : ∀ x, carre F (fun z => f' (fr.toLevel z)) (fun z => f' (fr.toLevel z)) x =
      carre (LevelModel F (Rd k)) f' f' (fr.toLevel x) :=
    fun x => fr.carre_comp_toLevel hf' hf' x
  have hL : ∀ x, mgenerator F V (fun z => f' (fr.toLevel z)) x =
      mgenerator (LevelModel F (Rd k)) V' f' (fr.toLevel x) :=
    fun x => fr.mgenerator_comp_toLevel hV hμ hV' hμ' hfact hf' x
  have hcfun : carre F (fun z => f' (fr.toLevel z)) (fun z => f' (fr.toLevel z)) =
      fun z => carre (LevelModel F (Rd k)) f' f' (fr.toLevel z) := funext hc
  have hLfun : mgenerator F V (fun z => f' (fr.toLevel z)) =
      fun z => mgenerator (LevelModel F (Rd k)) V' f' (fr.toLevel z) :=
    funext hL
  have h2 : carre2 F V (fun z => f' (fr.toLevel z)) y.val =
      carre2 (LevelModel F (Rd k)) V' f' y := by
    unfold carre2
    rw [hcfun, hLfun, fr.mgenerator_comp_toLevel hV hμ hV' hμ' hfact (hRN.1 f' f' hf' hf'),
      fr.carre_comp_toLevel hf' (hRN.2.1 f' hf'), hπ]
  rw [h2, hc, hπ] at h
  exact h

end Frame

end CutCur
