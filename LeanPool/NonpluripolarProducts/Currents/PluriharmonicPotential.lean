/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.BookCurrentProducts
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentL1Ddc
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ActualZeroLeviDistributionSmoothness
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-!
# Weyl's lemma for `dd^c`: two psh potentials of the same current differ by a pluriharmonic
    function

Source: `chapter_npp.tex`, `prop:npp1` (2) ("depend only on the currents `dd^c φ_j`") and the
remark after `def:npp:L146` ("independent of the choices … thanks to (1) and (2)"); Xia,
*Foundations of pluripotential theory*, proof of `prop:nonpluripolar-local-calculus`
("Dependence on the currents `dd^c u_j`": the distribution `v_j - u_j` has zero Laplacian, so by
Weyl's lemma `thm:weyl` it is a smooth function `w_j`, its complex Hessian vanishes, and
`v_j = u_j + w_j` everywhere since both sides are psh and agree almost everywhere,
`thm:psh-distribution-representative`).

Let `U ⊆ ℂ^{m+1}` be open and let `u, v` be psh on `U` and locally integrable (TN's
`LocalCurrentL1Ddc.IsL1PshOn`: psh and `≢ -∞` near every point).  The currents `dd^c u` and
`dd^c v` are TN's `ddcL1 U u = dd^c(u [1])`.

* `l1Current_eq_scalarTopCurrent` — `u [1]` is the top current of the regular distribution of `u`.
* `smoothDDC_eq_zero_of_leviForm_eq_zero` — a `C²` function whose Levi form vanishes at `z` has
  `dd^c f (z) = 0` (polarization of the Hermitian form).
* `eq_zero_of_positiveDistribution_of_neg` — a distribution `D` with `D ≥ 0` and `-D ≥ 0` is `0`.
* `exists_local_pluriharmonic_of_ddcL1_eq` — **Weyl's lemma for `dd^c`, local form**: if
  `dd^c u = dd^c v` then every point of `U` has a neighbourhood `W` and a smooth `f` with
  `dd^c f = 0` on `W` and `v = u + f` *everywhere* on `W`.  The smoothness of the zero-Levi
  distribution `v - u` is TN's `exists_smooth_local_representative_of_zero_levi` (mollification
  with an adapted radial kernel, which is the proof of Weyl's lemma); its hypothesis (all
  directional Levi distributions of `v - u` vanish) is derived from `dd^c(v - u) = 0` through the
  `β`-product test `SGPT.PSH.BookCurrent.hasNonnegativeDistributionalLevi_of_betaProduct_pairings`,
  applied to `v - u` and `u - v`.
* `exists_pluriharmonic_of_ddcL1_eq` — **global form**: `v = u + h` on all of `U` for a function
  `h` smooth on `U` with `dd^c h = 0` on `U` (the local functions agree on overlaps because
  `u > -∞` almost everywhere, and glue).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Currents

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc

/-! ### Linear algebra: vanishing Levi form -/

section Levi

variable {n : ℕ}

/-- **A vanishing Levi form forces `dd^c f = 0`**: if `f` is `C²` at `z` and
`L_f(z)(v) = 0` for every `v`, then the real `(1,1)`-form `dd^c f (z)` vanishes (polarization:
`D²f(v,w) = -D²f(iv,iw)`). -/
theorem smoothDDC_eq_zero_of_leviForm_eq_zero {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (h : ∀ v, leviForm f z v = 0) : smoothDDC f z = 0 := by
  set H := fderiv ℝ (fderiv ℝ f) z with hH
  have hsymm : ∀ v w, H v w = H w v := fun v w =>
    hf.isSymmSndFDerivAt (by simp) v w
  have hQ : ∀ v, H v v + H (Complex.I • v) (Complex.I • v) = 0 := by
    intro v
    have := h v
    simp only [leviForm, realHessian_eq_fderiv] at this
    rw [← hH] at this
    linarith
  have hpol : ∀ v w, H v w = -H (Complex.I • v) (Complex.I • w) := by
    intro v w
    have h1 := hQ (v + w)
    have h2 := hQ v
    have h3 := hQ w
    simp only [smul_add, map_add, _root_.add_apply] at h1
    rw [hsymm w v, hsymm (Complex.I • w) (Complex.I • v)] at h1
    linarith
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, smoothDDC_apply_eq_realHessian hf]
  simp only [realHessian_eq_fderiv, ← hH]
  have e : H (v 1) (Complex.I • v 0) = H (v 0) (Complex.I • v 1) := by
    rw [hpol (v 1) (Complex.I • v 0), smul_smul, Complex.I_mul_I, neg_one_smul]
    simp only [map_neg, neg_neg]
    exact hsymm _ _
  rw [e, sub_self, zero_div]
  rfl

end Levi

/-! ### Positive distributions -/

section Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

/-- **A distribution that is positive together with its negative is zero.** -/
theorem eq_zero_of_positiveDistribution_of_neg {D : 𝓓'(Ω, ℝ)} (hD : PositiveDistribution D)
    (hD' : PositiveDistribution (-D)) : D = 0 := by
  have hzero : ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → D ψ = 0 := fun ψ hψ =>
    le_antisymm (by simpa using hD' ψ hψ) (hD ψ hψ)
  ext φ
  obtain ⟨χ, hχ1, hχ⟩ := exists_testFunction_eq_one_nhds_compact φ.hasCompactSupport
    φ.tsupport_subset
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h1 : ∀ x, 0 ≤ (C • χ) x := fun x => by
    simpa using mul_nonneg hC0 (hχ x).1
  have h2 : ∀ x, 0 ≤ (C • χ + φ) x := by
    intro x
    change 0 ≤ C * χ x + φ x
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1.self_of_nhdsSet x hx), mul_one]
      have := hC x
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (φ x)]
    · rw [image_eq_zero_of_notMem_tsupport hx, add_zero]
      exact mul_nonneg hC0 (hχ x).1
  have e := hzero _ h2
  rw [map_add, hzero _ h1, zero_add] at e
  simpa using e

end Distribution

/-! ### The current `u [1]` as a scalar top current -/

section Current

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- `u [1]` is the top current of the regular distribution of `u`. -/
theorem l1Current_eq_scalarTopCurrent {u : ComplexModel n → EReal}
    (h : LocallyIntegrableOn (fun x => (u x).toReal) U volume) :
    l1Current U u = scalarTopCurrent (regularDistribution volume (fun x => (u x).toReal) h) := by
  ext γ φ
  rw [l1Current_apply h, scalarTopCurrent_apply, regularDistribution_apply]

theorem scalarTopCurrent_sub (S T : 𝓓'(U, ℝ)) :
    scalarTopCurrent (S - T) = scalarTopCurrent S - scalarTopCurrent T := by
  ext γ φ
  simp only [scalarTopCurrent_apply, LinearMap.sub_apply, _root_.sub_apply, mul_sub]

theorem scalarTopCurrent_neg (S : 𝓓'(U, ℝ)) : scalarTopCurrent (-S) = -scalarTopCurrent S := by
  ext γ φ
  simp only [scalarTopCurrent_apply, LinearMap.neg_apply, _root_.neg_apply, mul_neg]

theorem ddc_sub {q : ℕ} (S T : LocalProductCurrent n U (q + 1)) : ddc (S - T) = ddc S - ddc T := by
  rw [sub_eq_add_neg, ddc_add, ← neg_one_smul ℝ T, ddc_smul, neg_one_smul, ← sub_eq_add_neg]

theorem ddc_neg {q : ℕ} (S : LocalProductCurrent n U (q + 1)) : ddc (-S) = -ddc S := by
  rw [← neg_one_smul ℝ S, ddc_smul, neg_one_smul]

theorem regularDistribution_sub {f g : ComplexModel n → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hg : LocallyIntegrableOn g U volume) :
    regularDistribution volume f hf - regularDistribution volume g hg =
      regularDistribution volume (fun x => f x - g x) (hf.sub hg) := by
  ext φ
  rw [_root_.sub_apply, regularDistribution_apply, regularDistribution_apply,
    regularDistribution_apply, ← integral_sub (LocalCurrentL1Ddc.integrable_testFunction_mul hf φ)
      (LocalCurrentL1Ddc.integrable_testFunction_mul hg φ)]
  congr 1
  funext x
  ring

end Current

/-! ### Weyl's lemma for `dd^c` -/

section Weyl

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- A distribution `S` on `U ⊆ ℂ^{m+1}` with `dd^c S = 0` has vanishing directional Levi
distributions. -/
theorem distributionalLeviCLM_eq_zero_of_ddc_eq_zero {S : 𝓓'(U, ℝ)}
    (h : ddc (scalarTopCurrent S) = 0) (w : ComplexModel (m + 1)) :
    distributionalLeviCLM w S = 0 := by
  have hpos : ∀ T : 𝓓'(U, ℝ), ddc (scalarTopCurrent T) = 0 → HasNonnegativeDistributionalLevi T :=
    fun T hT => SGPT.PSH.BookCurrent.hasNonnegativeDistributionalLevi_of_betaProduct_pairings T
      fun β α φ _ _ => by simp [hT]
  have h1 := hpos S h w
  have h2 := hpos (-S) (by rw [scalarTopCurrent_neg, ddc_neg, h, neg_zero]) w
  rw [map_neg] at h2
  exact eq_zero_of_positiveDistribution_of_neg h1 h2

/-- `dd^c (v - u) = 0` as distributions when `dd^c u = dd^c v`. -/
theorem ddc_scalarTopCurrent_sub_eq_zero {u v : ComplexModel (m + 1) → EReal}
    (hu : IsL1PshOn U u) (hv : IsL1PshOn U v) (h : ddcL1 U u = ddcL1 U v) :
    ddc (scalarTopCurrent (regularDistribution volume (fun x => (v x).toReal)
      hv.locallyIntegrableOn -
      regularDistribution volume (fun x => (u x).toReal) hu.locallyIntegrableOn)) = 0 := by
  rw [scalarTopCurrent_sub, ddc_sub, ← l1Current_eq_scalarTopCurrent,
    ← l1Current_eq_scalarTopCurrent]
  change ddcL1 U v - ddcL1 U u = 0
  rw [h, sub_self]

/-- **Weyl's lemma for `dd^c`, local form.**  If `u, v` are psh and locally integrable on `U` and
`dd^c u = dd^c v`, then every point of `U` has an open neighbourhood `W ≤ U` and a smooth function
`f` with `dd^c f = 0` on `W` such that `v = u + f` everywhere on `W`. -/
theorem exists_local_pluriharmonic_of_ddcL1_eq {u v : ComplexModel (m + 1) → EReal}
    (hu : IsL1PshOn U u) (hv : IsL1PshOn U v) (h : ddcL1 U u = ddcL1 U v) :
    ∀ x ∈ U, ∃ (W : Opens (ComplexModel (m + 1))) (_ : W ≤ U), x ∈ W ∧
      ∃ f : ComplexModel (m + 1) → ℝ, ContDiff ℝ ∞ f ∧ (∀ z ∈ W, smoothDDC f z = 0) ∧
        ∀ z ∈ W, v z = u z + f z := by
  intro x hx
  set S := regularDistribution volume (fun x => (v x).toReal) hv.locallyIntegrableOn -
      regularDistribution volume (fun x => (u x).toReal) hu.locallyIntegrableOn with hS
  have hzero := distributionalLeviCLM_eq_zero_of_ddc_eq_zero
    (ddc_scalarTopCurrent_sub_eq_zero hu hv h)
  obtain ⟨W, hWU, f, hxW, hf, hfi, hres, hlevi⟩ :=
    ActualZeroLeviDistributionSmoothness.exists_smooth_local_representative_of_zero_levi volume S
      hzero x hx
  have hf2 : ContDiff ℝ 2 f := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hddc : ∀ z ∈ W, smoothDDC f z = 0 := fun z hz =>
    smoothDDC_eq_zero_of_leviForm_eq_zero hf2.contDiffAt (hlevi z hz)
  refine ⟨W, hWU, hxW, f, by exact_mod_cast hf, hddc, ?_⟩
  -- `v - u = f` almost everywhere on `W`
  have hres' : restrictDistribution S hWU =
      regularDistribution volume (fun x => (v x).toReal - (u x).toReal)
        ((hv.locallyIntegrableOn.sub hu.locallyIntegrableOn).mono_set hWU) := by
    rw [hS, regularDistribution_sub, restrictDistribution_regularDistribution]
  have hae := ae_eq_of_regularDistribution_eq volume _ hfi (hres'.symm.trans hres)
  have hu' := hu.mono hWU
  have hv' := hv.mono hWU
  have hae' : (fun z => v z) =ᵐ[volume.restrict (W : Set (ComplexModel (m + 1)))]
      fun z => u z + (f z : EReal) := by
    filter_upwards [hae, hu'.ae_ne_bot, hv'.ae_ne_bot,
      ae_restrict_mem W.isOpen.measurableSet] with z hz hzu hzv hzW
    have hut : u z ≠ ⊤ := (hu'.psh z hzW).ne_top
    have hvt : v z ≠ ⊤ := (hv'.psh z hzW).ne_top
    rw [← EReal.coe_toReal hut hzu, ← EReal.coe_toReal hvt hzv, ← EReal.coe_add]
    congr 1
    linarith
  have hfpsh : PlurisubharmonicOn (fun z => (f z : EReal)) (W : Set (ComplexModel (m + 1))) :=
    plurisubharmonicOn_coe_of_smoothDDC_eq_zero W.isOpen hf.contDiffOn
      (by exact_mod_cast hddc)
  exact PlurisubharmonicOn.eqOn_of_ae_eq hv'.psh (hu'.psh.add hfpsh) W.isOpen volume hae'

/-- Two continuous corrections of the same potential agree. -/
theorem eqOn_of_add_eq_add {u : ComplexModel (m + 1) → EReal} (hu : IsL1PshOn U u)
    {V : Set (ComplexModel (m + 1))} (hV : IsOpen V) (hVU : V ⊆ U) {f g : ComplexModel (m + 1) → ℝ}
    (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (h : ∀ z ∈ V, u z + (f z : EReal) = u z + (g z : EReal)) : EqOn f g V := by
  have hae : f =ᵐ[volume.restrict V] g := by
    have hfin := hu.ae_ne_bot
    rw [ae_restrict_iff' U.isOpen.measurableSet] at hfin
    rw [Filter.EventuallyEq, ae_restrict_iff' hV.measurableSet]
    filter_upwards [hfin] with z hz hzV
    have hzb := hz (hVU hzV)
    have hzt : u z ≠ ⊤ := (hu.psh z (hVU hzV)).ne_top
    have e := h z hzV
    rw [← EReal.coe_toReal hzt hzb, ← EReal.coe_add, ← EReal.coe_add] at e
    have := EReal.coe_injective e
    linarith
  exact Measure.eqOn_of_ae_eq hae hf hg (hV.interior_eq.symm ▸ subset_closure)

/-- **Weyl's lemma for `dd^c`** (FPT, proof of `prop:nonpluripolar-local-calculus`): if `u, v`
are psh and locally integrable on `U` and `dd^c u = dd^c v`, then `v = u + h` everywhere on `U`
for a function `h` that is smooth on `U` with `dd^c h = 0` on `U` (`h` is pluriharmonic). -/
theorem exists_pluriharmonic_of_ddcL1_eq {u v : ComplexModel (m + 1) → EReal}
    (hu : IsL1PshOn U u) (hv : IsL1PshOn U v) (h : ddcL1 U u = ddcL1 U v) :
    ∃ g : ComplexModel (m + 1) → ℝ, ContDiffOn ℝ ∞ g U ∧ (∀ z ∈ U, smoothDDC g z = 0) ∧
      ∀ z ∈ U, v z = u z + g z := by
  classical
  have hloc := exists_local_pluriharmonic_of_ddcL1_eq hu hv h
  choose! W hWU hxW f hf hddc heq using hloc
  set g : ComplexModel (m + 1) → ℝ := fun z => f z z with hg
  -- the local corrections agree on overlaps
  have hagree : ∀ x ∈ U, ∀ z ∈ W x, g z = f x z := by
    intro x hx z hz
    have hzU : z ∈ U := hWU x hx hz
    have hV : IsOpen ((W z : Set (ComplexModel (m + 1))) ∩ W x) := (W z).isOpen.inter (W x).isOpen
    have hE := eqOn_of_add_eq_add hu hV (fun y hy => hWU z hzU hy.1)
      (hf z hzU).continuous.continuousOn (hf x hx).continuous.continuousOn
      (fun y hy => by rw [← heq z hzU y hy.1, ← heq x hx y hy.2])
    exact hE ⟨hxW z hzU, hz⟩
  have hev : ∀ x ∈ U, g =ᶠ[𝓝 x] f x := fun x hx =>
    Filter.eventually_of_mem ((W x).isOpen.mem_nhds (hxW x hx)) fun z hz => hagree x hx z hz
  refine ⟨g, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact ((hf x hx).contDiffAt.congr_of_eventuallyEq (hev x hx)).contDiffWithinAt
  · rw [smoothDDC_congr (hev x hx)]
    exact hddc x hx x (hxW x hx)
  · rw [heq x hx x (hxW x hx), hagree x hx x (hxW x hx)]

end Weyl

end SGPT.Currents
