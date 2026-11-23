/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
meta import Mathlib.Tactic.Abel
meta import Mathlib.Tactic.GCongr
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Ring

/-!
# Hausdorff dimension of zero sets of polynomials

* `dimH_image_le_of_pointwise_lipschitz`: maps that are Lipschitz at each point of a set (with
  a constant and a radius depending on the point) do not raise Hausdorff dimension.
* `dimH_zeroSet_le`: the zero set of a nonzero real polynomial in `d` variables has Hausdorff
  dimension at most `d - 1`; `dimH_zeroSet_add_one_le` is the form `dimH + 1 ≤ d` for `d ≥ 1`.
-/

@[expose] public section

namespace DFT

open Set Filter Topology MeasureTheory

section Lipschitz

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Maps that are Lipschitz at each point of `t` (relative to `t`) send `μH[d]`-null subsets of
`t` to `μH[d]`-null sets. -/
theorem hausdorffMeasure_image_eq_zero_of_pointwise_lipschitz [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {t : Set X}
    (hf : ∀ x ∈ t, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ t, dist z x < δ → dist (f z) (f x) ≤ C * dist z x)
    {d : ℝ} (hd : 0 ≤ d) (ht : μH[d] t = 0) : μH[d] (f '' t) = 0 := by
  obtain ⟨c, hcc, htc⟩ := Measure.isSeparable_of_hausdorffMeasure_ne_top
    (ht.trans_ne ENNReal.zero_ne_top)
  let P (n : ℕ) (y : X) : Set X :=
    {x ∈ t | ∀ z ∈ t, dist z x ≤ (n + 1 : ℝ)⁻¹ → dist (f z) (f x) ≤ n * dist z x} ∩
      Metric.ball y ((n + 1 : ℝ)⁻¹ / 2)
  have hcover : t ⊆ ⋃ n, ⋃ y ∈ c, P n y := by
    intro x hx
    obtain ⟨C, δ, hδ₀, hδ⟩ := hf x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max C δ⁻¹)
    have hnδ : (n + 1 : ℝ)⁻¹ < δ := by rw [inv_lt_comm₀ (by positivity) hδ₀]; grind
    obtain ⟨y, hyc, hy⟩ := Metric.mem_closure_iff.1 (htc hx) _
      (by positivity : (0 : ℝ) < (n + 1 : ℝ)⁻¹ / 2)
    refine mem_iUnion_of_mem n (mem_biUnion hyc ⟨⟨hx, fun z hz hzx ↦ ?_⟩, Metric.mem_ball.2 hy⟩)
    calc
      dist (f z) (f x) ≤ C * dist z x := hδ z hz (hzx.trans_lt hnδ)
      _ ≤ n * dist z x := by grw [((le_max_left _ _).trans_lt hn).le]
  have hlip (n : ℕ) (y : X) : LipschitzOnWith n f (P n y) :=
    .of_dist_le_mul fun z ⟨⟨hzt, _⟩, hzb⟩ w ⟨⟨_, hwP⟩, hwb⟩ ↦ hwP z hzt <| by
      linarith [dist_triangle_right z w y, Metric.mem_ball.1 hzb, Metric.mem_ball.1 hwb]
  refine measure_mono_null (image_mono hcover) ?_
  simp only [image_iUnion, measure_iUnion_null_iff, measure_biUnion_null_iff hcc]
  intro n y _
  have hP : μH[d] (P n y) = 0 := measure_mono_null (fun x hx ↦ hx.1.1) ht
  simpa [hP] using (hlip n y).hausdorffMeasure_image_le hd

/-- Maps that are Lipschitz at each point of `t` (relative to `t`, with a constant and a radius
depending on the point) do not raise Hausdorff dimension. Metric-space version. -/
theorem dimH_image_le_of_pointwise_lipschitz {f : X → Y} {t : Set X}
    (hf : ∀ x ∈ t, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ t, dist z x < δ → dist (f z) (f x) ≤ C * dist z x) :
    dimH (f '' t) ≤ dimH t := by
  borelize X Y
  simpa [dimH_eq_iInf] using
    biInf_mono (fun r ↦ hausdorffMeasure_image_eq_zero_of_pointwise_lipschitz hf r.2)

end Lipschitz

section Level

/-- Near a point where `f : E → ℝ` has a nonzero strict derivative, the level sets of `f` have
Hausdorff dimension at most `finrank E - 1`: the projection onto `ker f'` along a vector `v` with
`f' v = 1` is antilipschitz on them. -/
theorem exists_nhds_dimH_level_add_one_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} (hf : HasStrictFDerivAt f f' x)
    (hf' : f' ≠ 0) :
    ∃ U ∈ 𝓝 x, ∀ c : ℝ, dimH ({y | f y = c} ∩ U) + 1 ≤ Module.finrank ℝ E := by
  obtain ⟨w, hw⟩ : ∃ w, f' w ≠ 0 := by
    by_contra! h; exact hf' (ContinuousLinearMap.ext h)
  set v := (f' w)⁻¹ • w
  have hv : f' v = 1 := by simp [v, hw]
  set K := LinearMap.ker (f' : E →ₗ[ℝ] ℝ)
  have hK : Module.finrank ℝ K + 1 = Module.finrank ℝ E := by
    have h := LinearMap.finrank_range_add_finrank_ker (f' : E →ₗ[ℝ] ℝ)
    have hr : LinearMap.range (f' : E →ₗ[ℝ] ℝ) = ⊤ :=
      LinearMap.range_eq_top.2 fun t ↦ ⟨t • v, by simp [hv]⟩
    rw [hr, finrank_top, Module.finrank_self] at h
    change 1 + Module.finrank ℝ K = _ at h
    omega
  let π : E → K := fun u ↦ ⟨u - f' u • v, by simp [K, hv]⟩
  set ε : ℝ := (2 * (‖v‖ + 1))⁻¹
  have hε : 0 < ε := by positivity
  have hεv : ε * ‖v‖ ≤ 1 / 2 := by
    rw [show ε * ‖v‖ = ‖v‖ / (2 * (‖v‖ + 1)) by simp [ε, div_eq_mul_inv, mul_comm],
      div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨U, hU, hUb⟩ := (Filter.eventually_prod_self_iff
    (r := fun a b ↦ ‖f a - f b - f' (a - b)‖ ≤ ε * ‖a - b‖)).1
    (by rw [← nhds_prod_eq]; exact hf.isLittleO.bound hε)
  refine ⟨U, hU, fun c ↦ ?_⟩
  set S := {y | f y = c} ∩ U
  have hanti : AntilipschitzWith 2 (fun p : S ↦ π p) := by
    refine AntilipschitzWith.of_le_mul_dist fun a b ↦ ?_
    have hab := hUb a a.2.2 b b.2.2
    rw [a.2.1, b.2.1, sub_self, zero_sub, norm_neg] at hab
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    set u := (a : E) - b
    have h1 : π a - π b = u - f' u • v := by
      simp [π, u, map_sub, sub_smul]; abel
    have h2 : ‖u‖ ≤ ‖u - f' u • v‖ + ‖f' u‖ * ‖v‖ := by
      calc ‖u‖ = ‖(u - f' u • v) + f' u • v‖ := by rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by rw [norm_smul])
    have h3 : ‖f' u‖ * ‖v‖ ≤ ‖u‖ / 2 := by
      calc ‖f' u‖ * ‖v‖ ≤ ε * ‖u‖ * ‖v‖ := by gcongr
        _ = ε * ‖v‖ * ‖u‖ := by ring
        _ ≤ 1 / 2 * ‖u‖ := by gcongr
        _ = ‖u‖ / 2 := by ring
    push_cast
    rw [h1]
    linarith
  have hS : dimH S ≤ Module.finrank ℝ K := by
    calc dimH S = dimH (univ : Set S) := by
          rw [← (isometry_subtype_coe (s := S)).dimH_image, image_univ, Subtype.range_coe]
      _ ≤ dimH ((fun p : S ↦ π p) '' univ) := hanti.le_dimH_image _
      _ ≤ dimH (univ : Set K) := dimH_mono (subset_univ _)
      _ = Module.finrank ℝ K := Real.dimH_univ_eq_finrank K
  rw [← hK]
  push_cast
  gcongr

end Level

section Polynomial

open MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- Polynomial evaluation has strict derivative `v ↦ ∑ i, (∂ᵢ P)(x) v i`. -/
theorem hasStrictFDerivAt_eval (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasStrictFDerivAt (fun y ↦ eval y P)
      (∑ i, eval x (pderiv i P) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) i) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasStrictFDerivAt_const a x
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext y; simp
    · simp [add_smul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have hfun : (fun y ↦ eval y (p * X n)) = fun y ↦ eval y p * y n := by ext; simp
    rw [hfun]
    refine (hp.mul (hasStrictFDerivAt_apply n x)).congr_fderiv ?_
    ext v
    simp [pderiv_X, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Pi.single_apply, apply_ite,
      ite_mul, mul_assoc]

omit [Fintype σ] in
/-- A real polynomial all of whose partial derivatives vanish is constant. -/
theorem eq_C_of_pderiv_eq_zero {P : MvPolynomial σ ℝ} (h : ∀ i, pderiv i P = 0) :
    P = C (P.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  · by_contra hne
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 (Ne.symm hm)
    have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have hc := coeff_pderiv (i := i) P (m - Finsupp.single i 1)
    rw [h i, tsub_add_cancel_of_le hle] at hc
    simp [hne, eq_comm] at hc
    linarith [Nat.cast_nonneg (α := ℝ) (m i - 1)]

omit [Fintype σ] in
/-- Taking a nonzero partial derivative lowers the total degree. -/
theorem totalDegree_pderiv_lt {P : MvPolynomial σ ℝ} {i : σ} (h : pderiv i P ≠ 0) :
    (pderiv i P).totalDegree < P.totalDegree := by
  classical
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (pderiv i P).support
    (fun s ↦ s.sum fun _ e ↦ e) (support_nonempty.2 h)
  have hm' : m + Finsupp.single i 1 ∈ P.support := by
    rw [mem_support_iff] at hm ⊢
    rw [coeff_pderiv] at hm
    exact left_ne_zero_of_mul hm
  have h1 := le_totalDegree hm'
  rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_single_index (by simp)] at h1
  have h2 : (pderiv i P).totalDegree = m.sum fun _ e ↦ e :=
    le_antisymm (Finset.sup_le hmax) (le_totalDegree hm)
  omega

/-- The zeros of `P` at which `∂ᵢ P` does not vanish form a set of Hausdorff dimension at most
`card σ - 1`. -/
theorem dimH_regular_zeroSet_le (P : MvPolynomial σ ℝ) (i : σ) :
    dimH {x : σ → ℝ | eval x P = 0 ∧ eval x (pderiv i P) ≠ 0} ≤ (Fintype.card σ : ENNReal) - 1 := by
  classical
  set R := {x : σ → ℝ | eval x P = 0 ∧ eval x (pderiv i P) ≠ 0}
  by_contra! h
  obtain ⟨x, hxR, hx⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH h
  have hf' : (∑ j, eval x (pderiv j P) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) j) ≠ 0 := by
    intro h0
    have := congrArg (fun L ↦ L (Pi.single i 1)) h0
    simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      zero_apply] at this
    exact hxR.2 this
  obtain ⟨U, hU, hUd⟩ := exists_nhds_dimH_level_add_one_le (hasStrictFDerivAt_eval P x) hf'
  have h1 := hx (R ∩ U) (inter_mem_nhdsWithin R hU)
  have h2 : dimH (R ∩ U) + 1 ≤ Fintype.card σ := by
    refine le_trans ?_ ((hUd 0).trans_eq (by simp))
    gcongr
    exact fun y hy ↦ hy.1
  exact absurd (ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top h2) (not_le.2 h1)

/-- The zero set of a nonzero real polynomial in `d` variables has Hausdorff dimension at most
`d - 1` (truncated subtraction in `ℝ≥0∞`). -/
theorem dimH_zeroSet_le {P : MvPolynomial σ ℝ} (hP : P ≠ 0) :
    dimH {x : σ → ℝ | eval x P = 0} ≤ (Fintype.card σ : ENNReal) - 1 := by
  induction hd : P.totalDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  by_cases hc : ∀ i, pderiv i P = 0
  · have hPC := eq_C_of_pderiv_eq_zero hc
    have : {x : σ → ℝ | eval x P = 0} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rw [hPC, eval_C]
      intro h0
      exact hP (by rw [hPC, h0, map_zero])
    simp [this]
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    have hsub : {x : σ → ℝ | eval x P = 0} ⊆
        {x | eval x P = 0 ∧ eval x (pderiv i P) ≠ 0} ∪ {x | eval x (pderiv i P) = 0} := by
      intro x hx
      by_cases h : eval x (pderiv i P) = 0
      exacts [Or.inr h, Or.inl ⟨hx, h⟩]
    refine (dimH_mono hsub).trans ?_
    rw [dimH_union]
    exact max_le (dimH_regular_zeroSet_le P i) (ih _ (hd ▸ totalDegree_pderiv_lt hi) hi rfl)

/-- The zero set of a nonzero real polynomial in `d ≥ 1` variables has Hausdorff dimension at
most `d - 1`. -/
theorem dimH_zeroSet_add_one_le [Nonempty σ] {P : MvPolynomial σ ℝ} (hP : P ≠ 0) :
    dimH {x : σ → ℝ | eval x P = 0} + 1 ≤ (Fintype.card σ : ENNReal) := by
  have h1 : (1 : ENNReal) ≤ Fintype.card σ := by exact_mod_cast Fintype.card_pos
  calc dimH {x : σ → ℝ | eval x P = 0} + 1 ≤ ((Fintype.card σ : ENNReal) - 1) + 1 := by
        gcongr; exact dimH_zeroSet_le hP
    _ = Fintype.card σ := tsub_add_cancel_of_le h1

end Polynomial

end DFT
