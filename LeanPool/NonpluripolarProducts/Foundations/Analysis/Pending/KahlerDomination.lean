/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ExteriorDerivative

/-!
# Domination of a closed real (1,1)-form by a Kähler background

On a compact complex manifold carrying a Kähler form `ω`, every smooth real
two-form `θ` satisfies `θ + A ω ≥ 0` for some `A > 0`. This is
`gnpp:kahler-domination`, the geometric input that turns the semipositivity
*hypothesis* of `Pending.BoundedGlobalTruncation` into a consequence of an
actual `KahlerBackground`.

The proof is the usual two-step compactness argument, carried out on the
genuine chart coefficients rather than on an abstract positivity cone.

* Pointwise, strict positivity of `ω` on complex lines gives a *quantitative*
  bound `m ‖v‖² ≤ ω_z(v, iv)` with `m > 0`: the function `v ↦ ω_z(v, iv)` is
  continuous and positive on the unit sphere of `ℂⁿ`, which is compact, and the
  function is homogeneous of degree two.
* The coefficient maps `z ↦ θ_z`, `z ↦ ω_z` are continuous, and both
  `θ_z(v, iv)` and the error `(ω_z - ω_{z₀})(v, iv)` are controlled by the
  operator norm times `‖v‖²`. So a single `A` works on a whole neighbourhood of
  each point, and compactness of `M` makes finitely many of them suffice.
* Semipositivity is a pointwise condition, so the estimate obtained in the
  preferred chart at a point transfers to *every* chart containing it: the
  transition derivative is complex-linear, hence carries the complex line
  `ℝv + ℝiv` to a complex line again.

No Kähler identity, no metric on `M`, and no partition of unity is used.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.KahlerDomination

open FirstPass FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ}

/-! ### Pointwise estimates on a single alternating two-form -/

/-- The value of a two-form on the complex line spanned by `v` is homogeneous
of degree two in `v`. -/
theorem lineValue_smul (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (t : ℝ)
    (v : ComplexModel n) :
    a ![t • v, Complex.I • (t • v)] = t * t * a ![v, Complex.I • v] := by
  rw [smul_comm]
  have h : (![t • v, t • (Complex.I • v)] : Fin 2 → ComplexModel n)
      = fun i => t • (![v, Complex.I • v] i) := by
    funext i; fin_cases i <;> simp
  rw [h, a.map_smul_univ, Fin.prod_univ_two, smul_eq_mul]

@[simp] theorem apply_zero_zero (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) :
    a ![(0 : ComplexModel n), (0 : ComplexModel n)] = 0 :=
  a.map_coord_zero (0 : Fin 2) rfl

theorem lineValue_zero (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) :
    a ![(0 : ComplexModel n), Complex.I • (0 : ComplexModel n)] = 0 := by
  simp

/-- The line value is bounded by the operator norm, quadratically in `v`. -/
theorem abs_lineValue_le (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (v : ComplexModel n) : |a ![v, Complex.I • v]| ≤ ‖a‖ * ‖v‖ ^ 2 := by
  have h := a.le_opNorm ![v, Complex.I • v]
  have hI : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul]; simp
  simpa [Fin.prod_univ_two, hI, Real.norm_eq_abs, sq] using h

/-- A lower bound for the line value in terms of the operator norm. -/
theorem neg_norm_mul_le_lineValue (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (v : ComplexModel n) : -(‖a‖ * ‖v‖ ^ 2) ≤ a ![v, Complex.I • v] :=
  neg_le_of_abs_le (abs_lineValue_le a v)

/-- **A strictly positive two-form is quantitatively positive.** The constant
comes from the minimum on the unit sphere of `ℂⁿ`, which is compact. -/
theorem exists_lineValue_lower_bound {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : ComplexModel n, m * ‖v‖ ^ 2 ≤ a ![v, Complex.I • v] := by
  rcases (sphere (0 : ComplexModel n) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have hmem : ‖v‖⁻¹ • v ∈ sphere (0 : ComplexModel n) 1 := by
        simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
      rw [hS] at hmem
      exact hmem
    subst hv
    simp
  · obtain ⟨v₀, hv₀S, hmin⟩ := (isCompact_sphere (0 : ComplexModel n) 1).exists_isMinOn hS
      (by fun_prop : ContinuousOn (fun v : ComplexModel n => a ![v, Complex.I • v])
        (sphere 0 1))
    have hv₀ : v₀ ≠ 0 := by
      intro h; rw [h] at hv₀S; simp at hv₀S
    refine ⟨a ![v₀, Complex.I • v₀], ha v₀ hv₀, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
      have hw : ‖v‖⁻¹ • v ∈ sphere (0 : ComplexModel n) 1 := by
        simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
      have hsc := lineValue_smul a ‖v‖ (‖v‖⁻¹ • v)
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hnv), one_smul] at hsc
      calc a ![v₀, Complex.I • v₀] * ‖v‖ ^ 2
          ≤ a ![‖v‖⁻¹ • v, Complex.I • (‖v‖⁻¹ • v)] * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hmin hw) (by positivity)
        _ = a ![v, Complex.I • v] := by rw [hsc]; ring

/-! ### Transport between charts -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The line value transforms tensorially.** A holomorphic change of chart has
a complex-linear derivative, so it carries the complex line `ℝv + ℝiv` to the
complex line spanned by the image of `v`; semipositivity is therefore a genuinely
pointwise condition on `M`, testable in any one chart around a point. -/
theorem lineValue_compatible (a : SmoothRealForm n M 2) (e f : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ (chartTransition e f).source) (v : ComplexModel n) :
    a.coeff e z ![v, Complex.I • v]
      = a.coeff f (chartTransition e f z)
          ![chartTransitionDerivative e f z v,
            Complex.I • chartTransitionDerivative e f z v] := by
  have hv : (fun i => chartTransitionDerivative e f z (![v, Complex.I • v] i))
      = ![chartTransitionDerivative e f z v,
          Complex.I • chartTransitionDerivative e f z v] := by
    funext i
    fin_cases i
    · simp
    · simpa using chartTransitionDerivative_complex_smul e f z hz Complex.I v
  rw [a.compatible e f z hz ![v, Complex.I • v], hv]

/-- A Hermitian form is semipositive chartwise, with room to spare. -/
theorem lineValue_nonneg_of_isHermitian {ω : SmoothRealForm n M 2} (hω : ω.IsHermitian)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (v : ComplexModel n) : 0 ≤ ω.coeff e z ![v, Complex.I • v] := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact ((hω e z hz).2 v hv).le

/-! ### A single constant works near a point -/

/-- **Local domination.** Near a point of a chart target a single `A > 0` makes
`θ + A ω` nonnegative on every complex line, for `ω` strictly positive at the
centre. Both the deficit of `θ` and the drift of `ω` are controlled by operator
norms, which are continuous in the base point. -/
theorem exists_eventually_domination (θ ω : SmoothRealForm n M 2)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target)
    (hω : IsStrictlyPositive (ω.coeff e z₀)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ z in 𝓝 z₀, z ∈ e.val.target ∧ ∀ v : ComplexModel n,
      0 ≤ θ.coeff e z ![v, Complex.I • v] + A * ω.coeff e z ![v, Complex.I • v] := by
  obtain ⟨m, hm, hmle⟩ := exists_lineValue_lower_bound hω
  set C : ℝ := ‖θ.coeff e z₀‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  refine ⟨2 * (C + 1) / m, by positivity, ?_⟩
  have htgt : e.val.target ∈ 𝓝 z₀ := e.val.open_target.mem_nhds hz₀
  have hωc : ContinuousAt (ω.coeff e) z₀ :=
    ((ω.smooth e).continuousOn).continuousAt htgt
  have hθc : ContinuousAt (θ.coeff e) z₀ :=
    ((θ.smooth e).continuousOn).continuousAt htgt
  have h1 : ∀ᶠ z in 𝓝 z₀, ‖ω.coeff e z - ω.coeff e z₀‖ < m / 2 := by
    simpa [dist_eq_norm] using Metric.tendsto_nhds.mp hωc (m / 2) (by positivity)
  have h2 : ∀ᶠ z in 𝓝 z₀, ‖θ.coeff e z - θ.coeff e z₀‖ < 1 := by
    simpa [dist_eq_norm] using Metric.tendsto_nhds.mp hθc 1 one_pos
  filter_upwards [htgt, h1, h2] with z hz hz1 hz2
  refine ⟨hz, fun v => ?_⟩
  have hv2 : (0 : ℝ) ≤ ‖v‖ ^ 2 := by positivity
  -- the drift of `ω` eats at most half of the pointwise lower bound
  have hsplit : ω.coeff e z ![v, Complex.I • v]
      = ω.coeff e z₀ ![v, Complex.I • v]
        + (ω.coeff e z - ω.coeff e z₀) ![v, Complex.I • v] := by simp
  have hdrift : |(ω.coeff e z - ω.coeff e z₀) ![v, Complex.I • v]|
      ≤ ‖ω.coeff e z - ω.coeff e z₀‖ * ‖v‖ ^ 2 := abs_lineValue_le _ v
  have hωz : m / 2 * ‖v‖ ^ 2 ≤ ω.coeff e z ![v, Complex.I • v] := by
    have hd := neg_le_of_abs_le hdrift
    have := hmle v
    nlinarith [mul_le_mul_of_nonneg_right hz1.le hv2]
  -- `θ` cannot be more negative than its operator norm allows
  have hθn : ‖θ.coeff e z‖ ≤ C + 1 := by
    have := norm_sub_norm_le (θ.coeff e z) (θ.coeff e z₀)
    linarith
  have hθz : -((C + 1) * ‖v‖ ^ 2) ≤ θ.coeff e z ![v, Complex.I • v] := by
    have := neg_norm_mul_le_lineValue (θ.coeff e z) v
    nlinarith [mul_le_mul_of_nonneg_right hθn hv2]
  have hA : (0 : ℝ) < 2 * (C + 1) / m := by positivity
  have hkey : 2 * (C + 1) / m * (m / 2 * ‖v‖ ^ 2) = (C + 1) * ‖v‖ ^ 2 := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_left hωz hA.le
  rw [hkey] at h3
  linarith

/-! ### The global statement -/

variable [CompactSpace M]

/-- **Domination by a Kähler background** (`gnpp:kahler-domination`). On a
compact complex manifold with a Hermitian form `ω`, every smooth real two-form
`θ` admits `A > 0` with `θ + A ω` semipositive. Compactness is essential: the
constant is the maximum of finitely many local ones. -/
theorem exists_isSemipositive_add_smul (θ ω : SmoothRealForm n M 2)
    (hω : ω.IsHermitian) :
    ∃ A : ℝ, 0 < A ∧ ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n,
        0 ≤ θ.coeff e z ![v, Complex.I • v] + A * ω.coeff e z ![v, Complex.I • v] := by
  classical
  -- a local constant and a neighbourhood around every point of `M`
  have hloc : ∀ x : M, ∃ A : ℝ, ∃ V : Set (ComplexModel n), 0 < A ∧
      V ∈ 𝓝 ((complexChartAt (n := n) x).val x) ∧ V ⊆ (complexChartAt (n := n) x).val.target ∧
      ∀ z ∈ V, ∀ v : ComplexModel n,
        0 ≤ θ.coeff (complexChartAt (n := n) x) z ![v, Complex.I • v]
          + A * ω.coeff (complexChartAt (n := n) x) z ![v, Complex.I • v] := by
    intro x
    have hz₀ : (complexChartAt (n := n) x).val x ∈ (complexChartAt (n := n) x).val.target :=
      (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
    obtain ⟨A, hA, hev⟩ :=
      exists_eventually_domination θ ω (complexChartAt (n := n) x) hz₀ (hω _ _ hz₀).2
    obtain ⟨V, hV, hVsub⟩ := Filter.eventually_iff_exists_mem.mp hev
    exact ⟨A, V, hA, hV, fun z hz => (hVsub z hz).1, fun z hz => (hVsub z hz).2⟩
  choose A V hApos hVmem hVsub hVdom using hloc
  -- pull the neighbourhoods back to `M` and use compactness
  set U : M → Set M := fun x =>
    (complexChartAt (n := n) x).val.source ∩ (complexChartAt (n := n) x).val ⁻¹' V x with hU
  have hUmem : ∀ x : M, U x ∈ 𝓝 x := by
    intro x
    refine inter_mem ((complexChartAt (n := n) x).val.open_source.mem_nhds
      (mem_complexChartAt_source x)) ?_
    exact (complexChartAt (n := n) x).val.continuousAt (mem_complexChartAt_source x)
      (hVmem x)
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => hUmem x)
  have hsum : (0 : ℝ) ≤ ∑ x ∈ t, A x :=
    Finset.sum_nonneg fun y _ => (hApos y).le
  refine ⟨1 + ∑ x ∈ t, A x, by linarith, ?_⟩
  intro f w hw v
  -- locate the underlying point of `M` in one of the finitely many pieces
  have hp : f.val.symm w ∈ f.val.source := f.val.map_target hw
  obtain ⟨x, hxt, hxU⟩ : ∃ x ∈ t, f.val.symm w ∈ U x := by
    have := ht (mem_univ (f.val.symm w))
    simpa using this
  set e := complexChartAt (n := n) x with he
  have hsrc : f.val.symm w ∈ e.val.source := hxU.1
  have hzV : e.val (f.val.symm w) ∈ V x := hxU.2
  have hzt : e.val (f.val.symm w) ∈ e.val.target := hVsub x hzV
  -- the change of chart is legitimate and carries complex lines to complex lines
  have hwsrc : w ∈ (chartTransition f e).source := by
    rw [chartTransition]
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨hw, hsrc⟩
  have hteq : chartTransition f e w = e.val (f.val.symm w) := rfl
  have hθt := lineValue_compatible θ f e hwsrc v
  have hωt := lineValue_compatible ω f e hwsrc v
  rw [hteq] at hθt hωt
  rw [hθt, hωt]
  -- the global constant dominates the local one, and `ω` is already nonnegative
  set D := chartTransitionDerivative f e w v with hD
  have hmono : A x ≤ 1 + ∑ y ∈ t, A y :=
    le_trans (Finset.single_le_sum (fun y _ => (hApos y).le) hxt) (by linarith)
  have hωnn : 0 ≤ ω.coeff e (e.val (f.val.symm w)) ![D, Complex.I • D] :=
    lineValue_nonneg_of_isHermitian hω e hzt D
  have hdom := hVdom x _ hzV D
  nlinarith [mul_le_mul_of_nonneg_right hmono hωnn]

/-! ### The closed `(1,1)` form of the statement -/

omit [CompactSpace M] in
/-- A nonnegative multiple of a semipositive form is semipositive. -/
theorem isSemipositive_smul {η : ClosedRealOneOneForm n M}
    (hη : η.val.IsSemipositive) {A : ℝ} (hA : 0 ≤ A) :
    (A • η).val.IsSemipositive := by
  intro e z hz v
  have h := hη e z hz v
  simpa [ClosedRealOneOneForm.coeff_smul] using mul_nonneg hA h

omit [CompactSpace M] in
/-- Enlarging the constant preserves domination, because the background is
itself nonnegative on complex lines. -/
theorem isSemipositive_add_smul_mono {θ η : ClosedRealOneOneForm n M}
    (hη : η.val.IsSemipositive) {A B : ℝ} (hAB : A ≤ B)
    (h : (θ + A • η).val.IsSemipositive) : (θ + B • η).val.IsSemipositive := by
  intro e z hz v
  have h1 := h e z hz v
  have h2 := hη e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h1 ⊢
  nlinarith

/-- **Domination by a Kähler background** (`gnpp:kahler-domination`), in the
form the rest of the theory consumes: for a smooth closed real `(1,1)`-form `θ`
on a compact Kähler manifold there is `A > 0` with `θ + A ω` semipositive. -/
theorem exists_pos_isSemipositive_add_smul (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ∃ A : ℝ, 0 < A ∧ (θ + A • omega.form).val.IsSemipositive := by
  obtain ⟨A, hA, h⟩ :=
    exists_isSemipositive_add_smul θ.val omega.form.val omega.isKahler.1
  refine ⟨A, hA, fun e z hz v => ?_⟩
  simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] using h e z hz v

omit [CompactSpace M] in
/-- **One further unit of `ω` upgrades semipositivity to Kähler.** Closedness
and type `(1,1)` are automatic for a sum of closed `(1,1)`-forms; only strict
positivity has to be recovered, and the extra copy of `ω` supplies it. -/
theorem isKahler_add_smul_succ (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {A : ℝ}
    (hsemi : (θ + A • omega.form).val.IsSemipositive) :
    (θ + (A + 1) • omega.form).val.IsKahler := by
  refine ⟨fun e z hz => ⟨fun a b => (θ + (A + 1) • omega.form).property.2 e z hz a b,
    fun v hv => ?_⟩, (θ + (A + 1) • omega.form).property.1⟩
  have h1 := hsemi e z hz v
  have h2 := (omega.isKahler.1 e z hz).2 v hv
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h1 ⊢
  nlinarith

/-- The blueprint form of the same statement: the dominating form can be taken
to be an honest Kähler form. -/
theorem exists_pos_isKahler_add_smul (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ∃ A : ℝ, 0 < A ∧ (θ + A • omega.form).val.IsKahler := by
  obtain ⟨A, hA, hsemi⟩ := exists_pos_isSemipositive_add_smul omega θ
  exact ⟨A + 1, by linarith, isKahler_add_smul_succ omega hsemi⟩

/-- A single constant dominates a whole finite family of backgrounds. This is
the shape `Pending.BoundedGlobalTruncation` needs: its semipositivity hypothesis
is one constant serving every slot at once. -/
theorem exists_pos_forall_isSemipositive_add_smul (omega : KahlerBackground n M)
    {ι : Type*} [Finite ι] (θ : ι → ClosedRealOneOneForm n M) :
    ∃ A : ℝ, 0 < A ∧ ∀ i, (θ i + A • omega.form).val.IsSemipositive := by
  classical
  let := Fintype.ofFinite ι
  choose A hApos hA using fun i => exists_pos_isSemipositive_add_smul omega (θ i)
  have hsum : (0 : ℝ) ≤ ∑ i, A i := Finset.sum_nonneg fun i _ => (hApos i).le
  refine ⟨1 + ∑ i, A i, by linarith, fun i => ?_⟩
  refine isSemipositive_add_smul_mono omega.isSemipositive ?_ (hA i)
  have := Finset.single_le_sum (f := A) (fun j _ => (hApos j).le) (Finset.mem_univ i)
  linarith

/-- **One constant makes a whole finite family Kähler at once.** This is the
family form of `gnpp:kahler-domination` as the blueprint states it: not merely
semipositive but genuinely Kähler in every slot, for a single `A > 0`. -/
theorem exists_pos_forall_isKahler_add_smul (omega : KahlerBackground n M)
    {ι : Type*} [Finite ι] (θ : ι → ClosedRealOneOneForm n M) :
    ∃ A : ℝ, 0 < A ∧ ∀ i, (θ i + A • omega.form).val.IsKahler := by
  obtain ⟨A, hA, hsemi⟩ := exists_pos_forall_isSemipositive_add_smul omega θ
  exact ⟨A + 1, by linarith, fun i => isKahler_add_smul_succ omega (hsemi i)⟩

end

end SGPT.Foundations.Analysis.Pending.KahlerDomination
