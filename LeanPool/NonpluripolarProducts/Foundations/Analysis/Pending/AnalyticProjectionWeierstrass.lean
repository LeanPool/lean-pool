/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicGermWeierstrassPreparation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicCoefficientPolynomials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PolynomialCommonRootResultant

/-!
# Local proper projection along a Weierstrass direction

Source: Gunning--Rossi, *Analytic functions of several complex variables*, III.B
(Theorem 1, the elimination step); Chirka, *Complex analytic sets*, §3.7.  A step of the
local parametrization of analytic sets, the missing input behind
`AnalyticIrreducibleComponents.eq_dim_of_regularAtDim`.

Let `A = {g_1 = … = g_s = 0}` near `0 ∈ E × ℂ` and let `G` vanish on `A` near `0`, with
`G (0, t) = t^d u(t)`, `u(0) ≠ 0`.  Then there are `δ, ε > 0` such that over the ball
`‖z‖ < δ` the part of `A` in `‖t‖ < ε` stays in `‖t‖ < ε/2` (the projection is proper),
and its projection `{z | ∃ t, ‖t‖ < ε, (z, t) ∈ A}` is the common zero set of finitely
many functions holomorphic on the ball.

## Proof

Weierstrass preparation turns `G` into `W = t^d + ∑_{k<d} a_k(z) t^k` (up to a unit), and
Weierstrass division by `W` writes `g_j = Q_j W + ρ_j` with `ρ_j` a polynomial in `t` of
degree `< d` with holomorphic coefficients.  For small `z` all roots of `W(z, ·)` are
small (`norm_lt_of_weierstrass_root`), so `(z, t) ∈ A` with `‖t‖ < ε` iff `t` is a common
root of `W(z, ·)` and all `ρ_j(z, ·)`.  Such a common root exists iff the resultants
`Res_{d,d}(W(z, ·), ∑_j l^j ρ_j(z, ·))` vanish for `l = 0, …, d s`
(`PolynomialCommonRootResultant`), and these are holomorphic in `z`
(`differentiableOn_resultant_map`).
-/

@[expose] public section

open Filter Topology Polynomial Metric

namespace SGPT.Foundations.Analysis.Pending.AnalyticProjectionWeierstrass

open HolomorphicCoefficientPolynomials

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Weierstrass polynomial `t^d + ∑_{k<d} a_k(z) t^k` as a function on `E × ℂ`. -/
def weierstrassFun (d : ℕ) (a : ℕ → E → ℂ) (x : E × ℂ) : ℂ :=
  x.2 ^ d + ∑ k ∈ Finset.range d, a k x.1 * x.2 ^ k

/-- Holomorphy near `0 ∈ E` lifts along the projection `E × ℂ → E`. -/
theorem eventually_differentiableAt_comp_fst {f : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ f z) :
    ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ (fun x : E × ℂ => f x.1) x := by
  have ht : Tendsto (fun x : E × ℂ => x.1) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_fst.tendsto (0 : E × ℂ))
  filter_upwards [ht.eventually hf] with x hx
  exact hx.comp x differentiableAt_fst

/-- Finitely many functions differentiable near `0` are differentiable on a common ball. -/
theorem exists_ball_differentiableOn {ι : Type*} [Finite ι] {f : ι → E → ℂ}
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (f i) z) :
    ∃ r > 0, ∀ i, DifferentiableOn ℂ (f i) (ball 0 r) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (eventually_all.mpr hf)
  exact ⟨r, hr, fun i z hz => (hball hz i).differentiableWithinAt⟩

/-- `∑_{k<d} c_k X^k` has degree `< d`. -/
theorem degree_sum_range_lt {R : Type*} [Semiring R] (d : ℕ) (c : ℕ → R) :
    (∑ k ∈ Finset.range d, C (c k) * X ^ k).degree < (d : WithBot ℕ) := by
  rw [Finset.sum_range (fun k => C (c k) * X ^ k)]
  exact degree_sum_fin_lt (fun i : Fin d => c i)

/-- `X^d + ∑_{k<d} c_k X^k` is monic of degree `d`. -/
theorem monic_X_pow_add_sum {R : Type*} [Semiring R] [Nontrivial R] (d : ℕ) (c : ℕ → R) :
    (X ^ d + ∑ k ∈ Finset.range d, C (c k) * X ^ k).Monic ∧
      (X ^ d + ∑ k ∈ Finset.range d, C (c k) * X ^ k).natDegree = d := by
  refine ⟨monic_X_pow_add (degree_sum_range_lt d c), ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_range_lt d c

/-- **Local proper projection along a Weierstrass direction.**  If `G` vanishes on
`A = {g_j = 0}` near `0` and `G (0, t) = t^d u(t)` with `u 0 ≠ 0`, then over a ball
`‖z‖ < δ` the points of `A` with `‖t‖ < ε` have `‖t‖ < ε / 2`, each such fibre has at most
`d` points, and the projection of those
points is the common zero set of finitely many functions holomorphic on the ball. -/
theorem exists_projection_eq_zeroLocus {s : ℕ} {g : Fin s → E × ℂ → ℂ}
    (hg : ∀ j, ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (g j) x) {G : E × ℂ → ℂ}
    (hG : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ G x) {d : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hGu : ∀ᶠ t in 𝓝 (0 : ℂ), G (0, t) = t ^ d * u t)
    (hGA : ∀ᶠ x in 𝓝 (0 : E × ℂ), (∀ j, g j x = 0) → G x = 0) :
    ∃ δ > 0, ∃ ε > 0, ∃ (M : ℕ) (h : Fin M → E → ℂ),
      (∀ i, DifferentiableOn ℂ (h i) (ball 0 δ)) ∧
      (∀ z ∈ ball (0 : E) δ, ∀ t : ℂ, ‖t‖ < ε → (∀ j, g j (z, t) = 0) → ‖t‖ < ε / 2) ∧
      (∀ z ∈ ball (0 : E) δ, {t : ℂ | ‖t‖ < ε ∧ ∀ j, g j (z, t) = 0}.Finite ∧
        {t : ℂ | ‖t‖ < ε ∧ ∀ j, g j (z, t) = 0}.ncard ≤ d) ∧
      ∀ z ∈ ball (0 : E) δ,
        (∃ t : ℂ, ‖t‖ < ε ∧ ∀ j, g j (z, t) = 0) ↔ ∀ i, h i z = 0 := by
  classical
  obtain ⟨q, hq, hq0, a, ha, ha0, hqG⟩ :=
    HolomorphicGermWeierstrassPreparation.exists_weierstrass_preparation hG hu hu0 hGu
  -- the Weierstrass polynomial as a function, and division of each `g j` by it
  have hWd : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ (weierstrassFun d a) x := by
    have hk : ∀ k ∈ Finset.range d, ∀ᶠ x in 𝓝 (0 : E × ℂ),
        DifferentiableAt ℂ (fun x : E × ℂ => a k x.1 * x.2 ^ k) x := fun k _ =>
      (eventually_differentiableAt_comp_fst (ha k)).mono fun x hx =>
        hx.mul (differentiableAt_snd.pow k)
    filter_upwards [(eventually_all_finset _).mpr hk] with x hx
    have hsum := DifferentiableAt.sum hx
    exact (differentiableAt_snd.pow d).add (by simpa [Finset.sum_fn] using hsum)
  have hW0 : ∀ᶠ t in 𝓝 (0 : ℂ), weierstrassFun d a (0, t) = t ^ d * (fun _ => (1 : ℂ)) t :=
    Eventually.of_forall fun t => by
      simp only [weierstrassFun, mul_one]
      rw [Finset.sum_eq_zero fun k hk => by rw [ha0 k (Finset.mem_range.mp hk), zero_mul],
        add_zero]
  have hdiv := fun j => germWeierstrassDivision E (weierstrassFun d a) hWd d (fun _ => (1 : ℂ))
    analyticAt_const one_ne_zero hW0 (g j) (hg j)
  choose Q _hQ r hr hdivj using hdiv
  -- a product ball on which all identities hold
  have hN1 : ∀ᶠ x in 𝓝 (0 : E × ℂ), q x ≠ 0 ∧ q x * G x = weierstrassFun d a x ∧
      ((∀ j, g j x = 0) → G x = 0) ∧
      ∀ j, g j x =
        Q j x * weierstrassFun d a x + ∑ k ∈ Finset.range d, r j k x.1 * x.2 ^ k := by
    filter_upwards [(continuousAt_zero_of_eventually_differentiableAt hq).eventually_ne hq0,
      hqG, hGA, eventually_all.mpr hdivj] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r1, hr1, hball1⟩ := Metric.mem_nhds_iff.mp hN1
  set ε : ℝ := min r1 1 with hεdef
  have hε : 0 < ε := lt_min hr1 one_pos
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε21 : ε / 2 ≤ 1 := by
    have := min_le_right r1 1
    linarith
  have hN2 : ∀ᶠ z in 𝓝 (0 : E), (∀ k ∈ Finset.range d, DifferentiableAt ℂ (a k) z ∧
      ‖a k z‖ * d < (ε / 2) ^ d) ∧
      ∀ j, ∀ k ∈ Finset.range d, DifferentiableAt ℂ (r j k) z := by
    refine (((eventually_all_finset _).mpr fun k hk => ?_).and
      (eventually_all.mpr fun j => (eventually_all_finset _).mpr fun k _ => hr j k))
    refine (ha k).and ?_
    have hc : ContinuousAt (fun z => ‖a k z‖ * d) 0 :=
      (continuousAt_zero_of_eventually_differentiableAt (ha k)).norm.mul continuousAt_const
    refine hc.eventually_lt continuousAt_const ?_
    simp only [ha0 k (Finset.mem_range.mp hk), norm_zero, zero_mul]
    exact pow_pos hε2 d
  obtain ⟨r2, hr2, hball2⟩ := Metric.mem_nhds_iff.mp hN2
  set δ : ℝ := min r1 r2 with hδdef
  have hδ : 0 < δ := lt_min hr1 hr2
  set U : Set E := ball (0 : E) δ with hUdef
  have hU2 : ∀ z ∈ U, z ∈ ball (0 : E) r2 := fun z hz => ball_subset_ball (min_le_right _ _) hz
  -- coefficients, extended by zero beyond degree `d`
  let a' : ℕ → E → ℂ := fun k => if k < d then a k else 0
  let r' : Fin s → ℕ → E → ℂ := fun j k => if k < d then r j k else 0
  have ha' : ∀ k, DifferentiableOn ℂ (a' k) U := by
    intro k z hz
    by_cases hk : k < d
    · simp only [a', hk, ite_true]
      exact ((hball2 (hU2 z hz)).1 k (Finset.mem_range.mpr hk)).1.differentiableWithinAt
    · simp only [a', hk, ite_false]
      exact differentiableWithinAt_const 0
  have hr' : ∀ j k, DifferentiableOn ℂ (r' j k) U := by
    intro j k z hz
    by_cases hk : k < d
    · simp only [r', hk, ite_true]
      exact ((hball2 (hU2 z hz)).2 j k (Finset.mem_range.mpr hk)).differentiableWithinAt
    · simp only [r', hk, ite_false]
      exact differentiableWithinAt_const 0
  let Wp : (holOnSubring U)[X] := X ^ d + ofCoeffs U d a' ha'
  let ρp : Fin s → (holOnSubring U)[X] := fun j => ofCoeffs U d (r' j) (hr' j)
  let cst : ℕ → ℕ → holOnSubring U := fun l j =>
    ⟨fun _ => (l : ℂ) ^ j, differentiableOn_const _⟩
  let Lp : ℕ → (holOnSubring U)[X] := fun l => ∑ j : Fin s, C (cst l j) * ρp j
  have hWmap : ∀ z, Wp.map (evalAt U z) =
      X ^ d + ∑ k ∈ Finset.range d, C (a' k z) * X ^ k := by
    intro z
    simp only [Wp, Polynomial.map_add, Polynomial.map_pow, map_X, map_ofCoeffs]
  have hLmap : ∀ z l, (Lp l).map (evalAt U z) =
      ∑ j : Fin s, C ((l : ℂ) ^ (j : ℕ)) * (ρp j).map (evalAt U z) := by
    intro z l
    simp only [Lp, Polynomial.map_sum, Polynomial.map_mul, map_C]
    rfl
  have hWeval : ∀ z t, (Wp.map (evalAt U z)).eval t = weierstrassFun d a (z, t) := by
    intro z t
    rw [hWmap]
    simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, weierstrassFun]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [a', Finset.mem_range.mp hk]
  have hρeval : ∀ z j t, ((ρp j).map (evalAt U z)).eval t =
      ∑ k ∈ Finset.range d, r j k z * t ^ k := by
    intro z j t
    simp only [ρp, map_ofCoeffs, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [r', Finset.mem_range.mp hk]
  have hWmonic : ∀ z, (Wp.map (evalAt U z)).Monic ∧ (Wp.map (evalAt U z)).natDegree = d := by
    intro z
    rw [hWmap]
    exact monic_X_pow_add_sum d fun k => a' k z
  have hρdeg : ∀ z j, ((ρp j).map (evalAt U z)).natDegree ≤ d := by
    intro z j
    simp only [ρp, map_ofCoeffs]
    exact natDegree_le_iff_degree_le.mpr (degree_sum_range_lt d _).le
  have hroot : ∀ z ∈ U, ∀ t : ℂ, weierstrassFun d a (z, t) = 0 → ‖t‖ < ε / 2 := by
    intro z hz t ht
    exact norm_lt_of_weierstrass_root hε2 hε21
      (fun k hk => ((hball2 (hU2 z hz)).1 k (Finset.mem_range.mpr hk)).2) ht
  have hmem : ∀ z ∈ U, ∀ t : ℂ, ‖t‖ < ε → ((z, t) : E × ℂ) ∈ ball (0 : E × ℂ) r1 := by
    intro z hz t ht
    rw [mem_ball_zero_iff, Prod.norm_def]
    exact max_lt ((mem_ball_zero_iff.mp hz).trans_le (min_le_left _ _))
      (ht.trans_le (min_le_left _ _))
  have hA : ∀ z ∈ U, ∀ t : ℂ, ‖t‖ < ε → ((∀ j, g j (z, t) = 0) ↔
      weierstrassFun d a (z, t) = 0 ∧ ∀ j, ∑ k ∈ Finset.range d, r j k z * t ^ k = 0) := by
    intro z hz t ht
    obtain ⟨-, h2, h3, h4⟩ := hball1 (hmem z hz t ht)
    constructor
    · intro hg0
      have hW : weierstrassFun d a (z, t) = 0 := by rw [← h2, h3 hg0, mul_zero]
      refine ⟨hW, fun j => ?_⟩
      have := h4 j
      rw [hg0 j, hW, mul_zero, zero_add] at this
      exact this.symm
    · rintro ⟨hW, hρ⟩ j
      rw [h4 j, hW, mul_zero, zero_add]
      exact hρ j
  refine ⟨δ, hδ, ε, hε, d * s + 1,
    fun l z => resultant (Wp.map (evalAt U z)) ((Lp l).map (evalAt U z)) d d,
    fun l => differentiableOn_resultant_map U _ _ d d, ?_, ?_, ?_⟩
  · intro z hz t ht hg0
    exact hroot z hz t ((hA z hz t ht).mp hg0).1
  · intro z hz
    -- the fibre lies in the root set of the monic polynomial `W(z, ·)` of degree `d`
    set P := Wp.map (evalAt U z)
    have hP0 : P ≠ 0 := (hWmonic z).1.ne_zero
    have hsub : {t : ℂ | ‖t‖ < ε ∧ ∀ j, g j (z, t) = 0} ⊆ (P.roots.toFinset : Set ℂ) := by
      rintro t ⟨ht, hg0⟩
      have hW := ((hA z hz t ht).mp hg0).1
      rw [← hWeval] at hW
      simpa [Multiset.mem_toFinset, mem_roots hP0] using hW
    refine ⟨(P.roots.toFinset.finite_toSet).subset hsub, ?_⟩
    calc {t : ℂ | ‖t‖ < ε ∧ ∀ j, g j (z, t) = 0}.ncard
        ≤ (P.roots.toFinset : Set ℂ).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = P.roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ = d := (hWmonic z).2
  · intro z hz
    have crit := PolynomialCommonRootResultant.exists_common_root_iff_forall_resultant_eq_zero
      (hWmonic z).1 (hWmonic z).2 (fun j => (ρp j).map (evalAt U z)) (hρdeg z)
    constructor
    · rintro ⟨t, ht, hg0⟩ i
      obtain ⟨hW, hρ⟩ := (hA z hz t ht).mp hg0
      have := crit.mp ⟨t, by rwa [hWeval], fun j => by rw [hρeval]; exact hρ j⟩ i
        (Nat.lt_succ_iff.mp i.2)
      change resultant _ ((Lp (i : ℕ)).map (evalAt U z)) d d = 0
      rw [hLmap]
      exact this
    · intro hall
      obtain ⟨t, hW, hρ⟩ := crit.mpr fun l hl => by
        have := hall ⟨l, Nat.lt_succ_of_le hl⟩
        change resultant _ ((Lp l).map (evalAt U z)) d d = 0 at this
        rwa [hLmap] at this
      rw [hWeval] at hW
      have ht := hroot z hz t hW
      refine ⟨t, by linarith, (hA z hz t (by linarith)).mpr ⟨hW, fun j => ?_⟩⟩
      rw [← hρeval]
      exact hρ j

end

end SGPT.Foundations.Analysis.Pending.AnalyticProjectionWeierstrass
