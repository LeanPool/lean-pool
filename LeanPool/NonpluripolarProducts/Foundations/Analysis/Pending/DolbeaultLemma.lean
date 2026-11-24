/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WirtingerCalculus
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalTwoFormPoincare

/-!
# The local Dolbeault lemma in degree `(0,1)`

On `ℂⁿ = EuclideanSpace ℂ (Fin n)`, a smooth `∂bar`-closed `(0,1)`-form, given by
its coefficients `a i = ∂bar_{e_i}`-components, has a smooth local `∂bar`-primitive.
The proof removes the coefficients one at a time, starting from the last
nonzero one, by the Cauchy–Green operator in that coordinate applied to the
coefficient times a polydisc cutoff; the cutoff is constant in the remaining
coordinates near the centre, so earlier coefficients stay holomorphic in them.
-/

@[expose] public section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.CauchyGreen

noncomputable section

variable {n : ℕ}

/-- The standard complex basis vector of `ℂⁿ`. -/
abbrev basisVec (i : Fin n) : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1

/-- `∂bar`-closedness of a `(0,1)`-form given by its coordinate coefficients. -/
def IsDbarClosedOn (a : Fin n → EuclideanSpace ℂ (Fin n) → ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ i j, ∀ x ∈ U, dbarDir (basisVec i) (a j) x = dbarDir (basisVec j) (a i) x

/-- A directional Wirtinger derivative commutes with the Cauchy–Green operator. -/
theorem dbarDir_cauchyGreen_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) {v : E} (hv : v ≠ 0)
    (u x : E) :
    dbarDir u (cauchyGreen v g) x = cauchyGreen v (dbarDir u g) x := by
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hint (u' : E) := integrable_inv_smul_comp (hDc.clm_apply continuous_const)
    (hasCompactSupport_fderiv_apply hc u') hv x
  have hsum : (∫ w : ℂ, w⁻¹ • ((fderiv ℝ g (x - w • v) u +
      I * fderiv ℝ g (x - w • v) (I • u)) / 2)) =
      ((∫ w : ℂ, w⁻¹ • fderiv ℝ g (x - w • v) u) +
        I * ∫ w : ℂ, w⁻¹ • fderiv ℝ g (x - w • v) (I • u)) / 2 := by
    rw [← integral_const_mul, ← integral_add (hint u) ((hint _).const_mul I), ← integral_div]
    congr 1
    funext w
    simp only [smul_eq_mul]
    ring
  simp only [dbarDir, fderiv_cauchyGreen_apply hg hc hv, cauchyGreen]
  rw [hsum]
  ring

section Cutoff

variable (x₀ : EuclideanSpace ℂ (Fin n)) {r : ℝ} (hr : 0 < r)

/-- A smooth polydisc cutoff: equal to one when every coordinate is within
`r` of the centre, supported where every coordinate is within `2r`. -/
def polydiscCutoff : EuclideanSpace ℂ (Fin n) → ℝ :=
  fun z ↦ ∏ k, (⟨r, 2 * r, hr, by linarith⟩ : ContDiffBump (0 : ℂ)) (z k - x₀ k)

theorem contDiff_polydiscCutoff : ContDiff ℝ ∞ (polydiscCutoff x₀ hr) := by
  refine contDiff_prod fun k _ ↦ ?_
  refine (ContDiffBump.contDiff _).comp ?_
  have : ContDiff ℝ ∞ (fun z : EuclideanSpace ℂ (Fin n) ↦ z k) :=
    ((EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  exact this.sub contDiff_const

theorem polydiscCutoff_eq_one {z : EuclideanSpace ℂ (Fin n)}
    (hz : ∀ k, ‖z k - x₀ k‖ ≤ r) : polydiscCutoff x₀ hr z = 1 := by
  refine Finset.prod_eq_one fun k _ ↦ ContDiffBump.one_of_mem_closedBall _ ?_
  simpa using hz k

theorem tsupport_polydiscCutoff_subset :
    tsupport (polydiscCutoff x₀ hr) ⊆ {z | ∀ k, ‖z k - x₀ k‖ ≤ 2 * r} := by
  refine closure_minimal (fun z hz k ↦ ?_) ?_
  · by_contra hk
    apply hz
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    apply Function.notMem_support.mp
    rw [ContDiffBump.support_eq]
    simp only [mem_ball, dist_zero_right, not_lt]
    exact (lt_of_not_ge hk).le
  · simp only [ofPred_forall]
    exact isClosed_iInter fun k ↦ isClosed_le
      (continuous_norm.comp ((EuclideanSpace.proj k :
        EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous.sub continuous_const))
      continuous_const

theorem norm_sub_le_of_coord_le {z : EuclideanSpace ℂ (Fin n)} {s : ℝ} (hs : 0 ≤ s)
    (hz : ∀ k, ‖z k - x₀ k‖ ≤ s) : ‖z - x₀‖ ≤ n * s := by
  have hsq : ‖z - x₀‖ ^ 2 ≤ (n * s) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ k, ‖(z - x₀) k‖ ^ 2 ≤ ∑ _k : Fin n, s ^ 2 := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          have := hz k
          simp only [PiLp.sub_apply]
          exact pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = n * s ^ 2 := by simp
      _ ≤ (n * s) ^ 2 := by
          rcases Nat.eq_zero_or_pos n with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ n := by exact_mod_cast h
            nlinarith [sq_nonneg s]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem hasCompactSupport_polydiscCutoff : HasCompactSupport (polydiscCutoff x₀ hr) := by
  refine (Metric.isCompact_of_isClosed_isBounded (isClosed_closedBall (x := x₀)
    (ε := n * (2 * r))) isBounded_closedBall).of_isClosed_subset (isClosed_tsupport _) ?_
  intro z hz
  rw [mem_closedBall, dist_eq_norm]
  exact norm_sub_le_of_coord_le x₀ (by positivity) (tsupport_polydiscCutoff_subset x₀ hr hz)

/-- Near points whose `i`th coordinate is within `r` of the centre, the cutoff
does not depend on the `i`th coordinate, so its `∂bar` in that coordinate vanishes. -/
theorem dbarDir_polydiscCutoff_eq_zero {i : Fin n} {y : EuclideanSpace ℂ (Fin n)}
    (hy : ‖y i - x₀ i‖ < r) :
    dbarDir (basisVec i) (fun z ↦ (polydiscCutoff x₀ hr z : ℂ)) y = 0 := by
  let ρ : ContDiffBump (0 : ℂ) := ⟨r, 2 * r, hr, by linarith⟩
  let χ' : EuclideanSpace ℂ (Fin n) → ℂ :=
    fun z ↦ ((∏ k ∈ Finset.univ.erase i, ρ (z k - x₀ k) : ℝ) : ℂ)
  have hopen : IsOpen {z : EuclideanSpace ℂ (Fin n) | ‖z i - x₀ i‖ < r} :=
    isOpen_lt (continuous_norm.comp ((EuclideanSpace.proj i :
      EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous.sub continuous_const)) continuous_const
  have heq : (fun z ↦ (polydiscCutoff x₀ hr z : ℂ)) =ᶠ[𝓝 y] χ' := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    simp only [polydiscCutoff, χ']
    rw [← Finset.mul_prod_erase Finset.univ (fun k ↦ ρ (z k - x₀ k)) (Finset.mem_univ i)]
    rw [show ρ (z i - x₀ i) = 1 from ρ.one_of_mem_closedBall (by simpa using hz.le), one_mul]
  have hinv (u : EuclideanSpace ℂ (Fin n)) (hu : ∀ k, k ≠ i → u k = 0) :
      fderiv ℝ χ' y u = 0 := by
    refine fderiv_apply_eq_zero_of_invariant (fun z t ↦ ?_) y
    have hk : ∀ k ∈ Finset.univ.erase i, ρ ((z + t • u) k - x₀ k) = ρ (z k - x₀ k) :=
      fun k hk ↦ by simp [hu k (Finset.ne_of_mem_erase hk)]
    simp only [χ', Finset.prod_congr rfl hk]
  rw [dbarDir_congr heq]
  simp only [dbarDir]
  rw [hinv _ (fun k hk ↦ by simp [basisVec, hk]),
    hinv _ (fun k hk ↦ by simp [basisVec, hk])]
  simp

end Cutoff

/-- Inductive form of the Dolbeault lemma: if the coefficients with index at
least `k` vanish, a smooth local `∂bar`-primitive exists. -/
theorem exists_dbar_primitive_aux (k : ℕ) :
    ∀ (U : Set (EuclideanSpace ℂ (Fin n))) (a : Fin n → EuclideanSpace ℂ (Fin n) → ℂ)
      (x₀ : EuclideanSpace ℂ (Fin n)), IsOpen U → x₀ ∈ U →
      (∀ i, ContDiffOn ℝ ∞ (a i) U) → IsDbarClosedOn a U →
      (∀ i : Fin n, k ≤ i.val → ∀ x ∈ U, a i x = 0) →
      ∃ W, IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧ ∃ f : EuclideanSpace ℂ (Fin n) → ℂ,
        ContDiff ℝ ∞ f ∧ ∀ i, ∀ x ∈ W, dbarDir (basisVec i) f x = a i x := by
  induction k with
  | zero =>
    intro U a x₀ hU hx₀ _ _ hzero
    exact ⟨U, hU, hx₀, Subset.rfl, fun _ ↦ 0, contDiff_const, fun i x hx ↦ by
      rw [dbarDir_const, hzero i (Nat.zero_le _) x hx]⟩
  | succ k ih =>
    intro U a x₀ hU hx₀ ha hclosed hzero
    by_cases hk : k < n
    swap
    · exact ih U a x₀ hU hx₀ ha hclosed fun i hi ↦ absurd i.isLt (by omega)
    let j : Fin n := ⟨k, hk⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
    set r : ℝ := δ / (2 * (n + 1)) with hr_def
    have hr : 0 < r := by positivity
    let χ := polydiscCutoff x₀ hr
    let V : Set (EuclideanSpace ℂ (Fin n)) := {z | ∀ k, ‖z k - x₀ k‖ < r}
    have hVopen : IsOpen V := by
      simp only [V, ofPred_forall]
      exact isOpen_iInter_of_finite fun k ↦ isOpen_lt
        (continuous_norm.comp ((EuclideanSpace.proj k :
          EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous.sub continuous_const))
        continuous_const
    have hx₀V : x₀ ∈ V := fun k ↦ by simpa using hr
    have hpoly : ∀ z : EuclideanSpace ℂ (Fin n), (∀ k, ‖z k - x₀ k‖ ≤ 2 * r) → z ∈ U := by
      intro z hz
      apply hδU
      rw [mem_ball, dist_eq_norm]
      calc ‖z - x₀‖ ≤ n * (2 * r) := norm_sub_le_of_coord_le x₀ (by positivity) hz
        _ < δ := by
          rw [hr_def]
          have hn : (0 : ℝ) < n + 1 := by positivity
          rw [show (n : ℝ) * (2 * (δ / (2 * (n + 1)))) = δ * (n / (n + 1)) by
            field_simp]
          have : (n : ℝ) / (n + 1) < 1 := by
            rw [div_lt_one hn]
            linarith
          nlinarith
    have hVU : V ⊆ U := fun z hz ↦ hpoly z fun k ↦ by linarith [hz k]
    have hsuppU : tsupport χ ⊆ U := fun z hz ↦
      hpoly z (tsupport_polydiscCutoff_subset x₀ hr hz)
    let b : EuclideanSpace ℂ (Fin n) → ℂ := fun z ↦ χ z • a j z
    have hb : ContDiff ℝ ∞ b := LocalPotentials.contDiff_smul_of_tsupport_subset hU
      (contDiff_polydiscCutoff x₀ hr) hsuppU (ha j)
    have hbc : HasCompactSupport b := (hasCompactSupport_polydiscCutoff x₀ hr).smul_right
    have hej : basisVec j ≠ 0 := by simp [basisVec]
    let g := cauchyGreen (basisVec j) b
    have hg : ContDiff ℝ ∞ g := contDiff_cauchyGreen hb hbc hej
    have hdg (i : Fin n) : ContDiff ℝ ∞ (dbarDir (basisVec i) g) := by
      have hD := hg.fderiv_right (m := ∞) (by simp)
      change ContDiff ℝ ∞ (fun x ↦ (fderiv ℝ g x (basisVec i) +
        I * fderiv ℝ g x (I • basisVec i)) / 2)
      exact ((hD.clm_apply contDiff_const).add
        (contDiff_const.mul (hD.clm_apply contDiff_const))).div_const _
    let a' : Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
      fun i z ↦ a i z - dbarDir (basisVec i) g z
    have hadiff (i : Fin n) {x} (hx : x ∈ U) : DifferentiableAt ℝ (a i) x :=
      ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have ha' : ∀ i, ContDiffOn ℝ ∞ (a' i) V := fun i ↦
      ((ha i).mono hVU).sub (hdg i).contDiffOn
    have hclosed' : IsDbarClosedOn a' V := by
      intro i l x hx
      simp only [a']
      rw [dbarDir_sub (hadiff l (hVU hx)) ((hdg l).differentiable (by simp) x),
        dbarDir_sub (hadiff i (hVU hx)) ((hdg i).differentiable (by simp) x),
        hclosed i l x (hVU hx), dbarDir_dbarDir_comm (hg.contDiffAt.of_le (by norm_cast))]
    have hzero' : ∀ i : Fin n, k ≤ i.val → ∀ x ∈ V, a' i x = 0 := by
      intro i hi x hx
      simp only [a']
      rcases hi.eq_or_lt with hij | hij
      · have hij' : i = j := Fin.ext hij.symm
        subst hij'
        rw [show dbarDir (basisVec j) g x = b x from
          dbarDir_cauchyGreen (hb.of_le (by simp)) hbc hej x]
        simp only [b, χ, polydiscCutoff_eq_one x₀ hr (fun k ↦ (hx k).le), one_smul, sub_self]
      · rw [hzero i hij x (hVU hx), dbarDir_cauchyGreen_comm (hb.of_le (by simp)) hbc hej]
        have hne : i ≠ j := fun h ↦ by
          rw [h] at hij
          exact lt_irrefl _ hij
        have hvanish : ∀ w : ℂ, dbarDir (basisVec i) b (x - w • basisVec j) = 0 := by
          intro w
          set y := x - w • basisVec j
          have hyi : y i = x i := by simp [y, basisVec, hne]
          by_cases hy : y ∈ tsupport χ
          · have hyU := hsuppU hy
            have hbeq : b = fun z ↦ (χ z : ℂ) * a j z := funext fun z ↦ Complex.real_smul
            rw [hbeq, dbarDir_ofReal_mul ((contDiff_polydiscCutoff x₀ hr).differentiable
              (by simp) y) (hadiff j hyU)]
            rw [dbarDir_polydiscCutoff_eq_zero x₀ hr (by rw [hyi]; exact hx i),
              hclosed i j y hyU]
            have hev : a i =ᶠ[𝓝 y] fun _ ↦ 0 := by
              filter_upwards [hU.mem_nhds hyU] with z hz
              exact hzero i hij z hz
            rw [dbarDir_congr hev, dbarDir_const]
            ring
          · have hev : b =ᶠ[𝓝 y] fun _ ↦ 0 := by
              filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with z hz
              simp [b, image_eq_zero_of_notMem_tsupport hz]
            rw [dbarDir_congr hev, dbarDir_const]
        simp [cauchyGreen, hvanish]
    obtain ⟨W, hW, hx₀W, hWV, f', hf', hf'eq⟩ := ih V a' x₀ hVopen hx₀V ha' hclosed' hzero'
    refine ⟨W, hW, hx₀W, hWV.trans hVU, fun z ↦ f' z + g z, hf'.add hg, fun i x hx ↦ ?_⟩
    rw [dbarDir_add (hf'.differentiable (by simp) x) (hg.differentiable (by simp) x),
      hf'eq i x hx]
    simp [a']

/-- **The local Dolbeault lemma in degree `(0,1)`.**  A smooth `∂bar`-closed
`(0,1)`-form on an open subset of `ℂⁿ` has, near every point, a smooth
`∂bar`-primitive. -/
theorem exists_dbar_primitive {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (a : Fin n → EuclideanSpace ℂ (Fin n) → ℂ) (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U)
    (hclosed : IsDbarClosedOn a U) {x₀ : EuclideanSpace ℂ (Fin n)} (hx₀ : x₀ ∈ U) :
    ∃ W, IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧ ∃ f : EuclideanSpace ℂ (Fin n) → ℂ,
      ContDiff ℝ ∞ f ∧ ∀ i, ∀ x ∈ W, dbarDir (basisVec i) f x = a i x :=
  exists_dbar_primitive_aux n U a x₀ hU hx₀ ha hclosed fun i hi ↦ absurd i.isLt (by omega)

end

end SGPT.Foundations.Analysis.Pending.CauchyGreen
