/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.FormDomain
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.VonNeumann
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential energy decay under a curvature bound for `P_t = exp (-t T†T)`

Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (2014), proofs of
Propositions 4.8.1 and 4.8.3, in the abstract Hilbert-space setting of `Generated`: `T` is closed
and densely defined between real Hilbert spaces, `A = T†T`, and the integrated curvature condition
is `ρ ‖T y‖² ≤ ‖A y‖²` for every `y ∈ D(A)` (for a diffusion, `∫ Γ(f) ≤ ρ⁻¹ ∫ (Lf)²`).

Under that condition the energy decays exponentially, `‖T (P_t f)‖² ≤ e^{-2ρt} ‖T f‖²` for every
`f ∈ D(T)`, and integrating `d/dt ‖P_t f‖² = -2 ‖T (P_t f)‖²` gives the finite-time bound
`‖f‖² - ‖P_t f‖² ≤ (1 - e^{-2ρt}) / ρ · ‖T f‖²` for `ρ > 0`. The limit `t → ∞` (ergodicity) is
not part of this file.
-/

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))


/-- The energy along the flow from `f ∈ D(A)` is `‖T (P_r f)‖² = ⟪P_r (A f), P_r f⟫`. -/
theorem norm_map_apply_sq_eq_inner (f : (adjointComp T).domain) {r : ℝ} (hr : 0 ≤ r) :
    ‖T ⟨apply T hT hd r f, (preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
      ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫ := by
  let x : (adjointComp T).domain :=
    ⟨apply T hT hd r f, preserves_domain T hT hd f hr⟩
  have hinner :
      ⟪adjointComp T x, (x : H₀)⟫ =
        ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (inner_adjointComp (T := T) hd x x.2.2)
  have hgen :
      adjointComp T x = apply T hT hd r (adjointComp T f) := by
    dsimp [x]
    exact generator_comm T hT hd f hr
  have hsub :
      (⟨apply T hT hd r f, (preserves_domain T hT hd f hr).2⟩ : T.domain) =
        ⟨(x : H₀), x.2.2⟩ := by
    apply Subtype.ext
    rfl
  calc
    ‖T ⟨apply T hT hd r f, (preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
        ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by rw [hsub]
    _ = ⟪adjointComp T x, (x : H₀)⟫ := hinner.symm
    _ = ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫ := by
      rw [hgen]

/-- The energy derivative: for `f ∈ D(A)` and `s > 0`,
`d/ds ⟪P_s (A f), P_s f⟫ = -2 ‖A (P_s f)‖²`. -/
theorem hasDerivAt_inner_apply (f : (adjointComp T).domain) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r => ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫)
      (-2 * ‖adjointComp T ⟨apply T hT hd s f, preserves_domain T hT hd f hs.le⟩‖ ^ 2) s := by
  let y : (adjointComp T).domain :=
    ⟨apply T hT hd s f, preserves_domain T hT hd f hs.le⟩
  let z : (adjointComp T).domain :=
    ⟨apply T hT hd s (adjointComp T f),
      mem_adjointComp_domain_apply_of_pos T hT hd (adjointComp T f) hs⟩
  have hgen : adjointComp T y = apply T hT hd s (adjointComp T f) := by
    dsimp [y]
    exact generator_comm T hT hd f hs.le
  have hz : (z : H₀) = adjointComp T y := by
    dsimp [z]
    exact hgen.symm
  have h1 :
      HasDerivAt (fun r => apply T hT hd r (adjointComp T f))
        (-adjointComp T z) s := by
    dsimp [z]
    exact hasDerivAt_apply_of_pos T hT hd (adjointComp T f) hs
  have h2 :
      HasDerivAt (fun r => apply T hT hd r (f : H₀))
        (-adjointComp T y) s := by
    dsimp [y]
    exact hasDerivAt_apply_of_pos T hT hd (f : H₀) hs
  have hsymm :
      ⟪adjointComp T z, (y : H₀)⟫ =
        ⟪(z : H₀), adjointComp T y⟫ := by
    calc
      ⟪adjointComp T z, (y : H₀)⟫ =
          ⟪T ⟨(z : H₀), z.2.2⟩, T ⟨(y : H₀), y.2.2⟩⟫ :=
        inner_adjointComp (T := T) hd z y.2.2
      _ = ⟪T ⟨(y : H₀), y.2.2⟩, T ⟨(z : H₀), z.2.2⟩⟫ := by
        rw [real_inner_comm]
      _ = ⟪adjointComp T y, (z : H₀)⟫ :=
        (inner_adjointComp (T := T) hd y z.2.2).symm
      _ = ⟪(z : H₀), adjointComp T y⟫ := by
        rw [real_inner_comm]
  have hfirst :
      ⟪apply T hT hd s (adjointComp T f), -adjointComp T y⟫ =
        -‖adjointComp T y‖ ^ 2 := by
    calc
      ⟪apply T hT hd s (adjointComp T f), -adjointComp T y⟫ =
          ⟪adjointComp T y, -adjointComp T y⟫ := by
        rw [hgen]
      _ = -⟪adjointComp T y, adjointComp T y⟫ := by
        rw [inner_neg_right]
      _ = -‖adjointComp T y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
  have hsecond :
      ⟪-adjointComp T z, apply T hT hd s f⟫ =
        -‖adjointComp T y‖ ^ 2 := by
    calc
      ⟪-adjointComp T z, apply T hT hd s f⟫ =
          -⟪adjointComp T z, (y : H₀)⟫ := by
        dsimp [y]
        rw [inner_neg_left]
      _ = -⟪(z : H₀), adjointComp T y⟫ := by
        rw [hsymm]
      _ = -⟪adjointComp T y, adjointComp T y⟫ := by
        rw [hz]
      _ = -‖adjointComp T y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
  have hder :=
    h1.inner ℝ h2
  have heq :
      ⟪apply T hT hd s (adjointComp T f), -adjointComp T y⟫ +
          ⟪-adjointComp T z, apply T hT hd s f⟫ =
        -2 * ‖adjointComp T y‖ ^ 2 := by
    rw [hfirst, hsecond]
    ring
  have hresult :
      HasDerivAt
        (fun r => ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫)
        (-2 * ‖adjointComp T y‖ ^ 2) s :=
    hder.congr_deriv heq
  simpa [y] using hresult

/-- The derivative of `r ↦ e^{-c r} E r`. -/
theorem hasDerivAt_exp_neg_mul_mul {E : ℝ → ℝ} {e c s : ℝ} (hE : HasDerivAt E e s) :
    HasDerivAt (fun r => Real.exp (-(c * r)) * E r)
      (Real.exp (-(c * s)) * (e - c * E s)) s := by
  have h1 : HasDerivAt (fun r : ℝ => -(c * r)) (-c) s := by
    simpa only [mul_one] using
      ((hasDerivAt_id' s).const_mul c).fun_neg
  have h2 := h1.exp
  exact (h2.fun_mul hE).congr_deriv (by ring)

/-- Grönwall on `[0, ∞)`: if `E` is continuous on `[0, ∞)` with `E'(s) ≤ c E(s)` for `s > 0`, then
`E t ≤ e^{c t} E 0` for `t ≥ 0`. -/
theorem le_exp_mul_of_hasDerivAt_le {E E' : ℝ → ℝ} {c : ℝ} (hc : ContinuousOn E (Ici 0))
    (hd : ∀ s, 0 < s → HasDerivAt E (E' s) s) (hle : ∀ s, 0 < s → E' s ≤ c * E s) {t : ℝ}
    (ht : 0 ≤ t) :
    E t ≤ Real.exp (c * t) * E 0 := by
  let G : ℝ → ℝ := fun r => Real.exp (-(c * r)) * E r
  have hG : ContinuousOn G (Ici 0) := by
    dsimp [G]
    exact
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).continuousOn.mul hc
  have hanti : AntitoneOn G (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Ici 0)
      (f := G)
      (f' := fun x => Real.exp (-(c * x)) * (E' x - c * E x))
      (convex_Ici (0 : ℝ)) hG ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      simpa [G] using
        (hasDerivAt_exp_neg_mul_mul (c := c) (s := x) (hd x hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact
        mul_nonpos_of_nonneg_of_nonpos
          (Real.exp_pos (-(c * x))).le (by
            linarith [hle x hx])
  have hGle : G t ≤ G 0 := by
    exact hanti (show (0 : ℝ) ∈ Ici 0 by simp) (show t ∈ Ici 0 by exact ht) ht
  have hGle' : G t ≤ E 0 := by
    simpa [G] using hGle
  have hrep : E t = Real.exp (c * t) * G t := by
    dsimp [G]
    rw [← mul_assoc, ← Real.exp_add]
    have hzero : c * t + -(c * t) = 0 := by
      ring
    rw [hzero, Real.exp_zero, one_mul]
  calc
    E t = Real.exp (c * t) * G t := hrep
    _ ≤ Real.exp (c * t) * E 0 :=
      mul_le_mul_of_nonneg_left hGle' (Real.exp_pos (c * t)).le

/-- The energy `r ↦ ⟪P_r (A f), P_r f⟫` is continuous on `[0, ∞)`. -/
theorem continuousOn_inner_apply (f : (adjointComp T).domain) :
    ContinuousOn (fun r => ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫) (Ici 0) := by
  have h₁ :
      ContinuousOn (fun r => apply T hT hd r (adjointComp T f)) (Ici 0) :=
    Generated.continuousOn T hT hd (adjointComp T f)
  have h₂ :
      ContinuousOn (fun r => apply T hT hd r (f : H₀)) (Ici 0) :=
    Generated.continuousOn T hT hd (f : H₀)
  exact h₁.inner h₂

/-- Exponential energy decay on `D(A)` under the curvature bound `ρ ‖T y‖² ≤ ‖A y‖²`. -/
theorem norm_map_apply_sq_le_exp_of_mem_adjointComp {ρ : ℝ}
    (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
    (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T ⟨apply T hT hd t f, (preserves_domain T hT hd f ht).2⟩‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
  let E : ℝ → ℝ :=
    fun r => ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫
  let E' : ℝ → ℝ := fun s =>
    if hs : 0 < s then
      -2 *
        ‖adjointComp T
          ⟨apply T hT hd s f, preserves_domain T hT hd f hs.le⟩‖ ^ 2
    else 0
  have hderiv : ∀ s, 0 < s → HasDerivAt E (E' s) s := by
    intro s hs
    have h := hasDerivAt_inner_apply T hT hd f hs
    simpa [E, E', hs] using h
  have hle : ∀ s, 0 < s → E' s ≤ (-2 * ρ) * E s := by
    intro s hs
    rw [show E' s =
        -2 *
          ‖adjointComp T
            ⟨apply T hT hd s f, preserves_domain T hT hd f hs.le⟩‖ ^ 2 by
      simp [E', hs]]
    let y : (adjointComp T).domain :=
      ⟨apply T hT hd s f, preserves_domain T hT hd f hs.le⟩
    have hnorm : ‖T ⟨y, y.2.2⟩‖ ^ 2 = E s := by
      simpa [E, y] using
        (norm_map_apply_sq_eq_inner T hT hd f hs.le)
    have hcurv' :
        ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2 :=
      hcurv y
    have hmain :
        -2 * ‖adjointComp T y‖ ^ 2 ≤
          (-2 * ρ) * ‖T ⟨y, y.2.2⟩‖ ^ 2 := by
      linarith
    calc
      -2 *
          ‖adjointComp T
            ⟨apply T hT hd s f, preserves_domain T hT hd f hs.le⟩‖ ^ 2
          ≤ -2 * ‖adjointComp T y‖ ^ 2 := by
            rfl
      _ ≤ (-2 * ρ) * ‖T ⟨y, y.2.2⟩‖ ^ 2 := hmain
      _ = (-2 * ρ) * E s := by
        rw [hnorm]
  have hgronwall :
      E t ≤ Real.exp ((-2 * ρ) * t) * E 0 :=
    le_exp_mul_of_hasDerivAt_le
      (E := E) (E' := E') (c := -2 * ρ)
      (continuousOn_inner_apply T hT hd f)
      hderiv hle ht
  have hzero : E 0 = ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
    calc
      E 0 = ⟪adjointComp T f, (f : H₀)⟫ := by
        dsimp [E]
        rw [Generated.zero_time T hT hd (adjointComp T f)]
        rw [Generated.zero_time T hT hd (f : H₀)]
      _ = ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
        rw [inner_adjointComp (T := T) hd f f.2.2]
        rw [real_inner_self_eq_norm_sq]
  calc
    ‖T ⟨apply T hT hd t f, (preserves_domain T hT hd f ht).2⟩‖ ^ 2 =
        E t := by
          simpa [E] using
            (norm_map_apply_sq_eq_inner T hT hd f ht)
    _ ≤ Real.exp ((-2 * ρ) * t) * E 0 := hgronwall
    _ = Real.exp (-2 * ρ * t) * ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
      rw [hzero]

/-- Exponential energy decay on the whole form domain `D(T)` under the curvature bound. -/
theorem norm_map_apply_sq_le_exp {ρ : ℝ}
    (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
    (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T ⟨apply T hT hd t f, preserves_form_domain T hT hd f ht⟩‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2 := by
  obtain ⟨u, hu, hu₁, hu₂⟩ :=
    exists_seq_mem_adjointComp_domain_tendsto_graph T hT hd f
  let v : ℕ → T.domain := fun n =>
    ⟨u n - (f : H₀), T.domain.sub_mem (hu n).2 f.2⟩
  let q : ℕ → T.domain := fun n =>
    ⟨apply T hT hd t (u n),
      preserves_form_domain T hT hd ⟨u n, (hu n).2⟩ ht⟩
  let q₀ : T.domain :=
    ⟨apply T hT hd t (f : H₀), preserves_form_domain T hT hd f ht⟩
  have hmap_sub : ∀ n, T (v n) =
      T ⟨u n, (hu n).2⟩ - T f := by
    intro n
    dsimp [v]
    exact T.map_sub ⟨u n, (hu n).2⟩ f
  have happly_sub : ∀ n,
      apply T hT hd t (u n - (f : H₀)) =
        apply T hT hd t (u n) - apply T hT hd t (f : H₀) := by
    intro n
    exact Generated.map_sub T hT hd ht (u n) (f : H₀)
  have hq_sub : ∀ n, q n - q₀ =
      ⟨apply T hT hd t (u n - (f : H₀)),
        preserves_form_domain T hT hd (v n) ht⟩ := by
    intro n
    apply Subtype.ext
    dsimp [q, q₀, v]
    exact (happly_sub n).symm
  have hbound : ∀ n,
      ‖T (q n) - T q₀‖ ≤ ‖T (v n)‖ := by
    intro n
    calc
      ‖T (q n) - T q₀‖ = ‖T (q n - q₀)‖ := by
        rw [T.map_sub]
      _ = ‖T ⟨apply T hT hd t (u n - (f : H₀)),
          preserves_form_domain T hT hd (v n) ht⟩‖ := by
        rw [hq_sub n]
      _ ≤ ‖T (v n)‖ :=
        norm_map_apply_le T hT hd (v n) ht
          (preserves_form_domain T hT hd (v n) ht)
  have hsub :
      Tendsto
        (fun n => T ⟨u n, (hu n).2⟩ - T f)
        atTop (𝓝 (T f - T f)) := by
    have hconst :
        Tendsto (fun _ : ℕ => T f) atTop (𝓝 (T f)) :=
      tendsto_const_nhds
    exact hu₂.sub hconst
  have hv_tendsto :
      Tendsto (fun n => T (v n)) atTop (𝓝 0) := by
    have h := hsub
    simpa only [hmap_sub, sub_self] using h
  have hv_norm :
      Tendsto (fun n => ‖T (v n)‖) atTop (𝓝 0) := by
    simpa using hv_tendsto.norm
  have hdiff_norm :
      Tendsto (fun n => ‖T (q n) - T q₀‖) atTop (𝓝 0) := by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hv_norm
    · filter_upwards with n
      exact norm_nonneg _
    · exact Filter.Eventually.of_forall hbound
  have hdiff :
      Tendsto (fun n => T (q n) - T q₀) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hdiff_norm
  have hq :
      Tendsto (fun n => T (q n)) atTop (𝓝 (T q₀)) := by
    have hconst :
        Tendsto (fun _ : ℕ => T q₀) atTop (𝓝 (T q₀)) :=
      tendsto_const_nhds
    have h := hdiff.add hconst
    simpa only [sub_add_cancel, zero_add] using h
  have hleft :
      Tendsto (fun n => ‖T (q n)‖ ^ 2) atTop (𝓝 (‖T q₀‖ ^ 2)) := by
    simpa using hq.norm.pow 2
  have hright :
      Tendsto
        (fun n => Real.exp (-2 * ρ * t) *
          ‖T ⟨u n, (hu n).2⟩‖ ^ 2)
        atTop
        (𝓝 (Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2)) := by
    have hnorm :
        Tendsto (fun n => ‖T ⟨u n, (hu n).2⟩‖ ^ 2) atTop
          (𝓝 (‖T f‖ ^ 2)) := by
      simpa using hu₂.norm.pow 2
    simpa using tendsto_const_nhds.mul hnorm
  have hle : ∀ n,
      ‖T (q n)‖ ^ 2 ≤
        Real.exp (-2 * ρ * t) * ‖T ⟨u n, (hu n).2⟩‖ ^ 2 := by
    intro n
    simpa [q] using
      (norm_map_apply_sq_le_exp_of_mem_adjointComp
        T hT hd hcurv ⟨u n, hu n⟩ ht)
  have hlimit :
      ‖T q₀‖ ^ 2 ≤ Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2 := by
    exact
      tendsto_le_of_eventuallyLE hleft hright
        (Filter.Eventually.of_forall hle)
  simpa [q₀] using hlimit

/-- The finite-time Poincaré bound under the curvature bound with `ρ > 0`: for `f ∈ D(T)` and
`t ≥ 0`, `‖f‖² - ‖P_t f‖² ≤ (1 - e^{-2ρt}) / ρ · ‖T f‖²`. -/
theorem norm_sq_sub_norm_apply_sq_le {ρ : ℝ} (hρ : 0 < ρ)
    (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
    (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖(f : H₀)‖ ^ 2 - ‖apply T hT hd t f‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ * ‖T f‖ ^ 2 := by
  let E0 : ℝ := ‖T f‖ ^ 2
  let φ : ℝ → ℝ := fun s =>
    ‖apply T hT hd s (f : H₀)‖ ^ 2 -
      Real.exp (-2 * ρ * s) * (E0 / ρ)
  have hcont_exp :
      ContinuousOn (fun s : ℝ => Real.exp (-2 * ρ * s)) (Ici 0) := by
    have harg : Continuous (fun s : ℝ => -2 * ρ * s) := by
      have hmul :
          Continuous (fun s : ℝ => (-2 * ρ) * s) :=
        (continuous_const.mul continuous_id :
          Continuous (fun s : ℝ => (-2 * ρ) * s))
      simpa [mul_assoc] using hmul
    have hcomp :
        Continuous (fun s : ℝ => Real.exp ((fun x : ℝ => -2 * ρ * x) s)) :=
      Real.continuous_exp.comp harg
    simpa only [Function.comp_apply] using hcomp.continuousOn
  have hcont : ContinuousOn φ (Ici 0) := by
    have hnorm :
        ContinuousOn
          (fun s : ℝ => ‖apply T hT hd s (f : H₀)‖ ^ 2) (Ici 0) :=
      (Generated.continuousOn T hT hd (f : H₀)).norm.pow 2
    have hterm :
        ContinuousOn
          (fun s : ℝ => Real.exp (-2 * ρ * s) * (E0 / ρ)) (Ici 0) :=
      hcont_exp.mul continuousOn_const
    exact hnorm.sub hterm
  let D : ℝ → ℝ := fun s =>
    if hs : 0 < s then
      -2 *
          ‖T ⟨apply T hT hd s (f : H₀),
            preserves_form_domain T hT hd f hs.le⟩‖ ^ 2 +
        2 * Real.exp (-2 * ρ * s) * E0
    else 0
  have hderiv : ∀ s, 0 < s → HasDerivAt φ (D s) s := by
    intro s hs
    let z : (adjointComp T).domain :=
      ⟨apply T hT hd s (f : H₀),
        mem_adjointComp_domain_apply_of_pos T hT hd (f : H₀) hs⟩
    have hinner :
        ⟪apply T hT hd s (f : H₀), -adjointComp T z⟫ =
          -‖T ⟨apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2 := by
      calc
        ⟪apply T hT hd s (f : H₀), -adjointComp T z⟫ =
            -⟪apply T hT hd s (f : H₀), adjointComp T z⟫ := by
              rw [inner_neg_right]
        _ = -⟪adjointComp T z, apply T hT hd s (f : H₀)⟫ := by
              rw [real_inner_comm]
        _ = -⟪T ⟨(z : H₀), z.2.2⟩, T ⟨(z : H₀), z.2.2⟩⟫ := by
              rw [inner_adjointComp (T := T) hd z z.2.2]
        _ = -‖T ⟨(z : H₀), z.2.2⟩‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
        _ = -‖T ⟨apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2 := by
              rfl
    have hnorm :
        HasDerivAt
          (fun r : ℝ => ‖apply T hT hd r (f : H₀)‖ ^ 2)
          (-2 * ‖T ⟨apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2) s := by
      have h :=
        (hasDerivAt_apply_of_pos T hT hd (f : H₀) hs).norm_sq
      exact h.congr_deriv (by
        rw [hinner]
        ring)
    have harg :
        HasDerivAt (fun r : ℝ => -(2 * ρ * r)) (-(2 * ρ)) s := by
      simpa only [mul_one] using
        ((hasDerivAt_id' s).const_mul (2 * ρ)).fun_neg
    have hexp :
        HasDerivAt (fun r : ℝ => Real.exp (-(2 * ρ * r)))
          (Real.exp (-(2 * ρ * s)) * (-(2 * ρ))) s :=
      harg.exp
    have hconst :
        HasDerivAt (fun _ : ℝ => E0 / ρ) 0 s :=
      hasDerivAt_const (x := s) (c := E0 / ρ)
    have hterm :
        HasDerivAt
          (fun r : ℝ => Real.exp (-(2 * ρ * r)) * (E0 / ρ))
          (-2 * Real.exp (-(2 * ρ * s)) * E0) s := by
      have h := hexp.fun_mul hconst
      exact h.congr_deriv (by
        field_simp [hρ.ne']
        ring)
    have hsub := hnorm.sub hterm
    have hsub' :
        HasDerivAt
          (fun r : ℝ =>
            ‖apply T hT hd r (f : H₀)‖ ^ 2 -
              Real.exp (-(2 * ρ * r)) * (E0 / ρ))
          (-2 * ‖T ⟨apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2 +
            2 * Real.exp (-(2 * ρ * s)) * E0) s :=
      hsub.congr_deriv (by ring)
    simpa [φ, D, hs, z] using hsub'
  have hnonneg : ∀ s ∈ interior (Ici (0 : ℝ)), 0 ≤ D s := by
    intro s hs
    have hs' : 0 < s := by
      simpa [interior_Ici] using hs
    dsimp [D]
    rw [dite_eq_left hs']
    have hdec :=
      norm_map_apply_sq_le_exp T hT hd hcurv f hs'.le
    have hdec' :
        ‖T ⟨apply T hT hd s (f : H₀),
            preserves_form_domain T hT hd f hs'.le⟩‖ ^ 2 ≤
          Real.exp (-2 * ρ * s) * E0 := by
      simpa [E0] using hdec
    linarith
  have hmono : MonotoneOn φ (Ici (0 : ℝ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Ici (0 : ℝ)) (f := φ) (f' := D)
      (convex_Ici (0 : ℝ)) hcont ?_ hnonneg
    intro s hs
    have hs' : 0 < s := by
      simpa [interior_Ici] using hs
    exact (hderiv s hs').hasDerivWithinAt
  have hφ : φ 0 ≤ φ t := by
    exact hmono (by simp) ht ht
  have hφ' :
      ‖(f : H₀)‖ ^ 2 - E0 / ρ ≤
        ‖apply T hT hd t (f : H₀)‖ ^ 2 -
          Real.exp (-2 * ρ * t) * (E0 / ρ) := by
    have hzero := Generated.zero_time T hT hd (f : H₀)
    simpa [φ, hzero, Real.exp_zero] using hφ
  have hmain :
      ‖(f : H₀)‖ ^ 2 - ‖apply T hT hd t (f : H₀)‖ ^ 2 ≤
        E0 / ρ - Real.exp (-2 * ρ * t) * (E0 / ρ) := by
    linarith
  calc
    ‖(f : H₀)‖ ^ 2 - ‖apply T hT hd t f‖ ^ 2
        ≤ E0 / ρ - Real.exp (-2 * ρ * t) * (E0 / ρ) := by
          simpa using hmain
    _ = (1 - Real.exp (-2 * ρ * t)) / ρ * ‖T f‖ ^ 2 := by
      dsimp [E0]
      field_simp [hρ.ne']

end FunctionalInequalities.Analysis.Semigroup.Generated
