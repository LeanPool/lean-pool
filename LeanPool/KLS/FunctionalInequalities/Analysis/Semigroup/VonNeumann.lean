/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.AdjointComp
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic

/-!
# von Neumann's theorem for `T†T`

For a closed densely defined operator
`T : H₀ →ₗ.[ℝ] H₁` between real Hilbert spaces.  `T†T` is `Analysis.Semigroup.adjointComp T`
(`AdjointComp.lean`) and `J_s = (1 + s T†T)⁻¹` is `Analysis.Semigroup.resolventCLM`
(`Resolvent/Basic.lean`, built from the weak equation `WeakResolvent` of `Form.lean`).

What is proved here:

* the form identity = `inner_adjointComp` / `inner_adjointComp_apply`: `⟪T†T x, y⟫ = ⟪T x, T y⟫` for
  `x ∈ D(T†T)`, `y ∈ D(T)`;
* the resolvent domain identity = `resolvent_add_smul_adjointComp` (with the two halves
  `mem_adjointComp_domain_resolventDomain` and `adjointComp_resolventDomain`):
  `J_s f ∈ D(T†T)` and `(1 + s T†T) J_s f = f`;
* self-adjointness of T†T = `isSelfAdjoint_adjointComp`: `T†T` is self-adjoint;
* density of D(T†T) = `dense_adjointComp_domain`: `D(T†T)` is dense;
* the resolvent defect identity = `sub_resolvent_eq_smul`: `f - J_s f = s • J_s (T†T f)` for `f ∈
  D(T†T)`.

Two further consequences of the form identity concern `J = I + T†T` on `{e ∈ D(T†T) : T†T e ∈
D(T)}`:
the expansion `norm_add_adjointComp_sq_add_norm_sq` of its graph norm,
`‖Je‖² + ‖T(Je)‖² = ‖e‖² + 3‖Te‖² + 3‖T†Te‖² + ‖T(T†Te)‖²`, and the resulting four-field
convergence `tendsto_of_tendsto_add_adjointComp`.

## Scope of the individual statements

Following the precedent of `Form.lean` (the shifted weak form drops `0 < s`, resolvent solvability
drops `Dense`) and
`Resolvent/Basic.lean` (resolvent contraction drops self-adjointness), hypotheses that turn out
to be
unnecessary are
**not** assumed:

* the form identity is proved without `T.IsClosed` and
  without `CompleteSpace H₁`: `inner_adjointComp` and the wrapper
  `inner_adjointComp_apply` live in the section before `CompleteSpace H₁` is introduced.  Only
  density of `D(T)` is used, and it is genuinely needed because Mathlib's `LinearPMap.adjoint`
  carries a junk value on a non-dense domain.
* The domain half of the resolvent domain identity, `mem_adjointComp_domain_resolventDomain`, needs
  **no density**: that
  `T (J_s f) ∈ D(T†)` follows from `mem_adjoint_domain_of_exists` applied to the weak equation,
  and only the identification of the value `T† (T (J_s f)) = s⁻¹ (f - J_s f)`
  (`adjointComp_resolventDomain`) uses `adjoint_apply_eq`, hence density.

## Order of the arguments

Deriving density of D(T†T) from self-adjointness of T†T via
`IsSelfAdjoint.dense_domain` would be circular here: `LinearPMap.IsFormalAdjoint.le_adjoint`, which
turns symmetry of `T†T` into
`T†T ≤ (T†T)†`, already requires `D(T†T)` to be dense.  So density of D(T†T) is proved first, by the
direct
argument (if `g ⊥ D(T†T)` then `g = u + T†T u` with `u = J_1 g`, and
`0 = ⟪u, g⟫ = ‖u‖² + ‖T u‖²`), and self-adjointness of T†T is then derived from it.

## Deliberately out of scope

Nothing here proves the adjoint-product identification or the semigroup limit (Yosida exponentials,
their strong convergence, the semigroup), nothing proves the quantitative resolvent bound,
resolvent commutation or the resolvent limits, and
nothing here concerns Buser's inequality, the Markov property, Bakry–Émery calculus or any KLS
quantity.  This module is general real Hilbert space material: no measure, no log-concavity.
-/

@[expose] public section
noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace LinearPMap

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]

/-- the form identity: `T†T` acts through the form.

For `x ∈ D(T†T)` and `y ∈ D(T)` one has `⟪T†T x, y⟫ = ⟪T x, T y⟫`.  This is
`LinearPMap.adjoint_isFormalAdjoint` read through `adjointComp_apply`; density of `D(T)` is
needed because Mathlib's adjoint is a junk value otherwise.  Neither `T.IsClosed` nor
completeness of `H₁` is used.  The membership of `y` is taken as a hypothesis rather than
packaged into a subtype, so that the lemma rewrites against goals mentioning a bare `y : H₀`. -/
theorem inner_adjointComp {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀))
    (x : (adjointComp T).domain) {y : H₀} (hy : y ∈ T.domain) :
    ⟪adjointComp T x, y⟫ = ⟪T ⟨(x : H₀), x.2.2⟩, T ⟨y, hy⟩⟫ := by
  rw [adjointComp_apply]
  exact LinearPMap.adjoint_isFormalAdjoint hd _ ⟨y, hy⟩

/-- The form identity, in pairing form: the version of
`inner_adjointComp` with `y` presented as an element of `T.domain`. -/
theorem inner_adjointComp_apply (T : H₀ →ₗ.[ℝ] H₁) (hd : Dense (T.domain : Set H₀))
    (x : (adjointComp T).domain) (y : T.domain) :
    ⟪adjointComp T x, (y : H₀)⟫ = ⟪T ⟨(x : H₀), x.2.2⟩, T y⟫ :=
  inner_adjointComp hd x y.2

/-- The Dirichlet form of `T†T`: for `x ∈ D(T†T)`, `⟪T†T x, x⟫ = ‖T x‖ ^ 2`.

the form identity with `y = x`, which is legitimate because `D(T†T) ⊆ D(T)`.  This is the form that
the
semigroup contracts; `FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq` is its
specialization to the closed weighted gradient.  Neither `T.IsClosed` nor completeness of `H₁`
is used. -/
theorem inner_adjointComp_self {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀))
    (x : (adjointComp T).domain) : ⟪adjointComp T x, (x : H₀)⟫ = ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by
  rw [inner_adjointComp hd x x.2.2, real_inner_self_eq_norm_sq]

/-- `T†T` is symmetric: it is a formal adjoint of itself.

Both sides of `⟪T†T x, y⟫ = ⟪x, T†T y⟫` equal `⟪T x, T y⟫` by the form identity, the right-hand one
after a
real inner-product flip.  This is the input that `LinearPMap.IsFormalAdjoint.le_adjoint` turns
into `T†T ≤ (T†T)†` once `D(T†T)` is known to be dense. -/
theorem adjointComp_isFormalAdjoint {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀)) :
    (adjointComp T).IsFormalAdjoint (adjointComp T) := by
  intro x y
  rw [inner_adjointComp hd x y.2.2, ← real_inner_comm ((x : H₀)) (adjointComp T y),
    inner_adjointComp hd y x.2.2]
  exact real_inner_comm _ _

/-- **The graph norm of `(I + T†T) e`.** For `e ∈ D(T†T)` with `T†T e ∈ D(T)`,
`‖e + T†T e‖² + ‖T e + T (T†T e)‖² = ‖e‖² + 3 ‖T e‖² + 3 ‖T†T e‖² + ‖T (T†T e)‖²`.

Both cross terms are the form identity: `⟪e, T†T e⟫ = ‖T e‖²` and `⟪T e, T (T†T e)⟫ = ‖T†T e‖²`.
Only
density of `D(T)` is used. -/
theorem norm_add_adjointComp_sq_add_norm_sq {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀))
    (e : (adjointComp T).domain) (he : (adjointComp T e : H₀) ∈ T.domain) :
    ‖(e : H₀) + adjointComp T e‖ ^ 2 + ‖T ⟨(e : H₀), e.2.2⟩ + T ⟨_, he⟩‖ ^ 2 =
      ‖(e : H₀)‖ ^ 2 + 3 * ‖T ⟨(e : H₀), e.2.2⟩‖ ^ 2 + 3 * ‖adjointComp T e‖ ^ 2 +
        ‖T ⟨_, he⟩‖ ^ 2 := by
  have h₁ : ⟪(e : H₀), adjointComp T e⟫ = ‖T ⟨(e : H₀), e.2.2⟩‖ ^ 2 := by
    rw [real_inner_comm, inner_adjointComp_self hd]
  have h₂ : ⟪T ⟨(e : H₀), e.2.2⟩, T ⟨_, he⟩⟫ = ‖adjointComp T e‖ ^ 2 := by
    rw [← inner_adjointComp hd e he, real_inner_self_eq_norm_sq]
  rw [norm_add_sq_real, norm_add_sq_real, h₁, h₂]
  ring

open Filter Topology in
/-- **Four-field convergence from the graph norm of `I + T†T`.** Let `xₙ, F ∈ D(T†T)` with
`T†T xₙ, T†T F ∈ D(T)`. If `xₙ + T†T xₙ → F + T†T F` and
`T xₙ + T (T†T xₙ) → T F + T (T†T F)`, then `xₙ → F`, `T xₙ → T F`, `T†T xₙ → T†T F` and
`T (T†T xₙ) → T (T†T F)`. This is `norm_add_adjointComp_sq_add_norm_sq` applied to
`xₙ - F`; only density of `D(T)` is used. -/
theorem tendsto_of_tendsto_add_adjointComp {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀))
    {x : ℕ → (adjointComp T).domain} (hx : ∀ n, (adjointComp T (x n) : H₀) ∈ T.domain)
    (F : (adjointComp T).domain) (hF : (adjointComp T F : H₀) ∈ T.domain)
    (h₁ : Tendsto (fun n => (x n : H₀) + adjointComp T (x n)) atTop
      (𝓝 ((F : H₀) + adjointComp T F)))
    (h₂ : Tendsto (fun n => T ⟨(x n : H₀), (x n).2.2⟩ + T ⟨_, hx n⟩) atTop
      (𝓝 (T ⟨(F : H₀), F.2.2⟩ + T ⟨_, hF⟩))) :
    Tendsto (fun n => (x n : H₀)) atTop (𝓝 (F : H₀)) ∧
      Tendsto (fun n => T ⟨(x n : H₀), (x n).2.2⟩) atTop (𝓝 (T ⟨(F : H₀), F.2.2⟩)) ∧
      Tendsto (fun n => adjointComp T (x n)) atTop (𝓝 (adjointComp T F)) ∧
      Tendsto (fun n => T ⟨_, hx n⟩) atTop (𝓝 (T ⟨_, hF⟩)) := by
  have hAe (n : ℕ) : adjointComp T (x n - F) = adjointComp T (x n) - adjointComp T F :=
    LinearPMap.map_sub _ _ _
  have he (n : ℕ) : (adjointComp T (x n - F) : H₀) ∈ T.domain := by
    rw [hAe]; exact T.domain.sub_mem (hx n) hF
  have hTe (n : ℕ) : T ⟨((x n - F : (adjointComp T).domain) : H₀), (x n - F).2.2⟩ =
      T ⟨(x n : H₀), (x n).2.2⟩ - T ⟨(F : H₀), F.2.2⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  have hTAe (n : ℕ) : T ⟨_, he n⟩ = T ⟨_, hx n⟩ - T ⟨_, hF⟩ := by
    rw [← LinearPMap.map_sub]
    congr 1
    exact Subtype.ext (by simp only [hAe, Submodule.coe_sub])
  set S : ℕ → ℝ := fun n =>
    ‖((x n - F : (adjointComp T).domain) : H₀) + adjointComp T (x n - F)‖ ^ 2 +
      ‖T ⟨_, (x n - F).2.2⟩ + T ⟨_, he n⟩‖ ^ 2 with hSdef
  have hS : Tendsto S atTop (𝓝 0) := by
    have ha (n : ℕ) : ((x n - F : (adjointComp T).domain) : H₀) + adjointComp T (x n - F) =
        ((x n : H₀) + adjointComp T (x n)) - ((F : H₀) + adjointComp T F) := by
      rw [hAe, Submodule.coe_sub]; abel
    have hb (n : ℕ) : T ⟨_, (x n - F).2.2⟩ + T ⟨_, he n⟩ =
        (T ⟨(x n : H₀), (x n).2.2⟩ + T ⟨_, hx n⟩) - (T ⟨(F : H₀), F.2.2⟩ + T ⟨_, hF⟩) := by
      rw [hTe, hTAe]; abel
    have h₁' := (tendsto_iff_norm_sub_tendsto_zero.mp h₁).pow 2
    have h₂' := (tendsto_iff_norm_sub_tendsto_zero.mp h₂).pow 2
    have hsum := h₁'.add h₂'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hsum
    refine hsum.congr fun n => ?_
    simp only [hSdef, ha, hb]
  have hkey (n : ℕ) := norm_add_adjointComp_sq_add_norm_sq hd (x n - F) (he n)
  have hsq {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hle : ∀ n, a n ^ 2 ≤ S n) :
      Tendsto a atTop (𝓝 0) := by
    have hr : Tendsto (fun n => √(S n)) atTop (𝓝 0) := by
      simpa using hS.sqrt
    refine squeeze_zero ha (fun n => ?_) hr
    rw [← Real.sqrt_sq (ha n)]
    exact Real.sqrt_le_sqrt (hle n)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tendsto_iff_norm_sub_tendsto_zero.mpr (hsq (fun n => norm_nonneg _) fun n => ?_)
    rw [← Submodule.coe_sub]
    nlinarith [hkey n, sq_nonneg ‖T ⟨_, (x n - F).2.2⟩‖, sq_nonneg ‖adjointComp T (x n - F)‖,
      sq_nonneg ‖T ⟨_, he n⟩‖]
  · refine tendsto_iff_norm_sub_tendsto_zero.mpr (hsq (fun n => norm_nonneg _) fun n => ?_)
    rw [← hTe]
    nlinarith [hkey n, sq_nonneg ‖((x n - F : (adjointComp T).domain) : H₀)‖,
      sq_nonneg ‖adjointComp T (x n - F)‖, sq_nonneg ‖T ⟨_, he n⟩‖]
  · refine tendsto_iff_norm_sub_tendsto_zero.mpr (hsq (fun n => norm_nonneg _) fun n => ?_)
    rw [← hAe]
    nlinarith [hkey n, sq_nonneg ‖((x n - F : (adjointComp T).domain) : H₀)‖,
      sq_nonneg ‖T ⟨_, (x n - F).2.2⟩‖, sq_nonneg ‖T ⟨_, he n⟩‖]
  · refine tendsto_iff_norm_sub_tendsto_zero.mpr (hsq (fun n => norm_nonneg _) fun n => ?_)
    rw [← hTAe]
    nlinarith [hkey n, sq_nonneg ‖((x n - F : (adjointComp T).domain) : H₀)‖,
      sq_nonneg ‖T ⟨_, (x n - F).2.2⟩‖, sq_nonneg ‖adjointComp T (x n - F)‖]

open Filter Topology in
/-- Graph convergence for `T†T` gives convergence of `T`: if `xₙ → y` and `T†T xₙ → T†T y`, then
`T xₙ → T y`, because `‖T (xₙ - y)‖² = ⟪T†T (xₙ - y), xₙ - y⟫`. -/
theorem tendsto_apply_of_tendsto_adjointComp {T : H₀ →ₗ.[ℝ] H₁}
    (hd : Dense (T.domain : Set H₀)) {x : ℕ → (adjointComp T).domain}
    {y : (adjointComp T).domain} (h0 : Tendsto (fun n => (x n : H₀)) atTop (𝓝 (y : H₀)))
    (h1 : Tendsto (fun n => adjointComp T (x n)) atTop (𝓝 (adjointComp T y))) :
    Tendsto (fun n => T ⟨(x n : H₀), (x n).2.2⟩) atTop (𝓝 (T ⟨(y : H₀), y.2.2⟩)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key (n : ℕ) : ‖T ⟨(x n : H₀), (x n).2.2⟩ - T ⟨(y : H₀), y.2.2⟩‖ ^ 2 ≤
      ‖adjointComp T (x n) - adjointComp T y‖ * ‖(x n : H₀) - y‖ := by
    have hTe : T ⟨((x n - y : (adjointComp T).domain) : H₀), (x n - y).2.2⟩ =
        T ⟨(x n : H₀), (x n).2.2⟩ - T ⟨(y : H₀), y.2.2⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    have hAe : adjointComp T (x n - y) = adjointComp T (x n) - adjointComp T y :=
      LinearPMap.map_sub _ _ _
    rw [← hTe, ← inner_adjointComp_self hd, hAe, Submodule.coe_sub]
    exact real_inner_le_norm _ _
  have hlim : Tendsto (fun n => ‖adjointComp T (x n) - adjointComp T y‖ * ‖(x n : H₀) - y‖)
      atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 h1).mul
      (tendsto_iff_norm_sub_tendsto_zero.1 h0)
  have hsq := squeeze_zero (fun n => by positivity) key hlim
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

section Resolvent

variable [CompleteSpace H₁]

/-- the resolvent domain identity, domain half: the weak solution `J_s f` lies in `D(T†T)`.

From the weak equation `⟪u, v⟫ + s ⟪T u, T v⟫ = ⟪f, v⟫` the vector `T u` pairs continuously
against `T v`, with representative `w = s⁻¹ (f - u)`, so `T u ∈ D(T†)` by
`LinearPMap.mem_adjoint_domain_of_exists`.  **Density of `D(T)` is not needed for this half**
(see the module docstring). -/
theorem mem_adjointComp_domain_resolventDomain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    {s : ℝ} (hs : 0 < s) (f : H₀) :
    ((resolventDomain T hT hs f : H₀)) ∈ (adjointComp T).domain := by
  set u := resolventDomain T hT hs f with hu
  refine ⟨mem_adjointCompDomain.mpr ⟨u.2, ?_⟩, u.2⟩
  have hue : (⟨(u : H₀), u.2⟩ : T.domain) = u := rfl
  rw [hue]
  refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨s⁻¹ • (f - (u : H₀)), ?_⟩
  intro v
  have h := resolventDomain_spec T hT hs f v
  rw [← hu] at h
  rw [real_inner_smul_left, inner_sub_left]
  field_simp
  linarith

/-- the resolvent domain identity, value half: `T† (T (J_s f)) = s⁻¹ (f - J_s f)`.

The same representative `w = s⁻¹ (f - u)` that witnesses membership in `D(T†)` is the value of
the adjoint, by `LinearPMap.adjoint_apply_eq`; this step does use density of `D(T)`.  The
membership proof is taken as an argument so that the statement does not depend on how it was
produced. -/
theorem adjointComp_resolventDomain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : H₀)
    (hmem : ((resolventDomain T hT hs f : H₀)) ∈ (adjointComp T).domain) :
    adjointComp T ⟨(resolventDomain T hT hs f : H₀), hmem⟩
      = s⁻¹ • (f - (resolventDomain T hT hs f : H₀)) := by
  set u := resolventDomain T hT hs f with hu
  rw [adjointComp_apply]
  refine LinearPMap.adjoint_apply_eq hd _ ?_
  intro v
  have h := resolventDomain_spec T hT hs f v
  rw [← hu] at h
  change ⟪s⁻¹ • (f - (u : H₀)), (v : H₀)⟫ = ⟪T u, T v⟫
  rw [real_inner_smul_left, inner_sub_left]
  field_simp
  linarith

/-- the resolvent domain identity: the resolvent inverts `1 + s T†T`.

For `s > 0` and every datum `f`, the weak solution `J_s f` lies in `D(T†T)` and satisfies
`J_s f + s • T†T (J_s f) = f`.  It is assembled from
`mem_adjointComp_domain_resolventDomain` and `adjointComp_resolventDomain`. -/
theorem resolvent_add_smul_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : H₀) :
    ∃ hu : resolventCLM T hT hs f ∈ (adjointComp T).domain,
      resolventCLM T hT hs f + s • adjointComp T ⟨resolventCLM T hT hs f, hu⟩ = f := by
  refine ⟨mem_adjointComp_domain_resolventDomain T hT hs f, ?_⟩
  change (resolventDomain T hT hs f : H₀) + s • adjointComp T
      ⟨(resolventDomain T hT hs f : H₀), mem_adjointComp_domain_resolventDomain T hT hs f⟩ = f
  rw [adjointComp_resolventDomain T hT hd hs f, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  abel

/-- `1 + T†T` is surjective: every `z : H₀` is `x + T†T x` for some `x ∈ D(T†T)`.

This is the resolvent domain identity at `s = 1`, and it is the only consequence of the resolvent
domain identity used in the proofs of self-adjointness of T†T and
density of D(T†T). -/
theorem exists_add_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (z : H₀) :
    ∃ x : (adjointComp T).domain, (x : H₀) + adjointComp T x = z := by
  have h1 : (0 : ℝ) < 1 := zero_lt_one
  refine
    ⟨⟨(resolventDomain T hT h1 z : H₀), mem_adjointComp_domain_resolventDomain T hT h1 z⟩, ?_⟩
  rw [adjointComp_resolventDomain T hT hd h1 z]
  rw [inv_one, one_smul]
  abel

/-- density of D(T†T): `D(T†T)` is dense.

Proved directly, not from self-adjointness of T†T (see the module docstring for why the other order
is not
available).  If `g` is orthogonal to `D(T†T)`, write `g = x + T†T x` with `x ∈ D(T†T)` by
surjectivity of `1 + T†T`; then `0 = ⟪x, g⟫ = ‖x‖² + ‖T x‖²` by the form identity, so `x = 0` and `g
= 0`.
A submodule of a complete inner product space with trivial orthogonal complement is dense. -/
theorem dense_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) :
    Dense (((adjointComp T).domain : Submodule ℝ H₀) : Set H₀) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  obtain ⟨x, hx⟩ := exists_add_adjointComp T hT hd g
  have hzero : ⟪(x : H₀), g⟫ = 0 := hg (x : H₀) x.2
  rw [← hx, inner_add_right, ← real_inner_comm ((x : H₀)) (adjointComp T x),
    inner_adjointComp hd x x.2.2, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hzero
  have hxz : (x : H₀) = 0 := by
    have : ‖(x : H₀)‖ = 0 := by
      nlinarith [norm_nonneg (x : H₀), sq_nonneg ‖T ⟨(x : H₀), x.2.2⟩‖]
    simpa using this
  have hx0 : x = 0 := Subtype.ext hxz
  rw [← hx, hx0]
  simp

/-- self-adjointness of T†T (von Neumann): `T†T` is self-adjoint.

Symmetry (`adjointComp_isFormalAdjoint`) together with density of `D(T†T)` (density of D(T†T)) gives
`T†T ≤ (T†T)†`.  For the reverse inclusion take `y ∈ D((T†T)†)`, solve `u + T†T u = y + (T†T)† y`
with `u ∈ D(T†T)` by surjectivity of `1 + T†T`, and test against an arbitrary `z = x + T†T x`:
both `⟪z, y⟫` and `⟪z, u⟫` collapse to `⟪x, y + (T†T)† y⟫`, so `y - u` is orthogonal to all of
`H₀` and therefore `y = u ∈ D(T†T)`, with `(T†T)† y = T†T u`.  The two inclusions have equal
domains, so `LinearPMap.eq_of_le_of_domain_eq` finishes. -/
theorem isSelfAdjoint_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) : IsSelfAdjoint (adjointComp T) := by
  have hdA := dense_adjointComp_domain T hT hd
  have hsym := adjointComp_isFormalAdjoint hd
  have hle : adjointComp T ≤ (adjointComp T)† := hsym.le_adjoint hdA
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdA (T := adjointComp T)
  have key : ∀ y : ((adjointComp T)†).domain, ∃ hm : (y : H₀) ∈ (adjointComp T).domain,
      adjointComp T ⟨(y : H₀), hm⟩ = (adjointComp T)† y := by
    intro y
    obtain ⟨u, hueq⟩ := exists_add_adjointComp T hT hd ((y : H₀) + (adjointComp T)† y)
    have hperp : ∀ z : H₀, ⟪z, (y : H₀) - (u : H₀)⟫ = 0 := by
      intro z
      obtain ⟨x, hxeq⟩ := exists_add_adjointComp T hT hd z
      have e1 : ⟪adjointComp T x, (y : H₀)⟫ = ⟪(x : H₀), (adjointComp T)† y⟫ := by
        rw [← real_inner_comm (adjointComp T x) ((y : H₀)), ← hfa y x]
        exact real_inner_comm _ _
      have e2 : ⟪adjointComp T x, (u : H₀)⟫ = ⟪(x : H₀), adjointComp T u⟫ := hsym x u
      have ea : ⟪(x : H₀) + adjointComp T x, (y : H₀)⟫
          = ⟪(x : H₀), (y : H₀) + (adjointComp T)† y⟫ := by
        rw [inner_add_left, inner_add_right, e1]
      have eb : ⟪(x : H₀) + adjointComp T x, (u : H₀)⟫
          = ⟪(x : H₀), (y : H₀) + (adjointComp T)† y⟫ := by
        rw [inner_add_left, e2, ← inner_add_right, hueq]
      rw [← hxeq, inner_sub_right, ea, eb, sub_self]
    have hyu : (y : H₀) = (u : H₀) :=
      sub_eq_zero.mp (inner_self_eq_zero.mp (hperp ((y : H₀) - (u : H₀))))
    refine ⟨hyu ▸ u.2, ?_⟩
    have hAu : adjointComp T ⟨(y : H₀), hyu ▸ u.2⟩ = adjointComp T u := by
      congr 1
      exact Subtype.ext hyu
    rw [hAu]
    have : (u : H₀) + adjointComp T u = (y : H₀) + (adjointComp T)† y := hueq
    rw [hyu] at this
    exact add_left_cancel this
  have hge : (adjointComp T)† ≤ adjointComp T := by
    refine ⟨fun y hy => (key ⟨y, hy⟩).choose, ?_⟩
    intro a b hab
    obtain ⟨hm, hval⟩ := key a
    have : b = ⟨(a : H₀), hm⟩ := Subtype.ext hab.symm
    rw [this, hval]
  rw [LinearPMap.isSelfAdjoint_def]
  exact LinearPMap.eq_of_le_of_domain_eq hge (le_antisymm hge.1 hle.1)

/-- the resolvent defect identity: the Yosida approximation on `D(T†T)`.

For `f ∈ D(T†T)`, `f - J_s f = s • J_s (T†T f)`; equivalently `L_s f = s⁻¹ (f - J_s f)` equals
`J_s (T†T f)`.  By the form identity, `f` itself solves the weak equation with datum `f + s • T†T
f`, so
uniqueness (`eq_resolventDomain`) gives `J_s (f + s • T†T f) = f`, and linearity of `J_s`
separates the two terms. -/
theorem sub_resolvent_eq_smul (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : (adjointComp T).domain) :
    (f : H₀) - resolventCLM T hT hs f = s • resolventCLM T hT hs (adjointComp T f) := by
  have hweak : WeakResolvent T s ((f : H₀) + s • adjointComp T f) ⟨(f : H₀), f.2.2⟩ := by
    intro v
    have h := inner_adjointComp hd f v.2
    rw [inner_add_left, real_inner_smul_left, h]
  have heq := eq_resolventDomain T hT hs hweak
  have h2 : resolventCLM T hT hs ((f : H₀) + s • adjointComp T f) = (f : H₀) := by
    rw [resolventCLM_apply, ← heq]
  rw [map_add, map_smul] at h2
  exact (eq_sub_of_add_eq' h2).symm

end Resolvent

end FunctionalInequalities.Analysis.Semigroup
