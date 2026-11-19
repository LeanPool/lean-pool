/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic

/-!
# Resolvent limits: `J_s → 1` as `s ↓ 0`, and commutation

The module proves:

* the quantitative resolvent bound, `norm_resolventCLM_sub_sq_le`: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2
  ≤ s * ‖T f‖ ^ 2`;
* strong resolvent convergence, `exists_delta_norm_resolventCLM_sub_lt`: `J_s → 1` strongly as `s ↓
  0`, in `ε`–`δ` form
  (`resolventCLM` carries the proof `0 < s` as an argument);
* resolvent commutation, `resolventCLM_comp_comm`: the resolvents commute, `J_s J_r = J_r J_s`.

The same module also proves the **graph-norm** convergence that the Bakry–Émery form-domain stage
needs and that the quantitative resolvent bound and resolvent commutation do not give: for
`f ∈ D(T)`, `T (J_s f) → T f` in `H₁`
(`exists_delta_norm_map_resolventDomain_sub_map_lt`), together with the two-parameter energy
identity `resolventDomain_energy_identity` behind it, antitonicity of `s ↦ ‖T (J_s f)‖ ^ 2`
(`norm_map_resolventDomain_sq_le_of_le`), its Cauchy consequence
(`norm_map_resolventDomain_sub_sq_le_sub`), the energy contraction
`‖T (J_s f)‖ ≤ ‖T f‖` (`norm_map_resolventDomain_le`) and the defect bound
`norm_map_resolventDomain_sub_map_sq_le`.  See the section below.

Everything is proved from the **weak equation** `WeakResolvent T s f u` of `Resolvent/Form.lean`
and the unique solvability of `Resolvent/Basic.lean`.  In particular:

**The adjoint never appears.**  No declaration here refers to `LinearPMap.adjoint`, to
`adjointComp` or to `adjointCompDomain`; the module does not import
`FunctionalInequalities.Analysis.Semigroup.AdjointComp`, and it proves none of the identities from
the
form identity to the resolvent defect identity.
It also proves nothing about the adjoint-product identification or the semigroup limit (the Yosida
exponentials, the semigroup laws, the generator), nothing about the Markov property or
Bakry–Émery calculus, and no step of Buser's inequality.  This is general real Hilbert space
material: no measure, no log-concavity, no KLS quantity.

## Sharper forms and hypotheses

The quantitative resolvent bound is proved through the **sharper**
`norm_resolventCLM_sub_sq_le_quarter`, with the constant
`s ‖T f‖ ^ 2 / 4` instead of `s ‖T f‖ ^ 2`.  The sharp form is the honest output of
the computation `‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫ ≤ s ‖T f‖ ^ 2 / 4`; the weaker
bound is kept as a wrapper.  The quantitative resolvent bound and resolvent commutation use
closedness only through `resolventCLM`, strong resolvent convergence genuinely needs density, and
completeness of `H₀`
and `H₁` is required for `resolventCLM` to exist at all.  Resolvent commutation could be routed
through the resolvent identity `J_s - J_r = (r - s) J_s T†T J_r`; the proof here instead shows
that `s • J_s f - r • J_r f + (r - s) • J_s (J_r f)` solves the weak equation with datum `0`,
hence vanishes, which is the same identity with the adjoint removed.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-! ## the quantitative resolvent bound — quantitative convergence on the domain -/

/--
The exact form of the quantitative resolvent bound's computation: testing the weak equation for `u =
J_s f` against
`v = u - f ∈ D(T)` gives `‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫`.

This is the only place where the weak equation is used in the proof of the quantitative resolvent
bound. -/
theorem norm_resolventCLM_sub_sq_eq (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (f : T.domain) :
    ‖resolventCLM T hT hs f - f‖ ^ 2 =
      -(s * ‖T (resolventDomain T hT hs (f : H₀))‖ ^ 2) +
        s * ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫ := by
  set u := resolventDomain T hT hs (f : H₀) with hudef
  have h := resolventDomain_spec T hT hs (f : H₀) (u - f)
  have hcoe : ((u - f : T.domain) : H₀) = (u : H₀) - (f : H₀) := rfl
  have hTsub : T (u - f) = T u - T f := T.map_sub u f
  rw [hcoe, hTsub] at h
  simp only [inner_sub_right] at h
  have hsym : ⟪(f : H₀), (u : H₀)⟫ = ⟪(u : H₀), (f : H₀)⟫ := real_inner_comm _ _
  have hTself : ⟪T u, T u⟫ = ‖T u‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hself :
    ‖resolventCLM T hT hs f - (f : H₀)‖ ^ 2 =
      ⟪(u : H₀), (u : H₀)⟫ - 2 * ⟪(u : H₀), (f : H₀)⟫ + ⟪(f : H₀), (f : H₀)⟫ := by
    have hru : resolventCLM T hT hs (f : H₀) = (u : H₀) := rfl
    rw [hru, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, hsym]
    ring
  rw [hself]
  rw [hTself] at h
  linarith [hsym]

/--
The quantitative resolvent bound, sharp form: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s ‖T f‖ ^ 2 / 4`.

Sharper than `norm_resolventCLM_sub_sq_le` by the factor `4`: the computation
`‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫` is closed by Cauchy–Schwarz and
`s (‖T u‖ - ‖T f‖ / 2) ^ 2 ≥ 0`, so the bound `‖T u‖ ≤ ‖T f‖` is
not needed. -/
theorem norm_resolventCLM_sub_sq_le_quarter (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ}
    (hs : 0 < s) (f : T.domain) : ‖resolventCLM T hT hs f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2 / 4 := by
  have hkey := norm_resolventCLM_sub_sq_eq T hT hs f
  have hcs :
    ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫ ≤
      ‖T (resolventDomain T hT hs (f : H₀))‖ * ‖T f‖ :=
    real_inner_le_norm _ _
  have h1 :
    s * ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫ ≤
      s * (‖T (resolventDomain T hT hs (f : H₀))‖ * ‖T f‖) :=
    mul_le_mul_of_nonneg_left hcs hs.le
  have h2 : 0 ≤ s * (‖T (resolventDomain T hT hs (f : H₀))‖ - ‖T f‖ / 2) ^ 2 :=
    mul_nonneg hs.le (sq_nonneg _)
  nlinarith [h1, h2]

/-- The quantitative resolvent bound: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s ‖T f‖ ^ 2`.

Obtained from the sharp `norm_resolventCLM_sub_sq_le_quarter`. -/
theorem norm_resolventCLM_sub_sq_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (f : T.domain) : ‖resolventCLM T hT hs f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2 := by
  have h := norm_resolventCLM_sub_sq_le_quarter T hT hs f
  nlinarith [mul_nonneg hs.le (sq_nonneg ‖T f‖)]

/-! ## strong resolvent convergence — strong convergence to the identity -/

/-- Strong resolvent convergence: `J_s f → f` as `s ↓ 0`, for every `f : H₀`.

Stated in `ε`–`δ` form because `resolventCLM` carries the proof `0 < s` as an argument.  Split
`‖J_s f - f‖ ≤ ‖J_s (f - g)‖ + ‖J_s g - g‖ + ‖g - f‖` for `g ∈ D(T)` within `ε / 3` of `f`
(density), bound the outer terms by the contraction property `norm_resolventCLM_le` and the middle
term by the quantitative resolvent bound, and take `δ = (ε / 3) ^ 2 / (‖T g‖ ^ 2 + 1)`. -/
theorem exists_delta_norm_resolventCLM_sub_lt (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hD : Dense (T.domain : Set H₀)) (f : H₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖resolventCLM T hT hs f - f‖ < ε := by
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨g, hgmem, hgdist⟩ := Metric.mem_closure_iff.mp (hD f) (ε / 3) hε3
  set gd : T.domain := ⟨g, hgmem⟩ with hgd
  have hfg : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  refine ⟨(ε / 3) ^ 2 / (‖T gd‖ ^ 2 + 1), by positivity, ?_⟩
  intro s hs hsδ
  have hden : (0 : ℝ) < ‖T gd‖ ^ 2 + 1 := by positivity
  have hsmall : s * ‖T gd‖ ^ 2 < (ε / 3) ^ 2 := by
    have h1 : s * (‖T gd‖ ^ 2 + 1) < (ε / 3) ^ 2 := by
      have := (lt_div_iff₀ hden).mp hsδ
      linarith
    nlinarith [hs.le, sq_nonneg ‖T gd‖]
  have hmid : ‖resolventCLM T hT hs g - g‖ < ε / 3 := by
    have hR1 : ‖resolventCLM T hT hs gd - gd‖ ^ 2 ≤ s * ‖T gd‖ ^ 2 :=
      norm_resolventCLM_sub_sq_le T hT hs gd
    have hcoe : ((gd : T.domain) : H₀) = g := rfl
    rw [hcoe] at hR1
    nlinarith [norm_nonneg (resolventCLM T hT hs g - g), hR1, hsmall]
  have houter : ‖resolventCLM T hT hs f - resolventCLM T hT hs g‖ < ε / 3 := by
    have hlin : resolventCLM T hT hs f - resolventCLM T hT hs g
        = resolventCLM T hT hs (f - g) := (map_sub _ _ _).symm
    rw [hlin]
    exact lt_of_le_of_lt (norm_resolventCLM_le T hT hs (f - g)) hfg
  have hlast : ‖g - f‖ < ε / 3 := by rwa [norm_sub_rev]
  have htri : ‖resolventCLM T hT hs f - f‖
      ≤ ‖resolventCLM T hT hs f - resolventCLM T hT hs g‖
        + ‖resolventCLM T hT hs g - g‖ + ‖g - f‖ := by
    have h1 : resolventCLM T hT hs f - f
        = (resolventCLM T hT hs f - resolventCLM T hT hs g)
          + (resolventCLM T hT hs g - g) + (g - f) := by abel
    have hab := norm_add_le (resolventCLM T hT hs f - resolventCLM T hT hs g)
      (resolventCLM T hT hs g - g)
    rw [h1]
    exact le_trans (norm_add_le _ _) (by linarith)
  linarith

/-! ## resolvent commutation — the resolvents commute -/

/-- The weak resolvent identity, with the adjoint removed: for all `s, r > 0` and every datum `f`,
`s • J_s f - r • J_r f + (r - s) • J_s (J_r f) = 0` inside `D(T)`.

Spectrally this is `s / (1 + s a) - r / (1 + r a) + (r - s) / ((1 + s a)(1 + r a)) = 0`.  The proof
is by uniqueness: the left-hand side solves the weak `s`-equation with datum `0`. -/
theorem resolventDomain_identity (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) (f : H₀) :
    s • resolventDomain T hT hs f - r • resolventDomain T hT hr f
        + (r - s) • resolventDomain T hT hs (resolventDomain T hT hr f : H₀) = 0 := by
  set p := resolventDomain T hT hs f with hp
  set q := resolventDomain T hT hr f with hq
  set w := resolventDomain T hT hs (q : H₀) with hw
  set z : T.domain := s • p - r • q + (r - s) • w with hz
  have hzcoe : (z : H₀) = s • (p : H₀) - r • (q : H₀) + (r - s) • (w : H₀) := rfl
  have hzT : T z = s • T p - r • T q + (r - s) • T w := by
    rw [hz, T.map_add, T.map_sub, T.map_smul, T.map_smul, T.map_smul]
  have hzero : WeakResolvent T s (0 : H₀) z := by
    intro v
    have hA := resolventDomain_spec T hT hs f v
    have hB := resolventDomain_spec T hT hr f v
    have hC := resolventDomain_spec T hT hs (q : H₀) v
    rw [hzcoe, hzT]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left]
    linear_combination s * hA - s * hB + (r - s) * hC
  have hzero' : WeakResolvent T s (0 : H₀) (0 : T.domain) := by
    intro v
    simp [T.map_zero]
  exact weakResolvent_unique hs hzero hzero'

/-- Resolvent commutation: the resolvents commute, `J_s J_r = J_r J_s`.

From `resolventDomain_identity`: `w = J_s (J_r f)` satisfies the weak `r`-equation with datum
`J_s f`, so `w = J_r (J_s f)` by uniqueness. -/
theorem resolventCLM_comp_comm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) :
    (resolventCLM T hT hs).comp (resolventCLM T hT hr)
      = (resolventCLM T hT hr).comp (resolventCLM T hT hs) := by
  ext f
  set p := resolventDomain T hT hs f with hp
  set q := resolventDomain T hT hr f with hq
  set w := resolventDomain T hT hs (q : H₀) with hw
  have hid := resolventDomain_identity T hT hs hr f
  rw [← hp, ← hq, ← hw] at hid
  have hidT : s • T p - r • T q + (r - s) • T w = 0 := by
    have : T (s • p - r • q + (r - s) • w) = s • T p - r • T q + (r - s) • T w := by
      rw [T.map_add, T.map_sub, T.map_smul, T.map_smul, T.map_smul]
    rw [← this, hid, T.map_zero]
  have hgoal : WeakResolvent T r (p : H₀) w := by
    intro v
    have hA := resolventDomain_spec T hT hs f v
    have hB := resolventDomain_spec T hT hr f v
    have hC := resolventDomain_spec T hT hs (q : H₀) v
    have hZ2 : s * ⟪T p, T v⟫ - r * ⟪T q, T v⟫ + (r - s) * ⟪T w, T v⟫ = 0 := by
      have := congrArg (fun x : H₁ => ⟪x, T v⟫) hidT
      simpa only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left]
        using this
    linear_combination hC + hZ2 + hB - hA
  have hfin : w = resolventDomain T hT hr (p : H₀) := eq_resolventDomain T hT hr hgoal
  simp only [ContinuousLinearMap.comp_apply, resolventCLM_apply, ← hp, ← hq, ← hw]
  exact congrArg (fun x : T.domain => (x : H₀)) hfin


/-! ## Graph-norm convergence of the resolvent

The quantitative resolvent bound and resolvent commutation above measure `J_s f - f` in the norm of
`H₀` only.  The Buser argument needs the
convergence in the **graph norm** of `T`: for `f ∈ D(T)` also `T (J_s f) → T f`.  That does not
follow from the quantitative resolvent bound and resolvent commutation, and it is not a
consequence of the `H₀`-contraction of `J_s` either: the
energies `‖T (J_s f)‖` have to be shown to converge, not merely to stay bounded.

Everything here is again proved from the weak equation alone; the adjoint still never appears,
and no spectral calculus, functional calculus or weak compactness argument is used.  The engine is
the two-parameter identity `resolventDomain_energy_identity`, obtained by testing the `s`-equation
against `J_s f - J_r f` and the `r`-equation against `J_r f - J_s f` and adding.  It simultaneously
gives

* the energy is antitone in `s` (`norm_map_resolventDomain_sq_le_of_le`), and
* a Cauchy estimate for the energies' increments
  (`norm_map_resolventDomain_sub_sq_le_sub`),

so the monotone bounded family `s ↦ ‖T (J_s f)‖ ^ 2` forces `T (J_s f)` to be a Cauchy family.
Completeness of `H₁` produces a limit and **closedness of `T`** identifies it with `T f`. -/

/-- The two-parameter energy identity of the resolvent: for all `s, r > 0` and every datum
`f : H₀`,

`2 ‖J_s f - J_r f‖² + (s + r) ‖T (J_s f) - T (J_r f)‖² + (s - r) (‖T (J_s f)‖² - ‖T (J_r f)‖²) = 0`.

Test the weak `s`-equation against `v = J_s f - J_r f`, the weak `r`-equation against
`v = J_r f - J_s f`, and add.  Spectrally the identity reads
`2 (α - β)² + (s + r)(√λ α - √λ β)² + (s - r) λ (α² - β²) = 0` with `α = 1/(1 + sλ)`,
`β = 1/(1 + rλ)`.  No regularity of the datum is required, and closedness enters only through
`resolventDomain` itself. -/
theorem resolventDomain_energy_identity (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (f : H₀) :
    2 * ‖(resolventDomain T hT hs f : H₀) - (resolventDomain T hT hr f : H₀)‖ ^ 2
        + (s + r) * ‖T (resolventDomain T hT hs f) - T (resolventDomain T hT hr f)‖ ^ 2
        + (s - r) * (‖T (resolventDomain T hT hs f)‖ ^ 2
            - ‖T (resolventDomain T hT hr f)‖ ^ 2) = 0 := by
  set u := resolventDomain T hT hs f with hu
  set w := resolventDomain T hT hr f with hw
  have h₁ := resolventDomain_spec T hT hs f (u - w)
  have h₂ := resolventDomain_spec T hT hr f (w - u)
  have hc : ((u - w : T.domain) : H₀) = (u : H₀) - (w : H₀) := rfl
  have hc' : ((w - u : T.domain) : H₀) = (w : H₀) - (u : H₀) := rfl
  have hm : T (u - w) = T u - T w := T.map_sub u w
  have hm' : T (w - u) = T w - T u := T.map_sub w u
  rw [hc, hm] at h₁
  rw [hc', hm'] at h₂
  rw [← hu] at h₁
  rw [← hw] at h₂
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h₁ h₂
  rw [real_inner_comm (u : H₀) (w : H₀), real_inner_comm (T u) (T w)] at h₂
  rw [norm_sub_sq_real (u : H₀) (w : H₀), norm_sub_sq_real (T u) (T w)]
  linear_combination 2 * h₁ + 2 * h₂

/-- The resolvent energy is antitone in `s`: for `0 < s ≤ r`,
`‖T (J_r f)‖ ² ≤ ‖T (J_s f)‖ ²`.

Immediate from `resolventDomain_energy_identity`: the first two summands are nonnegative, so
`(r - s) (‖T (J_s f)‖² - ‖T (J_r f)‖²) ≥ 0`.  No regularity of the datum is required. -/
theorem norm_map_resolventDomain_sq_le_of_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hsr : s ≤ r) (f : H₀) :
    ‖T (resolventDomain T hT hr f)‖ ^ 2 ≤ ‖T (resolventDomain T hT hs f)‖ ^ 2 := by
  rcases eq_or_lt_of_le hsr with h | h
  · subst h
    exact le_rfl
  · have hid := resolventDomain_energy_identity T hT hs hr f
    have hA : (0 : ℝ) ≤ ‖(resolventDomain T hT hs f : H₀) - (resolventDomain T hT hr f : H₀)‖ ^ 2 :=
      sq_nonneg _
    have hB : (0 : ℝ)
        ≤ ‖T (resolventDomain T hT hs f) - T (resolventDomain T hT hr f)‖ ^ 2 := sq_nonneg _
    nlinarith [hid, hA, hB, sub_pos.mpr h]

/-- The energy increments control the graph distance: for `0 < s ≤ r`,

`‖T (J_s f) - T (J_r f)‖² ≤ ‖T (J_s f)‖² - ‖T (J_r f)‖²`.

From `resolventDomain_energy_identity`, `(s + r) ‖T (J_s f) - T (J_r f)‖² ≤ (r - s) (‖T (J_s f)‖²
- ‖T (J_r f)‖²)`, and `r - s ≤ r + s` together with antitonicity of the energy finishes. -/
theorem norm_map_resolventDomain_sub_sq_le_sub (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hsr : s ≤ r) (f : H₀) :
    ‖T (resolventDomain T hT hs f) - T (resolventDomain T hT hr f)‖ ^ 2
      ≤ ‖T (resolventDomain T hT hs f)‖ ^ 2 - ‖T (resolventDomain T hT hr f)‖ ^ 2 := by
  have hid := resolventDomain_energy_identity T hT hs hr f
  have hmono := norm_map_resolventDomain_sq_le_of_le T hT hs hr hsr f
  have hA : (0 : ℝ) ≤ ‖(resolventDomain T hT hs f : H₀) - (resolventDomain T hT hr f : H₀)‖ ^ 2 :=
    sq_nonneg _
  nlinarith [hid, hmono, hA, hs, hr]

/-- The resolvent contracts the energy: for `f ∈ D(T)` and `s > 0`, `‖T (J_s f)‖ ≤ ‖T f‖`.

Testing the weak equation against `J_s f - f` gives
`s (⟪T (J_s f), T f⟫ - ‖T (J_s f)‖²) = ‖J_s f - f‖² ≥ 0`
(`norm_resolventCLM_sub_sq_eq`), so `‖T (J_s f)‖² ≤ ⟪T (J_s f), T f⟫ ≤ ‖T (J_s f)‖ ‖T f‖`. -/
theorem norm_map_resolventDomain_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (f : T.domain) : ‖T (resolventDomain T hT hs (f : H₀))‖ ≤ ‖T f‖ := by
  have hkey := norm_resolventCLM_sub_sq_eq T hT hs f
  have hnn : (0 : ℝ) ≤ ‖resolventCLM T hT hs (f : H₀) - (f : H₀)‖ ^ 2 := sq_nonneg _
  have hcs : ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫
      ≤ ‖T (resolventDomain T hT hs (f : H₀))‖ * ‖T f‖ := real_inner_le_norm _ _
  have hAP : ‖T (resolventDomain T hT hs (f : H₀))‖ ^ 2
      ≤ ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫ := by nlinarith [hkey, hnn, hs]
  rcases eq_or_lt_of_le (norm_nonneg (T (resolventDomain T hT hs (f : H₀)))) with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith [hAP, hcs]

/-- The energy defect bounds the graph defect: for `f ∈ D(T)` and `s > 0`,

`‖T (J_s f) - T f‖² ≤ ‖T f‖² - ‖T (J_s f)‖²`.

Same input as `norm_map_resolventDomain_le`: `⟪T (J_s f), T f⟫ ≥ ‖T (J_s f)‖²`, inserted into
`‖T (J_s f) - T f‖² = ‖T (J_s f)‖² - 2 ⟪T (J_s f), T f⟫ + ‖T f‖²`.  So the whole graph-norm
convergence reduces to `‖T (J_s f)‖ → ‖T f‖`. -/
theorem norm_map_resolventDomain_sub_map_sq_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ}
    (hs : 0 < s) (f : T.domain) :
    ‖T (resolventDomain T hT hs (f : H₀)) - T f‖ ^ 2
      ≤ ‖T f‖ ^ 2 - ‖T (resolventDomain T hT hs (f : H₀))‖ ^ 2 := by
  have hkey := norm_resolventCLM_sub_sq_eq T hT hs f
  have hnn : (0 : ℝ) ≤ ‖resolventCLM T hT hs (f : H₀) - (f : H₀)‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real (T (resolventDomain T hT hs (f : H₀))) (T f)]
  nlinarith [hkey, hnn, hs]

/-- Monotone energies force a Cauchy family: if `‖x n‖ ^ 2` is monotone and bounded above, and
the increments obey `‖x n - x m‖ ^ 2 ≤ ‖x n‖ ^ 2 - ‖x m‖ ^ 2` for `m ≤ n`, then `x` converges.

Purely metric bookkeeping for `exists_delta_norm_map_resolventDomain_sub_map_lt`, isolated so
that the resolvent argument reads as the three estimates that feed it. -/
private theorem exists_tendsto_of_energy_cauchy {H : Type*} [NormedAddCommGroup H]
    [CompleteSpace H] (x : ℕ → H) (C : ℝ) (hmono : Monotone fun n => ‖x n‖ ^ 2)
    (hbdd : ∀ n, ‖x n‖ ^ 2 ≤ C)
    (hstep : ∀ m n : ℕ, m ≤ n → ‖x n - x m‖ ^ 2 ≤ ‖x n‖ ^ 2 - ‖x m‖ ^ 2) :
    ∃ ξ : H, Filter.Tendsto x Filter.atTop (nhds ξ) := by
  have hbddAbove : BddAbove (Set.range fun n => ‖x n‖ ^ 2) := by
    refine ⟨C, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hbdd n
  have hlim : Filter.Tendsto (fun n => ‖x n‖ ^ 2) Filter.atTop (nhds (⨆ n, ‖x n‖ ^ 2)) :=
    tendsto_atTop_ciSup hmono hbddAbove
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro η hη
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq (η ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖x n - x N‖ ^ 2 ≤ ‖x n‖ ^ 2 - ‖x N‖ ^ 2 := hstep N n hn
  have h2 : |‖x n‖ ^ 2 - ‖x N‖ ^ 2| < η ^ 2 := by
    have h := hN n hn
    rwa [Real.dist_eq] at h
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x n - x N), hη, le_abs_self (‖x n‖ ^ 2 - ‖x N‖ ^ 2)]

/-- **Graph-norm convergence of the resolvent.** For `f ∈ D(T)` and every `ε > 0` there is
`δ > 0` with `‖T (J_s f) - T f‖ < ε` for every `0 < s < δ`; together with the quantitative resolvent
bound this says that
`J_s f → f` in the graph norm of `T`, i.e. that `J_s f` approximates `f` in the form domain.

Stated in `ε`–`δ` form because `resolventDomain` carries the proof `0 < s` as an argument.

Proof.  Along `s_n = 1 / (n + 1)` the energies `‖T (J_{s_n} f)‖ ^ 2` are monotone
(`norm_map_resolventDomain_sq_le_of_le`) and bounded by `‖T f‖ ^ 2`
(`norm_map_resolventDomain_le`), and the increments control the distances
(`norm_map_resolventDomain_sub_sq_le_sub`), so `T (J_{s_n} f)` converges in `H₁`; the quantitative
resolvent bound makes
`J_{s_n} f → f` in `H₀`, and **closedness of `T`** identifies the limit as `T f`.  Hence
`‖T (J_{s_n} f)‖ → ‖T f‖`, and `norm_map_resolventDomain_sub_map_sq_le` with antitonicity of the
energy transfers the resulting estimate from the sequence to every small `s`. -/
theorem exists_delta_norm_map_resolventDomain_sub_map_lt (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (f : T.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖T (resolventDomain T hT hs (f : H₀)) - T f‖ < ε := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hanti : ∀ m n : ℕ, m ≤ n → 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    intro m n hmn
    have hmn' : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have h := (Nat.cast_le (α := ℝ)).mpr hmn
      linarith
    exact one_div_le_one_div_of_le (by positivity) hmn'
  obtain ⟨ξ, hξ⟩ :=
    exists_tendsto_of_energy_cauchy (fun n : ℕ => T (resolventDomain T hT (hpos n) (f : H₀)))
      (‖T f‖ ^ 2)
      (monotone_nat_of_le_succ fun n =>
        norm_map_resolventDomain_sq_le_of_le T hT (hpos (n + 1)) (hpos n)
          (hanti n (n + 1) (Nat.le_succ n)) (f : H₀))
      (fun n => by
        have h := norm_map_resolventDomain_le T hT (hpos n) f
        nlinarith [norm_nonneg (T (resolventDomain T hT (hpos n) (f : H₀))), norm_nonneg (T f)])
      (fun m n hmn =>
        norm_map_resolventDomain_sub_sq_le_sub T hT (hpos n) (hpos m) (hanti m n hmn) (f : H₀))
  have h₀ :
    Filter.Tendsto (fun n : ℕ => (resolventDomain T hT (hpos n) (f : H₀) : H₀)) Filter.atTop
      (nhds (f : H₀)) := by
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    obtain ⟨N, hN⟩ :=
      exists_nat_one_div_lt (show (0 : ℝ) < η ^ 2 / (‖T f‖ ^ 2 + 1) by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hCpos : (0 : ℝ) < ‖T f‖ ^ 2 + 1 := by positivity
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := hanti N n hn
    have h2 := norm_resolventCLM_sub_sq_le_quarter T hT (hpos n) f
    rw [resolventCLM_apply] at h2
    have h4 : (1 : ℝ) / ((N : ℝ) + 1) < η ^ 2 / (‖T f‖ ^ 2 + 1) := by simpa using hN
    have h5 : (1 : ℝ) / ((n : ℝ) + 1) * (‖T f‖ ^ 2 + 1) < η ^ 2 :=
      (lt_div_iff₀ hCpos).mp (lt_of_le_of_lt h1 h4)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg ((resolventDomain T hT (hpos n) (f : H₀) : H₀) - (f : H₀)), hη, h2,
      h5, hpos n, sq_nonneg ‖T f‖]
  have hgraph : ((f : H₀), ξ) ∈ T.graph := by
    refine hT.mem_of_tendsto (h₀.prodMk_nhds hξ) (Filter.Eventually.of_forall fun n => ?_)
    exact T.mem_graph _
  have hTf : T f = ξ := by
    obtain ⟨y, hy1, hy2⟩ := T.mem_graph_iff.mp hgraph
    have hy1' : (y : H₀) = (f : H₀) := hy1
    have hy2' : T y = ξ := hy2
    rw [← Subtype.ext hy1' (α := H₀)]
    exact hy2'
  have hnorm :
    Filter.Tendsto (fun n : ℕ => ‖T f‖ ^ 2 - ‖T (resolventDomain T hT (hpos n) (f : H₀))‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hn2 :
      Filter.Tendsto (fun n : ℕ => ‖T (resolventDomain T hT (hpos n) (f : H₀))‖ ^ 2)
        Filter.atTop (nhds (‖T f‖ ^ 2)) := by
      rw [hTf]
      exact hξ.norm.pow 2
    have h := (tendsto_const_nhds (x := ‖T f‖ ^ 2) (f := Filter.atTop (α := ℕ))).sub hn2
    rwa [sub_self] at h
  obtain ⟨N, hN⟩ :
    ∃ N : ℕ, ‖T f‖ ^ 2 - ‖T (resolventDomain T hT (hpos N) (f : H₀))‖ ^ 2 < ε ^ 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm (ε ^ 2) (by positivity)
    refine ⟨N, ?_⟩
    have h := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  refine ⟨1 / ((N : ℝ) + 1), hpos N, ?_⟩
  intro s hs hsδ
  have hmono := norm_map_resolventDomain_sq_le_of_le T hT hs (hpos N) hsδ.le (f : H₀)
  have hdef := norm_map_resolventDomain_sub_map_sq_le T hT hs f
  nlinarith [hdef, hmono, hN, norm_nonneg (T (resolventDomain T hT hs (f : H₀)) - T f), hε]

end FunctionalInequalities.Analysis.Semigroup
