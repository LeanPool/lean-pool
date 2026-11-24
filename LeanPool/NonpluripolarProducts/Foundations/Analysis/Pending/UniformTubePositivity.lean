/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlaneTubePositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerDomination

/-!
# The tube estimate, uniform along a compact set

Source: Copy-4, step 6 of the proof of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`): *"For `B ≫ 1`, there is a relatively
compact neighbourhood `U` of `W` on a neighbourhood of whose closure
`Ω_U > 0`"*.

`Pending.PlaneTubePositivity.exists_isStrictlyPositive_add_smul_ddc_planeDistSq`
is the estimate at a SINGLE form: given `a` strictly positive along the tangent
plane, `a + B ddᶜ r_W²` is strictly positive for `B` large.  Step 6 needs one
`B` and one OPEN set serving every point of `W` at once.  That is what is proved
here, for an arbitrary continuous family `a : X → Λ²` and an arbitrary compact
`S ⊆ X`.

The two pointwise ingredients are NOT re-proved: `Pending.KahlerDomination`
already has them, in the unfolded notation `a ![v, i v]` rather than `quad a v`
(the two are definitionally equal, so its lemmas apply verbatim):
`abs_lineValue_le` is `|a(v, iv)| ≤ ‖a‖ ‖v‖²`, and `exists_lineValue_lower_bound`
is the unit-sphere minimum `m ‖v‖² ≤ a(v, iv)` with `m > 0`, including the
dimension-`0` case where the sphere is empty and every vector vanishes.  What is
new here is everything with a PARAMETER in it:

* `isStrictlyPositive_of_opNorm_sub_lt`: strict positivity is stable under a
  perturbation of operator norm `< m`; hence
* `isOpen_setOf_isStrictlyPositive` / `isOpen_inter_setOf_isStrictlyPositive`:
  strict positivity of a continuous family is an OPEN condition on the
  parameter.  (`Pending.KahlerPerturbation.eventually_isStrictlyPositive_coeff`
  is this for the particular family `u ↦ α.coeff e u`; that module is not in this
  lane's write set, so the two coexist.)
* `isStrictlyPositive_add_smul_mono`: for semipositive `b`, `a + B b` strictly
  positive and `B ≤ B'` give `a + B' b` strictly positive.  The two together
  turn the pointwise estimate into a monotone open cover of `S`, and compactness
  finishes.

The remaining theorems are the manuscript's sentence, in four shapes: for a
VARYING semipositive family `b : X → Λ²` (`..._family`), for a family continuous
only on an open `Ω` (`..._familyOn`), for a single fixed `b`, and for
`b = ddᶜ (planeDistSq n k)`.  The varying versions are the ones a manifold needs:
`ddᶜ r_W²` is read in a chart through a flattening of `W`, and the resulting form
depends on the base point even though the flat model's does not
(`Pending.LeviFormHolomorphicComp.leviForm_planeDistSq_comp`).

**Which one a GLOBAL tube function can use.**  All of the above ask `b` to be
semipositive at every parameter, and conclude for every `B ≥ B₀`.  That is true
of the chart tube `ddᶜ (r² ∘ F)`, which is psh on the whole chart because `F` is
holomorphic, but it is NOT true of a tube glued with a partition of unity: the
cross terms `dχ ∧ dᶜ r_i²` and `r_i² ddᶜ χ_i` have either sign off `W`, so
semipositivity holds only ALONG `W` — which is also all Copy-4 claims.  The last
theorem, `exists_isStrictlyPositive_add_smul_of_pos_on_null_atCompact`, is the
weakening that fits: `b` semipositive only on `S`, and ONE `B₀` on ONE open `U`.
Its quantifier order is the manuscript's ("for `B ≫ 1` there is a neighbourhood
`U`").

Everything is sorry-free and uses no input from the modification side.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.UniformTubePositivity

open FirstPass PositivityPerturbation PlaneTubePositivity

noncomputable section

variable {n : ℕ}

/-! ### Quantitative strict positivity -/

/-- The quadratic form is controlled by the operator norm.  This is
`Pending.KahlerDomination.abs_lineValue_le` in the `quad` notation; `quad a v` and
`a ![v, i v]` are definitionally equal. -/
theorem abs_quad_le_opNorm (a : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) (v : ComplexModel n) :
    |quad a v| ≤ ‖a‖ * ‖v‖ ^ 2 :=
  KahlerDomination.abs_lineValue_le a v

/-- **A strictly positive form is uniformly positive**: `m ‖v‖² ≤ a(v, iv)` for
some `m > 0`.  This is `Pending.KahlerDomination.exists_lineValue_lower_bound` in
the `quad` notation. -/
theorem exists_pos_forall_le_quad {a : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : ComplexModel n, m * ‖v‖ ^ 2 ≤ quad a v :=
  KahlerDomination.exists_lineValue_lower_bound ha

/-- **Strict positivity is stable in operator norm.** -/
theorem isStrictlyPositive_of_opNorm_sub_lt
    {a a' : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} {m : ℝ}
    (hbound : ∀ v : ComplexModel n, m * ‖v‖ ^ 2 ≤ quad a v) (h : ‖a' - a‖ < m) :
    IsStrictlyPositive a' := by
  intro v hv
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hsub : quad a' v - quad a v = quad (a' - a) v := rfl
  have hle : |quad (a' - a) v| ≤ ‖a' - a‖ * ‖v‖ ^ 2 := abs_quad_le_opNorm _ v
  have h1 : -(‖a' - a‖ * ‖v‖ ^ 2) ≤ quad a' v - quad a v := by
    rw [hsub]; exact neg_le_of_abs_le hle
  have h2 : m * ‖v‖ ^ 2 ≤ quad a v := hbound v
  have h3 : ‖a' - a‖ * ‖v‖ ^ 2 < m * ‖v‖ ^ 2 := by
    have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    exact mul_lt_mul_of_pos_right h hpos
  change 0 < quad a' v
  linarith

variable {X : Type*} [TopologicalSpace X]

/-- **Strict positivity of a continuous family is an open condition.** -/
theorem isOpen_setOf_isStrictlyPositive
    {a : X → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} (ha : Continuous a) :
    IsOpen {x : X | IsStrictlyPositive (a x)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨m, hm, hmb⟩ := exists_pos_forall_le_quad hx
  have hcont : ContinuousAt (fun y => ‖a y - a x‖) x :=
    ((ha.sub continuous_const).norm).continuousAt
  have hev : ∀ᶠ y in 𝓝 x, ‖a y - a x‖ < m := by
    have := hcont.eventually (eventually_lt_nhds (by simpa using hm))
    simpa using this
  exact hev.mono fun y hy => isStrictlyPositive_of_opNorm_sub_lt hmb hy

/-- **Strict positivity of a family continuous on an open set is an open condition
inside that set.** -/
theorem isOpen_inter_setOf_isStrictlyPositive {Ω : Set X} (hΩ : IsOpen Ω)
    {a : X → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} (ha : ContinuousOn a Ω) :
    IsOpen (Ω ∩ {x : X | IsStrictlyPositive (a x)}) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxΩ, hx⟩
  obtain ⟨m, hm, hmb⟩ := exists_pos_forall_le_quad hx
  have hcont : ContinuousAt (fun y => ‖a y - a x‖) x :=
    (((ha.continuousAt (hΩ.mem_nhds hxΩ)).sub continuousAt_const).norm)
  have hev : ∀ᶠ y in 𝓝 x, ‖a y - a x‖ < m := by
    have := hcont.eventually (eventually_lt_nhds (by simpa using hm))
    simpa using this
  exact inter_mem (hΩ.mem_nhds hxΩ)
    (hev.mono fun y hy => isStrictlyPositive_of_opNorm_sub_lt hmb hy)

/-! ### Monotonicity in the tube constant -/

/-- Adding a larger multiple of a semipositive form preserves strict
positivity. -/
theorem isStrictlyPositive_add_smul_mono
    {a b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} (hb : ∀ v, 0 ≤ quad b v)
    {B B' : ℝ} (hBB : B ≤ B') (h : IsStrictlyPositive (a + B • b)) :
    IsStrictlyPositive (a + B' • b) := by
  intro v hv
  have hq : 0 < quad (a + B • b) v := h v hv
  rw [quad_add, quad_smul_form] at hq
  have hmul : B * quad b v ≤ B' * quad b v := by
    have := hb v; nlinarith
  change 0 < quad (a + B' • b) v
  rw [quad_add, quad_smul_form]
  linarith

/-! ### The uniform tube estimate -/

/-- **The tube estimate, uniform along a compact parameter set**, for a varying
semipositive form.  For continuous families `a`, `b` of two-forms with `b`
semipositive everywhere, and a compact set `S` of parameters at which `a` is
strictly positive on the null directions of `b`, there are one constant `B₀` and
one OPEN set `U ⊇ S` such that `a x + B (b x)` is strictly positive for every
`B ≥ B₀` and every `x ∈ U`.

`b` has to vary: on a manifold `ddᶜ r_W²` is read in a chart through the
flattening of `W`, and the resulting form depends on the base point even though
the flat model's does not. -/
theorem exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_family
    {a b : X → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ}
    (hacont : Continuous a) (hbcont : Continuous b)
    (hb : ∀ (x : X) (v : ComplexModel n), 0 ≤ quad (b x) v)
    {S : Set X} (hS : IsCompact S)
    (hpos : ∀ x ∈ S, ∀ v : ComplexModel n, v ≠ 0 → quad (b x) v = 0 → 0 < quad (a x) v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧
      ∀ B : ℝ, B₀ ≤ B → ∀ x ∈ U, IsStrictlyPositive (a x + B • b x) := by
  set N : ℝ → Set X := fun B => {x : X | IsStrictlyPositive (a x + B • b x)} with hNdef
  have hNopen : ∀ B : ℝ, IsOpen (N B) := fun B =>
    isOpen_setOf_isStrictlyPositive (hacont.add (hbcont.const_smul B))
  have hNmono : ∀ {B B' : ℝ}, B ≤ B' → N B ⊆ N B' := fun {B B'} hBB x hx =>
    isStrictlyPositive_add_smul_mono (hb x) hBB hx
  -- every point of `S` is in `N k` for some natural `k`
  have hcover : S ⊆ ⋃ k : ℕ, N ((k : ℝ) + 1) := by
    intro x hx
    obtain ⟨B₁, hB₁, hB₁pos⟩ :=
      exists_isStrictlyPositive_add_smul_of_pos_on_null (hb x) (hpos x hx)
    obtain ⟨k, hk⟩ := exists_nat_ge B₁
    exact mem_iUnion.mpr ⟨k, hNmono (le_trans hk (by linarith)) (hB₁pos B₁ le_rfl)⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun k : ℕ => N ((k : ℝ) + 1))
    (fun k => hNopen _) hcover
  refine ⟨((t.sup id : ℕ) : ℝ) + 1, by positivity, N (((t.sup id : ℕ) : ℝ) + 1),
    hNopen _, ?_, fun B hB x hx => hNmono hB hx⟩
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (ht hx)
  have hks : (k : ℕ) ≤ t.sup id := Finset.le_sup (f := id) hk
  have hle : (k : ℝ) + 1 ≤ ((t.sup id : ℕ) : ℝ) + 1 := by
    have : (k : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := Nat.cast_le.mpr hks
    linarith
  exact hNmono hle hxk

/-- **The tube estimate, uniform along a compact parameter set**, for one fixed
semipositive form. -/
theorem exists_forall_isStrictlyPositive_add_smul_of_pos_on_null
    {a : X → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} (hacont : Continuous a)
    {b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} (hb : ∀ v, 0 ≤ quad b v)
    {S : Set X} (hS : IsCompact S)
    (hpos : ∀ x ∈ S, ∀ v : ComplexModel n, v ≠ 0 → quad b v = 0 → 0 < quad (a x) v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧
      ∀ B : ℝ, B₀ ≤ B → ∀ x ∈ U, IsStrictlyPositive (a x + B • b) :=
  exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_family hacont
    continuous_const (fun _ => hb) hS hpos

/-- **The uniform tube estimate on an open set.**  The version the chart picture
needs: `a` and `b` are only continuous on an open `Ω`, `b` is only semipositive
there, and the neighbourhood produced stays inside `Ω`. -/
theorem exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_familyOn
    {Ω : Set X} (hΩ : IsOpen Ω)
    {a b : X → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ}
    (hacont : ContinuousOn a Ω) (hbcont : ContinuousOn b Ω)
    (hb : ∀ x ∈ Ω, ∀ v : ComplexModel n, 0 ≤ quad (b x) v)
    {S : Set X} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (hpos : ∀ x ∈ S, ∀ v : ComplexModel n, v ≠ 0 → quad (b x) v = 0 → 0 < quad (a x) v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ U ⊆ Ω ∧
      ∀ B : ℝ, B₀ ≤ B → ∀ x ∈ U, IsStrictlyPositive (a x + B • b x) := by
  set N : ℝ → Set X := fun B => Ω ∩ {x : X | IsStrictlyPositive (a x + B • b x)} with hNdef
  have hNopen : ∀ B : ℝ, IsOpen (N B) := fun B =>
    isOpen_inter_setOf_isStrictlyPositive hΩ (hacont.add (hbcont.const_smul B))
  have hNmono : ∀ {B B' : ℝ}, B ≤ B' → N B ⊆ N B' := fun {B B'} hBB x hx =>
    ⟨hx.1, isStrictlyPositive_add_smul_mono (hb x hx.1) hBB hx.2⟩
  have hcover : S ⊆ ⋃ k : ℕ, N ((k : ℝ) + 1) := by
    intro x hx
    obtain ⟨B₁, hB₁, hB₁pos⟩ :=
      exists_isStrictlyPositive_add_smul_of_pos_on_null (hb x (hSΩ hx)) (hpos x hx)
    obtain ⟨k, hk⟩ := exists_nat_ge B₁
    exact mem_iUnion.mpr ⟨k, hNmono (le_trans hk (by linarith))
      ⟨hSΩ hx, hB₁pos B₁ le_rfl⟩⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun k : ℕ => N ((k : ℝ) + 1))
    (fun k => hNopen _) hcover
  refine ⟨((t.sup id : ℕ) : ℝ) + 1, by positivity, N (((t.sup id : ℕ) : ℝ) + 1),
    hNopen _, ?_, fun x hx => hx.1, fun B hB x hx => (hNmono hB hx).2⟩
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (ht hx)
  have hks : (k : ℕ) ≤ t.sup id := Finset.le_sup (f := id) hk
  have hle : (k : ℝ) + 1 ≤ ((t.sup id : ℕ) : ℝ) + 1 := by
    have : (k : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := Nat.cast_le.mpr hks
    linarith
  exact hNmono hle hxk

/-- **The uniform tube estimate with `b` semipositive only on `S`.**  This is the
shape a GLOBAL tube function can supply, and the manuscript's own quantifier order:
one `B₀`, one open `U ⊇ S`.

The stronger statements above ask semipositivity at every parameter and conclude
for every `B ≥ B₀`; a tube glued from chart tubes by a partition of unity has
neither property off `W`, because the cross terms `dχ ∧ dᶜ r_i²` and
`r_i² ddᶜ χ_i` change sign there.  Along `S` semipositivity is enough: the
monotone cover argument runs inside `S`, and the openness of strict positivity
then produces `U` directly. -/
theorem exists_isStrictlyPositive_add_smul_of_pos_on_null_atCompact
    {Ω : Set X} (hΩ : IsOpen Ω)
    {a b : X → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ}
    (hacont : ContinuousOn a Ω) (hbcont : ContinuousOn b Ω)
    {S : Set X} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (hb : ∀ x ∈ S, ∀ v : ComplexModel n, 0 ≤ quad (b x) v)
    (hpos : ∀ x ∈ S, ∀ v : ComplexModel n, v ≠ 0 → quad (b x) v = 0 → 0 < quad (a x) v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ U ⊆ Ω ∧
      ∀ x ∈ U, IsStrictlyPositive (a x + B₀ • b x) := by
  set N : ℝ → Set X := fun B => Ω ∩ {x : X | IsStrictlyPositive (a x + B • b x)} with hNdef
  have hNopen : ∀ B : ℝ, IsOpen (N B) := fun B =>
    isOpen_inter_setOf_isStrictlyPositive hΩ (hacont.add (hbcont.const_smul B))
  have hcover : S ⊆ ⋃ k : ℕ, N ((k : ℝ) + 1) := by
    intro x hx
    obtain ⟨B₁, hB₁, hB₁pos⟩ :=
      exists_isStrictlyPositive_add_smul_of_pos_on_null (hb x hx) (hpos x hx)
    obtain ⟨k, hk⟩ := exists_nat_ge B₁
    exact mem_iUnion.mpr ⟨k, hSΩ hx, hB₁pos _ (le_trans hk (by linarith))⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun k : ℕ => N ((k : ℝ) + 1))
    (fun k => hNopen _) hcover
  -- the maximum of the finitely many constants works AT every point of `S`,
  -- because `b x` is semipositive there
  set B₀ : ℝ := ((t.sup id : ℕ) : ℝ) + 1 with hB₀def
  have hSpos : ∀ x ∈ S, IsStrictlyPositive (a x + B₀ • b x) := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (ht hx)
    have hks : (k : ℕ) ≤ t.sup id := Finset.le_sup (f := id) hk
    have hle : (k : ℝ) + 1 ≤ B₀ := by
      have : (k : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := Nat.cast_le.mpr hks
      rw [hB₀def]; linarith
    exact isStrictlyPositive_add_smul_mono (hb x hx) hle hxk.2
  exact ⟨B₀, by rw [hB₀def]; positivity, N B₀, hNopen _,
    fun x hx => ⟨hSΩ hx, hSpos x hx⟩, fun x hx => hx.1, fun x hx => hx.2⟩

/-- **The tube estimate for `ddᶜ r_W²`, uniform along a compact parameter set.**
This is Copy-4's step 6 sentence: a continuous family of two-forms which is
strictly positive along the tangent plane at every parameter of a compact set
becomes strictly positive in all directions, for one constant `B₀` and on one
open neighbourhood of that set, after adding `B ddᶜ (planeDistSq n k)`.

The Levi form of `planeDistSq n k` is independent of the base point, so the
point `z₀` below only names the form. -/
theorem exists_forall_isStrictlyPositive_add_smul_ddc_planeDistSq {k : ℕ}
    {a : X → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} (hacont : Continuous a)
    (z₀ : ComplexModel n) {S : Set X} (hS : IsCompact S)
    (hpos : ∀ x ∈ S, ∀ v ∈ complexCoordinatePlane n k, v ≠ 0 → 0 < quad (a x) v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧
      ∀ B : ℝ, B₀ ≤ B → ∀ x ∈ U,
        IsStrictlyPositive (a x + B • smoothDDC (planeDistSq n k) z₀) := by
  have hC2 : ContDiffAt ℝ 2 (planeDistSq n k) z₀ :=
    (contDiff_planeDistSq.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hquad : ∀ v : ComplexModel n,
      quad (smoothDDC (planeDistSq n k) z₀) v = leviForm (planeDistSq n k) z₀ v / Real.pi :=
    fun v => smoothDDC_complexDiagonal_eq_leviForm hC2 v
  refine exists_forall_isStrictlyPositive_add_smul_of_pos_on_null hacont
    (fun v => ?_) hS (fun x hx v hv hnull => ?_)
  · rw [hquad]
    exact div_nonneg (leviForm_planeDistSq_nonneg z₀ v) Real.pi_nonneg
  · refine hpos x hx v ?_ hv
    rw [hquad, div_eq_zero_iff] at hnull
    rcases hnull with h | h
    · exact (leviForm_planeDistSq_eq_zero_iff z₀ v).mp h
    · exact absurd h Real.pi_ne_zero

end

end SGPT.Foundations.Analysis.Pending.UniformTubePositivity
