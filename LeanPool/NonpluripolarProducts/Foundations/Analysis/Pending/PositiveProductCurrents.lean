/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ProductTestForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.OrderUnitWeakCompactness

/-!
# Positive currents of bidimension `(q,q)` on a compact complex manifold

A *current of bidimension `(q,q)`* on a complex manifold `M` of dimension `n` (bidegree
`(n-q, n-q)`) is here a real linear functional on the test forms of degree `2q`,
`ProductTestForms.testSpace n M q` — the span of `h · β₁ ∧ ⋯ ∧ β_q` with `h` smooth and
`β_j` smooth real `(1,1)`-forms.  On a compact manifold every smooth form is a test form,
so no support condition appears.  It is *positive* (`demailly-cadg:III.1.13`, "weakly
positive") when it is nonnegative on the test forms that are strongly positive at every
point.  For a Kähler form `ω` the *mass* is the value on `ω^q`
(`demailly-cadg:III.1.14`, up to the normalisation `q!`).

The four operations of step B2 of the TN.4 plan (`scratch/tn4-plan-0133.md`), used by
Demailly--Păun's proof of `dp04-kahler-cone:2.6`/`2.12` and Boucksom's `bou02-volume:4.12`:

* **positivity and mass** — `IsPositive`, `mass`, `mass_nonneg`;
* **the mass controls a positive current** — `exists_abs_apply_le_mul_mass`: for every test
  form `φ` there is `c` with `|T φ| ≤ c · mass T` for every positive `T` (`ω^q` is an order
  unit, `ProductTestForms.exists_orderUnit_bound`);
* **weak compactness** — `isCompact_positive_mass_le` (positive currents of mass `≤ m` form a
  compact set for pointwise convergence) and `exists_ultrafilter_tendsto` (every family of
  positive currents of eventually bounded mass has a weak limit along an ultrafilter, which
  is again positive of mass `≤ m`): `demailly-cadg:III.1.23`;
* **push-forward** along a holomorphic map `f` — `pushforward` (`f_* T = T ∘ f^*`), with
  positivity (`IsPositive.pushforward`), a mass bound on a compact source
  (`exists_mass_pushforward_le`) and weak continuity (`tendsto_pushforward_apply`);
* **wedge with a smooth `(1,1)`-form** — `wedge` (`(T ∧ β)(φ) = T (φ ∧ β)`), positivity for a
  semipositive `β` (`IsPositive.wedge`), `mass_wedge_kahler` (`T ∧ ω` has the mass of `T`) and
  weak continuity.  With it, `T ∧ p₂^*ω` and the `(1,1)`-current `p₁_*(Θ ∧ p₂^*ω)` of
  `dp04-kahler-cone:2.12` are defined.

Positive currents give the same value on geometrically equal test forms
(`IsPositive.apply_eq_of_coeff_eqOn`): only coefficients on chart targets matter.

Not here: the trace measure `T ∧ ω^q` as a Borel measure, closedness, integration currents.
-/

@[expose] public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.PositiveProductCurrents

open FirstPass FirstPass.PositiveClasses StronglyPositiveForms ProductTestForms
  OrderUnitWeakCompactness

noncomputable section

section Basic

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n M) in
/-- A current of bidimension `(q,q)`: a real linear functional on the test forms of degree
`2q`. -/
abbrev ProductCurrent (q : ℕ) := testSpace n M q →ₗ[ℝ] ℝ

/-- Positivity of a current: nonnegative on the strongly positive test forms. -/
def IsPositive {q : ℕ} (T : ProductCurrent n M q) : Prop :=
  PositiveOn (positiveCone n M q) T

theorem IsPositive.add {q : ℕ} {S T : ProductCurrent n M q} (hS : IsPositive S)
    (hT : IsPositive T) : IsPositive (S + T) := fun φ hφ =>
  add_nonneg (hS φ hφ) (hT φ hφ)

theorem IsPositive.smul {q : ℕ} {T : ProductCurrent n M q} (hT : IsPositive T) {c : ℝ}
    (hc : 0 ≤ c) : IsPositive (c • T) := fun φ hφ =>
  mul_nonneg hc (hT φ hφ)

theorem isPositive_zero {q : ℕ} : IsPositive (0 : ProductCurrent n M q) := fun _ _ => le_rfl

/-- A test form whose coefficients vanish on every chart target is killed by every positive
current. -/
theorem IsPositive.apply_eq_zero_of_coeff_eqOn_zero {q : ℕ} {T : ProductCurrent n M q}
    (hT : IsPositive T) {φ : testSpace n M q}
    (hφ : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      (φ : SmoothRealForm n M (2 * q)).coeff e z = 0) : T φ = 0 := by
  have h₁ : φ ∈ positiveCone n M q := fun e z hz => by
    rw [hφ e z hz]
    exact (spCone q).zero_mem
  have h₂ : -φ ∈ positiveCone n M q := fun e z hz => by
    change -(φ : SmoothRealForm n M (2 * q)).coeff e z ∈ spCone q
    rw [hφ e z hz, neg_zero]
    exact (spCone q).zero_mem
  have a := hT φ h₁
  have b := hT (-φ) h₂
  rw [map_neg] at b
  linarith

/-- **Only the coefficients on chart targets matter**: positive currents agree on
geometrically equal test forms. -/
theorem IsPositive.apply_eq_of_coeff_eqOn {q : ℕ} {T : ProductCurrent n M q}
    (hT : IsPositive T) {φ ψ : testSpace n M q}
    (h : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      (φ : SmoothRealForm n M (2 * q)).coeff e z = (ψ : SmoothRealForm n M (2 * q)).coeff e z) :
    T φ = T ψ := by
  have := hT.apply_eq_zero_of_coeff_eqOn_zero (φ := φ - ψ) fun e z hz => by
    change (φ : SmoothRealForm n M (2 * q)).coeff e z - (ψ : SmoothRealForm n M (2 * q)).coeff e z
      = 0
    rw [h e z hz, sub_self]
  rw [map_sub] at this
  linarith

/-- The power `ω^q` of a Kähler form, as a test form. -/
def kahlerTest (w : KahlerBackground n M) (q : ℕ) : testSpace n M q :=
  ⟨formPow w.form.val q, formPow_mem_testSpace (fun e z hz => (w.isKahler.1 e z hz).1) q⟩

theorem kahlerTest_mem_positiveCone (w : KahlerBackground n M) (q : ℕ) :
    kahlerTest w q ∈ positiveCone n M q :=
  formPow_mem_positiveCone w.isKahler.1 q

/-- The mass of a current of bidimension `(q,q)` with respect to a Kähler form `ω` (the
variable `w`): its value on `ω^q`. -/
def mass (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) : ℝ :=
  T (kahlerTest w q)

theorem mass_nonneg (w : KahlerBackground n M) {q : ℕ} {T : ProductCurrent n M q}
    (hT : IsPositive T) : 0 ≤ mass w T :=
  hT _ (kahlerTest_mem_positiveCone w q)

theorem mass_add (w : KahlerBackground n M) {q : ℕ} (S T : ProductCurrent n M q) :
    mass w (S + T) = mass w S + mass w T := rfl

theorem mass_smul (w : KahlerBackground n M) {q : ℕ} (c : ℝ) (T : ProductCurrent n M q) :
    mass w (c • T) = c * mass w T := rfl

end Basic

/-! ### Mass bounds and weak compactness on a compact manifold -/

section Compact

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

theorem isOrderUnit_kahlerTest (w : KahlerBackground n M) (q : ℕ) :
    IsOrderUnit (positiveCone n M q) (kahlerTest w q) := fun φ =>
  exists_orderUnit_bound w.isKahler.1 q φ

/-- **The mass controls every value of a positive current**: for each test form `φ` there is
a constant `c ≥ 0` with `|T φ| ≤ c · mass T` for all positive currents `T`. -/
theorem exists_abs_apply_le_mul_mass (w : KahlerBackground n M) {q : ℕ}
    (φ : testSpace n M q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ProductCurrent n M q, IsPositive T → |T φ| ≤ c * mass w T := by
  obtain ⟨c, hc, h₁, h₂⟩ := isOrderUnit_kahlerTest w q φ
  exact ⟨c, hc, fun T hT => abs_le_mul_of_orderUnit hT h₁ h₂⟩

/-- **Weak compactness of positive currents of bounded mass** (`demailly-cadg:III.1.23`):
the positive currents of mass `≤ m`, viewed as functions on test forms, form a compact set for
the topology of pointwise convergence. -/
theorem isCompact_positive_mass_le (w : KahlerBackground n M) (q : ℕ) (m : ℝ) :
    IsCompact (positiveLeSet (positiveCone n M q) (kahlerTest w q) m) :=
  isCompact_positive_le (isOrderUnit_kahlerTest w q) m

/-- **Weak limits of positive currents of bounded mass.**  A family of positive currents whose
masses are eventually `≤ m` along a filter converges weakly, along some ultrafilter finer than
that filter, to a positive current of mass `≤ m`. -/
theorem exists_ultrafilter_tendsto (w : KahlerBackground n M) {q : ℕ} {m : ℝ} {ι : Type*}
    (l : Filter ι) [l.NeBot] (T : ι → ProductCurrent n M q) (hT : ∀ i, IsPositive (T i))
    (hm : ∀ᶠ i in l, mass w (T i) ≤ m) :
    ∃ (𝒰 : Ultrafilter ι) (S : ProductCurrent n M q), (𝒰 : Filter ι) ≤ l ∧ IsPositive S ∧
      mass w S ≤ m ∧ ∀ φ, Tendsto (fun i => T i φ) (𝒰 : Filter ι) (𝓝 (S φ)) :=
  OrderUnitWeakCompactness.exists_ultrafilter_tendsto (isOrderUnit_kahlerTest w q) l T hT hm

omit [CompactSpace M] in
/-- The mass is weakly continuous: along a weakly convergent family, masses converge. -/
theorem tendsto_mass {w : KahlerBackground n M} {q : ℕ} {ι : Type*} {l : Filter ι}
    {T : ι → ProductCurrent n M q} {S : ProductCurrent n M q}
    (h : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ))) :
    Tendsto (fun i => mass w (T i)) l (𝓝 (mass w S)) :=
  h (kahlerTest w q)

end Compact

/-! ### Push-forward along holomorphic maps -/

section Pushforward

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {f : V → M}

/-- **Push-forward** `f_* T = T ∘ f^*` of a current along a holomorphic map (every test form
on a compact source is compactly supported, so `f` is automatically proper there). -/
def pushforward (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) {q : ℕ}
    (T : ProductCurrent k V q) : ProductCurrent n M q :=
  T ∘ₗ pullbackTestLM hf q

variable (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)

theorem pushforward_apply {q : ℕ} (T : ProductCurrent k V q) (φ : testSpace n M q) :
    pushforward hf T φ = T (pullbackTestLM hf q φ) := rfl

theorem IsPositive.pushforward {q : ℕ} {T : ProductCurrent k V q} (hT : IsPositive T) :
    IsPositive (pushforward hf T) := fun _ hφ =>
  hT _ (pullbackTestLM_mem_positiveCone hf hφ)

theorem pushforward_add {q : ℕ} (S T : ProductCurrent k V q) :
    pushforward hf (S + T) = pushforward hf S + pushforward hf T := rfl

theorem pushforward_smul {q : ℕ} (c : ℝ) (T : ProductCurrent k V q) :
    pushforward hf (c • T) = c • pushforward hf T := rfl

/-- Push-forward is weakly continuous. -/
theorem tendsto_pushforward_apply {q : ℕ} {ι : Type*} {l : Filter ι}
    {T : ι → ProductCurrent k V q} {S : ProductCurrent k V q}
    (h : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ))) (φ : testSpace n M q) :
    Tendsto (fun i => pushforward hf (T i) φ) l (𝓝 (pushforward hf S φ)) :=
  h _

/-- On a compact source the mass of the push-forward is controlled by the mass. -/
theorem exists_mass_pushforward_le [CompactSpace V] (wV : KahlerBackground k V)
    (wM : KahlerBackground n M) (q : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ProductCurrent k V q, IsPositive T →
      mass wM (pushforward hf T) ≤ c * mass wV T := by
  obtain ⟨c, hc, hb⟩ := exists_abs_apply_le_mul_mass wV (pullbackTestLM hf q (kahlerTest wM q))
  exact ⟨c, hc, fun T hT => (le_abs_self _).trans (hb T hT)⟩

end Pushforward

/-! ### Wedge with a smooth `(1,1)`-form -/

section Wedge

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The wedge with a real `(1,1)`-form, `testSpace q → testSpace (q + 1)`. -/
def wedgeTestLM {β : SmoothRealForm n M 2} (hβ : β.IsTypeOneOne) (q : ℕ) :
    testSpace n M q →ₗ[ℝ] testSpace n M (q + 1) where
  toFun φ := ⟨wedgeTwo (φ : SmoothRealForm n M (2 * q)) β, wedgeTwo_mem_testSpace φ.2 hβ⟩
  map_add' φ ψ := Subtype.ext (wedgeTwo_add_left (φ : SmoothRealForm n M (2 * q)) ψ β)
  map_smul' c φ := by
    ext1
    exact wedgeTwo_smul_left c (φ : SmoothRealForm n M (2 * q)) β

/-- The wedge `T ∧ β` of a current of bidimension `(q+1,q+1)` with a real `(1,1)`-form:
`(T ∧ β)(φ) = T (φ ∧ β)`. -/
def wedge {β : SmoothRealForm n M 2} (hβ : β.IsTypeOneOne) {q : ℕ}
    (T : ProductCurrent n M (q + 1)) : ProductCurrent n M q :=
  T ∘ₗ wedgeTestLM hβ q

theorem wedge_apply {β : SmoothRealForm n M 2} (hβ : β.IsTypeOneOne) {q : ℕ}
    (T : ProductCurrent n M (q + 1)) (φ : testSpace n M q) :
    wedge hβ T φ = T (wedgeTestLM hβ q φ) := rfl

/-- The wedge of a positive current with a semipositive `(1,1)`-form is positive. -/
theorem IsPositive.wedge {β : SmoothRealForm n M 2} (hβ : β.IsTypeOneOne)
    (hβp : ∀ (e : ComplexChart n M) z, z ∈ e.val.target → IsSemipositiveOneOne (β.coeff e z))
    {q : ℕ} {T : ProductCurrent n M (q + 1)} (hT : IsPositive T) :
    IsPositive (PositiveProductCurrents.wedge hβ T) := fun _ hφ =>
  hT _ fun e z hz => wedge_mem_spCone (hφ e z hz) (hβp e z hz)

/-- `T ∧ ω` has the mass of `T`: `ω^q ∧ ω = ω^{q+1}`. -/
theorem mass_wedge_kahler (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M (q + 1)) :
    mass w (PositiveProductCurrents.wedge (fun e z hz => (w.isKahler.1 e z hz).1) T) =
      mass w T := rfl

/-- The wedge with a fixed form is weakly continuous. -/
theorem tendsto_wedge_apply {β : SmoothRealForm n M 2} (hβ : β.IsTypeOneOne) {q : ℕ}
    {ι : Type*} {l : Filter ι} {T : ι → ProductCurrent n M (q + 1)}
    {S : ProductCurrent n M (q + 1)} (h : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ)))
    (φ : testSpace n M q) :
    Tendsto (fun i => PositiveProductCurrents.wedge hβ (T i) φ) l
      (𝓝 (PositiveProductCurrents.wedge hβ S φ)) :=
  h _

end Wedge

end

end SGPT.Foundations.Analysis.Pending.PositiveProductCurrents
