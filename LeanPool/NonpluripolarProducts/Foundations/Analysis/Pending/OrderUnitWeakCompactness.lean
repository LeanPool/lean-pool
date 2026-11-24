/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Weak compactness of positive functionals with an order unit

Let `W` be a real vector space, `C ⊆ W` a set of "positive" vectors and `u ∈ W` an
*order unit* for `C`: every `φ ∈ W` satisfies `c • u - φ ∈ C` and `c • u + φ ∈ C` for
some `c ≥ 0`.  A linear functional `T` that is nonnegative on `C` is then bounded on
every vector by its value on `u`: `|T φ| ≤ c * T u`.  Consequently the positive
functionals with `T u ≤ m` form a compact set for the topology of pointwise
convergence (Tychonoff): they lie in the product of the compact intervals
`[-c_φ m, c_φ m]`, and linearity, positivity and `T u ≤ m` are closed conditions.

This is the functional-analytic core of the weak compactness of positive currents
of bounded mass (`demailly-cadg:III.1.23`), used in `dp04-kahler-cone:2.6` and
`bou02-volume:4.12` for weak limits of the forms `α_ε^p`: the test forms are `W`,
the strongly positive test forms are `C`, and a power `ω^q` of a Kähler form is the
order unit, whose value is the mass.  No topology on `W` is used and no
countability is assumed, so limits are taken along ultrafilters
(`exists_ultrafilter_tendsto`), which is what the later weak-limit arguments need.

## Main results

* `PositiveOn`, `IsOrderUnit` — nonnegativity on `C`; the order-unit property.
* `abs_le_mul_of_orderUnit` — the order-unit bound `|T φ| ≤ c * T u`.
* `isCompact_positive_le` — the positive linear maps with `g u ≤ m` form a compact
  subset of `W → ℝ` (product topology).
* `exists_ultrafilter_tendsto` — every family of positive functionals whose values on
  `u` are eventually `≤ m` has a pointwise limit along an ultrafilter finer than the
  given filter; the limit is a positive functional with value `≤ m` on `u`.
-/

@[expose] public section

open Set Filter Topology

namespace SGPT.Foundations.Analysis.Pending.OrderUnitWeakCompactness

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- `T` is nonnegative on the positive set `C`. -/
def PositiveOn (C : Set W) (T : W →ₗ[ℝ] ℝ) : Prop :=
  ∀ φ ∈ C, 0 ≤ T φ

/-- `u` is an order unit for `C`: every vector is squeezed between `± c • u` in the
order defined by `C`, for some `c ≥ 0`. -/
def IsOrderUnit (C : Set W) (u : W) : Prop :=
  ∀ φ : W, ∃ c : ℝ, 0 ≤ c ∧ c • u - φ ∈ C ∧ c • u + φ ∈ C

/-- The order-unit bound: a functional that is nonnegative on `C` is controlled on
`φ` by its value on the order unit. -/
theorem abs_le_mul_of_orderUnit {C : Set W} {u φ : W} {T : W →ₗ[ℝ] ℝ}
    (hT : PositiveOn C T) {c : ℝ} (h₁ : c • u - φ ∈ C) (h₂ : c • u + φ ∈ C) :
    |T φ| ≤ c * T u := by
  have a := hT _ h₁
  have b := hT _ h₂
  rw [map_sub, map_smul, smul_eq_mul] at a
  rw [map_add, map_smul, smul_eq_mul] at b
  rw [abs_le]
  constructor <;> linarith

/-- A positive functional is nonnegative on the order unit. -/
theorem apply_orderUnit_nonneg {C : Set W} {u : W} (hu : IsOrderUnit C u)
    {T : W →ₗ[ℝ] ℝ} (hT : PositiveOn C T) : 0 ≤ T u := by
  obtain ⟨c, hc, -, h₂⟩ := hu u
  have h := hT _ h₂
  rw [map_add, map_smul, smul_eq_mul] at h
  by_contra hneg
  have : (c + 1) * T u < 0 := mul_neg_of_pos_of_neg (by linarith) (lt_of_not_ge hneg)
  linarith

/-- The functions `W → ℝ` that are linear, nonnegative on `C` and at most `m` at `u`. -/
def positiveLeSet (C : Set W) (u : W) (m : ℝ) : Set (W → ℝ) :=
  {g | (∀ x y, g (x + y) = g x + g y) ∧ (∀ (a : ℝ) x, g (a • x) = a * g x) ∧
    (∀ φ ∈ C, 0 ≤ g φ) ∧ g u ≤ m}

theorem isClosed_positiveLeSet (C : Set W) (u : W) (m : ℝ) :
    IsClosed (positiveLeSet C u m) := by
  have h₁ : IsClosed {g : W → ℝ | ∀ x y, g (x + y) = g x + g y} := by
    have : {g : W → ℝ | ∀ x y, g (x + y) = g x + g y} =
        ⋂ x, ⋂ y, {g | g (x + y) = g x + g y} := by
      ext g; simp
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x).add (continuous_apply y))
  have h₂ : IsClosed {g : W → ℝ | ∀ (a : ℝ) x, g (a • x) = a * g x} := by
    have : {g : W → ℝ | ∀ (a : ℝ) x, g (a • x) = a * g x} =
        ⋂ (a : ℝ), ⋂ x, {g | g (a • x) = a * g x} := by
      ext g; simp
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun x =>
      isClosed_eq (continuous_apply _) (continuous_const.mul (continuous_apply _))
  have h₃ : IsClosed {g : W → ℝ | ∀ φ ∈ C, 0 ≤ g φ} := by
    have : {g : W → ℝ | ∀ φ ∈ C, 0 ≤ g φ} = ⋂ φ ∈ C, {g | 0 ≤ g φ} := by
      ext g; simp
    rw [this]
    exact isClosed_biInter fun φ _ => isClosed_le continuous_const (continuous_apply _)
  have h₄ : IsClosed {g : W → ℝ | g u ≤ m} :=
    isClosed_le (continuous_apply _) continuous_const
  exact h₁.inter (h₂.inter (h₃.inter h₄))

/-- The linear map underlying a point of `positiveLeSet`. -/
def toLinearMap {C : Set W} {u : W} {m : ℝ} (g : W → ℝ) (hg : g ∈ positiveLeSet C u m) :
    W →ₗ[ℝ] ℝ where
  toFun := g
  map_add' := hg.1
  map_smul' := hg.2.1

@[simp] theorem toLinearMap_apply {C : Set W} {u : W} {m : ℝ} (g : W → ℝ)
    (hg : g ∈ positiveLeSet C u m) (φ : W) : toLinearMap g hg φ = g φ := rfl

theorem mem_positiveLeSet {C : Set W} {u : W} {m : ℝ} {T : W →ₗ[ℝ] ℝ}
    (hT : PositiveOn C T) (hm : T u ≤ m) : ⇑T ∈ positiveLeSet C u m :=
  ⟨T.map_add, fun a x => by rw [map_smul, smul_eq_mul], hT, hm⟩

/-- **Weak compactness.**  If `u` is an order unit for `C`, the functionals that are
linear, nonnegative on `C` and at most `m` at `u` form a compact subset of `W → ℝ`
with the product topology (the topology of pointwise convergence). -/
theorem isCompact_positive_le {C : Set W} {u : W} (hu : IsOrderUnit C u) (m : ℝ) :
    IsCompact (positiveLeSet C u m) := by
  choose c hc0 hc₁ hc₂ using hu
  have hsub : positiveLeSet C u m ⊆
      Set.pi univ (fun φ => Icc (-(c φ * m)) (c φ * m)) := by
    intro g hg φ _
    let T := toLinearMap g hg
    have hT : PositiveOn C T := hg.2.2.1
    have hb := abs_le_mul_of_orderUnit hT (hc₁ φ) (hc₂ φ)
    have hle : c φ * T u ≤ c φ * m := mul_le_mul_of_nonneg_left hg.2.2.2 (hc0 φ)
    have := abs_le.mp (hb.trans hle)
    exact ⟨by simpa [T] using this.1, by simpa [T] using this.2⟩
  exact (isCompact_univ_pi fun φ => isCompact_Icc).of_isClosed_subset
    (isClosed_positiveLeSet C u m) hsub

/-- **Weak limits along ultrafilters.**  A family of functionals that are nonnegative
on `C` and eventually at most `m` at the order unit `u` converges pointwise, along some
ultrafilter finer than the given filter, to a functional with the same two
properties. -/
theorem exists_ultrafilter_tendsto {C : Set W} {u : W} (hu : IsOrderUnit C u) {m : ℝ}
    {ι : Type*} (l : Filter ι) [l.NeBot] (T : ι → W →ₗ[ℝ] ℝ)
    (hT : ∀ i, PositiveOn C (T i)) (hm : ∀ᶠ i in l, T i u ≤ m) :
    ∃ (𝒰 : Ultrafilter ι) (S : W →ₗ[ℝ] ℝ), (𝒰 : Filter ι) ≤ l ∧ PositiveOn C S ∧
      S u ≤ m ∧ ∀ φ, Tendsto (fun i => T i φ) (𝒰 : Filter ι) (𝓝 (S φ)) := by
  let 𝒰 : Ultrafilter ι := Ultrafilter.of l
  have h𝒰 : (𝒰 : Filter ι) ≤ l := Ultrafilter.of_le l
  let g : ι → W → ℝ := fun i => ⇑(T i)
  have hmem : ∀ᶠ i in (𝒰 : Filter ι), g i ∈ positiveLeSet C u m :=
    Filter.Eventually.mono (h𝒰 hm) fun i hi => mem_positiveLeSet (hT i) hi
  have hK := isCompact_positive_le hu m
  obtain ⟨f, hf, hlim⟩ := hK.ultrafilter_le_nhds (𝒰.map g)
    (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hmem)
  refine ⟨𝒰, toLinearMap f hf, h𝒰, hf.2.2.1, hf.2.2.2, fun φ => ?_⟩
  have h₁ : Tendsto g (𝒰 : Filter ι) (𝓝 f) := by
    simpa [Tendsto, Ultrafilter.coe_map] using hlim
  exact (continuous_apply φ).continuousAt.tendsto.comp h₁

end SGPT.Foundations.Analysis.Pending.OrderUnitWeakCompactness
