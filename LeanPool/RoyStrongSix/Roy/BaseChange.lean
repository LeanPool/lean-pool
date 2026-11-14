/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext

/-!
# Base change from a subfield `F ⊆ ℂ` to `ℂ` for coordinate vector spaces

Let `F` be a field with an algebra map `F → ℂ` (we use `F = ℚ` and `F = Qbar`), and `ι` a finite
index type. A vector of `ℂ^ι` is an *`F`-point* if all its coordinates lie in the image of `F`;
the `F`-points form an `F`-subspace `Fpts F ι`. A `ℂ`-subspace is *`F`-rational* if it is the
`ℂ`-span of an `F`-subspace of `F`-points.

Main results:
* `linearIndependent_of_Fpts`: `F`-independent `F`-points are `ℂ`-independent.
* `finrank_span_of_le_Fpts`: `dim_ℂ (span_ℂ A) = dim_F A`.
* `mem_span_iff_of_le_Fpts`: an `F`-point lies in `span_ℂ A` iff it lies in `A`.
* `span_inf_span_of_le_Fpts`: `span_ℂ A ⊓ span_ℂ B = span_ℂ (A ⊓ B)`.
* `isRat_ker`: the kernel of a `ℂ`-linear map sending `F`-points to `F`-points is `F`-rational.
* `map_Fpts_eq_of_surjective`: such a surjective map sends `F`-points onto `F`-points.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

namespace StrongSix.Roy

variable (F : Type*) [Field F] [Algebra F ℂ]

/-- The `F`-points of `ℂ^ι`, as an `F`-subspace. -/
def Fpts (ι : Type*) : Submodule F (ι → ℂ) where
  carrier := {x | ∀ i, x i ∈ (algebraMap F ℂ).range}
  add_mem' {x y} hx hy i := by
    obtain ⟨a, ha⟩ := hx i; obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  zero_mem' i := ⟨0, by rw [map_zero]; rfl⟩
  smul_mem' c x hx i := by
    obtain ⟨a, ha⟩ := hx i
    exact ⟨c * a, by rw [map_mul, ha, Pi.smul_apply, Algebra.smul_def]⟩

/-- A `ℂ`-subspace of `ℂ^ι` is `F`-rational if it is the span of an `F`-subspace of `F`-points. -/
def IsRat {ι : Type*} (S : Submodule ℂ (ι → ℂ)) : Prop :=
  ∃ A : Submodule F (ι → ℂ), A ≤ Fpts F ι ∧ S = span ℂ (A : Set (ι → ℂ))

/-- `f` sends `F`-points to `F`-points. -/
def PresF {ι κ : Type*} (f : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) : Prop :=
  ∀ x ∈ Fpts F ι, f x ∈ Fpts F κ

variable {F}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem single_mem_Fpts (i : ι) : (Pi.single i 1 : ι → ℂ) ∈ Fpts F ι := by
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by rw [map_one, Pi.single_eq_same]⟩
  · exact ⟨0, by rw [map_zero, Pi.single_eq_of_ne h]⟩

omit [Fintype ι] in
theorem Fpts_eq_span [Finite ι] :
    Fpts F ι = Submodule.span F (Set.range fun i : ι => (Pi.single i 1 : ι → ℂ)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    choose a ha using hx
    have : x = ∑ i, a i • (Pi.single i 1 : ι → ℂ) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, ha]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_Fpts i

omit [DecidableEq ι] [Fintype ι] in
omit [DecidableEq ι] in
instance [Finite ι] : FiniteDimensional F (Fpts F ι) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let : Fintype ι := Fintype.ofFinite ι
  rw [Fpts_eq_span]
  exact FiniteDimensional.span_of_finite F (Set.finite_range _)

omit [DecidableEq ι] [Fintype ι] in
theorem span_Fpts_eq_top [Finite ι] : span ℂ ((Fpts F ι : Submodule F (ι → ℂ)) : Set (ι → ℂ)) =
  ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • (Pi.single i 1 : ι → ℂ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span (single_mem_Fpts i))

omit [Fintype ι] [DecidableEq ι] in
/-- **Base change of linear independence.** -/
theorem linearIndependent_of_Fpts {κ : Type*} {v : κ → ι → ℂ}
    (hv : ∀ k, v k ∈ Fpts F ι) (hind : LinearIndependent F v) : LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff'] at hind ⊢
  intro s g hg k0 hk0
  by_contra hne
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F ℂ, φ (g k0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff F (g k0)).mp h)
  choose a ha using hv
  have key : ∑ k ∈ s, φ (g k) • v k = 0 := by
    funext i
    have hi : ∑ k ∈ s, g k * v k i = 0 := by
      have := congrFun hg i
      rw [Finset.sum_apply] at this
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    have h2 : ∑ k ∈ s, a k i * φ (g k) = 0 := by
      have h3 : φ (∑ k ∈ s, g k * v k i) = 0 := by rw [hi, map_zero]
      rw [map_sum] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← ha k i, mul_comm (g k), ← Algebra.smul_def, map_smul, smul_eq_mul]
    calc (∑ k ∈ s, φ (g k) • v k) i = ∑ k ∈ s, algebraMap F ℂ (a k i * φ (g k)) := by
          rw [Finset.sum_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Pi.smul_apply, Algebra.smul_def, ← ha k i, map_mul, mul_comm]
      _ = algebraMap F ℂ (∑ k ∈ s, a k i * φ (g k)) := by rw [map_sum]
      _ = 0 := by rw [h2, map_zero]
  exact hφ (hind s _ key k0 hk0)

omit [Fintype ι] [DecidableEq ι] in
/-- `span_ℂ A` equals the `ℂ`-span of an `F`-basis of `A`. -/
theorem span_eq_span_basis (A : Submodule F (ι → ℂ)) {κ : Type*} (b : Basis κ F A) :
    span ℂ (A : Set (ι → ℂ)) = span ℂ (Set.range fun i => (b i : ι → ℂ)) := by
  apply le_antisymm
  · rw [span_le]
    intro x hx
    have h1 : (⟨x, hx⟩ : A) ∈ span F (Set.range b) := by rw [b.span_eq]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span A.subtype h1
    rw [← Set.range_comp] at h2
    exact span_le_restrictScalars F ℂ _ h2
  · rw [span_le]
    rintro _ ⟨i, rfl⟩
    exact subset_span (b i).2

omit [DecidableEq ι] [Fintype ι] in
/-- `dim_ℂ (span_ℂ A) = dim_F A` for an `F`-subspace `A` of `F`-points. -/
theorem finrank_span_of_le_Fpts [Finite ι] (A : Submodule F (ι → ℂ)) (hA : A ≤ Fpts F ι) :
    finrank ℂ (span ℂ (A : Set (ι → ℂ))) = finrank F A := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional F A := Submodule.finiteDimensional_of_le hA
  let b := Module.finBasis F A
  have hind : LinearIndependent F (fun i => (b i : ι → ℂ)) :=
    b.linearIndependent.map' A.subtype (by simp)
  have hindC : LinearIndependent ℂ (fun i => (b i : ι → ℂ)) :=
    linearIndependent_of_Fpts (fun i => hA (b i).2) hind
  rw [span_eq_span_basis A b, finrank_span_eq_card hindC, Fintype.card_fin]

omit [DecidableEq ι] [Fintype ι] in
/-- An `F`-point lies in `span_ℂ A` iff it lies in `A`. -/
theorem mem_span_iff_of_le_Fpts [Finite ι] (A : Submodule F (ι → ℂ)) (hA : A ≤ Fpts F ι)
    {x : ι → ℂ} (hx : x ∈ Fpts F ι) : x ∈ span ℂ (A : Set (ι → ℂ)) ↔ x ∈ A := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun h => ?_, fun h => subset_span h⟩
  by_contra hxA
  have : FiniteDimensional F A := Submodule.finiteDimensional_of_le hA
  set B : Submodule F (ι → ℂ) := A ⊔ span F {x} with hB
  have hBle : B ≤ Fpts F ι := sup_le hA (by rw [span_le, Set.singleton_subset_iff]; exact hx)
  have hx0 : x ≠ 0 := fun h0 => hxA (h0 ▸ A.zero_mem)
  have hdisj : A ⊓ span F {x} = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hyA, hyx⟩
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp hyx
    by_cases hc : c = 0
    · rw [hc, zero_smul]; exact zero_mem _
    · exact absurd (by simpa [smul_smul, inv_mul_cancel₀ hc] using A.smul_mem c⁻¹ hyA) hxA
  have hdimB : finrank F B = finrank F A + 1 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq A (span F {x})
    rw [hdisj, finrank_bot, finrank_span_singleton hx0] at this
    omega
  have hspanB : span ℂ (B : Set (ι → ℂ)) = span ℂ (A : Set (ι → ℂ)) := by
    apply le_antisymm
    · rw [span_le]
      intro y hy
      obtain ⟨a, ha, z, hz, rfl⟩ := mem_sup.mp hy
      obtain ⟨c, rfl⟩ := mem_span_singleton.mp hz
      exact add_mem (subset_span ha) ((span ℂ (A : Set (ι → ℂ))).smul_of_tower_mem c h)
    · exact span_mono (le_sup_left : A ≤ B)
  have h1 := finrank_span_of_le_Fpts B hBle
  rw [hspanB, finrank_span_of_le_Fpts A hA] at h1
  omega

omit [DecidableEq ι] [Fintype ι] in
/-- The intersection of two `F`-rational spans is the span of the intersection. -/
theorem span_inf_span_of_le_Fpts [Finite ι] (A B : Submodule F (ι → ℂ)) (hA : A ≤ Fpts F ι)
    (hB : B ≤ Fpts F ι) :
    span ℂ (A : Set (ι → ℂ)) ⊓ span ℂ (B : Set (ι → ℂ)) =
      span ℂ ((A ⊓ B : Submodule F (ι → ℂ)) : Set (ι → ℂ)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hle : span ℂ ((A ⊓ B : Submodule F (ι → ℂ)) : Set (ι → ℂ)) ≤
      span ℂ (A : Set (ι → ℂ)) ⊓ span ℂ (B : Set (ι → ℂ)) :=
    le_inf (span_mono inf_le_left) (span_mono inf_le_right)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hsup : span ℂ ((A ⊔ B : Submodule F (ι → ℂ)) : Set (ι → ℂ)) =
      span ℂ (A : Set (ι → ℂ)) ⊔ span ℂ (B : Set (ι → ℂ)) := by
    rw [← span_union]
    apply le_antisymm
    · rw [span_le]
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hy
      exact add_mem (subset_span (Or.inl ha)) (subset_span (Or.inr hb))
    · exact span_mono (Set.union_subset (le_sup_left : A ≤ A ⊔ B) (le_sup_right : B ≤ A ⊔ B))
  have : FiniteDimensional F A := Submodule.finiteDimensional_of_le hA
  have : FiniteDimensional F B := Submodule.finiteDimensional_of_le hB
  have eC := Submodule.finrank_sup_add_finrank_inf_eq (span ℂ (A : Set (ι → ℂ)))
    (span ℂ (B : Set (ι → ℂ)))
  have eF := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [← hsup, finrank_span_of_le_Fpts _ (sup_le hA hB), finrank_span_of_le_Fpts A hA,
    finrank_span_of_le_Fpts B hB] at eC
  rw [finrank_span_of_le_Fpts _ (inf_le_left.trans hA)]
  omega

/-! ### Maps preserving `F`-points -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
omit [DecidableEq ι] [Fintype ι] in
/-- The `F`-linear restriction of an `F`-point-preserving map to `F`-points, as a submodule map. -/
theorem range_eq_span_map_Fpts [Finite ι] (f : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) :
    LinearMap.range f =
      span ℂ (((Fpts F ι).map (f.restrictScalars F) : Submodule F (κ → ℂ)) : Set (κ → ℂ)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ span ℂ ((Fpts F ι : Submodule F (ι → ℂ)) : Set (ι → ℂ)) := by
      rw [span_Fpts_eq_top]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span f hx
    refine span_mono ?_ this
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rw [span_le]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩

omit [DecidableEq ι] [DecidableEq κ] in
omit [Fintype ι] [Fintype κ] in
theorem finrank_range_eq [Finite ι] [Finite κ] (f : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (hf : PresF F f) :
    finrank ℂ (LinearMap.range f) = finrank F ((Fpts F ι).map (f.restrictScalars F)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  rw [range_eq_span_map_Fpts (F := F) f]
  apply finrank_span_of_le_Fpts
  rintro _ ⟨x, hx, rfl⟩
  exact hf x hx

omit [DecidableEq ι] in
theorem finrank_Fpts : finrank F (Fpts F ι) = Fintype.card ι := by
  classical
  have h := finrank_span_of_le_Fpts (F := F) (Fpts F ι) le_rfl
  rw [span_Fpts_eq_top, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  exact h.symm

omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ] in
/-- **Kernels of `F`-point-preserving maps are `F`-rational.** -/
theorem isRat_ker [Finite ι] [Finite κ] (f : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (hf : PresF F f) :
    IsRat F (LinearMap.ker f) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let : DecidableEq κ := Classical.decEq κ
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  set A : Submodule F (ι → ℂ) := (LinearMap.ker f).restrictScalars F ⊓ Fpts F ι with hA
  have hAle : A ≤ Fpts F ι := inf_le_right
  refine ⟨A, hAle, ?_⟩
  have hle : span ℂ (A : Set (ι → ℂ)) ≤ LinearMap.ker f := by
    rw [span_le]; intro x hx; exact hx.1
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  let fF : Fpts F ι →ₗ[F] (κ → ℂ) := (f.restrictScalars F).comp (Fpts F ι).subtype
  have hkermap : (LinearMap.ker fF).map (Fpts F ι).subtype = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hrange : LinearMap.range fF = (Fpts F ι).map (f.restrictScalars F) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have rnF := LinearMap.finrank_range_add_finrank_ker fF
  have rnC := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_Fpts] at rnF
  rw [Module.finrank_fintype_fun_eq_card, finrank_range_eq f hf] at rnC
  have hA' : finrank F A = finrank F (LinearMap.ker fF) := by
    rw [← hkermap, Submodule.finrank_map_subtype_eq]
  rw [finrank_span_of_le_Fpts A hAle, hA']
  omega

omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ] in
/-- A surjective `F`-point-preserving map sends `F`-points onto `F`-points. -/
theorem map_Fpts_eq_of_surjective [Finite ι] [Finite κ] (f : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (hf : PresF F f)
    (hs : Function.Surjective f) :
    (Fpts F ι).map (f.restrictScalars F) = Fpts F κ := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let : DecidableEq κ := Classical.decEq κ
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  have hle : (Fpts F ι).map (f.restrictScalars F) ≤ Fpts F κ := by
    rintro _ ⟨x, hx, rfl⟩; exact hf x hx
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [← finrank_range_eq f hf, LinearMap.range_eq_top.mpr hs, finrank_top,
    Module.finrank_fintype_fun_eq_card, finrank_Fpts]

end StrongSix.Roy

end LeanPool
