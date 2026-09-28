/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.ProjIcc

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Topology.Angle`.
* `ForMathlib.Topology.Order.Compact`.
* `ForMathlib.Topology.Order.Concatenation`.
* `ForMathlib.Topology.Order.Interval`.
* `ForMathlib.Topology.Order.IntervalExtension`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Angle
-/

@[expose] public section

open scoped unitInterval

namespace Real.Angle

/-- A continuous angle path starting at zero has a continuous real lift starting at zero. -/
theorem exists_continuous_lift_zero (θ : I → Real.Angle) (hθ : Continuous θ)
    (hzero : θ 0 = 0) :
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ ∀ t, (α t : Real.Angle) = θ t := by
  have hcov : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2 * Real.pi)
  obtain ⟨α, hα, hα0⟩ := hcov.exists_path_lifts
    (⟨θ, hθ⟩ : C(I, Real.Angle)) (0 : ℝ) (by simpa using hzero)
  exact ⟨α, α.continuous, hα0, fun t ↦ congrFun hα t⟩

end Real.Angle

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Compact
-/

@[expose] public section

/-- A positive continuous function has a positive uniform lower bound on a nonempty compact set. -/
theorem IsCompact.exists_pos_forall_le {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsCompact s) (hne : s.Nonempty) {f : X → ℝ}
    (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ m > 0, ∀ x ∈ s, m ≤ f x := by
  obtain ⟨x, hx, hxmin⟩ := hs.exists_isMinOn hne hf
  exact ⟨f x, hpos x hx, fun y hy ↦ hxmin hy⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Concatenation
-/

@[expose] public section

namespace Function

/-- Concatenate two functions on `[0, 1]` on the interval `[0, 2]`. -/
noncomputable def concatUnitIntervals {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E)
    (t : Set.Icc (0 : ℝ) 2) : E :=
  if (t : ℝ) ≤ 1 then x (Set.projIcc 0 1 (by norm_num) t)
  else y (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))

/-- Concatenation is continuous when the endpoint values agree. -/
theorem continuous_concatUnitIntervals {E : Type*} [TopologicalSpace E]
    {x y : Set.Icc (0 : ℝ) 1 → E} (hx : Continuous x) (hy : Continuous y)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    Continuous (concatUnitIntervals x y) := by
  unfold concatUnitIntervals
  apply continuous_if_le continuous_subtype_val continuous_const
  · simpa only [Function.comp_def] using
      (hx.comp (continuous_projIcc.comp continuous_subtype_val)).continuousOn
  · simpa only [Function.comp_def, Pi.sub_apply] using
      (hy.comp
        (continuous_projIcc.comp (continuous_subtype_val.sub continuous_const))).continuousOn
  intro t ht
  simpa [ht] using hjoin

@[simp] theorem concatUnitIntervals_zero {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨0, by norm_num⟩ = x ⟨0, by norm_num⟩ := by
  simp [concatUnitIntervals]

@[simp] theorem concatUnitIntervals_one {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨1, by norm_num⟩ = x ⟨1, by norm_num⟩ := by
  simp [concatUnitIntervals]

@[simp] theorem concatUnitIntervals_two {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨2, by norm_num⟩ = y ⟨1, by norm_num⟩ := by
  norm_num [concatUnitIntervals]

/-- Joined paths have precisely the union of the two original ranges. -/
theorem range_concatUnitIntervals {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    Set.range (concatUnitIntervals x y) = Set.range x ∪ Set.range y := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    unfold concatUnitIntervals
    split_ifs
    · exact Or.inl (Set.mem_range_self _)
    · exact Or.inr (Set.mem_range_self _)
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · refine ⟨⟨t, t.property.1, t.property.2.trans (by norm_num)⟩, ?_⟩
      simp [concatUnitIntervals, t.property.2, Set.projIcc_of_mem (by norm_num) t.property]
    · by_cases ht : (t : ℝ) = 0
      · refine ⟨⟨1, by norm_num⟩, ?_⟩
        rw [concatUnitIntervals_one, hjoin]
        congr 1
        exact Subtype.ext ht.symm
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        refine ⟨⟨(t : ℝ) + 1, by constructor <;> linarith [t.property.1, t.property.2]⟩, ?_⟩
        have hnot : ¬(t : ℝ) + 1 ≤ 1 := by linarith
        simp [concatUnitIntervals, hnot, Set.projIcc_of_mem (by norm_num) t.property]

/-- A strict cyclic cut preserves injectivity away from the final endpoint. -/
theorem injOn_concatUnitIntervals_comp_of_cyclic_endpoints
    {E : Type*} {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → E}
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b)
    (φ ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b)
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hφ₀ : φ ⟨0, by norm_num⟩ = s)
    (hψ₀ : ψ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩)
    (hψ₁ : ψ ⟨1, by norm_num⟩ = s) :
    Set.InjOn (concatUnitIntervals (x ∘ φ) (x ∘ ψ)) {t | (t : ℝ) < 2} := by
  have hab' : a < b := has.trans hsb
  have hinj' : Set.InjOn x {t | a < (t : ℝ)} := by
    intro p hp q hq hpq
    by_cases hpb : (p : ℝ) < b
    · by_cases hqb : (q : ℝ) < b
      · exact hinj hpb hqb hpq
      · have hqeq : q = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
          apply Subtype.ext
          exact le_antisymm q.property.2 (le_of_not_gt hqb)
        have hpa : p = (⟨a, le_rfl, hab⟩ : Set.Icc a b) := by
          apply hinj hpb hab'
          rw [hqeq] at hpq
          exact hpq.trans hclosed.symm
        exact False.elim ((ne_of_gt hp) (congrArg Subtype.val hpa))
    · have hpeq : p = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
        apply Subtype.ext
        exact le_antisymm p.property.2 (le_of_not_gt hpb)
      by_cases hqb : (q : ℝ) < b
      · have hqa : q = (⟨a, le_rfl, hab⟩ : Set.Icc a b) := by
          apply hinj hqb hab'
          rw [hpeq] at hpq
          exact hpq.symm.trans hclosed.symm
        exact False.elim ((ne_of_gt hq) (congrArg Subtype.val hqa))
      · have hqeq : q = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
          apply Subtype.ext
          exact le_antisymm q.property.2 (le_of_not_gt hqb)
        exact hpeq.trans hqeq.symm
  intro u hu v hv huv
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hv0 : 0 ≤ (v : ℝ) := v.property.1
  have hu2 : (u : ℝ) < 2 := hu
  have hv2 : (v : ℝ) < 2 := hv
  by_cases hu1 : (u : ℝ) ≤ 1
  · let pu : Set.Icc (0 : ℝ) 1 := ⟨u, hu0, hu1⟩
    have hueval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) u = x (φ pu) := by
      simp [concatUnitIntervals, hu1, pu,
        Set.projIcc_of_mem (by norm_num) ⟨hu0, hu1⟩]
    have hφu : (s : ℝ) ≤ φ pu := by
      rw [← hφ₀]
      exact hφ.monotone pu.property.1
    by_cases hv1 : (v : ℝ) ≤ 1
    · let pv : Set.Icc (0 : ℝ) 1 := ⟨v, hv0, hv1⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (φ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) ⟨hv0, hv1⟩]
      have hφv : (s : ℝ) ≤ φ pv := by
        rw [← hφ₀]
        exact hφ.monotone pv.property.1
      have hp : φ pu = φ pv := hinj' (has.trans_le hφu) (has.trans_le hφv)
        (hueval ▸ huv ▸ hveval)
      apply Subtype.ext
      simpa [pu, pv] using congrArg Subtype.val (hφ.injective hp)
    · have hv1' : 1 < (v : ℝ) := lt_of_not_ge hv1
      have hvp : 0 ≤ (v : ℝ) - 1 ∧ (v : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
      let pv : Set.Icc (0 : ℝ) 1 := ⟨(v : ℝ) - 1, hvp⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (ψ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) hvp]
      have hψvpos : a < (ψ pv : ℝ) := by
        have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pv by
          change 0 < (v : ℝ) - 1
          linarith)
        rw [hψ₀] at h
        exact h
      have hp : φ pu = ψ pv := hinj' (has.trans_le hφu) hψvpos
        (hueval ▸ huv ▸ hveval)
      have hψvlt : (ψ pv : ℝ) < s := by
        have h := hψ (show pv < (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) by
          change (v : ℝ) - 1 < 1
          linarith)
        rw [hψ₁] at h
        exact h
      exact False.elim ((not_le_of_gt hψvlt) (hp ▸ hφu))
  · have hu1' : 1 < (u : ℝ) := lt_of_not_ge hu1
    have hup : 0 ≤ (u : ℝ) - 1 ∧ (u : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
    let pu : Set.Icc (0 : ℝ) 1 := ⟨(u : ℝ) - 1, hup⟩
    have hueval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) u = x (ψ pu) := by
      simp [concatUnitIntervals, hu1, pu,
        Set.projIcc_of_mem (by norm_num) hup]
    have hψupos : a < (ψ pu : ℝ) := by
      have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pu by
        change 0 < (u : ℝ) - 1
        linarith)
      rw [hψ₀] at h
      exact h
    by_cases hv1 : (v : ℝ) ≤ 1
    · let pv : Set.Icc (0 : ℝ) 1 := ⟨v, hv0, hv1⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (φ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) ⟨hv0, hv1⟩]
      have hφv : (s : ℝ) ≤ φ pv := by
        rw [← hφ₀]
        exact hφ.monotone pv.property.1
      have hp : ψ pu = φ pv := hinj' hψupos (has.trans_le hφv)
        (hueval ▸ huv ▸ hveval)
      have hψult : (ψ pu : ℝ) < s := by
        have h := hψ (show pu < (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) by
          change (u : ℝ) - 1 < 1
          linarith)
        rw [hψ₁] at h
        exact h
      exact False.elim ((not_le_of_gt hψult) (hp ▸ hφv))
    · have hvp : 0 ≤ (v : ℝ) - 1 ∧ (v : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
      let pv : Set.Icc (0 : ℝ) 1 := ⟨(v : ℝ) - 1, hvp⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (ψ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) hvp]
      have hψvpos : a < (ψ pv : ℝ) := by
        have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pv by
          change 0 < (v : ℝ) - 1
          linarith)
        rw [hψ₀] at h
        exact h
      have hp : ψ pu = ψ pv := hinj' hψupos hψvpos (hueval ▸ huv ▸ hveval)
      have hp' := congrArg Subtype.val (hψ.injective hp)
      apply Subtype.ext
      simp [pu, pv] at hp'
      linarith

end Function

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Interval
-/

@[expose] public section

namespace Set

instance instCompactIccSpaceIcc (a b : ℝ) : CompactIccSpace (Icc a b) :=
  ⟨fun {_ _} ↦ isClosed_Icc.isCompact⟩

end Set

/-- Reverse a closed real interval about its midpoint. -/
def Set.Icc.reverse {a b : ℝ} (_hab : a ≤ b) :
    Set.Icc a b → Set.Icc a b := fun t ↦
  ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩

/-- Interval reversal is continuous. -/
theorem Set.Icc.continuous_reverse {a b : ℝ} (hab : a ≤ b) :
    Continuous (Set.Icc.reverse hab) :=
  (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

/-- Interval reversal is antitone. -/
theorem Set.Icc.antitone_reverse {a b : ℝ} (hab : a ≤ b) :
    Antitone (Set.Icc.reverse hab) := by
  intro x y hxy
  have hxy' : (x : ℝ) ≤ y := hxy
  change a + b - (y : ℝ) ≤ a + b - (x : ℝ)
  linarith

/-- Reversing a closed interval twice is the identity. -/
theorem Set.Icc.involutive_reverse {a b : ℝ} (hab : a ≤ b) :
    Function.Involutive (Set.Icc.reverse hab) := by
  intro x
  apply Subtype.ext
  simp [Set.Icc.reverse]

/-- Interval reversal is surjective. -/
theorem Set.Icc.surjective_reverse {a b : ℝ} (hab : a ≤ b) :
    Function.Surjective (Set.Icc.reverse hab) :=
  (Set.Icc.involutive_reverse hab).surjective

open Set Filter
open scoped Topology

/-- Replace the terminal value of a one-sided continuous function by its left limit. -/
theorem continuousOn_replace_right_endpoint {E : Type*} [TopologicalSpace E]
    {a b : ℝ} (hab : a < b) (f : ℝ → E) (z : E)
    (hr : ∀ t ∈ Ico a b, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hl : ∀ t ∈ Ioo a b, Tendsto f (𝓝[<] t) (𝓝 (f t)))
    (hb : Tendsto f (𝓝[<] b) (𝓝 z)) :
    ContinuousOn (fun t ↦ if t = b then z else f t) (Icc a b) := by
  let g : ℝ → E := fun t ↦ if t = b then z else f t
  have heql {t : ℝ} (ht : t ≤ b) : g =ᶠ[𝓝[<] t] f := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hne : u ≠ b := (lt_of_lt_of_le hu ht).ne
    simp [g, hne]
  have heqr {t : ℝ} (ht : t < b) : g =ᶠ[𝓝[>] t] f := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with u hu
    simp [g, (show u ≠ b from hu.ne)]
  intro t ht
  change ContinuousWithinAt g (Icc a b) t
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · have h : ContinuousWithinAt g (Ioi a) a := by
      change Tendsto g _ _
      simpa only [g, ite_eq_right hab.ne] using (hr a ⟨le_rfl, hab⟩).congr' (heqr hab).symm
    exact (continuousWithinAt_Ioi_iff_Ici.mp h).mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · apply ContinuousAt.continuousWithinAt
      apply continuousAt_iff_continuous_left'_right'.mpr
      constructor
      · change Tendsto g _ _
        simpa only [g, ite_eq_right htb.ne] using (hl t ⟨hat, htb⟩).congr' (heql htb.le).symm
      · change Tendsto g _ _
        simpa only [g, ite_eq_right htb.ne] using (hr t ⟨hat.le, htb⟩).congr' (heqr htb).symm
    · have h : ContinuousWithinAt g (Iio t) t := by
        change Tendsto g _ _
        simpa only [g, ite_eq_left rfl] using hb.congr' (heql le_rfl).symm
      exact (continuousWithinAt_Iio_iff_Iic.mp h).mono Icc_subset_Iic_self

/-- Every compact real interval carries finite monotone partitions, with prescribed
endpoints, whose mesh eventually falls below any positive threshold. -/
theorem Set.Icc.exists_partitions_mesh_tendsto_zero {a b : ℝ} (hab : a ≤ b) :
    ∃ cuts : ∀ k : ℕ, Fin (k + 2) → Set.Icc a b,
      (∀ k, Monotone (cuts k)) ∧ (∀ k, (cuts k 0 : ℝ) = a) ∧
      (∀ k, (cuts k (Fin.last (k + 1)) : ℝ) = b) ∧
      ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (k + 1),
        (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ := by
  let cuts (k : ℕ) (i : Fin (k + 2)) : Set.Icc a b :=
    ⟨a + (b - a) * (i : ℝ) / (k + 1), by
      have hk : (0 : ℝ) < k + 1 := by positivity
      have hi : (i : ℝ) ≤ k + 1 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      constructor
      · exact le_add_of_nonneg_right (div_nonneg
          (mul_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)) hk.le)
      · have hmul := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab)
        have hdiv : (b - a) * (i : ℝ) / (k + 1) ≤ b - a :=
          (div_le_iff₀ hk).mpr hmul
        linarith⟩
  refine ⟨cuts, ?_, ?_, ?_, ?_⟩
  · intro k i j hij
    change a + (b - a) * (i : ℝ) / (k + 1) ≤ a + (b - a) * (j : ℝ) / (k + 1)
    gcongr
    exact_mod_cast hij
  · intro k
    simp [cuts]
  · intro k
    dsimp [cuts]
    push_cast
    rw [mul_div_cancel_right₀ _ (by positivity)]
    ring
  · intro δ hδ
    have ht : Filter.Tendsto (fun k : ℕ ↦ (b - a) / (k + 1))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk
    intro i
    convert hk using 1
    dsimp [cuts]
    push_cast
    ring

/-- The increasing affine surjection between two nondegenerate closed intervals. -/
theorem Set.Icc.exists_affine_monotone_surjection {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ φ : Set.Icc a b → Set.Icc c d, Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
      ∀ t : Set.Icc a b, (φ t : ℝ) = c + ((t : ℝ) - a) / (b - a) * (d - c) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hdc : (0 : ℝ) < d - c := by linarith
  have hfrac : ∀ t : Set.Icc a b,
      0 ≤ ((t : ℝ) - a) / (b - a) ∧ ((t : ℝ) - a) / (b - a) ≤ 1 := by
    intro t
    refine ⟨div_nonneg (by linarith [t.property.1]) hba.le, ?_⟩
    rw [div_le_one hba]
    linarith [t.property.2]
  refine ⟨fun t ↦ ⟨c + ((t : ℝ) - a) / (b - a) * (d - c), ?_, ?_⟩, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · nlinarith [(hfrac t).1]
  · nlinarith [(hfrac t).2]
  · exact Continuous.subtype_mk (by fun_prop) _
  · intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    have hdiv : ((s : ℝ) - a) / (b - a) ≤ ((t : ℝ) - a) / (b - a) := by gcongr
    change c + ((s : ℝ) - a) / (b - a) * (d - c) ≤ c + ((t : ℝ) - a) / (b - a) * (d - c)
    nlinarith
  · intro y
    have hyl : 0 ≤ ((y : ℝ) - c) / (d - c) := div_nonneg (by linarith [y.property.1]) hdc.le
    have hyr : ((y : ℝ) - c) / (d - c) ≤ 1 := by
      rw [div_le_one hdc]
      linarith [y.property.2]
    refine ⟨⟨a + ((y : ℝ) - c) / (d - c) * (b - a), by nlinarith, by nlinarith⟩, ?_⟩
    apply Subtype.ext
    change c + (a + ((y : ℝ) - c) / (d - c) * (b - a) - a) / (b - a) * (d - c) = (y : ℝ)
    field_simp
    ring

/-- The decreasing affine surjection between two nondegenerate closed intervals: the increasing
one reflected in the midpoint of its codomain. -/
theorem Set.Icc.exists_affine_antitone_surjection {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ φ : Set.Icc a b → Set.Icc c d, Continuous φ ∧ Antitone φ ∧ Function.Surjective φ ∧
      ∀ t : Set.Icc a b, (φ t : ℝ) = d - ((t : ℝ) - a) / (b - a) * (d - c) := by
  obtain ⟨φ, hφc, hφm, hφs, hφv⟩ := Set.Icc.exists_affine_monotone_surjection hab hcd
  refine ⟨fun t ↦ ⟨c + d - (φ t : ℝ), ?_, ?_⟩, ?_, ?_, ?_, fun t ↦ ?_⟩
  · linarith [(φ t).property.2]
  · linarith [(φ t).property.1]
  · exact (continuous_const.sub (continuous_subtype_val.comp hφc)).subtype_mk _
  · intro s t hst
    exact Subtype.mk_le_mk.mpr (by linarith [show (φ s : ℝ) ≤ (φ t : ℝ) from hφm hst])
  · intro y
    have hy : c + d - (y : ℝ) ∈ Set.Icc c d :=
      ⟨by linarith [y.property.2], by linarith [y.property.1]⟩
    obtain ⟨t, ht⟩ := hφs ⟨c + d - (y : ℝ), hy⟩
    refine ⟨t, Subtype.ext ?_⟩
    change c + d - (φ t : ℝ) = (y : ℝ)
    rw [show (φ t : ℝ) = c + d - (y : ℝ) from congrArg Subtype.val ht]
    ring
  · change c + d - (φ t : ℝ) = _
    rw [hφv t]
    ring

/-- The translation of the unit interval onto a closed interval of length one. -/
theorem Set.Icc.exists_translation_surjection {c d : ℝ} (hcd : d = c + 1) :
    ∃ φ : Set.Icc (0 : ℝ) 1 → Set.Icc c d, Continuous φ ∧ Monotone φ ∧
      Function.Surjective φ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (φ u : ℝ) = c + (u : ℝ) := by
  obtain ⟨φ, hφc, hφm, hφs, hφv⟩ :=
    Set.Icc.exists_affine_monotone_surjection zero_lt_one (show c < d by rw [hcd]; linarith)
  exact ⟨φ, hφc, hφm, hφs, fun u ↦ by rw [hφv u, hcd]; ring⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Interval Extension
-/

@[expose] public section

noncomputable section
namespace OrderIso

/-- Extend an order isomorphism of open real intervals by matching the endpoints. -/
def extendIoo {a b c d : ℝ} (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) (x : Set.Icc a b) : Set.Icc c d :=
  if hxa : (x : ℝ) = a then ⟨c, le_rfl, hcd.le⟩
  else if hxb : (x : ℝ) = b then ⟨d, hcd.le, le_rfl⟩
  else let t := e ⟨x, lt_of_le_of_ne x.property.1 (Ne.symm hxa),
      lt_of_le_of_ne x.property.2 hxb⟩
    ⟨t, t.property.1.le, t.property.2.le⟩

/-- The extension maps the left endpoint to the left endpoint. -/
theorem extendIoo_left {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) :
    extendIoo hcd e ⟨a, le_rfl, hab.le⟩ = ⟨c, le_rfl, hcd.le⟩ := by
  simp [extendIoo]

/-- The extension maps the right endpoint to the right endpoint. -/
theorem extendIoo_right {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) :
    extendIoo hcd e ⟨b, hab.le, le_rfl⟩ = ⟨d, hcd.le, le_rfl⟩ := by
  simp [extendIoo, ne_of_gt hab]

/-- The extension agrees with the original order isomorphism on the interior. -/
theorem extendIoo_interior {a b c d : ℝ} (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) (x : Set.Ioo a b) :
    (extendIoo hcd e ⟨x, x.property.1.le, x.property.2.le⟩ : ℝ) = e x := by
  simp [extendIoo, ne_of_gt x.property.1, ne_of_lt x.property.2]

/-- The endpoint extension is monotone. -/
theorem monotone_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Monotone (extendIoo hcd e) := by
  intro x y hxy
  by_cases hx : (x : ℝ) = a
  · have he : x = ⟨a, le_rfl, hab.le⟩ := Subtype.ext hx
    rw [he, extendIoo_left hab]
    exact (extendIoo hcd e y).property.1
  by_cases hy : (y : ℝ) = b
  · have he : y = ⟨b, hab.le, le_rfl⟩ := Subtype.ext hy
    rw [he, extendIoo_right hab]
    exact (extendIoo hcd e x).property.2
  have hxlo : a < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
  have hyhi : (y : ℝ) < b := lt_of_le_of_ne y.property.2 hy
  have hxhi : (x : ℝ) < b := lt_of_le_of_lt hxy hyhi
  have hylo : a < (y : ℝ) := lt_of_lt_of_le hxlo hxy
  change (extendIoo hcd e x : ℝ) ≤ extendIoo hcd e y
  rw [extendIoo_interior hcd e ⟨x, hxlo, hxhi⟩,
    extendIoo_interior hcd e ⟨y, hylo, hyhi⟩]
  exact e.monotone hxy

/-- The endpoint extension is surjective. -/
theorem surjective_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Function.Surjective (extendIoo hcd e) := by
  intro y
  by_cases hyc : (y : ℝ) = c
  · refine ⟨⟨a, le_rfl, hab.le⟩, ?_⟩
    rw [extendIoo_left hab]
    exact Subtype.ext hyc.symm
  by_cases hyd : (y : ℝ) = d
  · refine ⟨⟨b, hab.le, le_rfl⟩, ?_⟩
    rw [extendIoo_right hab]
    exact Subtype.ext hyd.symm
  let y' : Set.Ioo c d := ⟨y, lt_of_le_of_ne y.property.1 (Ne.symm hyc),
    lt_of_le_of_ne y.property.2 hyd⟩
  let x := e.symm y'
  refine ⟨⟨x, x.property.1.le, x.property.2.le⟩, Subtype.ext ?_⟩
  rw [extendIoo_interior]
  exact congrArg Subtype.val (e.apply_symm_apply y')

/-- The endpoint extension is continuous. -/
theorem continuous_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Continuous (extendIoo hcd e) :=
  (monotone_extendIoo hab hcd e).continuous_of_surjective (surjective_extendIoo hab hcd e)

end OrderIso

end

end

end
