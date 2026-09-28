/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.BoundedVariation`.
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
# For Mathlib / Bounded Variation
-/

@[expose] public section

/-- The variation of a sum is at most the sum of the variations. -/
theorem eVariationOn.add_le {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] (f g : α → E) (s : Set α) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ ↦ edist_add_add_le _ _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- A sum of two functions of bounded variation has bounded variation. -/
theorem BoundedVariationOn.add {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) ?_
  exact eVariationOn.add_le f g s

/-- Variation bounds the increments along a finite monotone partition. -/
theorem eVariationOn.sum_edist_fin_le {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    {f : α → E} {s : Set α} {n : ℕ} (u : Fin (n + 1) → α)
    (hu : Monotone u) (hus : ∀ i, u i ∈ s) :
    ∑ i : Fin n, edist (f (u i.succ)) (f (u i.castSucc)) ≤ eVariationOn f s := by
  let v : ℕ → α := fun k ↦ u ⟨min k n, by omega⟩
  have hv : Monotone v := fun i j hij ↦ hu (min_le_min_right n hij)
  have h := eVariationOn.sum_le (f := f) (n := n) hv
    (fun k ↦ hus ⟨min k n, by omega⟩)
  rw [← Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [v]
  have h₁ : min (i.val + 1) n = i.val + 1 := Nat.min_eq_left (by omega)
  have h₀ : min i.val n = i.val := Nat.min_eq_left (by omega)
  congr 2 <;> apply congrArg u <;> apply Fin.ext
  · exact h₁.symm
  · exact h₀.symm

/-- Total variation bounds the sum of norms of increments on a finite partition. -/
theorem BoundedVariationOn.sum_norm_sub_fin_le {α E : Type*} [LinearOrder α]
    [NormedAddCommGroup E] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    {n : ℕ} (u : Fin (n + 1) → α) (hu : Monotone u) (hus : ∀ i, u i ∈ s) :
    ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ≤ (eVariationOn f s).toReal := by
  have h := ENNReal.toReal_mono hf (eVariationOn.sum_edist_fin_le u hu hus)
  rw [ENNReal.toReal_sum (fun i _ ↦ edist_ne_top _ _)] at h
  simpa only [edist_dist, dist_eq_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using h

/-- Squared increments are bounded by the largest increment times the total variation. -/
theorem BoundedVariationOn.sum_norm_sub_sq_fin_le {α E : Type*} [LinearOrder α]
    [NormedAddCommGroup E] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    {n : ℕ} (u : Fin (n + 1) → α) (hu : Monotone u) (hus : ∀ i, u i ∈ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ≤ δ) :
    ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2 ≤ δ * (eVariationOn f s).toReal := by
  calc
    _ ≤ ∑ i : Fin n, δ * ‖f (u i.succ) - f (u i.castSucc)‖ := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [hbound i, norm_nonneg (f (u i.succ) - f (u i.castSucc))]
    _ = δ * ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf.sum_norm_sub_fin_le u hu hus) hδ

/-- A telescoping sum of increments with quadratic remainders is controlled by the
largest increment times the total variation. -/
theorem BoundedVariationOn.abs_sub_sum_le_of_param_quadratic_remainder
    {α E : Type*} [LinearOrder α] [NormedAddCommGroup E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    {n : ℕ} (u : Fin (n + 1) → α) (hu : Monotone u) (hus : ∀ i, u i ∈ s)
    (A : α → ℝ) (L : Fin n → ℝ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hbound : ∀ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ≤ δ)
    (herror : ∀ i : Fin n,
      |A (u i.succ) - A (u i.castSucc) - L i| ≤
        C * ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2) :
    |A (u (Fin.last n)) - A (u 0) - ∑ i, L i| ≤ C * δ * (eVariationOn f s).toReal := by
  have htel : ∑ i : Fin n, (A (u i.succ) - A (u i.castSucc)) =
      A (u (Fin.last n)) - A (u 0) := by
    have hfirst := Fin.sum_univ_succ (fun i ↦ A (u i))
    have hlast := Fin.sum_univ_castSucc (fun i ↦ A (u i))
    rw [Finset.sum_sub_distrib]
    linarith
  rw [← htel, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, |A (u i.succ) - A (u i.castSucc) - L i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, C * ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ herror i)
    _ = C * ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ C * (δ * (eVariationOn f s).toReal) :=
      mul_le_mul_of_nonneg_left (hf.sum_norm_sub_sq_fin_le u hu hus hδ hbound) hC
    _ = _ := by ring

/-- If the increments of a real function `A` agree with a linear functional of the
increments of a bounded variation path up to a quadratic remainder on all parameter
pairs closer than a fixed positive threshold, then the linear sums along any family of
partitions whose mesh tends to zero converge to the endpoint increment of `A`. -/
theorem BoundedVariationOn.tendsto_sum_of_local_quadratic_remainder
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ} (hab : a ≤ b)
    {f : Set.Icc a b → E} (hf : BoundedVariationOn f Set.univ) (hfc : Continuous f)
    (A : Set.Icc a b → ℝ) (L : Set.Icc a b → E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (herror : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
      |A u - A t - L t (f u - f t)| ≤ C * ‖f u - f t‖ ^ 2)
    (N : ℕ → ℕ) (cuts : ∀ k, Fin (N k + 1) → Set.Icc a b)
    (hcuts : ∀ k, Monotone (cuts k))
    (hzero : ∀ k, (cuts k 0 : ℝ) = a)
    (hlast : ∀ k, (cuts k (Fin.last (N k)) : ℝ) = b)
    (hmesh : ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (N k),
      (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ) :
    Filter.Tendsto (fun k ↦ ∑ i : Fin (N k),
      L (cuts k i.castSucc) (f (cuts k i.succ) - f (cuts k i.castSucc)))
      Filter.atTop (nhds (A ⟨b, hab, le_rfl⟩ - A ⟨a, le_rfl, hab⟩)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := (eVariationOn f Set.univ).toReal with hVdef
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set η := ε / (C * V + 1) with hηdef
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hfc) η hη
  filter_upwards [hmesh (min δ δ₀) (lt_min hδ hδ₀)] with k hk
  have hinc (i : Fin (N k)) :
      ‖f (cuts k i.succ) - f (cuts k i.castSucc)‖ ≤ η := by
    have hle : (cuts k i.castSucc : ℝ) ≤ (cuts k i.succ : ℝ) :=
      hcuts k (Fin.castSucc_le_succ i)
    have hd : dist (cuts k i.succ) (cuts k i.castSucc) < δ := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
      exact lt_of_lt_of_le (hk i) (min_le_left _ _)
    simpa only [dist_eq_norm] using (hmod hd).le
  have hbound := hf.abs_sub_sum_le_of_param_quadratic_remainder (cuts k) (hcuts k)
    (fun _ ↦ Set.mem_univ _) A
    (fun i ↦ L (cuts k i.castSucc) (f (cuts k i.succ) - f (cuts k i.castSucc)))
    hC hη.le hinc
    (fun i ↦ herror (cuts k i.castSucc) (cuts k i.succ) (hcuts k (Fin.castSucc_le_succ i))
      (lt_of_lt_of_le (hk i) (min_le_right _ _)))
  have hleft : cuts k 0 = ⟨a, le_rfl, hab⟩ := Subtype.ext (hzero k)
  have hright : cuts k (Fin.last (N k)) = ⟨b, hab, le_rfl⟩ := Subtype.ext (hlast k)
  rw [hleft, hright] at hbound
  rw [Real.dist_eq, abs_sub_comm]
  apply hbound.trans_lt
  have hcancel : η * (C * V + 1) = ε := div_mul_cancel₀ ε (by positivity)
  change C * η * V < ε
  nlinarith

/-- Bounded variation on two adjacent closed intervals gives bounded variation on their
union. -/
theorem BoundedVariationOn.Icc_union_Icc {α E : Type*} [LinearOrder α]
    [PseudoEMetricSpace E] {f : α → E} {a b c : α} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : BoundedVariationOn f (Set.Icc a b)) (h₂ : BoundedVariationOn f (Set.Icc b c)) :
    BoundedVariationOn f (Set.Icc a c) := by
  have h := eVariationOn.Icc_add_Icc f hab hbc (Set.mem_univ b)
  simp only [Set.univ_inter] at h
  change eVariationOn f (Set.Icc a c) ≠ ⊤
  rw [← h]
  exact ENNReal.add_ne_top.mpr ⟨h₁, h₂⟩

/-- A function on the order subtype `Set.Icc a b` has bounded variation everywhere as soon as
it has bounded variation on the closed interval between the two endpoints of that subtype. -/
theorem BoundedVariationOn.univ_of_Icc_endpoints {α E : Type*} [LinearOrder α]
    [PseudoEMetricSpace E] {a b : α} (hab : a ≤ b) {g : Set.Icc a b → E}
    (h : BoundedVariationOn g (Set.Icc ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩)) :
    BoundedVariationOn g Set.univ := by
  have huniv : Set.Icc (⟨a, le_rfl, hab⟩ : Set.Icc a b) ⟨b, hab, le_rfl⟩ = Set.univ := by
    ext x
    simp only [Set.mem_Icc, Set.mem_univ, iff_true]
    exact ⟨x.2.1, x.2.2⟩
  rwa [huniv] at h

end

end
