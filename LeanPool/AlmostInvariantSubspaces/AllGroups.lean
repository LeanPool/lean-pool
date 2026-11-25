/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Families
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Almost invariant elements of a lattice, for all groups

Idea of the proof: a probability measure on the group for which the minimum of the mean distance is
nearly maximal, and several weights `t`.
-/

@[expose] public section

namespace AlmostInvariant.AllGroups

open AlmostInvariant (avg_const)
open KPFamLat (f act_one a_le_r)

variable {L G : Type*} [Lattice L] [Group G]

section basic
variable (act : G → L ≃o L) (hmul : ∀ g h x, act (g * h) x = act g (act h x))
  (rk : L → ℤ) (hstrict : StrictMono rk)
  (hmod : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y)
  (hinv : ∀ g x, rk (act g x) = rk x) (u : L)
  {ι : Type} [Fintype ι] [Nonempty ι] (σ : ι → G)

include hinv in
omit [Group G] in
theorem f_fixed (t : ℝ) (w : L) (hw : ∀ g, act g w = w) :
    f act rk u σ t w = (1 - t) * ((rk u : ℝ) - rk (w ⊓ u)) + t * ((rk w : ℝ) - rk (w ⊓ u)) := by
  have h : ∀ i, (rk u : ℝ) - rk (act (σ i) u ⊓ w) = (rk u : ℝ) - rk (w ⊓ u) := by
    intro i
    have : act (σ i) u ⊓ w = act (σ i) (u ⊓ w) := by rw [(act (σ i)).map_inf, hw]
    rw [this, hinv, inf_comm]
  unfold f
  rw [show (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ w)) = fun _ => (rk u : ℝ) - rk (w ⊓ u)
      from funext h,
    avg_const]
  ring

end basic

section final
variable (act : G → L ≃o L) (hmul : ∀ g h x, act (g * h) x = act g (act h x))
  (rk : L → ℤ) (hstrict : StrictMono rk)
  (hmod : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y)
  (hinv : ∀ g x, rk (act g x) = rk x) (u : L)

include hmul hstrict hmod hinv in
/-- **Weighted form for all groups.** For every interval `[lo, hi] ⊂ (0,1)` and `θ > 0` there are
a weight `t ∈ [lo, hi]` and a fixed
element `w` with `(1 - t) rk(u / w ⊓ u) + t rk(w / w ⊓ u) ≤ r + θ`. -/
theorem exists_fixed_weighted (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r)
    {lo hi θ : ℝ} (hlo : 0 < lo) (hlohi : lo < hi) (hhi : hi < 1) (hθ : 0 < θ) :
    ∃ t, lo ≤ t ∧ t ≤ hi ∧ ∃ w, (∀ g, act g w = w) ∧
      (1 - t) * ((rk u : ℝ) - rk (w ⊓ u)) + t * ((rk w : ℝ) - rk (w ⊓ u)) ≤ r + θ := by
  obtain ⟨t, htl, hth, w, hw, ι, hF, hN, σ, hval⟩ :=
    KPFamLat.exists_fixed_near_minimizer act hmul rk hstrict hmod hinv u r hr hlo hlohi hhi hθ
  rw [f_fixed act rk hinv u σ t w hw] at hval
  have har := a_le_r act rk hinv u σ hstrict (hlo.le.trans htl) (hth.trans hhi.le) r hr
  exact ⟨t, htl, hth, w, hw, by linarith⟩

include hmul hstrict hmod hinv in
/-- **Total error at most `2r`, for every group.** -/
theorem exists_fixed_total (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) :
    ∃ w, (∀ g, act g w = w) ∧ (rk u - rk (w ⊓ u)) + (rk w - rk (w ⊓ u)) ≤ 2 * r := by
  have hr0 : (0 : ℤ) ≤ r := by
    have := hr 1
    rw [act_one act hmul, inf_idem] at this
    linarith
  have hR : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  set δ : ℝ := 1 / (8 * (2 * r + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ2 : δ * (2 * r + 1) = 1 / 8 := by rw [hδ]; field_simp
  have hδsmall : δ ≤ 1 / 8 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨t, htl, hth, w, hw, hv⟩ := exists_fixed_weighted act hmul rk hstrict hmod hinv u r hr
    (lo := 1 / 2 - δ) (hi := 1 / 2 + δ) (θ := 1 / 8) (by linarith) (by linarith) (by linarith)
        (by norm_num)
  refine ⟨w, hw, ?_⟩
  have ha : (0 : ℝ) ≤ (rk u : ℝ) - rk (w ⊓ u) := by
    have : rk (w ⊓ u) ≤ rk u := hstrict.monotone inf_le_right
    have : (rk (w ⊓ u) : ℝ) ≤ rk u := by exact_mod_cast this
    linarith
  have hb : (0 : ℝ) ≤ (rk w : ℝ) - rk (w ⊓ u) := by
    have : rk (w ⊓ u) ≤ rk w := hstrict.monotone inf_le_left
    have : (rk (w ⊓ u) : ℝ) ≤ rk w := by exact_mod_cast this
    linarith
  by_contra hcon
  push Not at hcon
  have hc : (2 * r + 1 : ℝ) ≤ ((rk u : ℝ) - rk (w ⊓ u)) + ((rk w : ℝ) - rk (w ⊓ u)) := by
    have : 2 * r + 1 ≤ (rk u - rk (w ⊓ u)) + (rk w - rk (w ⊓ u)) := hcon
    exact_mod_cast this
  have m1 := mul_le_mul_of_nonneg_right (show 1 / 2 - δ ≤ 1 - t by linarith) ha
  have m2 := mul_le_mul_of_nonneg_right (show 1 / 2 - δ ≤ t by linarith) hb
  have m3 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 / 2 - δ by linarith)
  nlinarith

include hmul hstrict hmod hinv in
/-- **Single-orbit one-sided result for every group.** `rk(w / w ⊓ u) ≤ r` and
`rk(u / w ⊓ u) ≤ r (r + 1)`. -/
theorem exists_fixed_one_sided (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) :
    ∃ w, (∀ g, act g w = w) ∧ rk w - rk (w ⊓ u) ≤ r ∧ rk u - rk (w ⊓ u) ≤ r * (r + 1) := by
  obtain ⟨w, hw, hb, -⟩ :=
    KPFamLat.exists_fixed_family_one_sided act hmul rk hstrict hmod hinv u r hr
  have forward : ∀ g, rk u - rk (u ⊓ act g u) ≤ r := fun g => by
    simpa only [inf_comm u (act g u)] using hr g
  have backward : ∀ g, rk (act g u) - rk (act g u ⊓ u) ≤ r := fun g => by
    have bound := hr g⁻¹
    rw [← hinv g u, ← hinv g (act g⁻¹ u ⊓ u), (act g).map_inf, KPFamLat.act_inv act hmul,
      inf_comm u (act g u)] at bound
    exact bound
  obtain ⟨first, second⟩ := hb u forward backward
  exact ⟨w, hw, first, by simpa only [inf_comm u w] using second⟩

end final

open Module in
/-- Two bounds for one orbit in a finite-dimensional representation of an arbitrary group. -/
theorem almost_invariant_subspace_all {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r) ∧
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1)) := by
  classical
  let act : G → Submodule K V ≃o Submodule K V := AlmostInvariant.linearAct ρ
  have hmul := AlmostInvariant.linearAct_mul_apply ρ
  set rk : Submodule K V → ℤ := fun S => (finrank K S : ℤ)
  have hstrict : StrictMono rk := fun S T hST => by
    have h := Submodule.finrank_lt_finrank_of_lt hST
    change (finrank K S : ℤ) < finrank K T
    exact_mod_cast h
  have hmod : ∀ S T, rk (S ⊔ T) + rk (S ⊓ T) = rk S + rk T := fun S T => by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S T
    change (finrank K (S ⊔ T : Submodule K V) : ℤ) + finrank K (S ⊓ T : Submodule K V)
        = finrank K S + finrank K T
    exact_mod_cast h
  have hinv : ∀ g S, rk (act g S) = rk S := fun g S => by
    have h := LinearEquiv.finrank_map_eq (ρ g) S
    change (finrank K (S.map (ρ g : V →ₗ[K] V)) : ℤ) = finrank K S
    exact_mod_cast h
  have hr' : ∀ g, rk A - rk (act g A ⊓ A) ≤ r := fun g => by
    have h' : (finrank K A : ℤ) ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r := by
      exact_mod_cast hr g
    change (finrank K A : ℤ) - finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) ≤ r
    linarith
  constructor
  · obtain ⟨W, hW, h⟩ := AlmostInvariant.AllGroups.exists_fixed_total act hmul rk hstrict hmod
      hinv A r hr'
    refine ⟨W, hW, ?_⟩
    have : (finrank K W : ℤ) + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r := by
      simp only [rk] at h; linarith
    exact_mod_cast this
  · obtain ⟨W, hW, h1, h2⟩ := AlmostInvariant.AllGroups.exists_fixed_one_sided act hmul rk hstrict
      hmod hinv A r hr'
    refine ⟨W, hW, ?_, ?_⟩
    · have : (finrank K W : ℤ) ≤ finrank K (W ⊓ A : Submodule K V) + r := by
        simp only [rk] at h1; linarith
      exact_mod_cast this
    · have : (finrank K A : ℤ) ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1) := by
        simp only [rk] at h2; linarith
      exact_mod_cast this

end AlmostInvariant.AllGroups
