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
open KPFamLat (f a act_one a_le_r)

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
  classical
  have hr0 : (0 : ℝ) ≤ r := by
    have := hr 1
    rw [act_one act hmul, inf_idem] at this
    exact_mod_cast (by linarith : (0 : ℤ) ≤ r)
  set κ := lo * (1 - hi) with hκdef
  have hκ : 0 < κ := mul_pos hlo (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ((r : ℝ) + 1) / κ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : 0 < n := by exact_mod_cast hnpos
  set η := (hi - lo) / n with hηdef
  have hη : 0 < η := div_pos (by linarith) hnpos
  set ε := min (θ / 4) (min (η / 32) (κ / 32)) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε1 : ε ≤ θ / 4 := min_le_left _ _
  have hε2 : ε ≤ η / 32 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ κ / 32 := (min_le_right _ _).trans (min_le_right _ _)
  set t : ℕ → ℝ := fun j => lo + (min j n : ℕ) * η with htdef
  have hnη : (n : ℝ) * η = hi - lo := by rw [hηdef]; field_simp
  have htlo : ∀ j, lo ≤ t j := fun j => by
    have : (0 : ℝ) ≤ (min j n : ℕ) * η := by positivity
    simp only [htdef]; linarith
  have hthi : ∀ j, t j ≤ hi := fun j => by
    have h1 : ((min j n : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_right j n
    have : ((min j n : ℕ) : ℝ) * η ≤ n * η := mul_le_mul_of_nonneg_right h1 hη.le
    simp only [htdef]; linarith
  have ht0 : ∀ j, 0 ≤ t j := fun j => (hlo.le.trans (htlo j))
  have ht1 : ∀ j, t j ≤ 1 := fun j => (hthi j).trans hhi.le
  have hsep : ∀ i j, i < j → j < n → 16 * ε < t j - t i := by
    intro i j hij hjn
    have e1 : min i n = i := min_eq_left (by omega)
    have e2 : min j n = j := min_eq_left (by omega)
    simp only [htdef, e1, e2]
    have : ((i : ℝ) + 1) ≤ j := by exact_mod_cast hij
    nlinarith
  have hκt : ∀ j, j < n → κ ≤ t j * (1 - t j) := by
    intro j _
    have a1 := htlo j
    have a2 := hthi j
    have : lo * (1 - hi) ≤ t j * (1 - t j) := by nlinarith
    exact this
  have hbig : (r : ℝ) < n * (κ - 16 * ε) := by
    have h1 : κ / 2 ≤ κ - 16 * ε := by linarith
    have h2 : 2 * ((r : ℝ) + 1) < n * κ := by
      rw [div_lt_iff₀ hκ] at hn; linarith
    nlinarith
  -- a nearly maximal measure
  set A : Set ℝ := {x | ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (τ : ι → G),
    x = ∑ j ∈ Finset.range n, a act rk u τ (t j)} with hAdef
  have hAne : A.Nonempty := ⟨_, Unit, inferInstance, inferInstance, fun _ => (1 : G), rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨n * r, ?_⟩
    rintro x ⟨ι, _, _, τ, rfl⟩
    have := Finset.sum_le_sum (s := Finset.range n) (fun j _ =>
      a_le_r act rk hinv u τ hstrict (ht0 j) (ht1 j) r hr)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  obtain ⟨x, ⟨ι, hF, hN, σ, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hAne (show sSup A - ε < sSup A by
      linarith)
  have hsup : ∀ (κ' : Type) [Fintype κ'] [Nonempty κ'] (τ : κ' → G),
      ∑ j ∈ Finset.range n, a act rk u τ (t j) ≤ ∑ j ∈ Finset.range n, a act rk u σ (t j) + ε := by
    intro κ' _ _ τ
    have : ∑ j ∈ Finset.range n, a act rk u τ (t j) ∈ A := ⟨κ', inferInstance, inferInstance, τ,
        rfl⟩
    have := le_csSup hAbdd this
    linarith
  obtain ⟨j, hj, w, hw, hval⟩ :=
    KPFamLat.exists_fixed_of_levels act hmul rk hstrict hmod hinv u σ r hr hn0
      t ht0 ht1 hε hsep hκt hbig hsup
  rw [f_fixed act rk hinv u σ (t j) w hw] at hval
  have har := a_le_r act rk hinv u σ hstrict (ht0 j) (ht1 j) r hr
  exact ⟨t j, htlo j, hthi j, w, hw, by linarith⟩

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
/-- **The one-sided form of Kazhdan and Polishchuk, for every group:** `rk(w / w ⊓ u) ≤ r` and
`rk(u / w ⊓ u) ≤ r (r + 1)`. -/
theorem exists_fixed_one_sided (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) :
    ∃ w, (∀ g, act g w = w) ∧ rk w - rk (w ⊓ u) ≤ r ∧ rk u - rk (w ⊓ u) ≤ r * (r + 1) := by
  have hr0 : (0 : ℤ) ≤ r := by
    have := hr 1
    rw [act_one act hmul, inf_idem] at this
    linarith
  rcases hr0.lt_or_eq with hpos | hzero
  · have hR1 : (1 : ℝ) ≤ r := by exact_mod_cast hpos
    set R : ℝ := r + 1 with hRdef
    have hR : 2 ≤ R := by linarith
    set x : ℝ := 1 / R with hxdef
    have hxR : x * R = 1 := by rw [hxdef]; field_simp
    have hx0 : 0 < x := by positivity
    have hx2 : x ≤ 1 / 2 := by
      rw [hxdef, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    set δ : ℝ := x ^ 3 / 8 with hδdef
    have hδ0 : 0 < δ := by positivity
    have hδx : δ ≤ x / 32 := by
      have : x ^ 2 ≤ 1 / 4 := by nlinarith
      rw [hδdef]; nlinarith
    obtain ⟨t, htl, hth, w, hw, hv⟩ := exists_fixed_weighted act hmul rk hstrict hmod hinv u r hr
      (lo := 1 - x + δ) (hi := 1 - x + 2 * δ) (θ := δ / 2) (by linarith) (by linarith)
          (by linarith) (by linarith)
    refine ⟨w, hw, ?_, ?_⟩
    · have ha : (0 : ℝ) ≤ (rk u : ℝ) - rk (w ⊓ u) := by
        have : rk (w ⊓ u) ≤ rk u := hstrict.monotone inf_le_right
        have : (rk (w ⊓ u) : ℝ) ≤ rk u := by exact_mod_cast this
        linarith
      by_contra hcon
      push Not at hcon
      have hc : (r + 1 : ℝ) ≤ (rk w : ℝ) - rk (w ⊓ u) := by
        have : r + 1 ≤ rk w - rk (w ⊓ u) := hcon
        exact_mod_cast this
      have m1 := mul_nonneg (show (0 : ℝ) ≤ 1 - t by linarith) ha
      have m2 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ t by linarith)
      have m3 := mul_le_mul_of_nonneg_right htl (show (0 : ℝ) ≤ R by linarith)
      -- t * R ≥ (1 - x + δ) R = R - 1 + δ R ≥ r + δ
      have : (1 - x + δ) * R = r + δ * R := by
        have : (1 - x + δ) * R = R - x * R + δ * R := by ring
        rw [this, hxR]; ring
      nlinarith
    · have hb : (0 : ℝ) ≤ (rk w : ℝ) - rk (w ⊓ u) := by
        have : rk (w ⊓ u) ≤ rk w := hstrict.monotone inf_le_left
        have : (rk (w ⊓ u) : ℝ) ≤ rk w := by exact_mod_cast this
        linarith
      by_contra hcon
      push Not at hcon
      have hc : (r * (r + 1) + 1 : ℝ) ≤ (rk u : ℝ) - rk (w ⊓ u) := by
        have : r * (r + 1) + 1 ≤ rk u - rk (w ⊓ u) := hcon
        exact_mod_cast this
      have m1 := mul_nonneg (show (0 : ℝ) ≤ t by linarith) hb
      have m2 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 - t by linarith)
      -- (1 - t)(r (r+1) + 1) ≥ (x - 2 δ)(R^2 - R + 1) = R - 1 + x - 2 δ (R^2 - R + 1) > r + δ / 2
      have h1 : (x - 2 * δ) * (r * (r + 1) + 1) ≤ (1 - t) * (r * (r + 1) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e1 : x * (r * (r + 1) + 1) = r + x := by
        have : (r : ℝ) * (r + 1) + 1 = R * R - R + 1 := by rw [hRdef]; ring
        rw [this]
        have : x * (R * R - R + 1) = (x * R) * R - x * R + x := by ring
        rw [this, hxR]; rw [hRdef]; ring
      have e2 : δ * (r * (r + 1) + 1) * 8 = x * (x * x * (r * (r + 1) + 1)) := by rw [hδdef]; ring
      have e3 : x * x * (r * (r + 1) + 1) = 1 - x + x * x := by
        have : (r : ℝ) * (r + 1) + 1 = R * R - R + 1 := by rw [hRdef]; ring
        rw [this]
        have : x * x * (R * R - R + 1) = (x * R) * (x * R) - x * (x * R) + x * x := by ring
        rw [this, hxR]; ring
      rw [e3] at e2
      have : δ * (r * (r + 1) + 1) ≤ x / 8 := by nlinarith
      nlinarith
  · subst hzero
    obtain ⟨w, hw, h⟩ := exists_fixed_total act hmul rk hstrict hmod hinv u 0 hr
    have ha : rk (w ⊓ u) ≤ rk u := hstrict.monotone inf_le_right
    have hb : rk (w ⊓ u) ≤ rk w := hstrict.monotone inf_le_left
    exact ⟨w, hw, by linarith, by linarith⟩

end final

open Module in
/-- **Kazhdan-Polishchuk for every group, finite-dimensional `V`.** -/
theorem almost_invariant_subspace_all {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r) ∧
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1)) := by
  classical
  set act : G → Submodule K V ≃o Submodule K V := fun g => Submodule.orderIsoMapComap (ρ g)
  have hmul : ∀ g h a, act (g * h) a = act g (act h a) := by
    intro g h a
    ext x
    simp only [act, Submodule.orderIsoMapComap_apply, Submodule.mem_map, map_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ρ h y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
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
