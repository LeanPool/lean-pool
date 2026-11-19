/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.PalettePairCounting
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Close pairs on the circles with a radius cut

Formalizes Lemma P'' (a), (b), (c) of `docs/results/explicit-constant-gain-5-239-2026-10-20.md`
(§2) in count form, for the rows `Pa`, `Pb`, `Pc` of
`docs/results/explicit-constant-gain-1-40-2026-10-21.md` (as built by
`scripts/verify_constant_gain_1_40.py`). Thresholds are squared distances. Write
`P(s) = Σ_j (N_j(s) - 1)` for the ordered pairs of distinct indices at squared distance at
most `s`, `R(s)` for the number of palette values `r` with `r² ≤ s`, and `D` for the palette
size.

Take squared thresholds `0 ≤ u ≤ v` and `4u ≤ t`, and assume that every saturated circle
(three points of the configuration on a circle about a point, with radius in the palette)
of squared radius in `(u, v]` carries two distinct points within squared distance `t`. Under
no three collinear points and the degree cap three,

* (a) `P(v) - 2 n R(v) ≤ P(t)`;
* (b) `P(u) + P(v) - n R(u) - 2 n R(v) ≤ P(t)`;
* (c) `P(v) - P(u) - 2 n R(v) + 2 n R(u) ≤ P(t)`.

With the scale `ρ_s` and a tag `(ρ, r′)` of the source, the thresholds are
`u = (ρ/2)² ρ_s²`, `v = r′² ρ_s²`, `t = ρ² ρ_s²`, and the three bounds are the rows
`𝒜(ρ) ≥ 𝒜(r′) - 2ℛ(r′)`, `𝒜(ρ) ≥ 𝒜(ρ/2) + 𝒜(r′) - ℛ(ρ/2) - 2ℛ(r′)` and
`𝒜(ρ) ≥ 𝒜(r′) - 𝒜(ρ/2) - 2ℛ(r′) + 2ℛ(ρ/2)` times `n²`. When every palette value has
`r² ≤ v` (the case `r′ = 2`), `P(v) = n(n - 1)` and `R(v) = D`; the three bounds then read

* (a) `n(n - 1) - 2 n D ≤ P(t)`;
* (b) `P(u) + n(n - 1) - n R(u) - 2 n D ≤ P(t)`;
* (c) `n(n - 1) - P(u) - 2 n D + 2 n R(u) ≤ P(t)`.

Proof. At one apex `i`, count the ordered close pairs on the circle of each palette radius
`r` about `i`, with `d = d_r(i) ≤ 3` points on it. If `r² ≤ u`, then `r² ≤ t/4`, every pair
on the circle is close, and the count is `d(d - 1)`. If `u < r² ≤ v` and `d = 3`, the
saturated circle carries a close pair in both orders, so the count is at least `2`.
Otherwise the count is at least `0`. Hence the count is at least `2[r² ≤ v](d - 2)` for (a),
at least `2[r² ≤ u](d - 1) + 2[r² ≤ v](d - 2)` for (b), and at least
`2[r² ≤ v](d - 2) - 2[r² ≤ u](d - 2)` for (c) (this one uses `u ≤ v`). Summing over the
palette with `Σ_{r² ≤ s} d_r(i) = N_i(s) - 1` gives the bound per apex. Under no three
collinear points an ordered pair has at most two equidistant witnesses, so the total over
all apexes is at most `2 P(t)`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- The three charges as arithmetic. Let `k ≤ 3` be the number of points on a circle and
`c ≥ 0` its ordered close-pair count; let `A` (short radius) imply `B` (radius within the
cut). If `A` gives `c = k(k - 1)` and a saturated circle with `B` but not `A` gives `c ≥ 2`,
then `c` is at least the charge of (a), of (b) and of (c). -/
private lemma circle_charges_of_cases {k : ℕ} {c : ℝ} {A B : Prop} [Decidable A]
    [Decidable B] (hk : k ≤ 3) (hc0 : 0 ≤ c) (hAB : A → B)
    (hA : A → c = (k : ℝ) * ((k : ℝ) - 1)) (hB : ¬A → B → k = 3 → 2 ≤ c) :
    2 * (if B then (k : ℝ) - 2 else 0) ≤ c ∧
    2 * ((if A then (k : ℝ) - 1 else 0) + (if B then (k : ℝ) - 2 else 0)) ≤ c ∧
    2 * ((if B then (k : ℝ) - 2 else 0) - (if A then (k : ℝ) - 2 else 0)) ≤ c := by
  by_cases hA' : A
  · simp only [ite_eq_left hA', ite_eq_left (hAB hA'), hA hA']
    interval_cases k <;> norm_num
  · simp only [ite_eq_right hA']
    by_cases hB' : B
    · simp only [ite_eq_left hB']
      by_cases h3 : k = 3
      · have h2 := hB hA' hB' h3
        have hk3 : (k : ℝ) = 3 := by exact_mod_cast h3
        refine ⟨by linarith, by linarith, by linarith⟩
      · have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
        refine ⟨by linarith, by linarith, by linarith⟩
    · simp only [ite_eq_right hB']
      refine ⟨by linarith, by linarith, by linarith⟩

/-- The per-radius charges for the ordered close pairs on one circle. Let `d = d_r(i)` be
the number of points on the circle of palette radius `r` about the apex `i` and `c` the
number of ordered pairs of them within squared distance `t`. Then `c ≥ 2[r² ≤ v](d - 2)`,
`c ≥ 2([r² ≤ u](d - 1) + [r² ≤ v](d - 2))` and `c ≥ 2([r² ≤ v](d - 2) - [r² ≤ u](d - 2))`. -/
private lemma circle_closePairs_charges {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {u v t : ℝ}
    (huv : u ≤ v) (hut : 4 * u ≤ t)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t)
    (i : Fin n) {r : ℝ} (hr : r ∈ OrderedDistanceValues p) :
    2 * (if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0) ≤
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) ∧
    2 * ((if r ^ 2 ≤ u then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 1 else 0) +
        (if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0)) ≤
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) ∧
    2 * ((if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0) -
        (if r ^ 2 ≤ u then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0)) ≤
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) := by
  refine circle_charges_of_cases (hcap i r) (Nat.cast_nonneg _) (fun h ↦ h.trans huv)
    (fun hru ↦ ?_) (fun hru hrv h3 ↦ ?_)
  · have hrt : r ^ 2 ≤ t / 4 := by linarith
    rw [circle_offDiag_filter_eq_of_sq_le hrt i, Finset.offDiag_card,
      Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  · have hsat : (i, r) ∈ SaturatedDistanceIncidences p :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hr⟩, h3⟩
    obtain ⟨a, b, ha, hb, hab, hclose⟩ := hS (i, r) hsat (lt_of_not_ge hru) hrv
    have h2 : 1 < ((DistanceOutNeighborsAtValue p i r).offDiag.filter
        (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card := by
      refine Finset.one_lt_card.mpr ⟨(a, b), ?_, (b, a), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab.ne⟩, hclose⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hb, ha, hab.ne'⟩,
          by simpa [dist_comm] using hclose⟩
      · exact fun h ↦ hab.ne (Prod.ext_iff.mp h).1
    exact_mod_cast h2

/-- For `s ≥ 0` and a real `k`, summing `d_r(i) - k` over the palette values `r` with
`r² ≤ s` gives `(N_i(s) - 1) - k R(s)`. -/
private lemma sum_palette_ite_card_sub (p : Config n) {s : ℝ} (hs : 0 ≤ s) (k : ℝ)
    (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
        (if r ^ 2 ≤ s then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - k else 0) =
      ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p i) (p q) ^ 2 ≤ s)).card : ℝ) - 1) -
        k * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ s)).card : ℝ) := by
  rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Nat.cast_sum, ← closePairRow_card_eq_sum,
    closedBall_sq_card_eq_closePairRow_card_add_one p hs i]
  push_cast
  ring

/-- Summing a per-radius charge `g` over all apexes: if every circle carries at least
`2 g(i, r)` ordered close pairs, then `Σ_i Σ_r g(i, r) ≤ P(t)`. -/
private lemma sum_sum_charge_le {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) {t : ℝ} (ht : 0 ≤ t)
    (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, ∀ r ∈ OrderedDistanceValues p, 2 * g i r ≤
      (((DistanceOutNeighborsAtValue p i r).offDiag.filter
        (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ)) :
    ∑ i, ∑ r ∈ OrderedDistanceValues p, g i r ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  have hup := sum_sum_circle_closePairs_le hp hgp3 t
  rw [orderedClosePairs_card_eq_sum_closedBall_sq p ht] at hup
  have hlow : ∑ i, ∑ r ∈ OrderedDistanceValues p, 2 * g i r ≤
      ∑ i, ∑ r ∈ OrderedDistanceValues p,
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun r hr ↦ hg i r hr
  simp only [← Finset.mul_sum] at hlow
  linarith

/-- Summing a constant shift over the indices: `Σ_j ((N_j(s) - 1) - c) = P(s) - n c`. -/
private lemma sum_closedBall_sq_card_sub_one_sub_const (p : Config n) (s : ℝ) {c : ℝ} :
    ∑ j, (((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ s)).card : ℝ) - 1) - c) =
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ s)).card : ℝ) - 1) - (n : ℝ) * c := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- **Lemma P''(a) with a radius cut**, the row `Pa (ρ, r′)` with `r′ < 2` of
`scripts/verify_constant_gain_1_40.py` times `n²`
(`𝒜(r′) - 2ℛ(r′) - 𝒜(ρ) ≤ 0`, with `u = (ρ/2)² ρ_s²`, `v = r′² ρ_s²`, `t = ρ² ρ_s²`).
Take squared thresholds `0 ≤ u ≤ v` and `4u ≤ t`, and suppose that every saturated circle
of squared radius in `(u, v]` carries two distinct points within squared distance `t`.
Under no three collinear points and the degree cap three,

`P(v) - 2 n R(v) ≤ P(t)`,

where `P(s) = Σ_j (N_j(s) - 1)` counts the ordered pairs of distinct indices at squared
distance at most `s` and `R(s)` counts the palette values `r` with `r² ≤ s`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_radius_cut {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {u v t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hut : 4 * u ≤ t)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ v)).card : ℝ) - 1) -
        2 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ v)).card : ℝ) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  have ht : 0 ≤ t := by linarith
  have hv : 0 ≤ v := hu.trans huv
  have h := sum_sum_charge_le hp hgp3 ht
    (fun i r ↦ if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0)
    (fun i r hr ↦ (circle_closePairs_charges hcap huv hut hS i hr).1)
  rw [Finset.sum_congr rfl fun i _ ↦ sum_palette_ite_card_sub p hv 2 i,
    sum_closedBall_sq_card_sub_one_sub_const p v] at h
  linarith

/-- **Lemma P''(b) with a radius cut**, the row `Pb (ρ, r′)` with `r′ < 2` of
`scripts/verify_constant_gain_1_40.py` times `n²`
(`𝒜(r′) - 2ℛ(r′) - 𝒜(ρ) + 𝒜(ρ/2) - ℛ(ρ/2) ≤ 0`, with `u = (ρ/2)² ρ_s²`, `v = r′² ρ_s²`,
`t = ρ² ρ_s²`). Take squared thresholds `0 ≤ u ≤ v` and `4u ≤ t`, and suppose that every
saturated circle of squared radius in `(u, v]` carries two distinct points within squared
distance `t`. Under no three collinear points and the degree cap three,

`P(u) + P(v) - n R(u) - 2 n R(v) ≤ P(t)`,

where `P(s) = Σ_j (N_j(s) - 1)` counts the ordered pairs of distinct indices at squared
distance at most `s` and `R(s)` counts the palette values `r` with `r² ≤ s`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_radius_cut_add_short {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {u v t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hut : 4 * u ≤ t)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ u)).card : ℝ) - 1) +
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ v)).card : ℝ) - 1) -
        (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ u)).card : ℝ) -
        2 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ v)).card : ℝ) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  have ht : 0 ≤ t := by linarith
  have hv : 0 ≤ v := hu.trans huv
  have h := sum_sum_charge_le hp hgp3 ht
    (fun i r ↦ (if r ^ 2 ≤ u then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 1 else 0) +
      (if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0))
    (fun i r hr ↦ (circle_closePairs_charges hcap huv hut hS i hr).2.1)
  have e : ∀ i, ∑ r ∈ OrderedDistanceValues p,
      ((if r ^ 2 ≤ u then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 1 else 0) +
        (if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0)) =
      (((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p i) (p q) ^ 2 ≤ u)).card : ℝ) - 1) -
        1 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ u)).card : ℝ)) +
      (((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p i) (p q) ^ 2 ≤ v)).card : ℝ) - 1) -
        2 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ v)).card : ℝ)) := fun i ↦ by
    rw [Finset.sum_add_distrib, sum_palette_ite_card_sub p hu 1 i,
      sum_palette_ite_card_sub p hv 2 i]
  rw [Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_add_distrib,
    sum_closedBall_sq_card_sub_one_sub_const p u,
    sum_closedBall_sq_card_sub_one_sub_const p v] at h
  linarith

/-- **Lemma P''(c) with a radius cut**, the row `Pc (ρ, r′)` with `r′ < 2` of
`scripts/verify_constant_gain_1_40.py` times `n²`
(`𝒜(r′) - 2ℛ(r′) - 𝒜(ρ) - 𝒜(ρ/2) + 2ℛ(ρ/2) ≤ 0`, with `u = (ρ/2)² ρ_s²`, `v = r′² ρ_s²`,
`t = ρ² ρ_s²`). Take squared thresholds `0 ≤ u ≤ v` and `4u ≤ t`, and suppose that every
saturated circle of squared radius in `(u, v]` carries two distinct points within squared
distance `t`. Under no three collinear points and the degree cap three,

`P(v) - P(u) - 2 n R(v) + 2 n R(u) ≤ P(t)`,

where `P(s) = Σ_j (N_j(s) - 1)` counts the ordered pairs of distinct indices at squared
distance at most `s` and `R(s)` counts the palette values `r` with `r² ≤ s`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_radius_cut_sub_short {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {u v t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hut : 4 * u ≤ t)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ v)).card : ℝ) - 1) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ u)).card : ℝ) - 1) -
        2 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ v)).card : ℝ) +
        2 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ u)).card : ℝ) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  have ht : 0 ≤ t := by linarith
  have hv : 0 ≤ v := hu.trans huv
  have h := sum_sum_charge_le hp hgp3 ht
    (fun i r ↦ (if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0) -
      (if r ^ 2 ≤ u then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0))
    (fun i r hr ↦ (circle_closePairs_charges hcap huv hut hS i hr).2.2)
  have e : ∀ i, ∑ r ∈ OrderedDistanceValues p,
      ((if r ^ 2 ≤ v then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0) -
        (if r ^ 2 ≤ u then ((DistanceOutNeighborsAtValue p i r).card : ℝ) - 2 else 0)) =
      (((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p i) (p q) ^ 2 ≤ v)).card : ℝ) - 1) -
        2 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ v)).card : ℝ)) -
      (((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p i) (p q) ^ 2 ≤ u)).card : ℝ) - 1) -
        2 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ u)).card : ℝ)) := fun i ↦ by
    rw [Finset.sum_sub_distrib, sum_palette_ite_card_sub p hv 2 i,
      sum_palette_ite_card_sub p hu 2 i]
  rw [Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_sub_distrib,
    sum_closedBall_sq_card_sub_one_sub_const p v,
    sum_closedBall_sq_card_sub_one_sub_const p u] at h
  linarith

/-- If every palette value has `r² ≤ v` and `v ≥ 0`, then `P(v) = n(n - 1)`: every ordered
pair of distinct indices is within squared distance `v`. -/
theorem sum_closedBall_sq_card_sub_one_eq_of_palette_sq_le {p : Config n} {v : ℝ}
    (hv : 0 ≤ v) (hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ v) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ v)).card : ℝ) - 1) = (n : ℝ) * ((n : ℝ) - 1) := by
  have hall : ∀ j, (Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ v) = Finset.univ := by
    intro j
    apply Finset.filter_true_of_mem
    intro q _
    by_cases hjq : j = q
    · rw [hjq, dist_self]
      simpa using hv
    · apply hpal
      rw [OrderedDistanceValues, Finset.mem_image]
      exact ⟨(j, q), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hjq⟩, rfl⟩
  simp only [hall, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]

/-- If every palette value has `r² ≤ v`, then `R(v) = D`. -/
theorem palette_filter_card_eq_numDistancesOrdered_of_sq_le {p : Config n} {v : ℝ}
    (hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ v) :
    (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ v)).card : ℝ) =
      (NumDistancesOrdered p : ℝ) := by
  rw [Finset.filter_true_of_mem hpal, NumDistancesOrdered]

/-- **Lemma P''(a) with `r′ = 2`**, the row `Pa (ρ, 2)` of
`scripts/verify_constant_gain_1_40.py` times `n²`
(`-ε - 2𝔡 - 𝒜(ρ) ≤ -1`, with `u = (ρ/2)² ρ_s²`, `v = 4 ρ_s²`, `t = ρ² ρ_s²`). Take squared
thresholds `0 ≤ u ≤ v` and `4u ≤ t` with every palette value `r² ≤ v`, and suppose that
every saturated circle of squared radius in `(u, v]` carries two distinct points within
squared distance `t`. Under no three collinear points and the degree cap three,

`n(n - 1) - 2 n D ≤ P(t)`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_bounded_palette {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {u v t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hut : 4 * u ≤ t)
    (hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ v)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    (n : ℝ) * ((n : ℝ) - 1) - 2 * (n : ℝ) * (NumDistancesOrdered p : ℝ) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  have h := sum_closedBall_sq_card_sub_one_lower_bound_radius_cut hp hgp3 hcap hu huv hut hS
  rwa [sum_closedBall_sq_card_sub_one_eq_of_palette_sq_le (hu.trans huv) hpal,
    palette_filter_card_eq_numDistancesOrdered_of_sq_le hpal] at h

/-- **Lemma P''(b) with `r′ = 2`**, the row `Pb (ρ, 2)` of
`scripts/verify_constant_gain_1_40.py` times `n²`
(`-ε - 2𝔡 - 𝒜(ρ) + 𝒜(ρ/2) - ℛ(ρ/2) ≤ -1`, with `u = (ρ/2)² ρ_s²`, `v = 4 ρ_s²`,
`t = ρ² ρ_s²`). Take squared thresholds `0 ≤ u ≤ v` and `4u ≤ t` with every palette value
`r² ≤ v`, and suppose that every saturated circle of squared radius in `(u, v]` carries two
distinct points within squared distance `t`. Under no three collinear points and the degree
cap three,

`P(u) + n(n - 1) - n R(u) - 2 n D ≤ P(t)`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_bounded_palette_add_short {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {u v t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hut : 4 * u ≤ t)
    (hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ v)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ u)).card : ℝ) - 1) + (n : ℝ) * ((n : ℝ) - 1) -
        (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ u)).card : ℝ) -
        2 * (n : ℝ) * (NumDistancesOrdered p : ℝ) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  have h := sum_closedBall_sq_card_sub_one_lower_bound_radius_cut_add_short hp hgp3 hcap hu
    huv hut hS
  rwa [sum_closedBall_sq_card_sub_one_eq_of_palette_sq_le (hu.trans huv) hpal,
    palette_filter_card_eq_numDistancesOrdered_of_sq_le hpal] at h

/-- **Lemma P''(c) with `r′ = 2`**, the row `Pc (ρ, 2)` of
`scripts/verify_constant_gain_1_40.py` times `n²`
(`-ε - 2𝔡 - 𝒜(ρ) - 𝒜(ρ/2) + 2ℛ(ρ/2) ≤ -1`, with `u = (ρ/2)² ρ_s²`, `v = 4 ρ_s²`,
`t = ρ² ρ_s²`). Take squared thresholds `0 ≤ u ≤ v` and `4u ≤ t` with every palette value
`r² ≤ v`, and suppose that every saturated circle of squared radius in `(u, v]` carries two
distinct points within squared distance `t`. Under no three collinear points and the degree
cap three,

`n(n - 1) - P(u) - 2 n D + 2 n R(u) ≤ P(t)`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_bounded_palette_sub_short {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {u v t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hut : 4 * u ≤ t)
    (hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ v)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    (n : ℝ) * ((n : ℝ) - 1) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ u)).card : ℝ) - 1) -
        2 * (n : ℝ) * (NumDistancesOrdered p : ℝ) +
        2 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ u)).card : ℝ) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  have h := sum_closedBall_sq_card_sub_one_lower_bound_radius_cut_sub_short hp hgp3 hcap hu
    huv hut hS
  rwa [sum_closedBall_sq_card_sub_one_eq_of_palette_sq_le (hu.trans huv) hpal,
    palette_filter_card_eq_numDistancesOrdered_of_sq_le hpal] at h

end Esgk
