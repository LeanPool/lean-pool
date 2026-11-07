/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.AnnularTripleCollapse
public import LeanPool.DistinctDistances.EntropyCensus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Finite close-pair counting in a planar annulus

Formalizes the finite counting section of
`docs/results/annulus-atomic-limit-2026-10-13.md`.

GP4 bounds each distance degree by three. GP3 separately bounds the number
of apexes that can charge a fixed distinct base pair by two. Thresholds are
squared distances. No measure-limit classification or quantitative distance
improvement is asserted here.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}

/-- Squared Euclidean distance written in the two real coordinates. -/
lemma point_dist_sq_coordinates (p q : Point) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- Squared norm written in the two real coordinates. -/
lemma point_norm_sq_coordinates (p : Point) :
    ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- The orthonormal frame with the apex `p` at `(‖p‖, 0)`: coordinates `u, v` of
three points, with their squared norms, mutual squared distances, and squared
distances to the apex. -/
lemma exists_apex_frame (p : Point) (q : Fin 3 → Point) (ha0 : ‖p‖ ≠ 0) :
    ∃ u v : Fin 3 → ℝ, (∀ i, u i ^ 2 + v i ^ 2 = ‖q i‖ ^ 2) ∧
      (∀ i j, (u i - u j) ^ 2 + (v i - v j) ^ 2 = dist (q i) (q j) ^ 2) ∧
      ∀ i, (u i - ‖p‖) ^ 2 + v i ^ 2 = dist p (q i) ^ 2 := by
  set a := ‖p‖ with ha
  have hpa : p 0 ^ 2 + p 1 ^ 2 = a ^ 2 := (point_norm_sq_coordinates p).symm
  let u : Fin 3 → ℝ := fun i ↦ (p 0 * q i 0 + p 1 * q i 1) / a
  let v : Fin 3 → ℝ := fun i ↦ (-p 1 * q i 0 + p 0 * q i 1) / a
  have hnorm (i : Fin 3) : u i ^ 2 + v i ^ 2 = ‖q i‖ ^ 2 := by
    rw [point_norm_sq_coordinates]
    dsimp [u, v]
    field_simp [ha0]
    calc
      _ = (p 0 ^ 2 + p 1 ^ 2) * (q i 0 ^ 2 + q i 1 ^ 2) := by ring
      _ = _ := by rw [hpa]
  have hdist (i j : Fin 3) :
      (u i - u j) ^ 2 + (v i - v j) ^ 2 = dist (q i) (q j) ^ 2 := by
    rw [point_dist_sq_coordinates]
    dsimp [u, v]
    field_simp [ha0]
    calc
      _ = (p 0 ^ 2 + p 1 ^ 2) *
          ((q i 0 - q j 0) ^ 2 + (q i 1 - q j 1) ^ 2) := by ring
      _ = _ := by rw [hpa]
  have hapex (i : Fin 3) : (u i - a) ^ 2 + v i ^ 2 = dist p (q i) ^ 2 := by
    have hu : a * u i = p 0 * q i 0 + p 1 * q i 1 := by
      dsimp [u]; field_simp [ha0]
    calc
      _ = a ^ 2 - 2 * (a * u i) + (u i ^ 2 + v i ^ 2) := by ring
      _ = _ := by
        rw [hnorm, hu, point_norm_sq_coordinates, point_dist_sq_coordinates,
          point_norm_sq_coordinates]
        nlinarith [hpa]
  exact ⟨u, v, hnorm, hdist, hapex⟩

/-- The merged coordinate lemma in an arbitrary planar frame. -/
theorem annular_equidistant_triple_close_pair (p : Point) (q : Fin 3 → Point)
    {x : ℝ} (hx : 0 ≤ x) (hx34 : x ≤ 3 / 4)
    (hp : 1 - x ≤ ‖p‖ ^ 2)
    (hlo : ∀ i, 1 - x ≤ ‖q i‖ ^ 2) (hhi : ∀ i, ‖q i‖ ^ 2 ≤ 1)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ 4 * x := by
  let a := ‖p‖
  have ha : 1 / 2 ≤ a := by dsimp [a]; nlinarith [norm_nonneg p]
  have ha0 : a ≠ 0 := by linarith
  obtain ⟨u, v, hnorm, hdist, hapex⟩ := exists_apex_frame p q ha0
  have hapex' (i : Fin 3) : (a - u i) ^ 2 + v i ^ 2 = dist p (q i) ^ 2 := by
    calc
      (a - u i) ^ 2 + v i ^ 2 = (u i - a) ^ 2 + v i ^ 2 := by ring
      _ = dist p (q i) ^ 2 := hapex i
  obtain ⟨i, j, hij, hclose⟩ := annular_three_equidistant_has_close_pair u v ha hx
    (by linarith) (fun i ↦ by rw [hnorm]; exact hlo i)
    (fun i ↦ by rw [hnorm]; exact hhi i)
    (fun i j ↦ by rw [hapex', hapex', heq i j])
  exact ⟨i, j, hij, by rwa [hdist] at hclose⟩

/-- Translation and positive scaling of the arbitrary-frame close-pair lemma.
The original-coordinate squared threshold is `4*x*ρ²`. -/
theorem scaled_annular_equidistant_triple_close_pair
    (c p : Point) (q : Fin 3 → Point) {ρ x : ℝ}
    (hρ : 0 < ρ) (hx : 0 ≤ x) (hx34 : x ≤ 3 / 4)
    (hp : ρ ^ 2 * (1 - x) ≤ dist p c ^ 2)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ 4 * x * ρ ^ 2 := by
  let f : Point → Point := fun z ↦ ρ⁻¹ • (z - c)
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hf (z : Point) : ‖f z‖ ^ 2 = dist z c ^ 2 / ρ ^ 2 := by
    simp [f, norm_smul, Real.norm_eq_abs, dist_eq_norm, mul_pow, div_eq_mul_inv, mul_comm]
  have hd (z w : Point) : dist (f z) (f w) = dist z w / ρ := by
    simp only [f, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, dist_sub_right]
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨i, j, hij, hclose⟩ := annular_equidistant_triple_close_pair (f p)
    (fun i ↦ f (q i)) hx hx34
    (by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hp]))
    (fun i ↦ by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hlo i]))
    (fun i ↦ by rw [hf]; exact (div_le_iff₀ hsq).mpr (by simpa using hhi i))
    (fun i j ↦ by rw [hd, hd, heq i j])
  rw [hd, div_pow] at hclose
  exact ⟨i, j, hij, (div_le_iff₀ hsq).mp hclose⟩

/-- Saturated apex/palette incidences; the radius is a distance, not its square. -/
noncomputable def SaturatedDistanceIncidences (p : Config n) : Finset (Fin n × ℝ) :=
  (Finset.univ.product (OrderedDistanceValues p)).filter
    (fun ir ↦ (DistanceOutNeighborsAtValue p ir.1 ir.2).card = 3)

/-- A saturated incidence carries an increasing pair below `t` whenever every
indexed triple on its circle has a pair below `t`. -/
lemma saturated_incidence_increasing_pair_of_triple {p : Config n} {t : ℝ}
    {ir : Fin n × ℝ} (hir : ir ∈ SaturatedDistanceIncidences p)
    (htriple : ∀ f : Fin 3 → Fin n, (∀ i, dist (p ir.1) (p (f i)) = ir.2) →
      ∃ i j : Fin 3, i ≠ j ∧ dist (p (f i)) (p (f j)) ^ 2 ≤ t) :
    ∃ a b, a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      a < b ∧ dist (p a) (p b) ^ 2 ≤ t := by
  classical
  have hc := (Finset.mem_filter.mp hir).2
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp hc
  let f : Fin 3 → Fin n := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hmem (i : Fin 3) : f i ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 := by
    rw [hs]; fin_cases i <;> simp [f]
  have hd (i : Fin 3) : dist (p ir.1) (p (f i)) = ir.2 :=
    (Finset.mem_filter.mp (hmem i)).2.2
  obtain ⟨i, j, hij, hclose⟩ := htriple f hd
  rcases lt_or_gt_of_ne (hf.ne hij) with hlt | hgt
  · exact ⟨f i, f j, hmem i, hmem j, hlt, hclose⟩
  · exact ⟨f j, f i, hmem j, hmem i, hgt, by simpa [dist_comm] using hclose⟩

/-- Ordered distinct pairs below an inclusive squared-distance threshold. -/
noncomputable def OrderedClosePairs (p : Config n) (t : ℝ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).offDiag.filter (fun ij ↦ dist (p ij.1) (p ij.2) ^ 2 ≤ t)

/-- Each unordered close pair is represented once, with increasing indices. -/
noncomputable def IncreasingClosePairs (p : Config n) (t : ℝ) : Finset (Fin n × Fin n) :=
  (OrderedClosePairs p t).filter (fun ij ↦ ij.1 < ij.2)

/-- The ordered count is twice the increasing-index count, including empty cases. -/
theorem orderedClosePairs_card (p : Config n) (t : ℝ) :
    (OrderedClosePairs p t).card = 2 * (IncreasingClosePairs p t).card := by
  classical
  let s := OrderedClosePairs p t
  have hs : s.filter (fun ij ↦ ¬ij.1 < ij.2) =
      (IncreasingClosePairs p t).image Prod.swap := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hij, hlt⟩
      have hne := (Finset.mem_offDiag.mp (Finset.mem_filter.mp hij).1).2.2
      refine ⟨ij.swap, ?_, Prod.swap_swap ij⟩
      simp only [IncreasingClosePairs, OrderedClosePairs, Finset.mem_filter,
        Finset.mem_offDiag, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hne.symm, by simpa [dist_comm] using (Finset.mem_filter.mp hij).2⟩,
        lt_of_le_of_ne (le_of_not_gt hlt) hne.symm⟩
    · rintro ⟨ji, hji, rfl⟩
      have hlt := (Finset.mem_filter.mp hji).2
      have hji' := (Finset.mem_filter.mp hji).1
      constructor
      · simpa [s, OrderedClosePairs, Finset.mem_offDiag, ne_comm, dist_comm] using hji'
      · exact not_lt_of_gt hlt
  have hc := Finset.card_filter_add_card_filter_not (s := s) (p := fun ij ↦ ij.1 < ij.2)
  rw [hs, Finset.card_image_of_injective _ Prod.swap_injective] at hc
  change (IncreasingClosePairs p t).card + (IncreasingClosePairs p t).card =
    (OrderedClosePairs p t).card at hc
  omega

/-- Degree cap alone forces many saturated incidences. The real subtraction
keeps the conclusion valid when `n-1-2D` is negative. -/
theorem saturatedDistanceIncidences_lower_bound {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    (n : ℝ) * ((n : ℝ) - 1 - 2 * (NumDistancesOrdered p : ℝ)) ≤
      ((SaturatedDistanceIncidences p).card : ℝ) := by
  classical
  have hrow (i : Fin n) :
      (n : ℝ) - 1 - 2 * (NumDistancesOrdered p : ℝ) ≤
        (((OrderedDistanceValues p).filter
          (fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)).card : ℝ) := by
    have hd := sum_distanceDegreeDeficit p hn i
    have hcount :
        (∑ r ∈ OrderedDistanceValues p,
          (if (DistanceOutNeighborsAtValue p i r).card = 3 then (0 : ℝ) else 1)) ≤
        ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro r _hr
      split_ifs with h
      · rw [h]; norm_num
      · have hc : (DistanceOutNeighborsAtValue p i r).card ≤ 2 := by
          have := hcap i r
          omega
        have hcR : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 2 := by
          exact_mod_cast hc
        linarith
    have hsum :
        (∑ r ∈ OrderedDistanceValues p,
          (if (DistanceOutNeighborsAtValue p i r).card = 3 then (0 : ℝ) else 1)) =
        (((OrderedDistanceValues p).filter
          (fun r ↦ ¬(DistanceOutNeighborsAtValue p i r).card = 3)).card : ℝ) := by
      simp [Finset.sum_ite, Finset.sum_const]
    rw [hsum, hd] at hcount
    have hc := Finset.card_filter_add_card_filter_not
      (s := OrderedDistanceValues p)
      (p := fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)
    have hcR := congrArg (fun k : ℕ ↦ (k : ℝ)) hc
    simp only [Nat.cast_add] at hcR
    change _ + _ = (NumDistancesOrdered p : ℝ) at hcR
    linarith
  have hcard : (SaturatedDistanceIncidences p).card =
      ∑ i, ((OrderedDistanceValues p).filter
        (fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)).card := by
    unfold SaturatedDistanceIncidences
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.product_eq_sprod, Finset.sum_product]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦ hrow i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Nat.cast_sum, ← hcard] using h

/-- A saturated incidence contains a distinct close pair in the normalized annulus. -/
lemma saturated_incidence_has_close_pair {p : Config n} {x : ℝ}
    (hx : 0 ≤ x) (hx34 : x ≤ 3 / 4)
    (hlo : ∀ i, 1 - x ≤ ‖p i‖ ^ 2) (hhi : ∀ i, ‖p i‖ ^ 2 ≤ 1)
    {ir : Fin n × ℝ} (hir : ir ∈ SaturatedDistanceIncidences p) :
    ∃ a b, a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      a < b ∧ dist (p a) (p b) ^ 2 ≤ 4 * x := by
  exact saturated_incidence_increasing_pair_of_triple hir fun f hd ↦
    annular_equidistant_triple_close_pair (p ir.1) (fun i ↦ p (f i)) hx hx34 (hlo ir.1)
      (fun i ↦ hlo (f i)) (fun i ↦ hhi (f i))
      (fun i j ↦ (hd i).trans (hd j).symm)

/-- Charging one increasing-index pair per saturated incidence loses at most
two apexes per pair. GP3 is the only geometric assumption in this count. -/
theorem saturatedDistanceIncidences_le_orderedClosePairs {p : Config n} {t : ℝ}
    (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hpair : ∀ ir ∈ SaturatedDistanceIncidences p,
      ∃ a b, a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
        b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
        a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    (SaturatedDistanceIncidences p).card ≤ (OrderedClosePairs p t).card := by
  classical
  let S := SaturatedDistanceIncidences p
  have hex (ir : Fin n × ℝ) (hir : ir ∈ S) :
      ∃ ab : Fin n × Fin n,
        ab.1 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
        ab.2 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
        ab ∈ IncreasingClosePairs p t := by
    obtain ⟨a, b, ha, hb, hab, hclose⟩ := hpair ir hir
    exact ⟨(a, b), ha, hb, by
      simp [IncreasingClosePairs, OrderedClosePairs, Finset.mem_offDiag, hab, hab.ne, hclose]⟩
  let f : Fin n × ℝ → Fin n × Fin n := fun ir ↦
    if hir : ir ∈ S then Classical.choose (hex ir hir) else (ir.1, ir.1)
  have hf (ir : Fin n × ℝ) (hir : ir ∈ S) :
      (f ir).1 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      (f ir).2 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      f ir ∈ IncreasingClosePairs p t := by
    simpa only [f, dite_eq_left hir] using Classical.choose_spec (hex ir hir)
  have hbound : S.card ≤ 2 * (IncreasingClosePairs p t).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (fun ir hir ↦ (hf ir hir).2.2) 2
    intro ab hab
    have hne : ab.1 ≠ ab.2 := (Finset.mem_filter.mp hab).2.ne
    apply le_trans _ (indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp3 hne)
    apply Finset.card_le_card_of_injOn (fun ir : Fin n × ℝ ↦ ir.1)
    · intro ir hir
      obtain ⟨hirS, hirf⟩ := Finset.mem_filter.mp hir
      obtain ⟨ha, hb, _⟩ := hf ir hirS
      rw [hirf] at ha hb
      have hda := (Finset.mem_filter.mp ha).2.2
      have hdb := (Finset.mem_filter.mp hb).2.2
      simp only [Finset.mem_coe, IndexedEquidistantWitnesses, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hda.trans hdb.symm
    · intro ir hir jr hjr heq
      obtain ⟨hirS, hirf⟩ := Finset.mem_filter.mp hir
      obtain ⟨hjrS, hjrf⟩ := Finset.mem_filter.mp hjr
      have ha := (hf ir hirS).1
      have hb := (hf jr hjrS).1
      rw [hirf] at ha
      rw [hjrf] at hb
      have hda := (Finset.mem_filter.mp ha).2.2
      have hdb := (Finset.mem_filter.mp hb).2.2
      change ir.1 = jr.1 at heq
      apply Prod.ext heq
      rw [heq] at hda
      exact hda.symm.trans hdb
  simpa only [orderedClosePairs_card, S] using hbound

/-- Complete finite normalized close-pair bridge, with GP3 and GP4 explicit. -/
theorem annular_close_pairs_lower_bound {p : Config n}
    (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hgp4 : ∀ T ⊆ Config.toFinset p, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) (hx34 : x ≤ 3 / 4)
    (hlo : ∀ i, 1 - x ≤ ‖p i‖ ^ 2) (hhi : ∀ i, ‖p i‖ ^ 2 ≤ 1) :
    (n : ℝ) * ((n : ℝ) - 1 - 2 * (NumDistances p : ℝ)) ≤
      ((OrderedClosePairs p (4 * x)).card : ℝ) := by
  have hC := saturatedDistanceIncidences_lower_bound hn
    (distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hp hgp4)
  rw [← numDistances_eq_numDistancesOrdered_of_injective hp] at hC
  have hCL := saturatedDistanceIncidences_le_orderedClosePairs hp hgp3
    (fun _ hir ↦ saturated_incidence_has_close_pair hx hx34 hlo hhi hir)
  exact hC.trans (by exact_mod_cast hCL)

/-- Scaled-annulus incidence geometry, charged in the original configuration. -/
lemma saturated_incidence_has_close_pair_of_scaled_annulus
    {p : Config n} (c : Point) {ρ x : ℝ}
    (hρ : 0 < ρ) (hx : 0 ≤ x) (hx34 : x ≤ 3 / 4)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    {ir : Fin n × ℝ} (hir : ir ∈ SaturatedDistanceIncidences p) :
    ∃ a b, a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      a < b ∧ dist (p a) (p b) ^ 2 ≤ 4 * x * ρ ^ 2 := by
  exact saturated_incidence_increasing_pair_of_triple hir fun f hd ↦
    scaled_annular_equidistant_triple_close_pair c (p ir.1) (fun i ↦ p (f i)) hρ hx hx34
      (hlo ir.1) (fun i ↦ hlo (f i)) (fun i ↦ hhi (f i))
      (fun i j ↦ (hd i).trans (hd j).symm)

/-- The complete finite bridge from the merged annulus theorem and few
distinct distances. GP3 is explicit and separate from raw GP4. -/
theorem thin_annulus_close_pairs_lower_bound {p : Config n}
    (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hgp4 : ∀ T ⊆ Config.toFinset p, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 2 ≤ n) {δ : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ))
    (hx34 : 12 * δ + 4 / (n : ℝ) ≤ 3 / 4) :
    (n : ℝ) * ((n : ℝ) - 1 - 2 * (NumDistances p : ℝ)) ≤
      ((OrderedClosePairs p
        (4 * (12 * δ + 4 / (n : ℝ)) * distanceAnnulusRadius p ^ 2)).card : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcap := distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hp hgp4
  have hρ := distanceAnnulusRadius_pos hp hn hcap
  have hs := thin_annulus_sq_of_noFourCocircular hp hgp4 hn0 hD
  have hρsq := (distanceAnnulusRadius_bounds hn0 hcap).2.1
  have hq : 0 ≤ 3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
    rw [← sum_distanceDegreeDeficit p hn0 ⟨0, hn0⟩]
    apply Finset.sum_nonneg
    intro r _hr
    have hc : ((DistanceOutNeighborsAtValue p ⟨0, hn0⟩ r).card : ℝ) ≤ 3 := by
      exact_mod_cast hcap ⟨0, hn0⟩ r
    linarith
  have hD' := hD
  rw [numDistances_eq_numDistancesOrdered_of_injective hp] at hD'
  have hx : 0 ≤ 12 * δ + 4 / (n : ℝ) := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    field_simp
    nlinarith
  have hCL := saturatedDistanceIncidences_le_orderedClosePairs hp hgp3
    (fun _ hir ↦ saturated_incidence_has_close_pair_of_scaled_annulus
      (configCentroid p) hρ hx hx34
      (fun i ↦ by rw [hρsq]; nlinarith [(hs i).1])
      (fun i ↦ by rw [hρsq]; exact (hs i).2) hir)
  have hC := saturatedDistanceIncidences_lower_bound hn0 hcap
  rw [← numDistances_eq_numDistancesOrdered_of_injective hp] at hC
  exact hC.trans (by exact_mod_cast hCL)

/-- Density form without division: the finite interface for a weak-limit
consumer. The ordered count excludes the diagonal and uses squared distance. -/
theorem thin_annulus_close_pair_density {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 2 ≤ n) {δ : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ))
    (hx34 : 12 * δ + 4 / (n : ℝ) ≤ 3 / 4) :
    (1 / 3 - 2 * δ - 1 / (n : ℝ)) * (n : ℝ) ^ 2 ≤
      ((OrderedClosePairs p
        (4 * (12 * δ + 4 / (n : ℝ)) * distanceAnnulusRadius p ^ 2)).card : ℝ) := by
  have h := thin_annulus_close_pairs_lower_bound hp hgp.1 hgp.2 hn hD hx34
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmul := mul_le_mul_of_nonneg_left hD (le_of_lt hnR)
  have hid : (1 / 3 - 2 * δ - 1 / (n : ℝ)) * (n : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1 - 2 * ((1 / 3 + δ) * (n : ℝ))) := by
    field_simp; ring
  rw [hid]
  nlinarith

end Esgk
