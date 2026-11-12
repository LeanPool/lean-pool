/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3381T1PairedTriangulation
public import LeanPool.ApollonianSuperharmonic.P5662T1TriangulationBarycentricCoordinates
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex

-- [TABLET NODE: P3381T1TriangulationBoundary]

/-!
# P3381T1TriangulationBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TriangulationBoundaryProof

private theorem hsubAt142 :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (k : Fin t.count),
    let standard : Fin 3 → Real × Real := ![(0, 0), (1, 0), (0, 1)]
    ∀ (A : ℝ × ℝ ≃ₜ ℝ × ℝ), (∀ (w : Fin (3 : ℕ) → ℝ), ∑ i : Fin (3 : ℕ), w i = (1 : ℝ) → (A : ℝ ×
        ℝ → ℝ × ℝ) (∑ i : Fin (3 : ℕ), w i • standard i) = ∑ i : Fin (3 : ℕ), w i • (p.vertex ∘
        t.face k) i) → (
    let U : Set (Real × Real) :=
      Set.Ioo (0 : Real) (1 / 4) ×ˢ Set.Ioo (0 : Real) (1 / 4)
    A '' U ⊆ X) := by
  classical
  intro n p X K t k standard A hA U
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (0 < x.1 ∧ x.1 < 1 / 4) ∧ (0 < x.2 ∧ x.2 < 1 / 4) := hx
  let w : Fin 3 → Real := ![1 - x.1 - x.2, x.1, x.2]
  have hw : (∑ i, w i) = 1 := by
    rw [Fin.sum_univ_three]
    change (1 - x.1 - x.2) + x.1 + x.2 = 1
    ring
  have hwx : (∑ i, w i • standard i) = x := by
    apply Prod.ext <;> simp [Fin.sum_univ_three, standard, w]
  have hAx : A x = ∑ i, w i • p.vertex (t.face k i) := by
    rw [← hwx]
    exact hA w hw
  rw [t.source_cover]
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  rw [hAx]
  apply mem_convexHull_of_exists_fintype w (p.vertex ∘ t.face k)
  · intro i
    fin_cases i <;> dsimp [w]
    all_goals linarith [hx'.1.1, hx'.1.2, hx'.2.1, hx'.2.2]
  · exact hw
  · intro i
    exact Set.mem_range_self i
  · rfl

private theorem local_cones :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), (∃ (b : Fin t.count → ℝ × ℝ → Fin
        (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j = (1 : ℝ))
        ∧ (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j • p.vertex (t.face k j)
        = z) ∧ (∀ (k : Fin t.count), ∀ (w : Fin (3 : ℕ) → ℝ), ∑ j : Fin (3 : ℕ), w j = (1 : ℝ) →
        b k (∑ j : Fin (3 : ℕ), w j • p.vertex (t.face k j)) = w) ∧ (∀ (k : Fin t.count), ∀ (j :
            Fin (3 : ℕ)), Continuous fun (z : ℝ × ℝ) => b k z j) ∧ (∀ (k : Fin t.count), ∀ (z : ℝ ×
        ℝ), z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range (p.vertex ∘ t.face k)) ↔ ∀
            (j : Fin (3 : ℕ)), (0 : ℝ) ≤ b k z j) ∧ (∀ (k : Fin t.count), ∀ (i : Fin (3 : ℕ)), b k
        (p.vertex (t.face k i)) = Pi.single i (1 : ℝ)) ∧ ∀ (k : Fin t.count), ∀ (l : Fin
        t.count), ∀ z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (p.vertex '' (Set.range
        (t.face k) ∩ Set.range (t.face l))), ∀ (j : Fin (3 : ℕ)), t.face k j ∉ Set.range (t.face
        l) → b k z j = (0 : ℝ)) → ((∀ (i : Fin (n + (3 : ℕ))), ∀ (k : Fin t.count), p.vertex i ∈
        (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range (p.vertex ∘ t.face k)) ↔ i ∈
        Set.range (t.face k)) → (∀ i, ∃ r : Real, 0 < r ∧
        ∀ z ∈ Metric.ball (p.vertex i) r,
          z ∈ X ↔ ∃ k, i ∈ Set.range (t.face k) ∧
            ∃ w : Fin 3 → Real, (∀ j, 0 ≤ w j) ∧
              z = p.vertex i + ∑ j, w j • (p.vertex (t.face k j) - p.vertex i))) := by
  classical
  intro n p X K t coordinates vertex_incidence
  classical
  obtain ⟨b, bsum, breconstruct, bunique, bcontinuous, bhull, bvertex, bcommon⟩ :=
    coordinates
  let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
  have closed_D k : IsClosed (D k) :=
    ((Set.finite_range (p.vertex ∘ t.face k)).isCompact_convexHull Real).isClosed
  intro i
  let N : Set (Real × Real) := ⋂ k,
    (if i ∈ Set.range (t.face k) then Set.univ else (D k)ᶜ) ∩
      ⋂ j, (if t.face k j = i then {z | 0 < b k z j} else Set.univ)
  have open_N : IsOpen N := by
    apply isOpen_iInter_of_finite
    intro k
    apply IsOpen.inter
    · split_ifs
      · exact isOpen_univ
      · exact (closed_D k).isOpen_compl
    · apply isOpen_iInter_of_finite
      intro j
      split_ifs
      · exact isOpen_lt continuous_const (bcontinuous k j)
      · exact isOpen_univ
  have mem_N : p.vertex i ∈ N := by
    apply Set.mem_iInter.mpr
    intro k
    constructor
    · split_ifs with hki
      · trivial
      · exact fun h => hki ((vertex_incidence i k).mp h)
    · apply Set.mem_iInter.mpr
      intro j
      split_ifs with hji
      · change 0 < b k (p.vertex i) j
        rw [← hji, bvertex]
        simp
      · trivial
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp open_N _ mem_N
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hzN := Set.mem_iInter.mp (hball hz)
  constructor
  · intro hzX
    rw [t.source_cover] at hzX
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hzX
    have hki : i ∈ Set.range (t.face k) := by
      by_contra h
      have hnot := (hzN k).1
      simp only [h, ite_false] at hnot
      exact hnot hzk
    refine ⟨k, hki, b k z, (bhull k z).mp hzk, ?_⟩
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, bsum, one_smul, breconstruct]
    abel
  · rintro ⟨k, ⟨a, ha⟩, w, hw, heq⟩
    let d : Fin 3 → Real := Pi.single a 1
    let q : Fin 3 → Real := fun j => w j + (1 - ∑ s, w s) * d j
    have hqsum : (∑ j, q j) = 1 := by
      simp only [q, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [d]
    have hqz : (∑ j, q j • p.vertex (t.face k j)) = z := by
      simp only [q, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
      simp only [d, Pi.single_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, ha]
      rw [heq]
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
      rw [sub_smul, one_smul]
      abel
    have hbq : b k z = q := hqz ▸ bunique k q hqsum
    have hqnonneg : ∀ j, 0 ≤ q j := by
      intro j
      by_cases hja : j = a
      · have hpos := Set.mem_iInter.mp (hzN k).2 j
        simp only [hja, ha, ite_true, Set.mem_ofPred_eq] at hpos
        rw [hbq] at hpos
        simpa [hja] using hpos.le
      · simpa [q, d, Pi.single_apply, hja] using hw j
    rw [t.source_cover]
    exact Set.mem_iUnion.mpr ⟨k, (bhull k z).mpr (hbq ▸ hqnonneg)⟩

private theorem bcombo :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (b : Fin t.count → ℝ × ℝ → Fin (3
        : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j = (1 : ℝ)) →
        ((∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j • p.vertex (t.face k j)
        = z) → ((∀ (k : Fin t.count), ∀ (w : Fin (3 : ℕ) → ℝ), ∑ j : Fin (3 : ℕ), w j = (1 : ℝ) →
        b k (∑ j : Fin (3 : ℕ), w j • p.vertex (t.face k j)) = w) → (∀ {ι : Type}, ∀ [Fintype ι],
            ∀ (k : Fin t.count), ∀ (a : ι → ℝ), ∀ (f : ι → ℝ × ℝ), ∑ r : ι, a r = (1
            : ℝ)
        → ∀ (j : Fin (3 : ℕ)), b k (∑ r : ι, a r • f r) j = ∑ r : ι, a r * b k (f r) j))) := by
  classical
  intro n p X K t b bsum breconstruct bunique ι typeclassInstance0 k a f ha j
  let W : Fin 3 → Real := fun j => ∑ r, a r * b k (f r) j
  have hW : (∑ j, W j) = 1 := by
    simp only [W]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, bsum, mul_one]
    exact ha
  have hWz : (∑ j, W j • p.vertex (t.face k j)) = ∑ r, a r • f r := by
    simp only [W, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp_rw [mul_smul, ← Finset.smul_sum, breconstruct]
  have h := bunique k W hW
  rw [hWz] at h
  exact congrFun h j

private theorem hdisjoint :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (b : Fin t.count → ℝ × ℝ → Fin (3
        : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ
        × ℝ)) (Set.range (p.vertex ∘ t.face k)) ↔ ∀ (j : Fin (3 : ℕ)), (0 : ℝ) ≤ b k z j) → ((∀
            (k : Fin t.count), ∀ (l : Fin t.count), ∀ z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
        (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))), ∀ (j : Fin (3 : ℕ)), t.face
        k j ∉ Set.range (t.face l) → b k z j = (0 : ℝ)) → (
    let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
    (∀ k, ∀ l, (Set.range (t.face k) ⊆ Set.range (t.face l)) → (k = l)) → (∀ (k : Fin t.count), ∀
        (l : Fin t.count), k ≠ l → ∀ (z : ℝ × ℝ), (∀ (j : Fin (3 : ℕ)), (0 : ℝ) < b k z j) → z ∈ D l
        → False))) := by
  classical
  intro n p X K t b bhull bcommon D hfaces_subset k l hkl z hz hzl
  have hzk : z ∈ D k := (bhull k z).mpr fun j => (hz j).le
  have hzc : z ∈ convexHull Real
      (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))) := by
    rw [← t.source_intersection]
    exact ⟨hzk, hzl⟩
  apply hkl
  apply hfaces_subset k l
  rintro i ⟨j, rfl⟩
  by_contra hj
  exact (ne_of_gt (hz j)) (bcommon k l z hzc j hj)

private theorem edge_coords :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (b : Fin t.count → ℝ × ℝ → Fin (3
        : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (i : Fin (3 : ℕ)), b k (p.vertex (t.face k i)) =
        Pi.single i (1 : ℝ)) → ((∀ (a : Fin 3), ∀ (b : Fin 3), (a ≠ b) → (∃ c, a ≠ c ∧ b ≠ c)) →
        ((∀ k, ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (a : Real), ∀ (c : Real), (a + c = 1)
            → (∀ j, b k (a • x + c • y) j = a * b
        k x j + c * b k y j)) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (i ≠ j) →
        (∀ (u : ℝ),
    let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex j
    let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)}
    ∀ k ∈ I,
  ∃ (a : Fin (3 : ℕ)) (d : Fin (3 : ℕ)) (c : Fin (3 : ℕ)),
    t.face k a = i ∧ t.face k d = j ∧ a ≠ d ∧ a ≠ c ∧ d ≠ c ∧ b k z a = (1 : ℝ) - u ∧ b k z d = u
        ∧ b k z c = (0 : ℝ))))) := by
  classical
  intro n p X K t b bvertex third blinear i j hij u z I k hk
  obtain ⟨a, ha⟩ := hk.1
  obtain ⟨d, hd⟩ := hk.2
  have had : a ≠ d := by intro h; exact hij (ha.symm.trans (h ▸ hd))
  obtain ⟨c, hac, hdc⟩ := third a d had
  refine ⟨a, d, c, ha, hd, had, hac, hdc, ?_, ?_, ?_⟩
  all_goals dsimp [z]; rw [blinear k _ _ _ _ (by ring), ← ha, ← hd, bvertex, bvertex]
  · simp [had]
  · simp [Ne.symm had]
  · simp [Ne.symm hac, Ne.symm hdc]

private theorem mem_D :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K),
    let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
    ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ∀ (u : ℝ), (u ∈ Set.Ioo (0 : ℝ) (1 :
        ℝ)) → (
    let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex j
    let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)}
    ∀ k ∈ I, z ∈ D k) := by
  classical
  intro n p X K t D i j u hu z I k hk
  apply (convex_convexHull Real _).segment_subset
    (subset_convexHull Real _ ?_) (subset_convexHull Real _ ?_)
    (show z ∈ segment Real (p.vertex i) (p.vertex j) from ?_)
  · obtain ⟨a, ha⟩ := hk.1
    exact ⟨a, congrArg p.vertex ha⟩
  · obtain ⟨d, hd⟩ := hk.2
    exact ⟨d, congrArg p.vertex hd⟩
  · rw [segment_eq_image]
    exact ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩

private theorem containing :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (b : Fin t.count → ℝ × ℝ → Fin (3
        : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (l : Fin t.count), ∀ z ∈ (convexHull ℝ : Set (ℝ × ℝ) →
        Set (ℝ × ℝ)) (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))), ∀ (j : Fin (3 :
        ℕ)), t.face k j ∉ Set.range (t.face l) → b k z j = (0 : ℝ)) → (
    let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
    ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (∃ (k : Fin t.count), i ∈ Set.range
        (t.face k) ∧ j ∈ Set.range (t.face k)) → (∀ (u : ℝ), (u ∈ Set.Ioo (0 : ℝ) (1 : ℝ)) → (
    let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex j
    let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)}
    (∀ k, (k ∈ I) → (∃ a d c : Fin 3, t.face k a = i ∧ t.face k d = j ∧ a ≠ d ∧ a ≠ c ∧ d ≠ c ∧
        b k z a = 1 - u ∧ b k z d = u ∧ b k z c = 0)) → ((∀ k, (k ∈ I) → (z ∈ D k)) → (∀ (k : Fin
        t.count), z ∈ D k → k ∈ I))))) := by
  classical
  intro n p X K t b bcommon D i j hused u hu z I edge_coords mem_D k hk
  obtain ⟨l, hl⟩ := hused
  obtain ⟨a, d, c, ha, hd, had, hac, hdc, hza, hzd, hzc⟩ := edge_coords l hl
  have hcommon : z ∈ convexHull Real
      (p.vertex '' (Set.range (t.face l) ∩ Set.range (t.face k))) := by
    rw [← t.source_intersection]
    exact ⟨mem_D l hl, hk⟩
  constructor
  · by_contra hi
    have hzero := bcommon l k z hcommon a (ha ▸ hi)
    rw [hza] at hzero
    linarith [hu.2]
  · by_contra hj
    have hzero := bcommon l k z hcommon d (hd ▸ hj)
    rw [hzd] at hzero
    linarith [hu.1]

private theorem opposite :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (b : Fin t.count → ℝ × ℝ → Fin (3
        : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (j : Fin (3 : ℕ)), Continuous fun (z : ℝ × ℝ) => b k z
        j) → ((∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
        (Set.range (p.vertex ∘ t.face k)) ↔ ∀ (j : Fin (3 : ℕ)), (0 : ℝ) ≤ b k z j) → ((∀ (k :
            Fin t.count), ∀ (i : Fin (3 : ℕ)), b k (p.vertex (t.face k i)) = Pi.single i (1 : ℝ))
            → (
    let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
    (∀ (a : Fin 3), ∀ (b : Fin 3), ∀ (c : Fin 3), (a ≠ b) → ((a ≠ c) → ((b ≠ c) → (∀ j, j = a ∨ j
        = b ∨ j = c)))) → ((∀ k, ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (a : Real), ∀ (c :
            Real), (a + c = 1) → (∀ j, b k (a • x + c • y) j = a * b k x
        j + c * b k y j)) → ((∀ k, ∀ l, (k ≠ l) → (∀ z, (∀ j, 0 < b k z j) → ((z ∈ D l) →
            (False)))) → ((∀ (O : Set (Real × Real)), (IsOpen O) → (∀ z, (z ∈ O) → (∀ v, ∃ u :
            Real, 0 < u
        ∧ u < 1 ∧ (1 - u) • z + u • v ∈ O))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 :
        ℕ))), ∀ (u : ℝ), (u ∈ Set.Ioo (0 : ℝ) (1 : ℝ)) → (
    let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex j
    let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)}
    ∀ (k : Fin t.count), ∀ (l : Fin t.count), k ≠ l →
    k ∈ I →
      l ∈ I →
        ∀ (a : Fin (3 : ℕ)), ∀ (d : Fin (3 : ℕ)), ∀ (c : Fin (3 : ℕ)), ∀ (e : Fin (3 : ℕ)), ∀ (f
            : Fin (3 : ℕ)), ∀ (g : Fin (3 : ℕ)), t.face k a = i →
            t.face k d = j →
              a ≠ d →
                a ≠ c →
                  d ≠ c →
                    t.face l e = i →
                      t.face l f = j →
                        e ≠ f →
                          e ≠ g →
                            f ≠ g →
                              b k z a = (1 : ℝ) - u →
                                b k z d = u →
                                  b k z c = (0 : ℝ) →
                                    b l z e = (1 : ℝ) - u →
                                      b l z f = u → b l z g = (0 : ℝ) → b k (p.vertex (t.face l
                                          g)) c < (0 : ℝ))))))))) := by
  classical
  intro n p X K t b bcontinuous bhull bvertex D indices blinear hdisjoint perturb i j u hu z I k
      l hkl hk hl a d c e f g hka hkd had hac hdc hle hlf hef heg hfg hza hzd hzc hze hzf hzg
  by_contra hnot
  have hnonneg := le_of_not_gt hnot
  let O : Set (Real × Real) := {y | 0 < b k y a ∧ 0 < b k y d}
  have hO : IsOpen O :=
    (isOpen_lt continuous_const (bcontinuous k a)).inter
      (isOpen_lt continuous_const (bcontinuous k d))
  have hzO : z ∈ O := by
    dsimp [O]
    rw [hza, hzd]
    exact ⟨sub_pos.mpr hu.2, hu.1⟩
  obtain ⟨s, hs0, hs1, hys⟩ := perturb O hO z hzO (p.vertex (t.face l g))
  let y := (1 - s) • z + s • p.vertex (t.face l g)
  have hky : y ∈ D k := by
    apply (bhull k y).mpr
    intro r
    rcases indices a d c had hac hdc r with rfl | rfl | rfl
    · exact hys.1.le
    · exact hys.2.le
    · dsimp [y]
      rw [blinear k _ _ _ _ (by ring), hzc, mul_zero, zero_add]
      exact mul_nonneg hs0.le hnonneg
  apply hdisjoint l k hkl.symm y _ hky
  intro r
  dsimp [y]
  rw [blinear l _ _ _ _ (by ring), bvertex]
  rcases indices e f g hef heg hfg r with rfl | rfl | rfl
  · simp only [Pi.single_apply, heg, ite_false, mul_zero, add_zero, hze]
    exact mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hu.2)
  · simp only [Pi.single_apply, hfg, ite_false, mul_zero, add_zero, hzf]
    exact mul_pos (sub_pos.mpr hs1) hu.1
  · simp only [Pi.single_apply, ite_true, mul_one, hzg, mul_zero, zero_add]
    exact hs0

private theorem hnotAt427 :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (k : Fin t.count), ∀ (b : Fin
        t.count → ℝ × ℝ → Fin (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), z ∈ (convexHull
        ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range (p.vertex ∘ t.face k)) ↔ ∀ (j : Fin (3 : ℕ)),
            (0 : ℝ) ≤ b k z j) → ((∀ (k : Fin t.count), ∀ (i : Fin (3 : ℕ)), b k (p.vertex (t.face k
        i)) = Pi.single i (1 : ℝ)) → (
    let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
    (∀ k, IsClosed (D k)) → (∀ k, ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (a : Real), ∀ (c :
        Real), (a + c = 1) → (∀ j, b k (a • x + c • y) j = a * b k x j + c * b k y
        j)) → ((∀ (O : Set (Real × Real)), (IsOpen O) → (∀ z, (z ∈ O) → (∀ v, ∃ u : Real, 0 < u ∧
        u < 1 ∧ (1 - u) • z + u • v ∈ O))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 :
        ℕ))), ∀ (u : ℝ),
    let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex j
    let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)}
    (∀ k, (z ∈ D k) → (k ∈ I)) → ((I = {k}) → ((k ∈ I) → (∀ (a : Fin (3 : ℕ)), ∀ (c : Fin (3 :
        ℕ)), (a ≠ c) → ((b k z c = (0 : ℝ)) → (z ∉ interior X))))))))) := by
  classical
  intro n p X K t k b bhull bvertex D closed_D blinear perturb i j u z I containing hI hk a c hac
      hzc hzint
  let N : Set (Real × Real) := ⋂ l, if l = k then Set.univ else (D l)ᶜ
  have hN : IsOpen N := by
    apply isOpen_iInter_of_finite
    intro l
    split_ifs
    · exact isOpen_univ
    · exact (closed_D l).isOpen_compl
  have hzN : z ∈ N := by
    apply Set.mem_iInter.mpr
    intro l
    split_ifs with hl
    · trivial
    · intro hzl
      have hlI := containing l hzl
      rw [hI] at hlI
      exact hl hlI
  let v : Real × Real := (2 : Real) • z + (-1 : Real) • p.vertex (t.face k c)
  have hvc : b k v c = -1 := by
    dsimp [v]
    rw [blinear k _ _ _ _ (by norm_num), hzc, bvertex]
    simp
  obtain ⟨s, hs0, hs1, hys⟩ := perturb (N ∩ interior X)
    (hN.inter isOpen_interior) z ⟨hzN, hzint⟩ v
  let y : Real × Real := (1 - s) • z + s • v
  have hyX : y ∈ X := interior_subset hys.2
  rw [t.source_cover] at hyX
  obtain ⟨l, hyl⟩ := Set.mem_iUnion.mp hyX
  have hlk : l = k := by
    by_contra hl
    have hnot := Set.mem_iInter.mp hys.1 l
    simp only [hl, ite_false] at hnot
    exact hnot hyl
  have hyc := (bhull k y).mp (hlk ▸ hyl) c
  dsimp [y] at hyc
  rw [blinear k _ _ _ _ (by ring), hzc, hvc] at hyc
  linarith

private theorem hNX :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (k : Fin t.count), ∀ (b : Fin
        t.count → ℝ × ℝ → Fin (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), z ∈ (convexHull
        ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range (p.vertex ∘ t.face k)) ↔ ∀ (j : Fin (3 : ℕ)),
            (0 : ℝ) ≤ b k z j) → ((∀ (a : Fin 3), ∀ (b : Fin 3), ∀ (c : Fin 3), (a ≠ b) → ((a ≠
            c) → ((b ≠ c) → (∀ j, j =
        a ∨ j = b ∨ j = c)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ∀ (u : ℝ),
    let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex j
    ∀ (l : Fin t.count), ∀ (a : Fin (3 : ℕ)), ∀ (d : Fin (3 : ℕ)), ∀ (c : Fin (3 : ℕ)), (t.face k
        a = i) → ((t.face k d = j) → ((a ≠ d) → ((a ≠ c) → ((d ≠ c) → ((b k z a = (1 : ℝ) - u) →
        ((b k z d = u) → ((b k z c = (0 : ℝ)) → (∀ (e : Fin (3 : ℕ)), ∀ (f : Fin (3 : ℕ)), ∀ (g :
            Fin (3 : ℕ)), (t.face l e = i) → ((t.face l f = j) → ((e ≠ f) → ((e ≠ g) → ((f ≠ g) →
            ((b
        l z e = (1 : ℝ) - u) → ((b l z f = u) → ((b l z g = (0 : ℝ)) → ((b l (p.vertex (t.face k
        c)) g < (0 : ℝ)) → ((b l (p.vertex (t.face k a)) g = 0) → ((b l (p.vertex (t.face k d)) g
        = 0) → ((∀ y, b l y g = b k y c * b l (p.vertex (t.face k c)) g) → (
    let N : Set (Real × Real) :=
      {y | 0 < b k y a ∧ 0 < b k y d} ∩ {y | 0 < b l y e ∧ 0 < b l y f}
    (IsOpen N) → ((z ∈ N) → (N ⊆ X)))))))))))))))))))))))) := by
  classical
  intro n p X K t k b bhull indices i j u z l a d c hka hkd had hac hdc hza hzd hzc e f g hle hlf
      hef heg hfg hze hzf hzg hnegative hlga hlgd relation N hN hzN y hy
  rw [t.source_cover]
  by_cases hc : 0 ≤ b k y c
  · refine Set.mem_iUnion.mpr ⟨k, (bhull k y).mpr ?_⟩
    intro r
    rcases indices a d c had hac hdc r with rfl | rfl | rfl
    · exact hy.1.1.le
    · exact hy.1.2.le
    · exact hc
  · refine Set.mem_iUnion.mpr ⟨l, (bhull l y).mpr ?_⟩
    intro r
    rcases indices e f g hef heg hfg r with rfl | rfl | rfl
    · exact hy.2.1.le
    · exact hy.2.2.le
    · rw [relation]
      exact (mul_pos_of_neg_of_neg (lt_of_not_ge hc) hnegative).le

private theorem hfrontier :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), (IsCompact X) → ((∃ (b : Fin
        t.count → ℝ × ℝ → Fin (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 :
        ℕ), b k z j = (1 : ℝ)) ∧ (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j
        • p.vertex (t.face k j) = z) ∧ (∀ (k : Fin t.count), ∀ (w : Fin (3 : ℕ) → ℝ), ∑ j : Fin
        (3 : ℕ), w j = (1 : ℝ) → b k (∑ j : Fin (3 : ℕ), w j • p.vertex (t.face k j)) = w) ∧ (∀
            (k : Fin t.count), ∀ (j : Fin (3 : ℕ)), Continuous fun (z : ℝ × ℝ) => b k z j) ∧ (∀
            (k : Fin t.count), ∀ (z : ℝ × ℝ), z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            (Set.range
        (p.vertex ∘ t.face k)) ↔ ∀ (j : Fin (3 : ℕ)), (0 : ℝ) ≤ b k z j) ∧ (∀ (k : Fin t.count),
            ∀ (i : Fin (3 : ℕ)), b k (p.vertex (t.face k i)) = Pi.single i (1 : ℝ)) ∧ ∀ (k : Fin
        t.count), ∀ (l : Fin t.count), ∀ z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (p.vertex
        '' (Set.range (t.face k) ∩ Set.range (t.face l))), ∀ (j : Fin (3 : ℕ)), t.face k j ∉
        Set.range (t.face l) → b k z j = (0 : ℝ)) → ((∀ i, ∀ j, i ≠ j → (∃ k, i ∈ Set.range (t.face
        k) ∧ j ∈ Set.range (t.face k)) → ∀ z ∈ openSegment Real (p.vertex i) (p.vertex j), (z ∈
        interior X ↔ ¬ (j = i + 1 ∨ i = j + 1))) → (frontier X = ⋃ i, segment Real (p.vertex i)
        (p.vertex (i + 1))))) := by
  classical
  intro n p X K t hcompact coordinates edge_interior
  classical
  obtain ⟨b, bsum, breconstruct, bunique, bcontinuous, bhull, bvertex, bcommon⟩ :=
    coordinates
  have third (c : Fin 3) : ∃ a d, a ≠ d ∧ a ≠ c ∧ d ≠ c := by
    fin_cases c <;> decide
  have sum_three {E : Type} [AddCommMonoid E] (f : Fin 3 → E)
      (a d c : Fin 3) (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c) :
      (∑ j, f j) = f a + f d + f c := by
    fin_cases a <;> fin_cases d <;> fin_cases c
    all_goals first
      | exact (had rfl).elim
      | exact (hac rfl).elim
      | exact (hdc rfl).elim
      | (rw [Fin.sum_univ_three]; ac_rfl)
  have edge_used : ∀ i : Fin (n + 3),
      ∃ k, i ∈ Set.range (t.face k) ∧ i + 1 ∈ Set.range (t.face k) := by
    intro i
    have hne : i ≠ i + 1 := by
      intro hi
      have hzero : (0 : Fin (n + 3)) = 1 :=
        add_left_cancel (show i + 0 = i + 1 by simpa only [add_zero] using hi)
      exact Fin.zero_ne_one hzero
    have he := t.edge_count i (i + 1) hne
    simp only [true_or, ite_true] at he
    have hn : 0 < Set.ncard {k : Fin t.count |
        i ∈ Set.range (t.face k) ∧ i + 1 ∈ Set.range (t.face k)} := by
      rw [he]
      exact Nat.zero_lt_one
    exact (Set.ncard_pos (Set.toFinite _)).mp hn
  have edge_subset i j (hused : ∃ k, i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)) :
      segment Real (p.vertex i) (p.vertex j) ⊆ X := by
    obtain ⟨k, ⟨a, ha⟩, ⟨d, hd⟩⟩ := hused
    have hs : segment Real (p.vertex i) (p.vertex j) ⊆
        convexHull Real (Set.range (p.vertex ∘ t.face k)) := by
      apply (convex_convexHull Real _).segment_subset
      · exact subset_convexHull Real _ ⟨a, congrArg p.vertex ha⟩
      · exact subset_convexHull Real _ ⟨d, congrArg p.vertex hd⟩
    intro z hz
    rw [t.source_cover]
    exact Set.mem_iUnion.mpr ⟨k, hs hz⟩
  have polygon_frontier i : segment Real (p.vertex i) (p.vertex (i + 1)) ⊆ frontier X := by
    have hne : i ≠ i + 1 := by
      intro hi
      have hzero : (0 : Fin (n + 3)) = 1 :=
        add_left_cancel (show i + 0 = i + 1 by simpa only [add_zero] using hi)
      exact Fin.zero_ne_one hzero
    have hs : openSegment Real (p.vertex i) (p.vertex (i + 1)) ⊆ frontier X := by
      intro z hz
      have hzX := edge_subset i (i + 1) (edge_used i)
        (openSegment_subset_segment Real _ _ hz)
      apply (mem_frontier_iff_notMem_interior hzX).mpr
      have h := edge_interior i (i + 1) hne (edge_used i) z hz
      simpa using h
    exact (segment_subset_closure_openSegment (𝕜 := Real)).trans
      ((closure_mono hs).trans isClosed_frontier.closure_eq.subset)
  apply Set.Subset.antisymm
  · intro z hzfront
    have hzX : z ∈ X := hcompact.isClosed.frontier_subset hzfront
    rw [t.source_cover] at hzX
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hzX
    have hnonneg := (bhull k z).mp hzk
    have hnotpos : ¬ ∀ j, 0 < b k z j := by
      intro hpos
      have hopen : IsOpen {y : Real × Real | ∀ j, 0 < b k y j} := by
        have heq : {y : Real × Real | ∀ j, 0 < b k y j} =
            ⋂ j, {y : Real × Real | 0 < b k y j} := by ext; simp
        rw [heq]
        exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (bcontinuous k j)
      have hsub : {y : Real × Real | ∀ j, 0 < b k y j} ⊆ X := by
        intro y hy
        rw [t.source_cover]
        exact Set.mem_iUnion.mpr ⟨k, (bhull k y).mpr (fun j => (hy j).le)⟩
      exact hzfront.2 ((hopen.subset_interior_iff.mpr hsub) hpos)
    obtain ⟨c, hc⟩ := not_forall.mp hnotpos
    have hzc : b k z c = 0 := le_antisymm (le_of_not_gt hc) (hnonneg c)
    obtain ⟨a, d, had, hac, hdc⟩ := third c
    have hsum : b k z a + b k z d = 1 := by
      have h := bsum k z
      rw [sum_three _ a d c had hac hdc, hzc, add_zero] at h
      exact h
    have hzrepr : b k z a • p.vertex (t.face k a) +
        b k z d • p.vertex (t.face k d) = z := by
      have h := breconstruct k z
      rw [sum_three _ a d c had hac hdc, hzc, zero_smul, add_zero] at h
      exact h
    have hzseg : z ∈ segment Real (p.vertex (t.face k a)) (p.vertex (t.face k d)) :=
      ⟨b k z a, b k z d, hnonneg a, hnonneg d, hsum, hzrepr⟩
    by_cases hza : z = p.vertex (t.face k a)
    · exact Set.mem_iUnion.mpr ⟨t.face k a, hza ▸ left_mem_segment Real _ _⟩
    by_cases hzd : z = p.vertex (t.face k d)
    · exact Set.mem_iUnion.mpr ⟨t.face k d, hzd ▸ left_mem_segment Real _ _⟩
    have hzopen := mem_openSegment_of_ne_left_right (Ne.symm hza) (Ne.symm hzd) hzseg
    have hij : t.face k a ≠ t.face k d := fun h => had (t.face_injective k h)
    have hused : ∃ l, t.face k a ∈ Set.range (t.face l) ∧
        t.face k d ∈ Set.range (t.face l) := ⟨k, ⟨a, rfl⟩, ⟨d, rfl⟩⟩
    have hneighbor : t.face k d = t.face k a + 1 ∨ t.face k a = t.face k d + 1 := by
      by_contra h
      exact hzfront.2 ((edge_interior _ _ hij hused z hzopen).mpr h)
    rcases hneighbor with h | h
    · exact Set.mem_iUnion.mpr ⟨t.face k a, h ▸ hzseg⟩
    · refine Set.mem_iUnion.mpr ⟨t.face k d, ?_⟩
      rw [← h, segment_symm]
      exact hzseg
  · exact Set.iUnion_subset polygon_frontier

private theorem affine_chart :
    ∀ (q : Fin (3 : ℕ) → ℝ × ℝ), P3381T1TriangleDeterminant q ≠ (0 : ℝ) →
    ∃ (h : ℝ × ℝ ≃ₜ ℝ × ℝ),
      (h : ℝ × ℝ → ℝ × ℝ) (0 : ℝ × ℝ) = q (0 : Fin (3 : ℕ)) ∧
        (h : ℝ × ℝ → ℝ × ℝ) ((1 : ℝ), (0 : ℝ)) = q (1 : Fin (3 : ℕ)) ∧
          (h : ℝ × ℝ → ℝ × ℝ) ((0 : ℝ), (1 : ℝ)) = q (2 : Fin (3 : ℕ)) ∧
            (∀ (z : ℝ × ℝ), (h : ℝ × ℝ → ℝ × ℝ) z =
                  q (0 : Fin (3 : ℕ)) + z.1 • (q (1 : Fin (3 : ℕ)) - q (0 : Fin (3 : ℕ))) +
                    z.2 • (q (2 : Fin (3 : ℕ)) - q (0 : Fin (3 : ℕ)))) ∧
              ∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (a : ℝ), ∀ (b : ℝ), a + b = (1 : ℝ) →
                  (h : ℝ × ℝ → ℝ × ℝ) (a • x + b • y) = a • (h : ℝ × ℝ → ℝ × ℝ) x + b • (h : ℝ ×
                      ℝ → ℝ × ℝ) y := by
  classical
  intro q hq
  let standard : Fin 3 → Real × Real := ![(0, 0), (1, 0), (0, 1)]
  have hstandard : P3381T1TriangleDeterminant standard ≠ 0 := by
    change ((1 : Real) - 0) * (1 - 0) - (0 - 0) * (0 - 0) ≠ 0
    norm_num
  obtain ⟨h, hh⟩ := P3381T1AffineTriangleMap standard q hstandard hq
  have hplace z : h z = q 0 + z.1 • (q 1 - q 0) + z.2 • (q 2 - q 0) := by
    let w : Fin 3 → Real := ![1 - z.1 - z.2, z.1, z.2]
    have hsum : (∑ j, w j) = 1 := by
      rw [Fin.sum_univ_three]
      change (1 - z.1 - z.2) + z.1 + z.2 = 1
      ring
    have hwz : (∑ j, w j • standard j) = z := by
      apply Prod.ext <;> simp [Fin.sum_univ_three, standard, w]
    rw [← hwz, hh w hsum, hwz]
    apply Prod.ext <;> simp [Fin.sum_univ_three, w] <;> ring
  refine ⟨h, ?_, ?_, ?_, hplace, ?_⟩
  · simp [hplace]
  · simp [hplace]
  · simp [hplace]
  · intro x y a b hab
    have hb : b = 1 - a := by linarith
    rw [hplace, hplace, hplace, hb]
    apply Prod.ext <;> simp <;> ring

private theorem polygon_chart :
    (∀ (q : Fin 3 → Real × Real), (P3381T1TriangleDeterminant q ≠ 0) → (∃ h : (Real × Real) ≃ₜ
        (Real × Real), h 0 = q 0 ∧ h (1, 0) = q 1 ∧ h (0, 1) = q 2 ∧ (∀ z : Real × Real, h z = q
        0 + z.1 • (q 1 - q 0) + z.2 • (q 2 - q 0)) ∧ (∀ (x : Real × Real), ∀ (y : Real × Real), ∀
            (a : Real), ∀ (b : Real), a + b = 1 → h (a • x + b • y) = a • h x + b • h y))) → (∀
            {n : ℕ}, ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + (3 : ℕ))), ∃ (h : ℝ × ℝ
            ≃ₜ ℝ
        × ℝ),
    (h : ℝ × ℝ → ℝ × ℝ) (0 : ℝ × ℝ) = p.vertex i ∧
      (h : ℝ × ℝ → ℝ × ℝ) ((1 : ℝ), (0 : ℝ)) = p.vertex (i + (1 : Fin (n + (3 : ℕ)))) ∧
        (∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (a : ℝ), ∀ (b : ℝ), a + b = (1 : ℝ) →
              (h : ℝ × ℝ → ℝ × ℝ) (a • x + b • y) = a • (h : ℝ × ℝ → ℝ × ℝ) x + b • (h : ℝ × ℝ →
                  ℝ × ℝ) y) ∧
          ((h : ℝ × ℝ → ℝ × ℝ) ((0 : ℝ), (1 : ℝ)) = p.vertex (i - (1 : Fin (n + (3 : ℕ)))) ∨
            ∃ c < (0 : ℝ), (h : ℝ × ℝ → ℝ × ℝ) (c, (0 : ℝ)) = p.vertex (i - (1 : Fin (n + (3 :
                ℕ)))))) := by
  classical
  intro affine_chart n p i
  classical
  have hnext : i ≠ i + 1 := by
    intro hi
    have hzero : (0 : Fin (n + 3)) = 1 :=
      add_left_cancel (show i + 0 = i + 1 by simpa only [add_zero] using hi)
    exact Fin.zero_ne_one hzero
  have hprev : (i - 1 : Fin (n + 3)) ≠ i := by
    intro hi
    have h : i = i + 1 := by
      simpa only [sub_add_cancel] using congrArg (fun j : Fin (n + 3) => j + 1) hi
    exact hnext h
  have hvnext : p.vertex (i + 1) ≠ p.vertex i := fun h => hnext (p.injective h).symm
  have hvprev : p.vertex (i - 1) ≠ p.vertex i := fun h => hprev (p.injective h)
  let q : Fin 3 → Real × Real := ![p.vertex i, p.vertex (i + 1), p.vertex (i - 1)]
  by_cases hq : P3381T1TriangleDeterminant q ≠ 0
  · obtain ⟨h, h0, h1, h2, hplace, haffine⟩ := affine_chart q hq
    exact ⟨h, h0, h1, haffine, Or.inl h2⟩
  · have hdet : P3381T1TriangleDeterminant q = 0 := not_ne_iff.mp hq
    let a : Real × Real := p.vertex (i + 1) - p.vertex i
    have ha : a ≠ 0 := sub_ne_zero.mpr hvnext
    let v : Real × Real := p.vertex i + (-a.2, a.1)
    let q' : Fin 3 → Real × Real := ![p.vertex i, p.vertex (i + 1), v]
    have hdet' : P3381T1TriangleDeterminant q' = a.1 ^ 2 + a.2 ^ 2 := by
      simp [P3381T1TriangleDeterminant, q', v, a]
      ring
    have hq' : P3381T1TriangleDeterminant q' ≠ 0 := by
      rw [hdet']
      intro h
      have ha1 : a.1 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
      have ha2 : a.2 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
      exact ha (Prod.ext ha1 ha2)
    obtain ⟨h, h0, h1, h2, hplace, haffine⟩ := affine_chart q' hq'
    change h 0 = p.vertex i at h0
    change h (1, 0) = p.vertex (i + 1) at h1
    let x : Real × Real := h.symm (p.vertex (i - 1))
    have hx : p.vertex (i - 1) = p.vertex i + x.1 • a + x.2 • (-a.2, a.1) := by
      have hp := hplace x
      rw [h.apply_symm_apply] at hp
      simpa [q', v, a] using hp
    have hx2 : x.2 = 0 := by
      have hx1' := congrArg Prod.fst hx
      have hx2' := congrArg Prod.snd hx
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hx1' hx2'
      have hcross : x.2 * (a.1 ^ 2 + a.2 ^ 2) = 0 := by
        have hd : a.1 * ((p.vertex (i - 1)).2 - (p.vertex i).2) -
            ((p.vertex (i - 1)).1 - (p.vertex i).1) * a.2 = 0 := by
          simpa [P3381T1TriangleDeterminant, q, a] using hdet
        linear_combination hd - a.1 * hx2' + a.2 * hx1'
      exact (mul_eq_zero.mp hcross).resolve_right (hdet' ▸ hq')
    have hxc : h (x.1, 0) = p.vertex (i - 1) := by
      have heq : (x.1, 0) = x := Prod.ext rfl hx2.symm
      rw [heq]
      exact h.apply_symm_apply _
    have hcx : x.1 ≠ 0 := by
      intro hc
      apply hvprev
      rw [← hxc, hc]
      exact h0
    have hcnegative : x.1 < 0 := by
      by_contra hnot
      have hcpos : 0 < x.1 := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hcx)
      let s : Real := min x.1 1 / 2
      have hspos : 0 < s := by dsimp [s]; exact div_pos (lt_min hcpos zero_lt_one) (by norm_num)
      have hs1 : s < 1 := by dsimp [s]; linarith [min_le_right x.1 (1 : Real)]
      have hsc : s < x.1 := by dsimp [s]; linarith [min_le_left x.1 (1 : Real)]
      have hratio : 0 ≤ s / x.1 ∧ s / x.1 ≤ 1 :=
        ⟨(div_pos hspos hcpos).le, (div_le_one hcpos).mpr hsc.le⟩
      have next_segment : h (s, 0) ∈ segment Real (p.vertex i) (p.vertex (i + 1)) := by
        rw [segment_eq_image]
        refine ⟨s, ⟨hspos.le, hs1.le⟩, ?_⟩
        change (1 - s) • p.vertex i + s • p.vertex (i + 1) = h (s, 0)
        rw [← h0, ← h1, ← haffine 0 (1, 0) (1 - s) s (by ring)]
        congr 1
        apply Prod.ext <;> simp
      have prev_segment : h (s, 0) ∈ segment Real (p.vertex (i - 1)) (p.vertex ((i - 1) + 1)) := by
        rw [sub_add_cancel, segment_symm, segment_eq_image]
        refine ⟨s / x.1, hratio, ?_⟩
        change (1 - s / x.1) • p.vertex i + (s / x.1) • p.vertex (i - 1) = h (s, 0)
        rw [← h0, ← hxc, ← haffine 0 (x.1, 0) (1 - s / x.1) (s / x.1) (by ring)]
        congr 1
        apply Prod.ext <;> simp [div_mul_cancel₀ s hcx]
      have hmeet := p.edge_intersection i (i - 1) (Ne.symm hprev)
      have hmem : h (s, 0) ∈ segment Real (p.vertex i) (p.vertex (i + 1)) ∩
          segment Real (p.vertex (i - 1)) (p.vertex ((i - 1) + 1)) :=
        ⟨next_segment, prev_segment⟩
      rw [hmeet] at hmem
      rcases hmem.1 with hzero | hone
      · have heq : (s, (0 : Real)) = 0 := h.injective (hzero.trans h0.symm)
        have heq1 := congrArg Prod.fst heq
        change s = 0 at heq1
        linarith
      · have heq : (s, (0 : Real)) = (1, 0) := h.injective (hone.trans h1.symm)
        have heq1 := congrArg Prod.fst heq
        change s = 1 at heq1
        linarith
    exact ⟨h, h0, h1, haffine, Or.inr ⟨x.1, hcnegative, hxc⟩⟩

private theorem local_boundary_chart :
    (∀ {n : Nat}, ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∃ h : (Real × Real) ≃ₜ
        (Real × Real), h 0 = p.vertex i ∧ h (1, 0) = p.vertex (i + 1) ∧ (∀ (x : Real × Real), ∀
            (y : Real × Real), ∀ (a : Real), ∀ (b : Real), a + b = 1 → h (a • x + b • y) = a • h x +
        b • h y) ∧ (h (0, 1) = p.vertex (i - 1) ∨ ∃ c : Real, c < 0 ∧ h (c, 0) = p.vertex (i -
        1))) → (∀ {n : ℕ}, ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (ℝ × ℝ)), frontier X =
        ⋃ (i : Fin (n + (3 : ℕ))), segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ))))) →
    ∀ (i : Fin (n + (3 : ℕ))), ∀ (eps : ℝ), (0 : ℝ) < eps →
        ∃ (r : ℝ) (h : ℝ × ℝ ≃ₜ ℝ × ℝ) (straight : Bool),
          (0 : ℝ) < r ∧
            r ≤ eps ∧
              (h : ℝ × ℝ → ℝ × ℝ) (0 : ℝ × ℝ) = p.vertex i ∧
                (∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (a : ℝ), ∀ (b : ℝ), a + b = (1 : ℝ) →
                      (h : ℝ × ℝ → ℝ × ℝ) (a • x + b • y) = a • (h : ℝ × ℝ → ℝ × ℝ) x + b • (h :
                          ℝ × ℝ → ℝ × ℝ) y) ∧
                  ∀ z ∈ Metric.ball (p.vertex i) r,
                    z ∈ frontier X ↔
                      z ∈
                        (⇑h : ℝ × ℝ → ℝ × ℝ) ''
                          if straight = true then {x : ℝ × ℝ | x.2 = (0 : ℝ)}
                          else {x : ℝ × ℝ | (0 : ℝ) ≤ x.1 ∧ x.2 = (0 : ℝ) ∨ x.1 = (0 : ℝ) ∧ (0 :
                              ℝ) ≤ x.2}) := by
  classical
  intro polygon_chart n p X hb i eps heps
  classical
  obtain ⟨h, h0, h1, haffine, hprev⟩ := polygon_chart p i
  let F j := segment Real (p.vertex j) (p.vertex (j + 1))
  let N : Set (Real × Real) := ⋂ j,
    if j = i ∨ j + 1 = i then Set.univ else (F j)ᶜ
  have closed_F j : IsClosed (F j) := by
    dsimp [F]
    rw [← convexHull_pair]
    exact (((Set.finite_singleton (p.vertex (j + 1))).insert (p.vertex j)).isCompact_convexHull
        Real).isClosed
  have open_N : IsOpen N := by
    apply isOpen_iInter_of_finite
    intro j
    split_ifs
    · exact isOpen_univ
    · exact (closed_F j).isOpen_compl
  have mem_N : p.vertex i ∈ N := by
    apply Set.mem_iInter.mpr
    intro j
    split_ifs with hj
    · trivial
    · intro hvj
      have hji : j ≠ i := fun heq => hj (Or.inl heq)
      have hmeet := p.edge_intersection j i hji
      have hvmeet : p.vertex i ∈ F j ∩ F i :=
        ⟨hvj, left_mem_segment Real _ _⟩
      rw [hmeet] at hvmeet
      rcases hvmeet.1 with hv | hv
      · exact hj (Or.inl (p.injective hv).symm)
      · exact hj (Or.inr (p.injective hv).symm)
  have boundary_local z (hz : z ∈ N) :
      z ∈ frontier X ↔ z ∈ segment Real (p.vertex i) (p.vertex (i + 1)) ∨
        z ∈ segment Real (p.vertex i) (p.vertex (i - 1)) := by
    constructor
    · intro hzb
      rw [hb] at hzb
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzb
      by_cases hj : j = i ∨ j + 1 = i
      · rcases hj with rfl | hj
        · exact Or.inl hzj
        · have hj' : j = i - 1 := (eq_sub_iff_add_eq).mpr hj
          right
          subst j
          simpa only [sub_add_cancel, segment_symm] using hzj
      · have hnot := Set.mem_iInter.mp hz j
        simp only [hj, ite_false] at hnot
        exact (hnot hzj).elim
    · rintro (hz | hz)
      · rw [hb]
        exact Set.mem_iUnion.mpr ⟨i, hz⟩
      · rw [hb]
        refine Set.mem_iUnion.mpr ⟨i - 1, ?_⟩
        simpa only [sub_add_cancel, segment_symm] using hz
  have image_segment (x y : Real × Real) :
      h '' segment Real x y = segment Real (h x) (h y) := by
    calc
      h '' segment Real x y =
          (fun u : Real => h ((1 - u) • x + u • y)) '' Set.Icc 0 1 := by
        rw [segment_eq_image, Set.image_image]
      _ = (fun u : Real => (1 - u) • h x + u • h y) '' Set.Icc 0 1 := by
        congr 1
        funext u
        exact haffine x y (1 - u) u (by ring)
      _ = segment Real (h x) (h y) := (segment_eq_image Real _ _).symm
  have axis1 (x : Real × Real) : x ∈ segment Real 0 (1, 0) ↔
      0 ≤ x.1 ∧ x.1 ≤ 1 ∧ x.2 = 0 := by
    rw [segment_eq_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using And.intro hu.1 (And.intro hu.2 (rfl : (0 : Real) = 0))
    · rintro ⟨hx0, hx1, hx2⟩
      refine ⟨x.1, ⟨hx0, hx1⟩, ?_⟩
      apply Prod.ext <;> simp [hx2]
  have radius (O : Set (Real × Real)) (hO : IsOpen O) (hv : p.vertex i ∈ O) :
      ∃ r : Real, 0 < r ∧ r ≤ eps ∧ Metric.ball (p.vertex i) r ⊆ O := by
    obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hO _ hv
    refine ⟨min rho eps, lt_min hrho heps, min_le_right _ _, ?_⟩
    intro z hz
    exact hball (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _)))
  rcases hprev with h2 | ⟨c, hc, h2⟩
  · let O : Set (Real × Real) := N ∩
      {z | (h.symm z).1 < 1 ∧ (h.symm z).2 < 1}
    have hO : IsOpen O := open_N.inter
      ((isOpen_lt (continuous_fst.comp h.symm.continuous) continuous_const).inter
        (isOpen_lt (continuous_snd.comp h.symm.continuous) continuous_const))
    have hvO : p.vertex i ∈ O := by
      refine ⟨mem_N, ?_⟩
      change (h.symm (p.vertex i)).1 < 1 ∧ (h.symm (p.vertex i)).2 < 1
      rw [← h0, h.symm_apply_apply]
      norm_num
    obtain ⟨r, hr, hreps, hball⟩ := radius O hO hvO
    refine ⟨r, h, false, hr, hreps, h0, haffine, ?_⟩
    intro z hz
    have hzO := hball hz
    let x : Real × Real := h.symm z
    have hzx : z = h x := (h.apply_symm_apply z).symm
    have hx1 : x.1 < 1 := hzO.2.1
    have hx2 : x.2 < 1 := hzO.2.2
    have axis2 : x ∈ segment Real 0 (0, 1) ↔
        0 ≤ x.2 ∧ x.2 ≤ 1 ∧ x.1 = 0 := by
      rw [segment_eq_image]
      constructor
      · rintro ⟨u, hu, heq⟩
        rw [← heq]
        simpa using And.intro hu.1 (And.intro hu.2 (rfl : (0 : Real) = 0))
      · rintro ⟨hx0, hx1, hx2⟩
        refine ⟨x.2, ⟨hx0, hx1⟩, ?_⟩
        apply Prod.ext <;> simp [hx2]
    rw [boundary_local z hzO.1, hzx, ← h0, ← h1, ← h2,
      ← image_segment, ← image_segment]
    simp only [Bool.false_eq_true, ite_false, h.injective.mem_set_image,
      Set.mem_ofPred_eq, axis1, axis2]
    constructor
    · rintro (⟨hxa, hxb, hxc⟩ | ⟨hxa, hxb, hxc⟩)
      · exact Or.inl ⟨hxa, hxc⟩
      · exact Or.inr ⟨hxc, hxa⟩
    · rintro (⟨hxa, hxb⟩ | ⟨hxa, hxb⟩)
      · exact Or.inl ⟨hxa, hx1.le, hxb⟩
      · exact Or.inr ⟨hxb, hx2.le, hxa⟩
  · let O : Set (Real × Real) := N ∩ {z | c < (h.symm z).1 ∧ (h.symm z).1 < 1}
    have hO : IsOpen O := open_N.inter
      ((isOpen_lt continuous_const (continuous_fst.comp h.symm.continuous)).inter
        (isOpen_lt (continuous_fst.comp h.symm.continuous) continuous_const))
    have hvO : p.vertex i ∈ O := by
      refine ⟨mem_N, ?_⟩
      change c < (h.symm (p.vertex i)).1 ∧ (h.symm (p.vertex i)).1 < 1
      rw [← h0, h.symm_apply_apply]
      exact ⟨hc, by norm_num⟩
    obtain ⟨r, hr, hreps, hball⟩ := radius O hO hvO
    refine ⟨r, h, true, hr, hreps, h0, haffine, ?_⟩
    intro z hz
    have hzO := hball hz
    let x : Real × Real := h.symm z
    have hzx : z = h x := (h.apply_symm_apply z).symm
    have hcx : c < x.1 := hzO.2.1
    have hx1 : x.1 < 1 := hzO.2.2
    have axisc : x ∈ segment Real 0 (c, 0) ↔ c ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 0 := by
      rw [segment_eq_image]
      constructor
      · rintro ⟨u, hu, heq⟩
        rw [← heq]
        simp only [smul_zero, zero_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zero]
        exact ⟨by nlinarith [hu.2], mul_nonpos_of_nonneg_of_nonpos hu.1 hc.le, trivial⟩
      · rintro ⟨hcx, hx0, hx2⟩
        refine ⟨x.1 / c, ⟨div_nonneg_of_nonpos hx0 hc.le,
          (div_le_one_of_neg hc).mpr hcx⟩, ?_⟩
        apply Prod.ext <;> simp [hx2, div_mul_cancel₀ _ hc.ne]
    rw [boundary_local z hzO.1, hzx, ← h0, ← h1, ← h2,
      ← image_segment, ← image_segment]
    simp only [ite_true, h.injective.mem_set_image, Set.mem_ofPred_eq, axis1, axisc]
    constructor
    · rintro (⟨hxa, hxb, hxc⟩ | ⟨hxa, hxb, hxc⟩) <;> exact hxc
    · intro hxzero
      by_cases hx0 : 0 ≤ x.1
      · exact Or.inl ⟨hx0, hx1.le, hxzero⟩
      · exact Or.inr ⟨hcx.le, (lt_of_not_ge hx0).le, hxzero⟩

private theorem split_sets :
    ∀ {A : Set (ℝ × ℝ)}, ∀ {B : Set (ℝ × ℝ)}, ∀ {S : Set (ℝ × ℝ)}, ∀ {T : Set (ℝ × ℝ)}, IsOpen A →
    IsOpen B →
      Disjoint A B →
        IsPathConnected S →
          IsPathConnected T → S ∪ T = A ∪ B → A.Nonempty → B.Nonempty → IsPathConnected A ∧
              IsPathConnected B := by
  classical
  intro A B S T hA hB hAB hS hT hcover hneA hneB
  have hscover : S ⊆ A ∪ B := by rw [← hcover]; exact Set.subset_union_left
  have htcover : T ⊆ A ∪ B := by rw [← hcover]; exact Set.subset_union_right
  have hs := hS.isConnected.isPreconnected.subset_or_subset hA hB hAB hscover
  have ht := hT.isConnected.isPreconnected.subset_or_subset hA hB hAB htcover
  have eqs (hSA : S ⊆ A) (hTB : T ⊆ B) : S = A ∧ T = B := by
    constructor
    · apply Set.Subset.antisymm hSA
      intro x hx
      have hx' : x ∈ S ∪ T := by rw [hcover]; exact Or.inl hx
      rcases hx' with hxS | hxT
      · exact hxS
      · exact (Set.disjoint_left.mp hAB hx (hTB hxT)).elim
    · apply Set.Subset.antisymm hTB
      intro x hx
      have hx' : x ∈ S ∪ T := by rw [hcover]; exact Or.inr hx
      rcases hx' with hxS | hxT
      · exact (Set.disjoint_left.mp hAB (hSA hxS) hx).elim
      · exact hxT
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · obtain ⟨x, hx⟩ := hneB
    have hx' : x ∈ S ∪ T := by rw [hcover]; exact Or.inr hx
    rcases hx' with hxS | hxT
    · exact (Set.disjoint_left.mp hAB (hs hxS) hx).elim
    · exact (Set.disjoint_left.mp hAB (ht hxT) hx).elim
  · obtain ⟨rfl, rfl⟩ := eqs hs ht
    exact ⟨hS, hT⟩
  · have hSA : T ⊆ A := ht
    have hTB : S ⊆ B := hs
    have hcover' : T ∪ S = A ∪ B := by rw [Set.union_comm]; exact hcover
    have eqA : T = A := by
      apply Set.Subset.antisymm hSA
      intro x hx
      have hx' : x ∈ T ∪ S := by rw [hcover']; exact Or.inl hx
      rcases hx' with hxT | hxS
      · exact hxT
      · exact (Set.disjoint_left.mp hAB hx (hTB hxS)).elim
    have eqB : S = B := by
      apply Set.Subset.antisymm hTB
      intro x hx
      have hx' : x ∈ T ∪ S := by rw [hcover']; exact Or.inr hx
      rcases hx' with hxT | hxS
      · exact (Set.disjoint_left.mp hAB (hSA hxT) hx).elim
      · exact hxS
    exact ⟨eqA ▸ hT, eqB ▸ hS⟩
  · obtain ⟨x, hx⟩ := hneA
    have hx' : x ∈ S ∪ T := by rw [hcover]; exact Or.inl hx
    rcases hx' with hxS | hxT
    · exact (Set.disjoint_left.mp hAB hx (hs hxS)).elim
    · exact (Set.disjoint_left.mp hAB hx (ht hxT)).elim

private theorem affine_sectors :
    ∀ (h : (Real × Real) ≃ₜ (Real × Real)), (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (a :
        Real), ∀ (b : Real), a + b = 1 →
        h (a • x + b • y) = a • h x + b • h y) → (∀ (r : Real), (0 < r) → (∀ (straight : Bool),
    let R : Set (Real × Real) := if straight then {x | x.2 = 0}
        else {x | (0 ≤ x.1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ 0 ≤ x.2)}
      ∃ S T : Set (Real × Real), IsPathConnected S ∧ IsPathConnected T ∧
        Disjoint S T ∧ S ∪ T = Metric.ball (h 0) r \ h '' R)) := by
  classical
  intro h haffine r hr straight
  classical
  intro R
  let C : Set (Real × Real) := h ⁻¹' Metric.ball (h 0) r
  have hCconvex : Convex Real C := by
    intro x hx y hy a b ha hb hab
    change h (a • x + b • y) ∈ Metric.ball (h 0) r
    rw [haffine x y a b hab]
    exact (convex_ball (h 0) r) hx hy ha hb hab
  have hCopen : IsOpen C := Metric.isOpen_ball.preimage h.continuous
  have hCzero : (0 : Real × Real) ∈ C := by
    change h 0 ∈ Metric.ball (h 0) r
    exact Metric.mem_ball_self hr
  obtain ⟨d, hd, hdC⟩ := Metric.isOpen_iff.mp hCopen 0 hCzero
  have hpC : (d / 2, d / 2) ∈ C := by
    apply hdC
    simp only [Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
      Real.dist_eq, sub_zero, max_self]
    rw [abs_of_pos (by linarith : 0 < d / 2)]
    linarith
  have hnC : (-d / 2, -d / 2) ∈ C := by
    apply hdC
    simp only [Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
      Real.dist_eq, sub_zero, max_self]
    rw [abs_of_neg (by linarith : -d / 2 < 0)]
    linarith
  let Q : Set (Real × Real) := if straight then Set.univ ×ˢ Set.Ioi (0 : Real)
    else Set.Ioi (0 : Real) ×ˢ Set.Ioi (0 : Real)
  let E : Set (Real × Real) := if straight then Set.univ ×ˢ Set.Iio (0 : Real)
    else (Set.Iio (0 : Real) ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Iio (0 : Real))
  have hCQ : IsPathConnected (C ∩ Q) := by
    apply Convex.isPathConnected
    · apply hCconvex.inter
      cases straight
      · exact (convex_Ioi (0 : Real)).prod (convex_Ioi (0 : Real))
      · exact convex_univ.prod (convex_Ioi (0 : Real))
    · refine ⟨(d / 2, d / 2), hpC, ?_⟩
      cases straight <;> simp [Q, show 0 < d / 2 by linarith]
  have hCE : IsPathConnected (C ∩ E) := by
    cases straight
    · have h1 : IsPathConnected (C ∩ (Set.Iio (0 : Real) ×ˢ Set.univ)) := by
        apply (hCconvex.inter ((convex_Iio (0 : Real)).prod convex_univ)).isPathConnected
        exact ⟨(-d / 2, -d / 2), hnC, by simp; linarith⟩
      have h2 : IsPathConnected (C ∩ (Set.univ ×ˢ Set.Iio (0 : Real))) := by
        apply (hCconvex.inter (convex_univ.prod (convex_Iio (0 : Real)))).isPathConnected
        exact ⟨(-d / 2, -d / 2), hnC, by simp; linarith⟩
      have heq : C ∩ E = (C ∩ (Set.Iio (0 : Real) ×ˢ Set.univ)) ∪
          (C ∩ (Set.univ ×ˢ Set.Iio (0 : Real))) := by
        dsimp [E]
        exact Set.inter_union_distrib_left _ _ _
      rw [heq]
      exact h1.union h2 ⟨(-d / 2, -d / 2), ⟨hnC, by simp; linarith⟩,
        ⟨hnC, by simp; linarith⟩⟩
    · apply (hCconvex.inter (convex_univ.prod (convex_Iio (0 : Real)))).isPathConnected
      exact ⟨(-d / 2, -d / 2), hnC, by simp []; linarith⟩
  have hcomplement x : x ∉ R ↔ x ∈ Q ∨ x ∈ E := by
    cases straight <;>
      simp only [R, Q, E, Bool.false_eq_true, ite_false, ite_true, Set.mem_ofPred_eq,
        Set.mem_prod, Set.mem_univ, Set.mem_Iio, Set.mem_Ioi, Set.mem_union,
        true_and, and_true]
    · change ¬ ((0 ≤ x.1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ 0 ≤ x.2)) ↔
        (0 < x.1 ∧ 0 < x.2) ∨ (x.1 < 0 ∨ x.2 < 0)
      constructor
      · intro hx
        by_cases h1 : x.1 < 0
        · exact Or.inr (Or.inl h1)
        by_cases h2 : x.2 < 0
        · exact Or.inr (Or.inr h2)
        left
        constructor
        · have hne : x.1 ≠ 0 := by intro h; exact hx (Or.inr ⟨h, le_of_not_gt h2⟩)
          exact lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm hne)
        · have hne : x.2 ≠ 0 := by intro h; exact hx (Or.inl ⟨le_of_not_gt h1, h⟩)
          exact lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm hne)
      · intro hx hR
        rcases hx with hx | hx
        · rcases hR with hR | hR <;> linarith
        · rcases hx with hx | hx <;> rcases hR with hR | hR <;> linarith
    · change x.2 ≠ 0 ↔ 0 < x.2 ∨ x.2 < 0
      exact ne_iff_lt_or_gt.trans or_comm
  have hQE : Disjoint Q E := by
    apply Set.disjoint_left.mpr
    intro x hxQ hxE
    cases straight <;>
      simp only [Q, E, Bool.false_eq_true, ite_false, ite_true, Set.mem_prod,
        Set.mem_univ, Set.mem_Iio, Set.mem_Ioi, Set.mem_union, true_and, and_true] at hxQ hxE
    · change 0 < x.1 ∧ 0 < x.2 at hxQ
      change x.1 < 0 ∨ x.2 < 0 at hxE
      rcases hxE with hxE | hxE <;> linarith [hxQ.1, hxQ.2]
    · change 0 < x.2 at hxQ
      change x.2 < 0 at hxE
      linarith
  refine ⟨h '' (C ∩ Q), h '' (C ∩ E), hCQ.image h.continuous,
    hCE.image h.continuous, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
    have hzx' : z = x := h.injective hzx
    subst z
    exact Set.disjoint_left.mp hQE hx.2 hz.2
  · ext y
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      all_goals refine ⟨hx.1, ?_⟩
      all_goals rintro ⟨z, hz, heq⟩
      all_goals have hzx : z = x := h.injective heq
      all_goals subst z
      · exact (hcomplement x).mpr (Or.inl hx.2) hz
      · exact (hcomplement x).mpr (Or.inr hx.2) hz
    · rintro ⟨hyB, hyR⟩
      have hxC : h.symm y ∈ C := by
        change h (h.symm y) ∈ Metric.ball (h 0) r
        simpa using hyB
      have hxR : h.symm y ∉ R := by
        intro hx
        exact hyR ⟨h.symm y, hx, h.apply_symm_apply y⟩
      rcases (hcomplement _).mp hxR with hxQ | hxE
      · exact Or.inl ⟨h.symm y, ⟨hxC, hxQ⟩, h.apply_symm_apply y⟩
      · exact Or.inr ⟨h.symm y, ⟨hxC, hxE⟩, h.apply_symm_apply y⟩

private theorem vertex_in_closure :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), (∃ (b : Fin t.count → ℝ × ℝ → Fin
        (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j = (1 : ℝ))
        ∧ (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j • p.vertex (t.face k j)
        = z) ∧ (∀ (k : Fin t.count), ∀ (w : Fin (3 : ℕ) → ℝ), ∑ j : Fin (3 : ℕ), w j = (1 : ℝ) →
        b k (∑ j : Fin (3 : ℕ), w j • p.vertex (t.face k j)) = w) ∧ (∀ (k : Fin t.count), ∀ (j :
            Fin (3 : ℕ)), Continuous fun (z : ℝ × ℝ) => b k z j) ∧ (∀ (k : Fin t.count), ∀ (z : ℝ ×
        ℝ), z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range (p.vertex ∘ t.face k)) ↔ ∀
            (j : Fin (3 : ℕ)), (0 : ℝ) ≤ b k z j) ∧ (∀ (k : Fin t.count), ∀ (i : Fin (3 : ℕ)), b k
        (p.vertex (t.face k i)) = Pi.single i (1 : ℝ)) ∧ ∀ (k : Fin t.count), ∀ (l : Fin
        t.count), ∀ z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (p.vertex '' (Set.range
        (t.face k) ∩ Set.range (t.face l))), ∀ (j : Fin (3 : ℕ)), t.face k j ∉ Set.range (t.face
        l) → b k z j = (0 : ℝ)) → (∀ i, p.vertex i ∈ closure (interior X)) := by
  classical
  intro n p X K t coordinates
  obtain ⟨b, bsum, breconstruct, bunique, bcontinuous, bhull, bvertex, bcommon⟩ :=
    coordinates
  let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
  have closed_D k : IsClosed (D k) :=
    ((Set.finite_range (p.vertex ∘ t.face k)).isCompact_convexHull Real).isClosed
  have interior_D k : (interior (D k)).Nonempty := by
    let w : Fin 3 → Real := fun _ => 1 / 3
    have hw : (∑ j, w j) = 1 := by norm_num [Fin.sum_univ_three, w]
    let z := ∑ j, w j • p.vertex (t.face k j)
    have hz : ∀ j, 0 < b k z j := by
      intro j
      change 0 < b k (∑ j, w j • p.vertex (t.face k j)) j
      rw [bunique k w hw]
      norm_num [w]
    have hopen : IsOpen {y : Real × Real | ∀ j, 0 < b k y j} := by
      have heq : {y : Real × Real | ∀ j, 0 < b k y j} =
          ⋂ j, {y : Real × Real | 0 < b k y j} := by ext; simp
      rw [heq]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (bcontinuous k j)
    have hsub : {y : Real × Real | ∀ j, 0 < b k y j} ⊆ D k := by
      intro y hy
      exact (bhull k y).mpr (fun j => (hy j).le)
    exact ⟨z, (hopen.subset_interior_iff.mpr hsub) hz⟩
  have D_subset k : D k ⊆ X := by
    intro z hz
    rw [t.source_cover]
    exact Set.mem_iUnion.mpr ⟨k, hz⟩
  intro i
  obtain ⟨k, j, hkj⟩ := t.vertex_used i
  have hvD : p.vertex i ∈ D k := by
    exact subset_convexHull Real _ ⟨j, congrArg p.vertex hkj⟩
  have hvclosure : p.vertex i ∈ closure (interior (D k)) := by
    rw [(convex_convexHull Real _).closure_interior_eq_closure_of_nonempty_interior
      (interior_D k), (closed_D k).closure_eq]
    exact hvD
  exact closure_mono (interior_mono (D_subset k)) hvclosure

private theorem hcoverUV :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), (IsCompact X) → (
    ∀ (i : Fin (n + (3 : ℕ))), ∀ (r : ℝ),
    let U := Metric.ball (p.vertex i) r ∩ interior X
    ∀ (h : ℝ × ℝ ≃ₜ ℝ × ℝ), ∀ (straight : Bool), (∀ z ∈ Metric.ball (p.vertex i) r, z ∈ frontier
        X ↔ z ∈ (⇑h : ℝ × ℝ → ℝ × ℝ) '' if straight = true then {x : ℝ × ℝ | x.2 = (0 : ℝ)} else
        {x : ℝ × ℝ | (0 : ℝ) ≤ x.1 ∧ x.2 = (0 : ℝ) ∨ x.1 = (0 : ℝ) ∧ (0 : ℝ) ≤ x.2}) → (
    let R : Set (Real × Real) := if straight then {x | x.2 = 0}
      else {x | (0 ≤ x.1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ 0 ≤ x.2)}
    ∀ (S : Set (ℝ × ℝ)), ∀ (T : Set (ℝ × ℝ)), (S ∪ T = Metric.ball (p.vertex i) r \ (⇑h : ℝ × ℝ →
        ℝ × ℝ) '' R) → (
    let V := Metric.ball (p.vertex i) r \ X
    S ∪ T = U ∪ V))) := by
  classical
  intro n p X hcompact i r U h straight hboundary R S T hcover V
  rw [hcover]
  ext z
  constructor
  · rintro ⟨hzball, hzR⟩
    have hznot : z ∉ frontier X := by
      intro hz
      exact hzR ((hboundary z hzball).mp hz)
    by_cases hzX : z ∈ X
    · exact Or.inl ⟨hzball, (mem_interior_iff_notMem_frontier hzX).mpr hznot⟩
    · exact Or.inr ⟨hzball, hzX⟩
  · rintro (⟨hzball, hzint⟩ | ⟨hzball, hznotX⟩)
    · refine ⟨hzball, ?_⟩
      intro hzR
      have hzfront := (hboundary z hzball).mpr hzR
      exact hzfront.2 hzint
    · refine ⟨hzball, ?_⟩
      intro hzR
      have hzfront := (hboundary z hzball).mpr hzR
      exact hznotX (hcompact.isClosed.frontier_subset hzfront)

end TriangulationBoundaryProof

namespace TriangulationInteriorSides

private theorem hUne :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (i : Fin (n +
        (3 : ℕ))), ∀ (r : ℝ),
    let U := Metric.ball (p.vertex i) r ∩ interior X
    (∀ (i : Fin (n + (3 : ℕ))), p.vertex i ∈ closure (interior X)) → (((0 : ℝ) < r) →
        (U.Nonempty)) := by
  classical
  intro n p X i r U vertex_in_closure hr
  exact mem_closure_iff.mp (vertex_in_closure i)
    (Metric.ball (p.vertex i) r) Metric.isOpen_ball (Metric.mem_ball_self hr)

private theorem hVne :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (i : Fin (n +
        (3 : ℕ))), ∀ (r : ℝ), ((0 : ℝ) < r) → (
    let V := Metric.ball (p.vertex i) r \ X
    (p.vertex i ∈ frontier X) → (V.Nonempty)) := by
  classical
  intro n p X i r hr V hvfrontier
  rw [frontier_eq_closure_inter_closure] at hvfrontier
  exact mem_closure_iff.mp hvfrontier.2 (Metric.ball (p.vertex i) r)
    Metric.isOpen_ball (Metric.mem_ball_self hr)

end TriangulationInteriorSides

namespace TriangulationInteriorChart

private theorem hinterior :
    ∀ (X : Set (Real × Real)), ∀ (A : ℝ × ℝ ≃ₜ ℝ × ℝ),
    let U : Set (Real × Real) :=
      Set.Ioo (0 : Real) (1 / 4) ×ˢ Set.Ioo (0 : Real) (1 / 4)
    (have U := Set.Ioo (0 : ℝ) (1 / 4 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (1 / 4 : ℝ); (⇑A : ℝ × ℝ → ℝ × ℝ)
        '' U ⊆ X) → ((IsOpen (A '' U)) → ((interior X).Nonempty)) := by
  classical
  intro X A U hsub hAU
  refine ⟨A (1 / 8, 1 / 8), (hAU.subset_interior_iff.mpr hsub) ?_⟩
  exact Set.mem_image_of_mem A (by norm_num [U])

end TriangulationInteriorChart

theorem P3381T1TriangulationBoundary {n : Nat}
    (p : P3381T1PolygonBoundary n) (X K : Set (Real × Real))
    (t : P3381T1PairedTriangulation p X K) :
    IsCompact X ∧ (interior X).Nonempty ∧
      (frontier X = ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))) ∧
      ∀ i, ∃ r : Real, 0 < r ∧
        (∀ z ∈ Metric.ball (p.vertex i) r,
          z ∈ X ↔ ∃ k, i ∈ Set.range (t.face k) ∧
            ∃ w : Fin 3 → Real, (∀ j, 0 ≤ w j) ∧
              z = p.vertex i + ∑ j, w j • (p.vertex (t.face k j) - p.vertex i)) ∧
        IsPathConnected (Metric.ball (p.vertex i) r ∩ interior X) ∧
        IsPathConnected (Metric.ball (p.vertex i) r \ X) := by
-- BODY
  have hcompact : IsCompact X := by
    rw [t.source_cover]
    exact isCompact_iUnion fun k =>
      (Set.finite_range (p.vertex ∘ t.face k)).isCompact_convexHull Real
  obtain ⟨k, _j, _hkj⟩ := t.vertex_used (0 : Fin (n + 3))
  let standard : Fin 3 → Real × Real := ![(0, 0), (1, 0), (0, 1)]
  have hstandard : P3381T1TriangleDeterminant standard ≠ 0 := by
    change ((1 : Real) - 0) * (1 - 0) - (0 - 0) * (0 - 0) ≠ 0
    norm_num
  obtain ⟨A, hA⟩ := P3381T1AffineTriangleMap standard (p.vertex ∘ t.face k)
    hstandard (t.source_nondegenerate k)
  let U : Set (Real × Real) :=
    Set.Ioo (0 : Real) (1 / 4) ×ˢ Set.Ioo (0 : Real) (1 / 4)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hsub := TriangulationBoundaryProof.hsubAt142 n p X K t k A hA
  have hAU : IsOpen (A '' U) := A.isOpenMap U hU
  have hinterior : (interior X).Nonempty := TriangulationInteriorChart.hinterior X A hsub hAU
  -- Barycentric coordinates record both triangle inequalities and exact face support.
  obtain ⟨coordinates, vertex_incidence⟩ :=
    P5662T1TriangulationBarycentricCoordinates p X K t
  -- Avoid nonincident triangles and keep the opposite-face coordinate positive.
  have local_cones := TriangulationBoundaryProof.local_cones n p X K t coordinates vertex_incidence
  -- The edge ledger selects one triangle or two triangles on opposite sides.
  have edge_interior :
      ∀ i j, i ≠ j → (∃ k, i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)) →
        ∀ z ∈ openSegment Real (p.vertex i) (p.vertex j),
          (z ∈ interior X ↔ ¬ (j = i + 1 ∨ i = j + 1)) := by
    classical
    obtain ⟨b, bsum, breconstruct, bunique, bcontinuous, bhull, bvertex, bcommon⟩ :=
      coordinates
    let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
    have closed_D k : IsClosed (D k) :=
      ((Set.finite_range (p.vertex ∘ t.face k)).isCompact_convexHull Real).isClosed
    have third (a b : Fin 3) (hab : a ≠ b) : ∃ c, a ≠ c ∧ b ≠ c := by
      fin_cases a <;> fin_cases b
      all_goals first | exact (hab rfl).elim | decide
    have sum_three {E : Type} [AddCommMonoid E] (f : Fin 3 → E)
        (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
        (∑ j, f j) = f a + f b + f c := by
      fin_cases a <;> fin_cases b <;> fin_cases c
      all_goals first
        | exact (hab rfl).elim
        | exact (hac rfl).elim
        | exact (hbc rfl).elim
        | (rw [Fin.sum_univ_three]; ac_rfl)
    have indices (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) j :
        j = a ∨ j = b ∨ j = c := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases j
      all_goals first
        | exact (hab rfl).elim
        | exact (hac rfl).elim
        | exact (hbc rfl).elim
        | decide
    have bcombo {ι : Type} [Fintype ι] k (a : ι → Real) (f : ι → Real × Real)
        (ha : (∑ r, a r) = 1) j := TriangulationBoundaryProof.bcombo n p
            X K t b bsum breconstruct bunique (ι := ι) k a f ha j
    have blinear k (x y : Real × Real) (a c : Real) (hac : a + c = 1) j :
        b k (a • x + c • y) j = a * b k x j + c * b k y j := by
      let w : Fin 2 → Real := ![a, c]
      let f : Fin 2 → Real × Real := ![x, y]
      have hw : (∑ r, w r) = 1 := by simpa [Fin.sum_univ_two, w] using hac
      simpa [Fin.sum_univ_two, w, f] using bcombo k w f hw j
    have hfaces_subset k l (h : Set.range (t.face k) ⊆ Set.range (t.face l)) : k = l := by
      apply t.face_distinct
      apply Set.eq_of_subset_of_ncard_le h
      rw [Set.ncard_range_of_injective (t.face_injective k),
        Set.ncard_range_of_injective (t.face_injective l)]
    have hdisjoint k l (hkl : k ≠ l) z
        (hz : ∀ j, 0 < b k z j) (hzl : z ∈ D l) := TriangulationBoundaryProof.hdisjoint n
            p X K t b bhull bcommon hfaces_subset k l hkl z hz hzl
    have perturb (O : Set (Real × Real)) (hO : IsOpen O) z (hz : z ∈ O) v :
        ∃ u : Real, 0 < u ∧ u < 1 ∧ (1 - u) • z + u • v ∈ O := by
      have hzc : z ∈ closure (openSegment Real z v) :=
        segment_subset_closure_openSegment (left_mem_segment Real z v)
      obtain ⟨y, hyO, hyseg⟩ := mem_closure_iff.mp hzc O hO hz
      rw [openSegment_eq_image] at hyseg
      obtain ⟨u, hu, rfl⟩ := hyseg
      exact ⟨u, hu.1, hu.2, hyO⟩
    intro i j hij hused z hz
    rw [openSegment_eq_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex j
    let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)}
    have edge_coords k (hk : k ∈ I) := TriangulationBoundaryProof.edge_coords n p
            X K t b bvertex third blinear i j hij u k hk
    have mem_D k (hk : k ∈ I) := TriangulationBoundaryProof.mem_D n p X K t i j u hu k hk
    have containing k (hk : z ∈ D k) := TriangulationBoundaryProof.containing n p X K t b
        bcommon i j hused u hu edge_coords mem_D k hk
    have opposite k l (hkl : k ≠ l) (hk : k ∈ I) (hl : l ∈ I)
        a d c e f g (hka : t.face k a = i) (hkd : t.face k d = j)
        (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c)
        (hle : t.face l e = i) (hlf : t.face l f = j)
        (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
        (hza : b k z a = 1 - u) (hzd : b k z d = u) (hzc : b k z c = 0)
        (hze : b l z e = 1 - u) (hzf : b l z f = u) (hzg : b l z g = 0) :=
            TriangulationBoundaryProof.opposite n p X K t b
            bcontinuous bhull bvertex indices blinear hdisjoint perturb i j u hu k l hkl hk hl a
            d c e f g hka hkd had hac hdc hle hlf hef heg hfg hza hzd hzc hze hzf hzg
    have hcard := t.edge_count i j hij
    change I.ncard = _ at hcard
    by_cases hneighbor : j = i + 1 ∨ i = j + 1
    · simp only [hneighbor, ite_true] at hcard
      obtain ⟨k, hI⟩ := Set.ncard_eq_one.mp hcard
      have hk : k ∈ I := by rw [hI]; simp
      obtain ⟨a, d, c, hka, hkd, had, hac, hdc, hza, hzd, hzc⟩ := edge_coords k hk
      have hnot := TriangulationBoundaryProof.hnotAt427 n p X K t k b bhull
          bvertex closed_D blinear perturb i j u containing hI hk a c hac hzc
      simp only [hneighbor, not_true_eq_false, iff_false]
      exact hnot
    · simp only [hneighbor, ite_false, hused, ite_true] at hcard
      obtain ⟨k, l, hkl, hI⟩ := Set.ncard_eq_two.mp hcard
      have hk : k ∈ I := by rw [hI]; simp
      have hl : l ∈ I := by rw [hI]; simp
      obtain ⟨a, d, c, hka, hkd, had, hac, hdc, hza, hzd, hzc⟩ := edge_coords k hk
      obtain ⟨e, f, g, hle, hlf, hef, heg, hfg, hze, hzf, hzg⟩ := edge_coords l hl
      have hnegative := opposite l k hkl.symm hl hk e f g a d c
        hle hlf hef heg hfg hka hkd had hac hdc hze hzf hzg hza hzd hzc
      have hlga : b l (p.vertex (t.face k a)) g = 0 := by
        rw [hka, ← hle, bvertex]
        simp [Ne.symm heg]
      have hlgd : b l (p.vertex (t.face k d)) g = 0 := by
        rw [hkd, ← hlf, bvertex]
        simp [Ne.symm hfg]
      have relation y : b l y g = b k y c * b l (p.vertex (t.face k c)) g := by
        calc
          b l y g = b l (∑ r, b k y r • p.vertex (t.face k r)) g :=
            congrArg (fun x => b l x g) (breconstruct k y).symm
          _ = ∑ r, b k y r * b l (p.vertex (t.face k r)) g :=
            bcombo l _ _ (bsum k y) g
          _ = b k y c * b l (p.vertex (t.face k c)) g := by
            rw [sum_three _ a d c had hac hdc, hlga, hlgd]
            simp
      let N : Set (Real × Real) :=
        {y | 0 < b k y a ∧ 0 < b k y d} ∩ {y | 0 < b l y e ∧ 0 < b l y f}
      have hN : IsOpen N :=
        ((isOpen_lt continuous_const (bcontinuous k a)).inter
          (isOpen_lt continuous_const (bcontinuous k d))).inter
          ((isOpen_lt continuous_const (bcontinuous l e)).inter
            (isOpen_lt continuous_const (bcontinuous l f)))
      have hzN : z ∈ N := by
        change (0 < b k z a ∧ 0 < b k z d) ∧ (0 < b l z e ∧ 0 < b l z f)
        rw [hza, hzd, hze, hzf]
        exact ⟨⟨sub_pos.mpr hu.2, hu.1⟩, ⟨sub_pos.mpr hu.2, hu.1⟩⟩
      have hNX := TriangulationBoundaryProof.hNX n p X K t k b bhull indices i j u l a d
          c hka hkd had hac hdc hza hzd hzc e f g hle hlf hef heg hfg hze hzf hzg hnegative hlga
          hlgd relation hN hzN
      have hzint : z ∈ interior X := (hN.subset_interior_iff.mpr hNX) hzN
      simp only [hneighbor, not_false_eq_true, iff_true]
      exact hzint
  -- Classify triangle points, then include vertices by closure of the open edges.
  have hfrontier := TriangulationBoundaryProof.hfrontier n p X K t hcompact coordinates
      edge_interior
  have affine_chart (q : Fin 3 → Real × Real)
      (hq : P3381T1TriangleDeterminant q ≠ 0) := TriangulationBoundaryProof.affine_chart q hq
  -- Straight vertices give opposite rays; a same-direction pair would overlap edges.
  have polygon_chart {n : Nat} (p : P3381T1PolygonBoundary n) (i : Fin (n + 3)) :=
      TriangulationBoundaryProof.polygon_chart affine_chart (n := n) p i
  have local_boundary_chart {n : Nat} (p : P3381T1PolygonBoundary n)
      (X : Set (Real × Real))
      (hb : frontier X = ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)))
      (i : Fin (n + 3)) (eps : Real) (heps : 0 < eps) :=
          TriangulationBoundaryProof.local_boundary_chart polygon_chart (n := n) p X hb i
                eps heps
  have split_sets {A B S T : Set (Real × Real)}
      (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
      (hS : IsPathConnected S) (hT : IsPathConnected T)
      (hcover : S ∪ T = A ∪ B) (hneA : A.Nonempty) (hneB : B.Nonempty) :=
          TriangulationBoundaryProof.split_sets (A := A) (B
          := B) (S := S) (T := T) hA hB hAB hS hT hcover hneA hneB
  -- The large sector is a union of two intersecting half-planes in a convex ball preimage.
  have affine_sectors (h : (Real × Real) ≃ₜ (Real × Real))
      (haffine : ∀ (x y : Real × Real) (a b : Real), a + b = 1 →
        h (a • x + b • y) = a • h x + b • h y)
      (r : Real) (hr : 0 < r) (straight : Bool) := TriangulationBoundaryProof.affine_sectors h
          haffine r hr straight
  -- Nondegenerate closed triangles are closures of their ambient interiors.
  have vertex_in_closure := TriangulationBoundaryProof.vertex_in_closure n p X K t coordinates
  refine ⟨hcompact, hinterior, hfrontier, ?_⟩
  intro i
  obtain ⟨eps, heps, hcone⟩ := local_cones i
  obtain ⟨r, h, straight, hr, hreps, h0, haffine, hboundary⟩ :=
    local_boundary_chart p X hfrontier i eps heps
  let R : Set (Real × Real) := if straight then {x | x.2 = 0}
    else {x | (0 ≤ x.1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ 0 ≤ x.2)}
  obtain ⟨S, T, hS, hT, hST, hcover⟩ := affine_sectors h haffine r hr straight
  change S ∪ T = Metric.ball (h 0) r \ h '' R at hcover
  rw [h0] at hcover
  let U := Metric.ball (p.vertex i) r ∩ interior X
  let V := Metric.ball (p.vertex i) r \ X
  have hUopen : IsOpen U := Metric.isOpen_ball.inter isOpen_interior
  have hVopen : IsOpen V := Metric.isOpen_ball.sdiff hcompact.isClosed
  have hUV : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    exact hzV.2 (interior_subset hzU.2)
  have hUne := TriangulationInteriorSides.hUne n p X i r vertex_in_closure hr
  have hvfrontier : p.vertex i ∈ frontier X := by
    rw [hfrontier]
    exact Set.mem_iUnion.mpr ⟨i, left_mem_segment Real _ _⟩
  have hVne := TriangulationInteriorSides.hVne n p X i r hr hvfrontier
  have hcoverUV := TriangulationBoundaryProof.hcoverUV n p X hcompact i r h
      straight hboundary S T hcover
  obtain ⟨hU, hV⟩ := split_sets hUopen hVopen hUV hS hT hcoverUV hUne hVne
  refine ⟨r, hr, ?_, hU, hV⟩
  intro z hz
  exact hcone z (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) hreps))

end ApollonianSuperharmonic

end
