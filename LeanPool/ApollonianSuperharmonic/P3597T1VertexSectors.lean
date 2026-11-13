/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.AffineLineMapProperties
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P3597T1SideCrossing
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.LocallyConstant.Basic

-- [TABLET NODE: P3597T1VertexSectors]

/-!
# P3597T1VertexSectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace VertexSectorProof

private theorem hgeneric :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let C := P3544T1BoundaryCarrier p
        ∀ x : Real × Real, x ∉ C → ∃ d : Real × Real, (∀ j, d.1 * (p.vertex j - x).2 - d.2 *
            (p.vertex j - x).1 ≠ 0) ∧ (∀ j, d.1 * (p.vertex (j + 1) - p.vertex j).2 - d.2 *
                (p.vertex
            (j + 1) - p.vertex j).1 ≠ 0) ) := by
  classical
  intro n p C x hx
  apply (P3597T1GenericRayStability p).1 x
  intro j hj
  have hv : p.vertex j ∈ C := by
    exact Set.mem_iUnion.mpr ⟨j, left_mem_segment Real _ _⟩
  exact hx (hj ▸ hv)

private theorem hparity :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        ∀ x d : Real × Real, x ∉ C → (∀ j, d.1 * (p.vertex j - x).2 - d.2 * (p.vertex j - x).1 ≠
            0) →
            (∀ j, d.1 * (p.vertex (j + 1) - p.vertex j).2 - d.2 * (p.vertex (j + 1) - p.vertex
                j).1 ≠
            0) → (x ∈ O ↔ Set.ncard {j : Fin (n + 3) | ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real
            (p.vertex j) (p.vertex (j + 1))} % 2 = 1) ) := by
  classical
  intro n p O C x d hx hdv hde
  constructor
  · rintro ⟨_, d', hdv', hde', hodd⟩
    exact (P3597T1DirectionParity p x d d' hx hdv hdv').trans hodd
  · intro hodd
    exact ⟨hx, d, hdv, hde, hodd⟩

private theorem hlocal :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        (∀ x : Real × Real, x ∉ C → ∃ d : Real × Real, (∀ j, d.1 * (p.vertex j - x).2 - d.2 *
            (p.vertex j - x).1 ≠ 0) ∧ (∀ j, d.1 * (p.vertex (j + 1) - p.vertex j).2 - d.2 *
                (p.vertex
            (j + 1) - p.vertex j).1 ≠ 0)) → ((∀ x d : Real × Real, x ∉ C → (∀ j, d.1 * (p.vertex j -
            x).2 - d.2 * (p.vertex j - x).1 ≠ 0) → (∀ j, d.1 * (p.vertex (j + 1) - p.vertex j).2 -
            d.2 * (p.vertex (j + 1) - p.vertex j).1 ≠ 0) → (x ∈ O ↔ Set.ncard {j : Fin (n + 3) | ∃ t
            : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))} % 2 = 1)) → (∀
            x : Real × Real, x ∉ C → ∃ r : Real, 0 < r ∧ ∀ y ∈ Metric.ball x r, y ∉ C ∧ (y ∈ O ↔ x ∈
            O))) ) := by
  classical
  intro n p O C hgeneric hparity x hx
  obtain ⟨d, hdv, hde⟩ := hgeneric x hx
  obtain ⟨r, hr, hstable⟩ := (P3597T1GenericRayStability p).2.1 x d hx hdv hde
  refine ⟨r, hr, ?_⟩
  intro y hy
  obtain ⟨hyC, hdy, hsides⟩ := hstable y hy
  refine ⟨hyC, ?_⟩
  have hcount : Set.ncard {j : Fin (n + 3) | ∃ t : Real, 0 < t ∧
        y + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))} % 2 =
      Set.ncard {j : Fin (n + 3) | ∃ t : Real, 0 < t ∧
        x + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))} % 2 := by
    exact congrArg (fun S : Set (Fin (n + 3)) => Set.ncard S % 2) (Set.ext hsides)
  rw [hparity y d hyC hdy hde, hparity x d hx hdv hde, hcount]

private theorem hvnot :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let J : Set (Fin (n + 3)) := {j | j ≠ i ∧ j + 1 ≠ i}
        let K : Set (Real × Real) := ⋃ j ∈ J,
          segment Real (p.vertex j) (p.vertex (j + 1))
        v ∉ K ) := by
  classical
  intro n p i v J K hvK
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hvK
  obtain ⟨hjJ, hvseg⟩ := Set.mem_iUnion.mp hj
  have hii : v ∈ segment Real (p.vertex i) (p.vertex (i + 1)) := by
    dsimp [v]
    exact left_mem_segment Real _ _
  have hmem : v ∈ segment Real (p.vertex i) (p.vertex (i + 1)) ∩
      segment Real (p.vertex j) (p.vertex (j + 1)) := ⟨hii, hvseg⟩
  rw [p.edge_intersection i j hjJ.1.symm] at hmem
  have hend : (v = p.vertex i ∨ v = p.vertex (i + 1)) ∧
      (v = p.vertex j ∨ v = p.vertex (j + 1)) := by
    simpa only [Set.mem_ofPred_eq] using hmem
  rcases hend.2 with hjleft | hjright
  · have heq : i = j := p.injective (by simpa [v] using hjleft)
    exact hjJ.1 heq.symm
  · have heq : i = j + 1 := p.injective (by simpa [v] using hjright)
    exact hjJ.2 heq.symm

private theorem haddne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ j : Fin (n + 3), j + 1 ≠ j
    ) := by
  classical
  intro n j hj
  have hv' := congrArg Fin.val hj
  simp only [Fin.val_add] at hv'
  have hv'' : (j.val + 1) % (n + 3) = j.val := by simpa using hv'
  by_cases hlt : j.val + 1 < n + 3
  · rw [Nat.mod_eq_of_lt hlt] at hv''
    omega
  · have heq : j.val + 1 = n + 3 := by omega
    rw [heq, Nat.mod_self] at hv''
    omega

private theorem haddinj :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ x y : Fin (n + 3), x + 1 = y + 1 → x = y
    ) := by
  classical
  intro n x y hxy
  apply Fin.ext
  have hv := congrArg Fin.val hxy
  simp only [Fin.val_add] at hv
  have hv' : (x.val + 1) % (n + 3) = (y.val + 1) % (n + 3) := by simpa using hv
  have hxbound : x.val + 1 ≤ n + 3 := by omega
  have hybound : y.val + 1 ≤ n + 3 := by omega
  by_cases hxwrap : x.val + 1 = n + 3
  · have hywrap : y.val + 1 = n + 3 := by
      by_contra hne
      have hylt : y.val + 1 < n + 3 := by omega
      rw [hxwrap, Nat.mod_self, Nat.mod_eq_of_lt hylt] at hv'
      omega
    rw [hxwrap, Nat.mod_self, hywrap, Nat.mod_self] at hv'
    omega
  · have hxlt : x.val + 1 < n + 3 := by omega
    by_cases hywrap : y.val + 1 = n + 3
    · rw [Nat.mod_eq_of_lt hxlt, hywrap, Nat.mod_self] at hv'
      omega
    · have hylt : y.val + 1 < n + 3 := by omega
      rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hv'
      omega

private theorem hcrosszero :
    (by
      classical
      exact
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        ∀ x z : Real × Real, x ≠ 0 → cross x z = 0 → ∃ c : Real, z = c • x ) := by
  classical
  intro cross x z hx hD
  by_cases hx1 : x.1 = 0
  · have hx2 : x.2 ≠ 0 := by
      intro h
      apply hx
      ext <;> simp [hx1, h]
    have hz1 : z.1 = 0 := by
      dsimp [cross] at hD
      rw [hx1] at hD
      have hprod : x.2 * z.1 = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with hzero | hzero
      · exact (hx2 hzero).elim
      · exact hzero
    refine ⟨z.2 / x.2, ?_⟩
    ext
    · simp [hx1, hz1]
    · simp
      field_simp
  · let c := z.1 / x.1
    refine ⟨c, ?_⟩
    have hdet : x.1 * z.2 = x.2 * z.1 := by
      dsimp [cross] at hD
      linarith
    ext
    · simp [c]
      field_simp
    · simp [c]
      field_simp
      nlinarith [hdet]

private theorem hcarrierLocal :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        let J : Set (Fin (n + 3)) := {j | j ≠ i ∧ j + 1 ≠ i}
        let K : Set (Real × Real) := ⋃ j ∈ J,
          segment Real (p.vertex j) (p.vertex (j + 1))
        ∀ (rK : ℝ), ∀ (hballK : Metric.ball v rK ⊆ Kᶜ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        (prev + 1 = i) → ((∀ x y : Fin (n + 3), x + 1 = y + 1 → x = y) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (r ≤ rK) → (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x ∈ segment Real v
            (p.vertex (i
            + 1)) ∨ x ∈ segment Real (p.vertex prev) v)))) ) := by
  classical
  intro n p i C v J K rK hballK prev hprev haddinj r hrKle x hx
  constructor
  · intro hxC
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxC
    by_cases hji : j = i
    · left
      simpa [v, hji] using hj
    · by_cases hjp : j + 1 = i
      · right
        have hji' : j = prev := haddinj j prev (hjp.trans hprev.symm)
        simpa [v, hji', hprev] using hj
      · have hjJ : j ∈ J := ⟨hji, hjp⟩
        have hxK : x ∈ K := Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjJ, hj⟩⟩
        have hxKc : x ∈ Kᶜ := hballK (Metric.ball_subset_ball hrKle hx)
        exact False.elim (hxKc hxK)
  · rintro (hx | hx)
    · have : x ∈ C := Set.mem_iUnion.mpr ⟨i, by simpa [v] using hx⟩
      exact this
    · have : x ∈ C := Set.mem_iUnion.mpr ⟨prev, by simpa [hprev] using hx⟩
      exact this

private theorem hsegA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let a := p.vertex (i + 1) - v
        (∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) → (∀ x : Real ×
            Real, (x ∈ segment Real v (p.vertex (i + 1)) ↔ ∃ t : Real, t ∈ Set.Icc 0 1 ∧ x = v + t •
            a)) ) := by
  classical
  intro n p i v a hlineMap x
  rw [segment_eq_image_lineMap]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ht, ?_⟩
    rw [← htx, hlineMap]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [hlineMap]

private theorem hsegB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let b := p.vertex prev - v
        (∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) → (∀ x : Real ×
            Real, (x ∈ segment Real (p.vertex prev) v ↔ ∃ t : Real, t ∈ Set.Icc 0 1 ∧ x = v + t •
                b)) ) := by
  classical
  intro n p i v prev b hlineMap x
  rw [segment_symm Real (p.vertex prev) v, segment_eq_image_lineMap]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ht, ?_⟩
    rw [← htx, hlineMap]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [hlineMap]

private theorem hRayA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        (0 < dist v (p.vertex (i + 1))) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (r ≤ dist v (p.vertex (i + 1)) / 2) → ((∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x
            y t = x + t • (y - x)) → ((∀ (u : Real × Real), ∀ (t : Real), 0 ≤ t → dist (v + t • u) v
            = t * dist (v + u) v) → (∀ x : Real × Real, x ∈ Metric.ball v r → ∀ t : Real, 0 < t →
                x =
            v + t • a → x ∈ segment Real v (p.vertex (i + 1)))))) ) := by
  classical
  intro n p i v rK prev a hdistA r hrAle hlineMap hdistRadial x hx t ht hxeq
  have hdistx : dist (v + t • a) v < r := by
    simpa [hxeq] using (Metric.mem_ball.mp hx)
  have he : v + a = p.vertex (i + 1) := by dsimp [a]; abel
  have hdist : dist (v + t • a) v = t * dist v (p.vertex (i + 1)) := by
    calc
      dist (v + t • a) v = t * dist (v + a) v := hdistRadial a t ht.le
      _ = t * dist v (p.vertex (i + 1)) := by rw [he, dist_comm]
  have hdistx' : dist v (v + t • a) < r := by simpa [dist_comm] using hdistx
  have htlt : t < 1 := by nlinarith [hdistx', hdist]
  have hmem := lineMap_mem_segment Real v (p.vertex (i + 1))
    (show t ∈ Set.Icc 0 1 from ⟨ht.le, htlt.le⟩)
  rw [hlineMap] at hmem
  rw [hxeq]
  simpa [a] using hmem

private theorem hRayB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let b := p.vertex prev - v
        (0 < dist v (p.vertex prev)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (r ≤ dist v (p.vertex prev) / 2) → ((∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x
            y t
            = x + t • (y - x)) → ((∀ (u : Real × Real), ∀ (t : Real), 0 ≤ t → dist (v + t • u) v = t
            * dist (v + u) v) → (∀ x : Real × Real, x ∈ Metric.ball v r → ∀ t : Real, 0 < t → x =
                v +
            t • b → x ∈ segment Real (p.vertex prev) v)))) ) := by
  classical
  intro n p i v rK prev b hdistB r hrBle hlineMap hdistRadial x hx t ht hxeq
  have hdistx : dist (v + t • b) v < r := by
    simpa [hxeq] using (Metric.mem_ball.mp hx)
  have he : v + b = p.vertex prev := by dsimp [b]; abel
  have hdistB' : dist (v + t • b) v = t * dist v (p.vertex prev) := by
    calc
      dist (v + t • b) v = t * dist (v + b) v := hdistRadial b t ht.le
      _ = t * dist v (p.vertex prev) := by rw [he, dist_comm]
  have htlt : t < 1 := by nlinarith [hdistx, hdistB']
  have hmem := lineMap_mem_segment Real v (p.vertex prev)
    (show t ∈ Set.Icc 0 1 from ⟨ht.le, htlt.le⟩)
  rw [hlineMap] at hmem
  have hmem' : v + t • b ∈ segment Real (p.vertex prev) v := by
    rw [segment_symm Real (p.vertex prev) v]
    simpa [b] using hmem
  rw [hxeq]
  exact hmem'

private theorem hcarrierRays :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x ∈ segment Real v (p.vertex (i + 1)) ∨ x
            ∈ segment Real (p.vertex prev) v)) → ((∀ x : Real × Real, (x ∈ segment Real v (p.vertex
            (i + 1)) ↔ ∃ t : Real, t ∈ Set.Icc 0 1 ∧ x = v + t • a)) → ((∀ x : Real × Real, (x ∈
            segment Real (p.vertex prev) v ↔ ∃ t : Real, t ∈ Set.Icc 0 1 ∧ x = v + t • b)) → ((∀ x :
            Real × Real, x ∈ Metric.ball v r → ∀ t : Real, 0 < t → x = v + t • a → x ∈ segment
                Real v
            (p.vertex (i + 1))) → ((∀ x : Real × Real, x ∈ Metric.ball v r → ∀ t : Real, 0 < t → x =
            v + t • b → x ∈ segment Real (p.vertex prev) v) → (∀ x : Real × Real, x ∈ Metric.ball
                v r
            → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t • a) ∨ (∃ t : Real, 0 < t ∧ x = v +
                t •
            b))))))) ) := by
  classical
  intro n p i C v rK prev a b r hcarrierLocal hsegA hsegB hRayA hRayB x hx
  rw [hcarrierLocal x hx]
  constructor
  · rintro (hA | hB)
    · obtain ⟨t, ht, hxt⟩ := (hsegA x).mp hA
      rcases eq_or_ne t 0 with ht0 | ht0
      · left
        simpa [ht0] using hxt
      · right
        left
        refine ⟨t, ?_⟩
        exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), hxt⟩
    · obtain ⟨t, ht, hxt⟩ := (hsegB x).mp hB
      rcases eq_or_ne t 0 with ht0 | ht0
      · left
        simpa [ht0] using hxt
      · right
        right
        refine ⟨t, ?_⟩
        exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), hxt⟩
  · rintro (h | h | h)
    · subst x
      left
      exact left_mem_segment Real _ _
    · obtain ⟨t, ht, hxt⟩ := h
      left
      exact hRayA x hx t ht hxt
    · obtain ⟨t, ht, hxt⟩ := h
      right
      exact hRayB x hx t ht hxt

private theorem hnoPosMultiple :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        (prev + 1 = i) → ((prev ≠ i) → ((p.vertex (i + 1) ≠ v) → (
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        (∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) → (¬ ∃ c :
            Real,
            0 < c ∧ b = c • a)))) ) := by
  classical
  intro n p i v prev hprev hprevne hnextVertex a b hlineMap
  rintro ⟨c, hc, hba⟩
  let t := 1 / (2 * c + 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hct : 0 < c * t := mul_pos hc ht
  have hctlt : c * t < 1 := by
    dsimp [t]
    have hden : 0 < 2 * c + 2 := by positivity
    have he : c * (1 / (2 * c + 2)) = c / (2 * c + 2) := by
      field_simp
    rw [he, div_lt_iff₀ hden]
    nlinarith
  have htlt : t < 1 := by
    dsimp [t]
    have hden : 0 < 2 * c + 2 := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith
  let q := v + (c * t) • a
  have hqA : q ∈ segment Real v (p.vertex (i + 1)) := by
    have hseg := lineMap_mem_segment Real v (p.vertex (i + 1))
      (show c * t ∈ Set.Icc 0 1 from ⟨hct.le, hctlt.le⟩)
    rw [hlineMap] at hseg
    simpa [q, a] using hseg
  have hqb : v + t • b = q := by
    rw [hba, smul_smul]
    congr 1
    ring
  have hqB : q ∈ segment Real (p.vertex prev) v := by
    rw [← hqb, segment_symm Real (p.vertex prev) v]
    have hseg := lineMap_mem_segment Real v (p.vertex prev)
      (show t ∈ Set.Icc 0 1 from ⟨ht.le, htlt.le⟩)
    rw [hlineMap] at hseg
    simpa [b] using hseg
  have hqOpen : q ∈ openSegment Real v (p.vertex (i + 1)) := by
    have hopen := lineMap_mem_openSegment Real v (p.vertex (i + 1))
      (show c * t ∈ Set.Ioo 0 1 from ⟨hct, hctlt⟩)
    rw [hlineMap] at hopen
    simpa [q, a] using hopen
  have hinter : q ∈ segment Real v (p.vertex (i + 1)) ∩
      segment Real (p.vertex prev) v := ⟨hqA, hqB⟩
  have hinter' : q ∈ segment Real (p.vertex i) (p.vertex (i + 1)) ∩
      segment Real (p.vertex prev) (p.vertex (prev + 1)) := by
    simpa [v, hprev] using hinter
  rw [p.edge_intersection i prev hprevne.symm] at hinter'
  have hends : (q = v ∨ q = p.vertex (i + 1)) ∧
      (q = p.vertex prev ∨ q = v) := by
    simpa [v, hprev] using hinter'
  rcases hends.1 with hqv | hqe
  · rw [hqv] at hqOpen
    have heq := (left_mem_openSegment_iff.mp hqOpen)
    exact hnextVertex (by simpa [v] using heq.symm)
  · rw [hqe] at hqOpen
    have heq := (right_mem_openSegment_iff.mp hqOpen)
    exact hnextVertex (by simpa [v] using heq.symm)

private theorem happroach :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        (0 < dist v (p.vertex (i + 1))) → ((∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t
            = x + t • (y - x)) → ((∀ (u : Real × Real), ∀ (t : Real), 0 ≤ t → dist (v + t • u) v = t
            * dist (v + u) v) → (∀ ε : Real, 0 < ε → ∃ x : Real × Real, x ∈ openSegment Real v
            (p.vertex (i + 1)) ∧ dist v x < ε / 2))) ) := by
  classical
  intro n p i v hdistA hlineMap hdistRadial ε hε
  let a := p.vertex (i + 1) - v
  let d := dist v (p.vertex (i + 1))
  let t := min (1 / 2) (ε / (4 * (d + 1)))
  have ht : 0 < t := by
    dsimp [t]
    apply lt_min
    · norm_num
    · positivity
  have htle : t ≤ ε / (4 * (d + 1)) := min_le_right _ _
  have htlt : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hdist : dist (v + t • a) v = t * d := by
    have he : v + a = p.vertex (i + 1) := by dsimp [a]; abel
    rw [hdistRadial a t ht.le, he, dist_comm]
  have hclose : dist v (v + t • a) < ε / 2 := by
    rw [dist_comm, hdist]
    have hd0 : 0 ≤ d := dist_nonneg
    calc
      t * d ≤ (ε / (4 * (d + 1))) * d := mul_le_mul_of_nonneg_right htle hd0
      _ < ε / 4 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      _ < ε / 2 := by linarith
  let x := v + t • a
  have hopen : x ∈ openSegment Real v (p.vertex (i + 1)) := by
    have hmem := lineMap_mem_openSegment Real v (p.vertex (i + 1))
      (show t ∈ Set.Ioo 0 1 from ⟨ht, htlt⟩)
    rw [hlineMap] at hmem
    simpa [x, a] using hmem
  exact ⟨x, hopen, by simpa [x] using hclose⟩

private theorem hvOdd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let v := p.vertex i
        (∀ ε : Real, 0 < ε → ∃ x : Real × Real, x ∈ openSegment Real v (p.vertex (i + 1)) ∧ dist v x
            < ε / 2) → (v ∈ closure O) ) := by
  classical
  intro n p i O v happroach
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x, hxopen, hxclose⟩ := happroach ε hε
  obtain ⟨_, _, _, hxO, _⟩ := P3597T1SideCrossing p i x hxopen
  obtain ⟨y, hyO, hydist⟩ := (Metric.mem_closure_iff.mp hxO) (ε / 2) (by linarith)
  refine ⟨y, hyO, ?_⟩
  calc
    dist v y ≤ dist v x + dist x y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxclose hydist
    _ = ε := by ring

private theorem hvEven :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        (∀ ε : Real, 0 < ε → ∃ x : Real × Real, x ∈ openSegment Real v (p.vertex (i + 1)) ∧ dist v x
            < ε / 2) → (v ∈ closure (O ∪ C)ᶜ) ) := by
  classical
  intro n p i O C v happroach
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x, hxopen, hxclose⟩ := happroach ε hε
  obtain ⟨_, _, _, _, hxEven⟩ := P3597T1SideCrossing p i x hxopen
  obtain ⟨y, hyEven, hydist⟩ := (Metric.mem_closure_iff.mp hxEven) (ε / 2) (by linarith)
  refine ⟨y, hyEven, ?_⟩
  calc
    dist v y ≤ dist v x + dist x y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxclose hydist
    _ = ε := by ring

private theorem hdetuw :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        0 < cross u w ∨ cross u w = 0 ) := by
  classical
  intro n p i v prev a b cross u w
  by_cases hpos : 0 < cross a b
  · left
    simp only [u, w, ite_eq_left hpos]
    exact hpos
  · by_cases hzero : cross a b = 0
    · right
      simp only [u, w, ite_eq_right hpos]
      have hswap : cross b a = -cross a b := by dsimp [cross]; ring
      rw [hswap, hzero]
      simp
    · left
      have hneg : cross a b < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
      have hswap : cross b a = -cross a b := by dsimp [cross]; ring
      simp only [u, w, ite_eq_right hpos]
      rw [hswap]
      exact neg_pos.mpr hneg

private theorem hcarrierUW :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t •
            a) ∨ (∃ t : Real, 0 < t ∧ x = v + t • b))) → (
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        ∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t
            • u)
            ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) ) := by
  classical
  intro n p i C v rK prev a b cross r hcarrierRays u w x hx
  by_cases hpos : 0 < cross a b
  · simp only [u, w, ite_eq_left hpos]
    exact hcarrierRays x hx
  · simp only [u, w, ite_eq_right hpos]
    have hrays := hcarrierRays x hx
    constructor
    · intro hc
      rcases hrays.mp hc with hv | ha | hb
      · exact Or.inl hv
      · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inl hb)
    · intro hc
      rcases hc with hv | hb | ha
      · exact hrays.mpr (Or.inl hv)
      · exact hrays.mpr (Or.inr (Or.inr hb))
      · exact hrays.mpr (Or.inr (Or.inl ha))

private theorem hconstOn :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        (∀ x : Real × Real, x ∉ C → ∃ r : Real, 0 < r ∧ ∀ y ∈ Metric.ball x r, y ∉ C ∧ (y ∈ O ↔ x ∈
            O)) → (∀ S : Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x ∈ S, ∀ y ∈ S,
            (x ∈ O ↔ y ∈ O)) ) := by
  classical
  intro n p O C hlocal S hconn hSC x hx y hy
  let f : S → Bool := fun z => decide ((z : Real × Real) ∈ O)
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨ρ, hρ, hstable⟩ := hlocal z.1 (hSC z.1 z.2)
    let U : Set S := Subtype.val ⁻¹' Metric.ball z.1 ρ
    refine ⟨U, Metric.isOpen_ball.preimage continuous_subtype_val, ?_, ?_⟩
    · exact Metric.mem_ball_self hρ
    · intro z' hz'
      have hzball : (z' : Real × Real) ∈ Metric.ball z.1 ρ := hz'
      have hsame := (hstable z' hzball).2
      have hbool : decide ((z' : Real × Real) ∈ O) = decide ((z : Real × Real) ∈ O) := by
        by_cases hzO : (z' : Real × Real) ∈ O
        · by_cases hzbase : (z : Real × Real) ∈ O
          · simp [hzO, hzbase]
          · exact False.elim (hzbase (hsame.mp hzO))
        · by_cases hzbase : (z : Real × Real) ∈ O
          · exact False.elim (hzO (hsame.mpr hzbase))
          · simp [hzO, hzbase]
      simpa [f] using hbool
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn.2
  have heq := hf.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  change (decide (x ∈ O) = decide (y ∈ O)) at heq
  by_cases hxo : x ∈ O <;> by_cases hyo : y ∈ O <;> simp [hxo, hyo] at heq ⊢

private theorem hsmallScale :
    (by
      classical
      exact
        ∀ z : Real × Real, ∀ δ : Real, 0 < δ → ∃ t : Real, 0 < t ∧ t • z ∈ Metric.ball ((0 : Real),
            (0 : Real)) δ ) := by
  classical
  intro z δ hδ
  let t := δ / (‖z‖ + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hn : ‖t • z‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hd : 0 < ‖z‖ + 1 := by positivity
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hd).2 (by nlinarith [norm_nonneg z])
  have hmem : t • z ∈ Metric.ball ((0 : Real), (0 : Real)) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (t • z : Real × Real) - (0, 0) = t • z := by ext <;> simp
    rw [he]
    exact hn
  exact ⟨t, ht, hmem⟩

private theorem hNandW :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (0 < r) → (
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ z : Real × Real, ∀ δ : Real, 0 < δ → ∃ t : Real, 0 < t ∧ t • z ∈ Metric.ball ((0 : Real),
            (0 : Real)) δ) → (
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        0 < cross u w → IsPathConnected N ∧ IsPathConnected W))) ) := by
  classical
  intro n p i v rK prev a b cross hcrossLinear r hr u w hsmallScale N W hD
  let H : Set (Real × Real) := {z | z ∈ Metric.ball ((0 : Real), (0 : Real)) r ∧
    0 < cross u z ∧ cross w z < 0}
  have hconv : Convex Real H := by
    exact (convex_ball _ _).inter
      ((convex_halfSpace_gt (hcrossLinear u) 0).inter
        (convex_halfSpace_lt (hcrossLinear w) 0))
  have hne : H.Nonempty := by
    let z := u + w
    have hzu : 0 < cross u z := by
      have he : cross u z = cross u w := by dsimp [z, cross]; ring
      rw [he]
      exact hD
    have hzw : cross w z < 0 := by
      have he : cross w z = -cross u w := by dsimp [z, cross]; ring
      rw [he]
      linarith
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball
      ((0 : Real), (0 : Real)) (Metric.mem_ball_self hr)
    obtain ⟨t, ht, hsmall⟩ := hsmallScale z δ hδ
    refine ⟨t • z, hball hsmall, ?_, ?_⟩
    · rw [(hcrossLinear u).map_smul]
      change 0 < t * cross u z
      exact mul_pos ht hzu
    · rw [(hcrossLinear w).map_smul]
      change t * cross w z < 0
      exact mul_neg_of_pos_of_neg ht hzw
  have hpH : IsPathConnected H := hconv.isPathConnected hne
  have himage : (fun z : Real × Real => z + v) '' H = N := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨hzball, hzu, hzw⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hzball ⊢
        have he : (z : Real × Real) - (0, 0) = z := by ext <;> simp
        rw [he] at hzball
        have he' : (z + v : Real × Real) - v = z := by abel
        rw [he']
        exact hzball
      · simpa using hzu
      · simpa using hzw
    · intro hx
      rcases hx with ⟨hxball, hxu, hxw⟩
      refine ⟨x - v, ?_, by simp⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hxball ⊢
        have he : (x - v : Real × Real) - (0, 0) = x - v := by ext <;> simp
        rw [he]
        exact hxball
      · exact hxu
      · exact hxw
  have hN : IsPathConnected N :=
    himage ▸ hpH.image (continuous_id.add continuous_const)
  let z := u + w
  have hzu : cross u z = cross u w := by dsimp [z, cross]; ring
  have hzw : cross w z = -cross u w := by dsimp [z, cross]; ring
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball
    ((0 : Real), (0 : Real)) (Metric.mem_ball_self hr)
  obtain ⟨t, ht, hsmall⟩ := hsmallScale z δ hδ
  let H₁ : Set (Real × Real) := {z | z ∈ Metric.ball ((0 : Real), (0 : Real)) r ∧
    cross u z < 0}
  let H₂ : Set (Real × Real) := {z | z ∈ Metric.ball ((0 : Real), (0 : Real)) r ∧
    0 < cross w z}
  have hconv₁ : Convex Real H₁ :=
    (convex_ball _ _).inter (convex_halfSpace_lt (hcrossLinear u) 0)
  have hconv₂ : Convex Real H₂ :=
    (convex_ball _ _).inter (convex_halfSpace_gt (hcrossLinear w) 0)
  have hsmallNeg : -(t • z) ∈ Metric.ball ((0 : Real), (0 : Real)) r := by
    have hsmall' : t • z ∈ Metric.ball ((0 : Real), (0 : Real)) r := hball hsmall
    rw [Metric.mem_ball, dist_eq_norm] at hsmall' ⊢
    have he : (-(t • z) : Real × Real) - (0, 0) = -(t • z) := by ext <;> simp
    have he' : (t • z : Real × Real) - (0, 0) = t • z := by ext <;> simp
    rw [he]
    rw [he'] at hsmall'
    simpa [norm_neg] using hsmall'
  have hnegU : cross u (-(t • z)) < 0 := by
    rw [(hcrossLinear u).map_neg, (hcrossLinear u).map_smul]
    change -(t * cross u z) < 0
    rw [hzu]
    exact neg_neg_of_pos (mul_pos ht hD)
  have hposW : 0 < cross w (-(t • z)) := by
    rw [(hcrossLinear w).map_neg, (hcrossLinear w).map_smul]
    change 0 < -(t * cross w z)
    rw [hzw]
    nlinarith [mul_pos ht hD]
  have hne₁ : H₁.Nonempty := ⟨-(t • z), hsmallNeg, hnegU⟩
  have hne₂ : H₂.Nonempty := ⟨-(t • z), hsmallNeg, hposW⟩
  have hov : (H₁ ∩ H₂).Nonempty :=
    ⟨-(t • z), ⟨hsmallNeg, hnegU⟩, ⟨hsmallNeg, hposW⟩⟩
  have hpWide : IsPathConnected (H₁ ∪ H₂) :=
    (hconv₁.isPathConnected hne₁).union (hconv₂.isPathConnected hne₂) hov
  have himageWide : (fun z : Real × Real => z + v) '' (H₁ ∪ H₂) = W := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with hz | hz
      · rcases hz with ⟨hzball, hzu⟩
        refine ⟨?_, Or.inl ?_⟩
        · rw [Metric.mem_ball, dist_eq_norm] at hzball ⊢
          have he : (z : Real × Real) - (0, 0) = z := by ext <;> simp
          rw [he] at hzball
          have he' : (z + v : Real × Real) - v = z := by abel
          rw [he']
          exact hzball
        · simpa using hzu
      · rcases hz with ⟨hzball, hzw⟩
        refine ⟨?_, Or.inr ?_⟩
        · rw [Metric.mem_ball, dist_eq_norm] at hzball ⊢
          have he : (z : Real × Real) - (0, 0) = z := by ext <;> simp
          rw [he] at hzball
          have he' : (z + v : Real × Real) - v = z := by abel
          rw [he']
          exact hzball
        · simpa using hzw
    · intro hx
      rcases hx with ⟨hxball, hsign⟩
      refine ⟨x - v, ?_, by simp⟩
      have hballx : x - v ∈ Metric.ball ((0 : Real), (0 : Real)) r := by
        rw [Metric.mem_ball, dist_eq_norm] at hxball ⊢
        have he : (x - v : Real × Real) - (0, 0) = x - v := by ext <;> simp
        rw [he]
        exact hxball
      rcases hsign with hsign | hsign
      · exact Or.inl ⟨hballx, hsign⟩
      · exact Or.inr ⟨hballx, hsign⟩
  have hW : IsPathConnected W :=
    himageWide ▸ hpWide.image (continuous_id.add continuous_const)
  exact ⟨hN, hW⟩

private theorem hzeroUNegW :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → ((∀ x z : Real × Real, x ≠ 0 → cross x z =
            0 → ∃ c : Real, z = c • x) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t •
            u) ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) → ((u ≠ 0) → ((cross w u = -cross u w) → (0 <
            cross u w → ∀ x : Real × Real, x ∈ Metric.ball v r → cross u (x - v) = 0 → cross w (x -
            v) < 0 → x ∈ C))))) ) := by
  classical
  intro n p i C v rK prev a b cross hcrossLinear hcrosszero r u w hcarrierUW hu0 hswapuw hD x hx
      hA hB
  obtain ⟨t, hzt⟩ := hcrosszero u (x - v) hu0 hA
  have hcalc : cross w (x - v) = -(t * cross u w) := by
    rw [hzt, (hcrossLinear w).map_smul]
    change t * cross w u = -(t * cross u w)
    rw [hswapuw]
    ring
  have ht : 0 < t := by nlinarith [hB, hcalc, hD]
  have hxeq : x = v + t • u := by
    calc x = v + (x - v) := by abel
    _ = v + t • u := by rw [hzt]
  exact (hcarrierUW x hx).2 (Or.inr (Or.inl ⟨t, ht, hxeq⟩))

private theorem hzeroWPosU :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → ((∀ x z : Real × Real, x ≠ 0 → cross x z =
            0 → ∃ c : Real, z = c • x) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t •
            u) ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) → ((w ≠ 0) → (0 < cross u w → ∀ x : Real ×
            Real, x ∈ Metric.ball v r → cross w (x - v) = 0 → 0 < cross u (x - v) → x ∈ C)))) )
                := by
  classical
  intro n p i C v rK prev a b cross hcrossLinear hcrosszero r u w hcarrierUW hw0 hD x hx hB hA
  obtain ⟨t, hzt⟩ := hcrosszero w (x - v) hw0 hB
  have hcalc : cross u (x - v) = t * cross u w := by
    rw [hzt, (hcrossLinear u).map_smul]
    simp only [smul_eq_mul]
  have ht : 0 < t := by nlinarith [hA, hcalc, hD]
  have hxeq : x = v + t • w := by
    calc x = v + (x - v) := by abel
    _ = v + t • w := by rw [hzt]
  exact (hcarrierUW x hx).2 (Or.inr (Or.inr ⟨t, ht, hxeq⟩))

private theorem hzeroBoth :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → ((∀ x z : Real × Real, x ≠ 0 → cross x z =
            0 → ∃ c : Real, z = c • x) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t •
            u) ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) → ((u ≠ 0) → ((cross w u = -cross u w) → (0 <
            cross u w → ∀ x : Real × Real, x ∈ Metric.ball v r → cross u (x - v) = 0 → cross w (x -
            v) = 0 → x ∈ C))))) ) := by
  classical
  intro n p i C v rK prev a b cross hcrossLinear hcrosszero r u w hcarrierUW hu0 hswapuw hD x hx
      hA hB
  obtain ⟨t, hzt⟩ := hcrosszero u (x - v) hu0 hA
  have hcalc : cross w (x - v) = -(t * cross u w) := by
    rw [hzt, (hcrossLinear w).map_smul]
    change t * cross w u = -(t * cross u w)
    rw [hswapuw]
    ring
  have ht : t = 0 := by nlinarith [hB, hcalc, hD]
  rw [ht] at hzt
  have hz : x - v = 0 := by simpa using hzt
  have hxv : x = v := sub_eq_zero.mp hz
  exact (hcarrierUW x hx).2 (Or.inl hxv)

private theorem hNoff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t •
            u) ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) → (
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        (∀ z : Real × Real, cross z z = 0) → (∀ x : Real × Real, x ∈ N → x ∉ C))) ) := by
  classical
  intro n p i C v rK prev a b cross hcrossLinear r u w hcarrierUW N hcrossSelf x hx hxc
  rcases hx with ⟨hxball, hA, hB⟩
  rcases (hcarrierUW x hxball).mp hxc with hv | hu | hw
  · subst x
    simp [cross] at hA
  · obtain ⟨t, ht, hxeq⟩ := hu
    have hz : x - v = t • u := by rw [hxeq]; abel
    rw [hz, (hcrossLinear u).map_smul, hcrossSelf] at hA
    simp only [smul_eq_mul, mul_zero] at hA
    exact (lt_irrefl 0) hA
  · obtain ⟨t, ht, hxeq⟩ := hw
    have hz : x - v = t • w := by rw [hxeq]; abel
    rw [hz, (hcrossLinear w).map_smul, hcrossSelf] at hB
    simp only [smul_eq_mul, mul_zero] at hB
    exact (lt_irrefl 0) hB

private theorem hWoff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (0 < cross u w ∨ cross u w = 0) → ((∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x =
            v ∨
            (∃ t : Real, 0 < t ∧ x = v + t • u) ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) → (
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (cross w u = -cross u w) → ((∀ z : Real × Real, cross z z = 0) → (∀ x : Real × Real, x ∈ W →
            x ∉ C))))) ) := by
  classical
  intro n p i C v rK prev a b cross hcrossLinear r u w hdetuw hcarrierUW W hswapuw hcrossSelf x
      hx hxc
  rcases hx with ⟨hxball, hW⟩
  rcases (hcarrierUW x hxball).mp hxc with hv | hu | hw
  · subst x
    simp [cross] at hW
  · obtain ⟨t, ht, hxeq⟩ := hu
    have hz : x - v = t • u := by rw [hxeq]; abel
    have hA : cross u (x - v) = 0 := by
      rw [hz, (hcrossLinear u).map_smul, hcrossSelf]
      simp
    have hB : cross w (x - v) = -(t * cross u w) := by
      rw [hz, (hcrossLinear w).map_smul]
      change t * cross w u = -(t * cross u w)
      rw [hswapuw]
      ring
    rcases hW with hneg | hpos
    · rw [hA] at hneg
      linarith
    · rcases hdetuw with hDpos | hDzero
      · have hBneg : cross w (x-v) < 0 := by
          rw [hB]
          exact neg_neg_of_pos (mul_pos ht hDpos)
        linarith
      · rw [hDzero] at hB
        simp at hB
        linarith
  · obtain ⟨t, ht, hxeq⟩ := hw
    have hz : x - v = t • w := by rw [hxeq]; abel
    have hB : cross w (x - v) = 0 := by
      rw [hz, (hcrossLinear w).map_smul, hcrossSelf]
      simp
    have hA : cross u (x - v) = t * cross u w := by
      rw [hz, (hcrossLinear u).map_smul]
      simp only [smul_eq_mul]
    rcases hW with hneg | hpos
    · rcases hdetuw with hDpos | hDzero
      · have hApos : 0 < cross u (x-v) := by rw [hA]; exact mul_pos ht hDpos
        linarith
      · rw [hDzero] at hA
        simp at hA
        linarith
    · rw [hB] at hpos
      linarith

private theorem hcover :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (0 < cross u w → ∀ x : Real × Real, x ∈ Metric.ball v r → cross u (x - v) = 0 → cross w (x -
            v) < 0 → x ∈ C) → ((0 < cross u w → ∀ x : Real × Real, x ∈ Metric.ball v r → cross w
                (x -
            v) = 0 → 0 < cross u (x - v) → x ∈ C) → ((0 < cross u w → ∀ x : Real × Real, x ∈
            Metric.ball v r → cross u (x - v) = 0 → cross w (x - v) = 0 → x ∈ C) → (0 < cross u w
                → ∀
            x : Real × Real, x ∈ Metric.ball v r → x ∉ C → x ∈ N ∨ x ∈ W))) ) := by
  classical
  intro n p i C v rK prev a b cross r u w N W hzeroUNegW hzeroWPosU hzeroBoth hD x hx hxC
  rcases lt_trichotomy 0 (cross u (x-v)) with hApos | hAzero | hAneg
  · rcases lt_trichotomy 0 (cross w (x-v)) with hBpos | hBzero | hBneg
    · exact Or.inr ⟨hx, Or.inr hBpos⟩
    · exact False.elim (hxC (hzeroWPosU hD x hx (by simpa using hBzero.symm) hApos))
    · exact Or.inl ⟨hx, hApos, hBneg⟩
  · rcases lt_trichotomy 0 (cross w (x-v)) with hBpos | hBzero | hBneg
    · exact Or.inr ⟨hx, Or.inr hBpos⟩
    · exact False.elim (hxC (hzeroBoth hD x hx (by simpa using hAzero.symm)
        (by simpa using hBzero.symm)))
    · exact False.elim (hxC (hzeroUNegW hD x hx (by simpa using hAzero.symm) hBneg))
  · exact Or.inr ⟨hx, Or.inl hAneg⟩

private theorem hx0ballAt924 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        (0 < dist v (p.vertex (i + 1))) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (0 < r) → (
        let d := dist v (p.vertex (i + 1))
        let τ := min (1 / 2) (r / (4 * (d + 1)))
        (τ ≤ r / (4 * (d + 1))) → (
        let x0 := v + τ • a
        (dist v x0 = τ * d) → (x0 ∈ Metric.ball v r)))) ) := by
  classical
  intro n p i v rK prev a hdistA r hr d τ hτle x0 hdistance
  rw [Metric.mem_ball, dist_comm, hdistance]
  have hd0 : 0 ≤ d := dist_nonneg
  have hbound : τ * d ≤ (r / (4 * (d + 1))) * d :=
    mul_le_mul_of_nonneg_right hτle hd0
  have hfrac : (r / (4 * (d + 1))) * d < r := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have hd0 : 0 ≤ d := dist_nonneg
    nlinarith
  exact lt_of_le_of_lt hbound hfrac

private theorem hqaAt937 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let a := p.vertex (i + 1) - v
        (a ≠ 0) → (
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let q : Real × Real := (-a.2, a.1)
        0 < cross a q) ) := by
  classical
  intro n p i v a ha cross q
  have hnz : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_cases h : a.1 = 0
    · right
      intro h2
      exact ha (Prod.ext h h2)
    · exact Or.inl h
  have hcalc : cross a q = a.1 ^ 2 + a.2 ^ 2 := by
    change a.1 * a.1 - a.2 * (-a.2) = a.1 ^ 2 + a.2 ^ 2
    ring
  rw [hcalc]
  rcases hnz with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg a.2)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg a.1) (sq_pos_of_ne_zero h)

private theorem hUopenAt954 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let d := dist v (p.vertex (i + 1))
        let τ := min (1 / 2) (r / (4 * (d + 1)))
        let x0 := v + τ • a
        ∀ (rS : ℝ),
        let U : Set (Real × Real) := if 0 < cross a b then
          Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | cross b (y-v) < 0}
          else Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | 0 < cross b (y-v)}
        IsOpen U ) := by
  classical
  intro n p i v rK prev a b cross r d τ x0 rS U
  by_cases hab : 0 < cross a b
  · have hc : Continuous (fun y : Real × Real => cross b (y-v)) := by
      change Continuous (fun y : Real × Real =>
        b.1 * (y.2-v.2) - b.2 * (y.1-v.1))
      fun_prop
    simp only [U, ite_eq_left hab]
    exact (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
      (isOpen_lt hc (continuous_const : Continuous fun _ : Real × Real => (0 : Real)))
  · have hc : Continuous (fun y : Real × Real => cross b (y-v)) := by
      change Continuous (fun y : Real × Real =>
        b.1 * (y.2-v.2) - b.2 * (y.1-v.1))
      fun_prop
    simp only [U, ite_eq_right hab]
    exact (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
      (isOpen_lt (continuous_const : Continuous fun _ : Real × Real => (0 : Real)) hc)

private theorem hx0UAt970 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        ((0 : ℝ) < cross u w) → (
        let d := dist v (p.vertex (i + 1))
        let τ := min (1 / 2) (r / (4 * (d + 1)))
        (0 < τ) → (
        let x0 := v + τ • a
        (x0 ∈ Metric.ball v r) → ((x0 - v = τ • a) → (∀ (rS : ℝ), ((0 : ℝ) < rS) → (
        let U : Set (Real × Real) := if 0 < cross a b then
          Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | cross b (y-v) < 0}
          else Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | 0 < cross b (y-v)}
        x0 ∈ U)))))) ) := by
  classical
  intro n p i v rK prev a b cross hcrossLinear r u w hD d τ hτ x0 hx0ball hx0form rS hrS U
  by_cases hab : 0 < cross a b
  · have hbcalc : cross b (x0-v) = -(τ * cross a b) := by
      rw [hx0form, (hcrossLinear b).map_smul]
      change τ * cross b a = -(τ * cross a b)
      have hswap : cross b a = -cross a b := by dsimp [cross]; ring
      rw [hswap]
      ring
    have hbneg : cross b (x0-v) < 0 := by rw [hbcalc]; exact neg_neg_of_pos (mul_pos hτ hab)
    simp [U, hab, Metric.mem_ball_self hrS, hx0ball, hbneg]
  · have habneg : cross a b < 0 := by
      have hba : 0 < cross b a := by simpa [u, w, hab] using hD
      have hswap : cross b a = -cross a b := by dsimp [cross]; ring
      rw [hswap] at hba
      linarith
    have hbcalc : cross b (x0-v) = -(τ * cross a b) := by
      rw [hx0form, (hcrossLinear b).map_smul]
      change τ * cross b a = -(τ * cross a b)
      have hswap : cross b a = -cross a b := by dsimp [cross]; ring
      rw [hswap]
      ring
    have hbpos : 0 < cross b (x0-v) := by
      rw [hbcalc]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hτ habneg)
    simp [U, hab, Metric.mem_ball_self hrS, hx0ball, hbpos]

private theorem hplusball :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let d := dist v (p.vertex (i + 1))
        let τ := min (1 / 2) (r / (4 * (d + 1)))
        let x0 := v + τ • a
        let q : Real × Real := (-a.2, a.1)
        ∀ (δ : ℝ), ∀ (s : ℝ), (‖s • q‖ < δ) → (x0 + s • q ∈ Metric.ball x0 δ) ) := by
  classical
  intro n p i v rK prev a r d τ x0 q δ s hsmallNorm
  have hdist : dist (x0 + s • q) x0 = dist (s • q) (0, 0) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    ext <;> simp
  rw [Metric.mem_ball, hdist]
  rw [dist_eq_norm]
  have he : (s • q : Real × Real) - (0, 0) = s • q := by ext <;> simp
  rw [he]
  exact hsmallNorm

private theorem hminusball :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let d := dist v (p.vertex (i + 1))
        let τ := min (1 / 2) (r / (4 * (d + 1)))
        let x0 := v + τ • a
        let q : Real × Real := (-a.2, a.1)
        ∀ (δ : ℝ), ∀ (s : ℝ), (‖s • q‖ < δ) → (x0 - s • q ∈ Metric.ball x0 δ) ) := by
  classical
  intro n p i v rK prev a r d τ x0 q δ s hsmallNorm
  have hdist : dist (x0 - s • q) x0 = dist (-(s • q)) (0, 0) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    ext <;> simp
  rw [Metric.mem_ball, hdist]
  rw [dist_eq_norm]
  have he : (-(s • q) : Real × Real) - (0, 0) = -(s • q) := by ext <;> simp
  rw [he]
  simpa only [norm_neg] using hsmallNorm

private theorem hAminusAt1037 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (∀ z : Real × Real, cross z z = 0) → (
        let d := dist v (p.vertex (i + 1))
        let τ := min (1 / 2) (r / (4 * (d + 1)))
        let x0 := v + τ • a
        let q : Real × Real := (-a.2, a.1)
        ∀ (s : ℝ),
        let ym := x0 - s • q
        cross a (ym-v) = -(s * cross a q))) ) := by
  classical
  intro n p i v rK prev a cross hcrossLinear r hcrossSelf d τ x0 q s ym
  have he : ym-v = τ • a - s • q := by
    ext <;> simp [ym, x0] <;> ring
  calc
    cross a (ym-v) = cross a (τ • a - s • q) := by rw [he]
    _ = cross a (τ • a) - cross a (s • q) := (hcrossLinear a).map_sub _ _
    _ = 0 - s * cross a q := by
      rw [(hcrossLinear a).map_smul, (hcrossLinear a).map_smul, hcrossSelf]
      simp only [smul_eq_mul, mul_zero]
    _ = -(s * cross a q) := by ring

private theorem hOppAt1058 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let d := dist v (p.vertex (i + 1))
        let τ := min (1 / 2) (r / (4 * (d + 1)))
        let x0 := v + τ • a
        ∀ (rS : ℝ), (∃ (s : Bool), ∀ y ∈ Metric.ball x0 rS, y ∈ P3544T1RayParity p ↔ if s = true
            then (0 : ℝ) < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i + (1 : Fin (n + (3
            : ℕ)))), y] else P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i + (1 : Fin (n +
            (3 : ℕ)))), y] < (0 : ℝ)) → (
        let q : Real × Real := (-a.2, a.1)
        let U : Set (Real × Real) := if 0 < cross a b then
          Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | cross b (y-v) < 0}
          else Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | 0 < cross b (y-v)}
        ∀ (s : ℝ),
        let yp := x0 + s • q
        let ym := x0 - s • q
        (yp ∈ U) → ((ym ∈ U) → ((0 < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), yp])
            → ((P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] < 0) → ((yp ∈ O ↔
                ym ∉
            O)))))) ) := by
  classical
  intro n p i O v rK prev a b cross r d τ x0 rS hside q U s yp ym hypU hymU hdetp hdetm
  rcases hside with ⟨sbit, hrule⟩
  have hypS : yp ∈ Metric.ball x0 rS := by
    by_cases hab : 0 < cross a b
    · have ht := hypU
      simp only [U, ite_eq_left hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.1
    · have ht := hypU
      simp only [U, ite_eq_right hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.1
  have hymS : ym ∈ Metric.ball x0 rS := by
    by_cases hab : 0 < cross a b
    · have ht := hymU
      simp only [U, ite_eq_left hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.1
    · have ht := hymU
      simp only [U, ite_eq_right hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.1
  by_cases hsbit : sbit
  · have hpiff := hrule yp hypS
    have hmiff := hrule ym hymS
    have hpiff' : yp ∈ O ↔ 0 < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), yp] := by
      simpa only [O, ite_eq_left hsbit] using hpiff
    have hmiff' : ym ∈ O ↔ 0 < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] := by
      simpa only [O, ite_eq_left hsbit] using hmiff
    have hp : yp ∈ O := hpiff'.mpr hdetp
    have hm : ym ∉ O := by
      intro hm
      have hh := hmiff'.mp hm
      linarith
    simp [hp, hm]
  · have hpiff := hrule yp hypS
    have hmiff := hrule ym hymS
    have hpiff' : yp ∈ O ↔ P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), yp] < 0 := by
      simpa only [O, ite_eq_right hsbit] using hpiff
    have hmiff' : ym ∈ O ↔ P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] < 0 := by
      simpa only [O, ite_eq_right hsbit] using hmiff
    have hp : yp ∉ O := by
      intro hp
      have hh := hpiff'.mp hp
      linarith
    have hm : ym ∈ O := hmiff'.mpr hdetm
    simp [hp, hm]

private theorem hOddEqAt1181 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (0 < cross u w → ∀ x : Real × Real, x ∈ Metric.ball v r → x ∉ C → x ∈ N ∨ x ∈ W) → (((0 : ℝ)
            < cross u w) → (∀ (xN : ℝ × ℝ), ∀ (xW : ℝ × ℝ), (xN ∈ O ↔ xW ∉ O) → ((∀ x, x ∈ N → (x
                ∈ O
            ↔ xN ∈ O)) → ((∀ x, x ∈ W → (x ∈ O ↔ xW ∈ O)) → ((∀ x, x ∈ O → x ∉ C) → ((xN ∈ O) →
            (Metric.ball v r ∩ O = N))))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u w N W hcover hD xN xW hOpp hNconstant hWconstant hOoff hn
  ext x
  constructor
  · rintro ⟨hxb, hxo⟩
    rcases hcover hD x hxb (hOoff x hxo) with hxn | hxw
    · exact hxn
    · have hxwo := (hWconstant x hxw).mp hxo
      exact False.elim ((hOpp.mp hn) hxwo)
  · intro hxn
    have hxo : x ∈ O := (hNconstant x hxn).mpr hn
    exact ⟨hxn.1, hxo⟩

private theorem hEvenEqAt1192 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (∀ x : Real × Real, x ∈ W → x ∉ C) → ((0 < cross u w → ∀ x : Real × Real, x ∈ Metric.ball
            v r
            → x ∉ C → x ∈ N ∨ x ∈ W) → (((0 : ℝ) < cross u w) → (∀ (xN : ℝ × ℝ), ∀ (xW : ℝ × ℝ), (xN
            ∈ O ↔ xW ∉ O) → ((∀ x, x ∈ N → (x ∈ O ↔ xN ∈ O)) → ((∀ x, x ∈ W → (x ∈ O ↔ xW ∈ O)) →
            ((xN ∈ O) → (Metric.ball v r \ (O ∪ C) = W))))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u w N W hWoff hcover hD xN xW hOpp hNconstant hWconstant hn
  ext x
  constructor
  · rintro ⟨hxb, hnot⟩
    have hnotO : x ∉ O := by intro hxo; exact hnot (Or.inl hxo)
    have hnotC : x ∉ C := by intro hxc; exact hnot (Or.inr hxc)
    rcases hcover hD x hxb hnotC with hxn | hxw
    · have hxo := (hNconstant x hxn).mpr hn
      exact False.elim (hnotO hxo)
    · exact hxw
  · intro hxw
    have hnotO : x ∉ O := by
      intro hxo
      have hxwo := (hWconstant x hxw).mp hxo
      exact (hOpp.mp hn) hxwo
    have hnotC := hWoff x hxw
    refine ⟨hxw.1, ?_⟩
    intro hu
    rcases hu with hxo | hxc
    · exact hnotO hxo
    · exact hnotC hxc

private theorem hOddEqAt1218 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (0 < cross u w → ∀ x : Real × Real, x ∈ Metric.ball v r → x ∉ C → x ∈ N ∨ x ∈ W) → (((0 : ℝ)
            < cross u w) → (∀ (xN : ℝ × ℝ), ∀ (xW : ℝ × ℝ), (xN ∈ O ↔ xW ∉ O) → ((∀ x, x ∈ N → (x
                ∈ O
            ↔ xN ∈ O)) → ((∀ x, x ∈ W → (x ∈ O ↔ xW ∈ O)) → ((∀ x, x ∈ O → x ∉ C) → ((xN ∉ O) →
            (Metric.ball v r ∩ O = W))))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u w N W hcover hD xN xW hOpp hNconstant hWconstant hOoff hn
  ext x
  constructor
  · rintro ⟨hxb, hxo⟩
    rcases hcover hD x hxb (hOoff x hxo) with hxn | hxw
    · have hxno := (hNconstant x hxn).mp hxo
      exact False.elim (hn hxno)
    · exact hxw
  · intro hxw
    have hxwo : xW ∈ O := by
      by_contra hnotW
      exact hn (hOpp.mpr hnotW)
    have hxo : x ∈ O := (hWconstant x hxw).mpr hxwo
    exact ⟨hxw.1, hxo⟩

private theorem hEvenEqAt1232 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (∀ x : Real × Real, x ∈ N → x ∉ C) → ((0 < cross u w → ∀ x : Real × Real, x ∈ Metric.ball
            v r
            → x ∉ C → x ∈ N ∨ x ∈ W) → (((0 : ℝ) < cross u w) → (∀ (xN : ℝ × ℝ), ∀ (xW : ℝ × ℝ), (xN
            ∈ O ↔ xW ∉ O) → ((∀ x, x ∈ N → (x ∈ O ↔ xN ∈ O)) → ((∀ x, x ∈ W → (x ∈ O ↔ xW ∈ O)) →
            ((xN ∉ O) → (Metric.ball v r \ (O ∪ C) = N))))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u w N W hNoff hcover hD xN xW hOpp hNconstant hWconstant hn
  ext x
  constructor
  · rintro ⟨hxb, hnot⟩
    have hnotC : x ∉ C := by intro hxc; exact hnot (Or.inr hxc)
    have hnotO : x ∉ O := by intro hxo; exact hnot (Or.inl hxo)
    rcases hcover hD x hxb hnotC with hxn | hxw
    · exact hxn
    · have hxwo : xW ∈ O := by
        by_contra hnotW
        exact hn (hOpp.mpr hnotW)
      have hxo := (hWconstant x hxw).mpr hxwo
      exact False.elim (hnotO hxo)
  · intro hxn
    have hnotO : x ∉ O := by
      intro hxo
      exact hn ((hNconstant x hxn).mp hxo)
    have hnotC := hNoff x hxn
    refine ⟨hxn.1, ?_⟩
    intro hu
    rcases hu with hxo | hxc
    · exact hnotO hxo
    · exact hnotC hxc

private theorem hcneg :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (¬ ∃ c : Real, 0 < c ∧ b = c • a) → (
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        ∀ (c : ℝ), (w = c • u) → ((c ≠ 0) → (c < 0))) ) := by
  classical
  intro n p i v prev a b cross hnoPosMultiple u w c hcw hcne
  have hcnot : ¬0 < c := by
    intro hcpos
    by_cases hab : 0 < cross a b
    · apply hnoPosMultiple ⟨c, hcpos, ?_⟩
      simpa [u, w, hab] using hcw
    · have hcw' : a = c • b := by simpa [u, w, hab] using hcw
      have hrel : b = c⁻¹ • a := by
        have hmul : c⁻¹ * c = (1 : Real) := inv_mul_cancel₀ hcne
        calc
          b = (1 : Real) • b := by simp
          _ = (c⁻¹ * c) • b := by rw [hmul]
          _ = c⁻¹ • (c • b) := by rw [smul_smul]
          _ = c⁻¹ • a := by rw [← hcw']
      exact hnoPosMultiple ⟨c⁻¹, inv_pos.mpr hcpos, hrel⟩
  exact lt_of_le_of_ne (le_of_not_gt hcnot) hcne

private theorem hlineCarrier :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ x z : Real × Real, x ≠ 0 → cross x z = 0 → ∃ c : Real, z = c • x) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t •
            u) ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) → ((u ≠ 0) → (∀ (c : ℝ), (w = c • u) → ((c ≠
            0) → ((c < 0) → (∀ x ∈ Metric.ball v r, cross u (x-v) = 0 → x ∈ C)))))) ) := by
  classical
  intro n p i C v rK prev a b cross hcrosszero r u w hcarrierUW hu0 c hcw hcne hcneg x hx hzero
  obtain ⟨t, hzt⟩ := hcrosszero u (x-v) hu0 hzero
  have hxform : x = v + t • u := by
    calc x = v + (x-v) := by abel
      _ = v + t • u := by rw [hzt]
  by_cases ht : 0 < t
  · exact (hcarrierUW x hx).2 (Or.inr (Or.inl ⟨t, ht, hxform⟩))
  · by_cases ht0 : t = 0
    · rw [ht0, zero_smul] at hxform
      exact (hcarrierUW x hx).2 (Or.inl (by simpa using hxform))
    · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
      have htc : 0 < t / c := div_pos_of_neg_of_neg htneg hcneg
      have hsmul : t • u = (t / c) • w := by
        rw [hcw, smul_smul, div_mul_cancel₀ t hcne]
      rw [hsmul] at hxform
      exact (hcarrierUW x hx).2 (Or.inr (Or.inr ⟨t / c, htc, hxform⟩))

private theorem hcarrierZero :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ x : Real × Real, x ∈ Metric.ball v r → (x ∈ C ↔ x = v ∨ (∃ t : Real, 0 < t ∧ x = v + t •
            u) ∨ (∃ t : Real, 0 < t ∧ x = v + t • w))) → ((∀ z : Real × Real, cross z z = 0) → (∀
                (c : ℝ), (w = c • u) → (∀ x, x ∈ Metric.ball v r → x ∈ C → cross u (x-v) = 0))))
                ) := by
  classical
  intro n p i C v rK prev a b cross hcrossLinear r u w hcarrierUW hcrossSelf c hcw x hx hxc
  rcases (hcarrierUW x hx).mp hxc with hv | hu | hw
  · subst x
    simp [cross]
  · obtain ⟨t, ht, he⟩ := hu
    have he' : x-v = t • u := by rw [he]; abel
    rw [he', (hcrossLinear u).map_smul, hcrossSelf]
    simp
  · obtain ⟨t, ht, he⟩ := hw
    have he' : x-v = t • w := by rw [he]; abel
    rw [he', hcw, (hcrossLinear u).map_smul, (hcrossLinear u).map_smul, hcrossSelf]
    simp

private theorem hqu :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        (a ≠ 0) → ((b ≠ 0) → (
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        0 < cross u qline)) ) := by
  classical
  intro n p i v prev a b ha hb cross u qline
  have hnz : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_cases hpos : 0 < cross a b
    · have hA : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
        by_contra h
        push Not at h
        exact ha (Prod.ext h.1 h.2)
      simpa only [u, ite_eq_left hpos] using hA
    · have hB : b.1 ≠ 0 ∨ b.2 ≠ 0 := by
        by_contra h
        push Not at h
        exact hb (Prod.ext h.1 h.2)
      simpa only [u, ite_eq_right hpos] using hB
  have hcalc : cross u qline = u.1 ^ 2 + u.2 ^ 2 := by
    change u.1 * u.1 - u.2 * (-u.2) = u.1 ^ 2 + u.2 ^ 2
    ring
  rw [hcalc]
  rcases hnz with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg u.2)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg u.1) (sq_pos_of_ne_zero h)

private theorem htranslate :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        ∀ z : Real × Real, z ∈ Metric.ball (0, 0) r → v + z ∈ Metric.ball v r ) := by
  classical
  intro n p i v rK prev r z hz
  have hzero : ((0 : Real), (0 : Real)) = (0 : Real × Real) := by
    ext <;> simp
  have he : dist (v + z) v = dist z (0, 0) := by
    calc
      dist (v + z) v = dist (v + z) (v + (0 : Real × Real)) := by simp
      _ = dist z 0 := dist_add_left v z 0
      _ = dist z (0, 0) := by rw [← hzero]
  rw [Metric.mem_ball, he]
  exact hz

private theorem hxmdet :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        (0 < cross u qline) → (∀ (tm : ℝ), ((0 : ℝ) < tm) → (
        let xm := v + (-tm) • qline
        cross u (xm-v) < 0))) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u qline hqu tm htm xm
  have he : xm-v = (-tm) • qline := by
    dsimp only [xm]
    exact add_sub_cancel_left v ((-tm) • qline)
  have hpos : 0 < tm * cross u qline := mul_pos htm hqu
  calc
    cross u (xm-v) = (-tm) * cross u qline := by
      rw [he, (hcrossLinear u).map_smul, smul_eq_mul]
    _ = -(tm * cross u qline) := by rw [neg_mul]
    _ < 0 := neg_neg_of_pos hpos

private theorem htranslateAt :
    (by
      classical
      exact
        ∀ (x0 : ℝ × ℝ), ∀ (δ : ℝ), ∀ z : Real × Real, z ∈ Metric.ball (0, 0) δ → x0 + z ∈
            Metric.ball
            x0 δ ) := by
  classical
  intro x0 δ z hz
  have hz0 : ((0 : Real), (0 : Real)) = (0 : Real × Real) := by ext <;> simp
  have he : dist (x0 + z) x0 = dist z (0, 0) := by
    calc
      dist (x0 + z) x0 = dist (x0 + z) (x0 + (0 : Real × Real)) := by simp
      _ = dist z 0 := dist_add_left x0 z 0
      _ = dist z (0, 0) := by rw [← hz0]
  rw [Metric.mem_ball, he]
  exact hz

private theorem hOppAt1494 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        ∀ (x0 : ℝ × ℝ), ∀ (rS : ℝ), (∃ (s : Bool), ∀ y ∈ Metric.ball x0 rS, y ∈ P3544T1RayParity p
            ↔ if s = true then (0 : ℝ) < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i + (1
            : Fin (n + (3 : ℕ)))), y] else P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i +
            (1 : Fin (n + (3 : ℕ)))), y] < (0 : ℝ)) → (
        let U : Set (Real × Real) := Metric.ball x0 rS ∩ Metric.ball v r
        ∀ (s : ℝ), ∀ (t : ℝ),
        let yp := x0 + s • qside
        let ym := x0 + t • (-qside)
        (yp ∈ U) → ((ym ∈ U) → ((0 < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), yp])
            → ((P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] < 0) → ((yp ∈ O ↔
                ym ∉
            O)))))) ) := by
  classical
  intro n p i O v rK prev a b cross r u qline qside x0 rS hside U s t yp ym hypU hymU hdetp hdetm
  rcases hside with ⟨sbit, hrule⟩
  have hypS : yp ∈ Metric.ball x0 rS := hypU.1
  have hymS : ym ∈ Metric.ball x0 rS := hymU.1
  by_cases hsbit : sbit
  · have hpiff := hrule yp hypS
    have hmiff := hrule ym hymS
    have hpiff' : yp ∈ O ↔ 0 < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), yp] := by
      simpa only [O, ite_eq_left hsbit] using hpiff
    have hmiff' : ym ∈ O ↔ 0 < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] := by
      simpa only [O, ite_eq_left hsbit] using hmiff
    have hp : yp ∈ O := hpiff'.mpr hdetp
    have hm : ym ∉ O := by intro hm; have hh := hmiff'.mp hm; linarith
    simp [hp, hm]
  · have hpiff := hrule yp hypS
    have hmiff := hrule ym hymS
    have hpiff' : yp ∈ O ↔ P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), yp] < 0 := by
      simpa only [O, ite_eq_right hsbit] using hpiff
    have hmiff' : ym ∈ O ↔ P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] < 0 := by
      simpa only [O, ite_eq_right hsbit] using hmiff
    have hp : yp ∉ O := by intro hp; have hh := hpiff'.mp hp; linarith
    have hm : ym ∈ O := hmiff'.mpr hdetm
    simp [hp, hm]

private theorem hLopp :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        let qline : Real × Real := (-u.2, u.1)
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        (0 < cross u qside ∨ cross u qside < 0) → (∀ (x0 : ℝ × ℝ), ∀ (rS : ℝ),
        let U : Set (Real × Real) := Metric.ball x0 rS ∩ Metric.ball v r
        ∀ (s : ℝ), ((0 : ℝ) < s) → (∀ (t : ℝ), ((0 : ℝ) < t) → (
        let yp := x0 + s • qside
        let ym := x0 + t • (-qside)
        (yp ∈ U) → ((ym ∈ U) → (((yp ∈ O ↔ ym ∉ O)) → ((cross u (yp-v) = s * cross u qside) →
            ((cross
            u (ym-v) = -(t * cross u qside)) → (∃ xP ∈ Lp, ∃ xM ∈ Lm, (xP ∈ O ↔ xM ∉ O))))))))) )
                := by
  classical
  intro n p i O v rK prev a b cross r u Lp Lm qline qside hcrossuQ x0 rS U s hs t ht yp ym hypU
      hymU hOpp hUplus hUminus
  rcases hcrossuQ with huq | huq
  · have hP : yp ∈ Lp := ⟨hypU.2, by rw [hUplus]; exact mul_pos hs huq⟩
    have hM : ym ∈ Lm := ⟨hymU.2, by rw [hUminus]; exact neg_neg_of_pos (mul_pos ht huq)⟩
    exact ⟨yp, hP, ym, hM, hOpp⟩
  · have hP : ym ∈ Lp := ⟨hymU.2, by rw [hUminus]; exact neg_pos.mpr (mul_neg_of_pos_of_neg ht huq)⟩
    have hM : yp ∈ Lm := ⟨hypU.2, by rw [hUplus]; exact mul_neg_of_pos_of_neg hs huq⟩
    have hOpp' : (ym ∈ O ↔ yp ∉ O) := by
      constructor
      · intro hym hyo
        exact (hOpp.mp hyo) hym
      · intro hnp
        by_contra hym
        exact hnp (hOpp.mpr hym)
    exact ⟨ym, hP, yp, hM, hOpp'⟩

private theorem hOddEqAt1554 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        (∀ x ∈ Metric.ball v r, x ∉ C → x ∈ Lp ∨ x ∈ Lm) → (∀ (xP : ℝ × ℝ), ∀ (xM : ℝ × ℝ), (xP ∈
            O ↔
            xM ∉ O) → ((∀ x, x ∈ Lp → (x ∈ O ↔ xP ∈ O)) → ((∀ x, x ∈ Lm → (x ∈ O ↔ xM ∈ O)) → ((∀
                x, x ∈ O → x ∉ C) → ((xP ∈ O) → (Metric.ball v r ∩ O = Lp)))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u Lp Lm hLcover xP xM hOpp hPconstant hMconstant hOoff hn
  ext x
  constructor
  · rintro ⟨hxb, hxo⟩
    rcases hLcover x hxb (hOoff x hxo) with hxp | hxm
    · exact hxp
    · have hxmo := (hMconstant x hxm).mp hxo
      exact False.elim ((hOpp.mp hn) hxmo)
  · intro hxp
    have hxo : x ∈ O := (hPconstant x hxp).mpr hn
    exact ⟨hxp.1, hxo⟩

private theorem hEvenEqAt1565 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        (∀ x, x ∈ Lm → x ∉ C) → ((∀ x ∈ Metric.ball v r, x ∉ C → x ∈ Lp ∨ x ∈ Lm) → (∀ (xP : ℝ ×
            ℝ), ∀ (xM : ℝ × ℝ), (xP ∈ O ↔ xM ∉ O) → ((∀ x, x ∈ Lp → (x ∈ O ↔ xP ∈ O)) → ((∀ x, x
            ∈ Lm →
            (x ∈ O ↔ xM ∈ O)) → ((xP ∈ O) → (Metric.ball v r \ (O ∪ C) = Lm)))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u Lp Lm hLmoff hLcover xP xM hOpp hPconstant hMconstant hn
  ext x
  constructor
  · rintro ⟨hxb, hnot⟩
    have hnotO : x ∉ O := by intro hxo; exact hnot (Or.inl hxo)
    have hnotC : x ∉ C := by intro hxc; exact hnot (Or.inr hxc)
    rcases hLcover x hxb hnotC with hxp | hxm
    · have hxo := (hPconstant x hxp).mpr hn
      exact False.elim (hnotO hxo)
    · exact hxm
  · intro hxm
    have hnotO : x ∉ O := by
      intro hxo
      have hxmo := (hMconstant x hxm).mp hxo
      exact (hOpp.mp hn) hxmo
    have hnotC := hLmoff x hxm
    refine ⟨hxm.1, ?_⟩
    intro hu
    rcases hu with hxo | hxc
    · exact hnotO hxo
    · exact hnotC hxc

private theorem hOddEqAt1591 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        (∀ x ∈ Metric.ball v r, x ∉ C → x ∈ Lp ∨ x ∈ Lm) → (∀ (xP : ℝ × ℝ), ∀ (xM : ℝ × ℝ), (xP ∈
            O ↔
            xM ∉ O) → ((∀ x, x ∈ Lp → (x ∈ O ↔ xP ∈ O)) → ((∀ x, x ∈ Lm → (x ∈ O ↔ xM ∈ O)) → ((∀
                x, x ∈ O → x ∉ C) → ((xP ∉ O) → (Metric.ball v r ∩ O = Lm)))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u Lp Lm hLcover xP xM hOpp hPconstant hMconstant hOoff hn
  ext x
  constructor
  · rintro ⟨hxb, hxo⟩
    rcases hLcover x hxb (hOoff x hxo) with hxp | hxm
    · have hxpo := (hPconstant x hxp).mp hxo
      exact False.elim (hn hxpo)
    · exact hxm
  · intro hxm
    have hxmo : xM ∈ O := by
      by_contra hnotM
      exact hn (hOpp.mpr hnotM)
    have hxo : x ∈ O := (hMconstant x hxm).mpr hxmo
    exact ⟨hxm.1, hxo⟩

private theorem hEvenEqAt1605 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        (∀ x, x ∈ Lp → x ∉ C) → ((∀ x ∈ Metric.ball v r, x ∉ C → x ∈ Lp ∨ x ∈ Lm) → (∀ (xP : ℝ ×
            ℝ), ∀ (xM : ℝ × ℝ), (xP ∈ O ↔ xM ∉ O) → ((∀ x, x ∈ Lp → (x ∈ O ↔ xP ∈ O)) → ((∀ x, x
            ∈ Lm →
            (x ∈ O ↔ xM ∈ O)) → ((xP ∉ O) → (Metric.ball v r \ (O ∪ C) = Lp)))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u Lp Lm hLpoff hLcover xP xM hOpp hPconstant hMconstant hn
  ext x
  constructor
  · rintro ⟨hxb, hnot⟩
    have hnotC : x ∉ C := by intro hxc; exact hnot (Or.inr hxc)
    have hnotO : x ∉ O := by intro hxo; exact hnot (Or.inl hxo)
    rcases hLcover x hxb hnotC with hxp | hxm
    · exact hxp
    · have hxmo : xM ∈ O := by
        by_contra hnotM
        exact hn (hOpp.mpr hnotM)
      have hxo := (hMconstant x hxm).mpr hxmo
      exact False.elim (hnotO hxo)
  · intro hxp
    have hnotO : x ∉ O := by
      intro hxo
      exact hn ((hPconstant x hxp).mp hxo)
    have hnotC := hLpoff x hxp
    refine ⟨hxp.1, ?_⟩
    intro hu
    rcases hu with hxo | hxc
    · exact hnotO hxo
    · exact hnotC hxc

end VertexSectorProof

namespace VertexSectorDetails

private theorem hsegcompact :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ j : Fin (n + 3), IsCompact (segment
            Real (p.vertex j) (p.vertex (j + 1))) ) := by
  classical
  intro n p j
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

private theorem hKcompact :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), (∀ j : Fin (n + 3),
            IsCompact (segment Real (p.vertex j) (p.vertex (j + 1)))) → (
        let J : Set (Fin (n + 3)) := {j | j ≠ i ∧ j + 1 ≠ i}
        let K : Set (Real × Real) := ⋃ j ∈ J,
          segment Real (p.vertex j) (p.vertex (j + 1))
        IsCompact K) ) := by
  classical
  intro n p i hsegcompact J K
  dsimp [K]
  exact (Set.toFinite J).isCompact_biUnion fun j hj => hsegcompact j

private theorem hprev :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (i : Fin (n + 3)),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        prev + 1 = i ) := by
  classical
  intro n i prev
  apply Fin.ext
  simp only [Fin.val_add]
  by_cases h : i.val = 0
  · simp [prev, h]
  · have hiv := i.isLt
    simp only [h, ↓reduceIte, Fin.coe_ofNat_eq_mod, Nat.one_mod, prev]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h), Nat.mod_eq_of_lt hiv]

private theorem hprevne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (i : Fin (n + 3)),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        (prev + 1 = i) → ((∀ j : Fin (n + 3), j + 1 ≠ j) → (prev ≠ i)) ) := by
  classical
  intro n i prev hprev haddne heq
  have : i + 1 = i := by simp [heq] at hprev
  exact haddne i this

private theorem hnextVertex :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        (i + 1 ≠ i) → (p.vertex (i + 1) ≠ v) ) := by
  classical
  intro n p i v hnextne h
  have hi : i + 1 = i := p.injective (by simpa [v] using h)
  exact hnextne hi

private theorem hprevVertex :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        (prev ≠ i) → (p.vertex prev ≠ v) ) := by
  classical
  intro n p i v prev hprevne h
  have hi : prev = i := p.injective (by simpa [v] using h)
  exact hprevne hi

private theorem hcrossLinear :
    (by
      classical
      exact
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        ∀ u : Real × Real, IsLinearMap Real (cross u) ) := by
  classical
  intro cross u
  refine IsLinearMap.mk ?_ ?_
  · intro x y
    simp [cross, mul_add]
    ring
  · intro c x
    simp [cross]
    ring

private theorem hr :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ), ∀ (hrK : rK > (0 : ℝ)),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        (0 < dist v (p.vertex (i + 1))) → ((0 < dist v (p.vertex prev)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        0 < r)) ) := by
  classical
  intro n p i v rK hrK prev hdistA hdistB r
  dsimp [r]
  positivity


private theorem hdistRadial :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (u : Real × Real), ∀ (t : Real), 0 ≤ t → dist (v + t • u) v = t * dist (v + u) v ) := by
  classical
  intro n p i v u t ht
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : v + t • u - v = t • u := by abel
  have h2 : v + u - v = u := by abel
  rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

private theorem hu0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        (a ≠ 0) → ((b ≠ 0) → (
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        u ≠ 0)) ) := by
  classical
  intro n p i v prev a b ha hb cross u
  by_cases hpos : 0 < cross a b
  · simpa only [u, ite_eq_left hpos] using ha
  · simpa only [u, ite_eq_right hpos] using hb

private theorem hw0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        (a ≠ 0) → ((b ≠ 0) → (
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let w := if 0 < cross a b then b else a
        w ≠ 0)) ) := by
  classical
  intro n p i v prev a b ha hb cross w
  by_cases hpos : 0 < cross a b
  · simpa only [w, ite_eq_left hpos] using hb
  · simpa only [w, ite_eq_right hpos] using ha

private theorem hswapuw :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        cross w u = -cross u w ) := by
  classical
  intro n p i v prev a b cross u w
  dsimp [cross]
  ring

private theorem hcrossSelf :
    (by
      classical
      exact
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        ∀ z : Real × Real, cross z z = 0 ) := by
  classical
  intro cross z
  dsimp [cross]
  ring

private theorem hsectorOpp :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let v := p.vertex i
        ∀ (rK : ℝ), (rK > (0 : ℝ)) → (
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        (a ≠ 0) → (
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → ((0 < dist v (p.vertex (i + 1))) → ((0
            < dist v (p.vertex prev)) → (
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (0 < r) → ((∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) →
            ((∀ (u : Real × Real), ∀ (t : Real), 0 ≤ t → dist (v + t • u) v = t * dist (v + u) v)
            → (
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ z : Real × Real, ∀ δ : Real, 0 < δ → ∃ t : Real, 0 < t ∧ t • z ∈ Metric.ball ((0 :
            Real), (0 : Real)) δ) → (
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (∀ z : Real × Real, cross z z = 0) → (0 < cross u w → ∃ xN ∈ N, ∃ xW ∈ W, (xN ∈ O ↔ xW ∉
            O)))))))))))) := by
  classical
  intro n p i O v rK hrK prev a b ha cross hcrossLinear hdistA hdistB r hr hlineMap hdistRadial u
      w hsmallScale N W hcrossSelf hD
  let d := dist v (p.vertex (i + 1))
  let τ := min (1 / 2) (r / (4 * (d + 1)))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτle : τ ≤ r / (4 * (d + 1)) := min_le_right _ _
  have hτlt : τ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let x0 := v + τ • a
  have hx0seg : x0 ∈ openSegment Real v (p.vertex (i + 1)) := by
    have hm := lineMap_mem_openSegment Real v (p.vertex (i + 1))
      (show τ ∈ Set.Ioo 0 1 from ⟨hτ, hτlt⟩)
    rw [hlineMap] at hm
    have he : v + a = p.vertex (i + 1) := by dsimp [a]; abel
    simpa [x0, he] using hm
  have hdistance : dist v x0 = τ * d := by
    have he : v + a = p.vertex (i + 1) := by dsimp [a]; abel
    rw [dist_comm, hdistRadial a τ hτ.le, he, dist_comm]
  have hx0ball : x0 ∈ Metric.ball v r := VertexSectorProof.hx0ballAt924 n p i rK hdistA hr hτle
      hdistance
  have hx0form : x0 - v = τ • a := by dsimp [x0]; abel
  obtain ⟨rS, hrS, hside, _, _⟩ := P3597T1SideCrossing p i x0 hx0seg
  let q : Real × Real := (-a.2, a.1)
  have hqa : 0 < cross a q := VertexSectorProof.hqaAt937 n p i ha
  let U : Set (Real × Real) := if 0 < cross a b then
    Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | cross b (y-v) < 0}
    else Metric.ball x0 rS ∩ Metric.ball v r ∩ {y | 0 < cross b (y-v)}
  have hUopen : IsOpen U := VertexSectorProof.hUopenAt954 n p i rK rS
  have hx0U : x0 ∈ U := VertexSectorProof.hx0UAt970 n p i rK hcrossLinear hD hτ hx0ball hx0form
      rS hrS
  obtain ⟨δ, hδ, hballU⟩ := Metric.isOpen_iff.mp hUopen x0 hx0U
  obtain ⟨s, hs, hsmall⟩ := hsmallScale q δ hδ
  have hsmallNorm : ‖s • q‖ < δ := by
    have hh := hsmall
    rw [Metric.mem_ball, dist_eq_norm] at hh
    have he : (s • q : Real × Real) - (0, 0) = s • q := by ext <;> simp
    rw [he] at hh
    exact hh
  have hplusball : x0 + s • q ∈ Metric.ball x0 δ := VertexSectorProof.hplusball n p i rK δ s
      hsmallNorm
  have hminusball : x0 - s • q ∈ Metric.ball x0 δ := VertexSectorProof.hminusball n p i rK δ s
      hsmallNorm
  let yp := x0 + s • q
  let ym := x0 - s • q
  have hypU : yp ∈ U := hballU (by simpa [yp] using hplusball)
  have hymU : ym ∈ U := hballU (by simpa [ym] using hminusball)
  have hAplus : cross a (yp-v) = s * cross a q := by
    have he : yp-v = τ • a + s • q := by dsimp [yp, x0]; abel
    rw [he, (hcrossLinear a).map_add, (hcrossLinear a).map_smul,
      (hcrossLinear a).map_smul, hcrossSelf]
    simp only [smul_eq_mul, mul_zero, zero_add]
  have hAminus : cross a (ym-v) = -(s * cross a q) := VertexSectorProof.hAminusAt1037 n p i rK
      hcrossLinear hcrossSelf s
  have hdetformula : ∀ y : Real × Real,
      P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), y] = cross a (y-v) := by
    intro y
    simp [P3381T1TriangleDeterminant, cross, a, v]
    ring
  have hdetp : 0 < P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), yp] := by
    rw [hdetformula, hAplus]
    exact mul_pos hs hqa
  have hdetm : P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] < 0 := by
    rw [hdetformula, hAminus]
    exact neg_neg_of_pos (mul_pos hs hqa)
  have hOpp : (yp ∈ O ↔ ym ∉ O) := VertexSectorProof.hOppAt1058 n p i rK rS hside s hypU hymU
      hdetp hdetm
  by_cases hab : 0 < cross a b
  · have hbp : cross b (yp-v) < 0 := by
      have ht := hypU
      simp only [U, ite_eq_left hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.2
    have hbm : cross b (ym-v) < 0 := by
      have ht := hymU
      simp only [U, ite_eq_left hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.2
    have hyball : yp ∈ Metric.ball v r := by
      have ht := hypU
      simp only [U, ite_eq_left hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.2
    have hmball : ym ∈ Metric.ball v r := by
      have ht := hymU
      simp only [U, ite_eq_left hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.2
    have hApluspos : 0 < cross u (yp-v) := by
      rw [show u = a by simp [u, hab], hAplus]
      exact mul_pos hs hqa
    have hAminusneg : cross u (ym-v) < 0 := by
      rw [show u = a by simp [u, hab], hAminus]
      exact neg_neg_of_pos (mul_pos hs hqa)
    have hwp : cross w (yp-v) < 0 := by simpa [w, hab] using hbp
    exact ⟨yp, ⟨hyball, hApluspos, hwp⟩, ym,
      ⟨hmball, Or.inl hAminusneg⟩, hOpp⟩
  · have habneg : cross a b < 0 := by
      have hba : 0 < cross b a := by simpa [u, w, hab] using hD
      have hswap : cross b a = -cross a b := by dsimp [cross]; ring
      rw [hswap] at hba
      linarith
    have hbp : 0 < cross b (yp-v) := by
      have ht := hypU
      simp only [U, ite_eq_right hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.2
    have hbm : 0 < cross b (ym-v) := by
      have ht := hymU
      simp only [U, ite_eq_right hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.2
    have hyball : yp ∈ Metric.ball v r := by
      have ht := hypU
      simp only [U, ite_eq_right hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.2
    have hmball : ym ∈ Metric.ball v r := by
      have ht := hymU
      simp only [U, ite_eq_right hab, Set.mem_inter_iff, Set.mem_ofPred_eq] at ht
      exact ht.1.2
    have hUminus : 0 < cross u (ym-v) := by
      rw [show u = b by simp [u, hab]]
      exact hbm
    have hWplus : 0 < cross w (yp-v) := by
      rw [show w = a by simp [w, hab], hAplus]
      exact mul_pos hs hqa
    have hNside : cross w (ym-v) < 0 := by
      rw [show w = a by simp [w, hab], hAminus]
      exact neg_neg_of_pos (mul_pos hs hqa)
    have hOpp' : (ym ∈ O ↔ yp ∉ O) := by
      constructor
      · intro hym hyo
        exact (hOpp.mp hyo) hym
      · intro hnp
        by_contra hym
        exact hnp (hOpp.mpr hym)
    exact ⟨ym, ⟨hmball, hUminus, hNside⟩, yp,
      ⟨hyball, Or.inr hWplus⟩, hOpp'⟩

private theorem hNconstant :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ S : Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x ∈ S, ∀ y ∈ S, (x ∈ O
            ↔ y ∈ O)) → (
        let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          0 < cross u (x - v) ∧ cross w (x - v) < 0}
        (∀ x : Real × Real, x ∈ N → x ∉ C) → (∀ (xN : ℝ × ℝ), (xN ∈ N) → ((IsPathConnected N) →
            (∀ x, x ∈ N → (x ∈ O ↔ xN ∈ O))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u w hconstOn N hNoff xN hxN hNpath x hx
  exact hconstOn N hNpath.isConnected (fun y hy => hNoff y hy) x hx xN hxN

private theorem hWconstant :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ S : Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x ∈ S, ∀ y ∈ S, (x ∈ O
            ↔ y ∈ O)) → (
        let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
          (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
        (∀ x : Real × Real, x ∈ W → x ∉ C) → (∀ (xW : ℝ × ℝ), (xW ∈ W) → ((IsPathConnected W) →
            (∀ x, x ∈ W → (x ∈ O ↔ xW ∈ O))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u w hconstOn W hWoff xW hxW hWpath x hx
  exact hconstOn W hWpath.isConnected (fun y hy => hWoff y hy) x hx xW hxW

private theorem hOoffAt2413 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        ∀ x, x ∈ O → x ∉ C ) := by
  classical
  intro n p O C x hx
  change x ∉ C ∧ _ at hx
  exact hx.1

private theorem habzero :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (cross u w = (0 : ℝ)) → (cross a b = 0) ) := by
  classical
  intro n p i v prev a b cross u w hDzero
  by_cases hab : 0 < cross a b
  · simpa [u, w, hab] using hDzero
  · have hba : cross b a = 0 := by simpa [u, w, hab] using hDzero
    have hswap : cross b a = -cross a b := by dsimp [cross]; ring
    rw [hswap] at hba
    linarith

private theorem hcne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (w ≠ 0) → (∀ (c : ℝ), (w = c • u) → (c ≠ 0)) ) := by
  classical
  intro n p i v prev a b cross u w hw0 c hcw hc
  rw [hc, zero_smul] at hcw
  exact hw0 hcw

private theorem hLpoff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        (∀ x, x ∈ Metric.ball v r → x ∈ C → cross u (x-v) = 0) → (
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        ∀ x, x ∈ Lp → x ∉ C) ) := by
  classical
  intro n p i C v rK prev a b cross r u hcarrierZero Lp x hx hxc
  change x ∈ Metric.ball v r ∧ 0 < cross u (x-v) at hx
  have hz := hcarrierZero x hx.1 hxc
  exact (lt_irrefl (0 : Real)) (by rw [hz] at hx; exact hx.2)

private theorem hLmoff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        (∀ x, x ∈ Metric.ball v r → x ∈ C → cross u (x-v) = 0) → (
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        ∀ x, x ∈ Lm → x ∉ C) ) := by
  classical
  intro n p i C v rK prev a b cross r u hcarrierZero Lm x hx hxc
  change x ∈ Metric.ball v r ∧ cross u (x-v) < 0 at hx
  have hz := hcarrierZero x hx.1 hxc
  exact (lt_irrefl (0 : Real)) (by rw [hz] at hx; exact hx.2)

private theorem hLcover :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        (∀ x ∈ Metric.ball v r, cross u (x-v) = 0 → x ∈ C) → (
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        ∀ x ∈ Metric.ball v r, x ∉ C → x ∈ Lp ∨ x ∈ Lm) ) := by
  classical
  intro n p i C v rK prev a b cross r u hlineCarrier Lp Lm x hx hxc
  have hne : cross u (x-v) ≠ 0 := by
    intro hzero
    exact hxc (hlineCarrier x hx hzero)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact Or.inr ⟨hx, hneg⟩
  · exact Or.inl ⟨hx, hpos⟩

private theorem hLpconv :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        let HP : Set (Real × Real) := {z | 0 < cross u z}
        (Convex Real ((fun x : Real × Real => x + (-v)) ⁻¹' HP)) → (Convex Real Lp) ) := by
  classical
  intro n p i v rK prev a b cross r u Lp HP hpreP
  change Convex Real (Metric.ball v r ∩ (fun x : Real × Real => x + (-v)) ⁻¹' HP)
  exact (convex_ball v r).inter hpreP

private theorem hLmconv :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        let HM : Set (Real × Real) := {z | cross u z < 0}
        (Convex Real ((fun x : Real × Real => x + (-v)) ⁻¹' HM)) → (Convex Real Lm) ) := by
  classical
  intro n p i v rK prev a b cross r u Lm HM hpreM
  change Convex Real (Metric.ball v r ∩ (fun x : Real × Real => x + (-v)) ⁻¹' HM)
  exact (convex_ball v r).inter hpreM

private theorem hxpdet :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        (0 < cross u qline) → (∀ (tp : ℝ), ((0 : ℝ) < tp) → (
        let xp := v + tp • qline
        0 < cross u (xp-v)))) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u qline hqu tp htp xp
  have he : xp-v = tp • qline := by
    dsimp only [xp]
    exact add_sub_cancel_left v (tp • qline)
  rw [he, (hcrossLinear u).map_smul]
  simp only [smul_eq_mul]
  exact mul_pos htp hqu

private theorem hcrossua :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let w := if 0 < cross a b then b else a
        (∀ z : Real × Real, cross z z = 0) → ((cross u w = (0 : ℝ)) → (cross u a = 0)) ) := by
  classical
  intro n p i v prev a b cross u w hcrossSelf hDzero
  by_cases hpos : 0 < cross a b
  · simpa [u, hpos] using hcrossSelf a
  · have hba : cross b a = 0 := by simpa [u, w, hpos] using hDzero
    simpa [u, hpos] using hba

private theorem hcrossaQ :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        (a ≠ 0) → (
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → ((∀ x z : Real × Real, x ≠ 0 → cross x
            z = 0 → ∃ c : Real, z = c • x) → (
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        (0 < cross u qline) → ((cross u a = 0) → (cross a qline ≠ 0))))) ) := by
  classical
  intro n p i v prev a b ha cross hcrossLinear hcrosszero u qline hqu hcrossua hz
  obtain ⟨c, hc⟩ := hcrosszero a qline ha hz
  have hzero : cross u qline = 0 := by
    rw [hc, (hcrossLinear u).map_smul, hcrossua]
    simp
  exact (ne_of_gt hqu) hzero

private theorem hqaAt2526 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        (cross a qline ≠ 0) → (
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        0 < cross a qside)) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u qline hcrossaQ qside
  by_cases hpos : 0 < cross a qline
  · simp [qside, hpos]
  · have hneg : cross a qline < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hcrossaQ
    rw [show qside = -qline by simp [qside, hpos], (hcrossLinear a).map_neg]
    exact neg_pos.mpr hneg

private theorem hcrossuQ :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        (0 < cross u qline) → (
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        0 < cross u qside ∨ cross u qside < 0)) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u qline hqu qside
  by_cases hpos : 0 < cross a qline
  · left
    simpa [qside, hpos] using hqu
  · right
    have hneg : cross u (-qline) = -cross u qline := (hcrossLinear u).map_neg qline
    rw [show qside = -qline by simp [qside, hpos], hneg]
    exact neg_neg_of_pos hqu

private theorem hx0ballAt2541 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        (0 < r) → (∀ (x0 : ℝ × ℝ), (dist v x0 < r / (2 : ℝ)) → (x0 ∈ Metric.ball v r)) ) := by
  classical
  intro n p i v rK prev r hr x0 hx0dist
  rw [Metric.mem_ball, dist_comm]
  exact lt_of_lt_of_le hx0dist (by linarith)

private theorem hAplusAt2561 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        (∀ z : Real × Real, cross z z = 0) → (
        let qline : Real × Real := (-u.2, u.1)
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        ∀ (x0 : ℝ × ℝ), ∀ (t0 : ℝ), (x0-v = t0 • a) → (∀ (s : ℝ),
        let yp := x0 + s • qside
        cross a (yp-v) = s * cross a qside))) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u hcrossSelf qline qside x0 t0 hx0form s yp
  have he : yp-v = t0 • a + s • qside := by rw [← hx0form]; dsimp [yp]; abel
  rw [he, (hcrossLinear a).map_add, (hcrossLinear a).map_smul,
    (hcrossLinear a).map_smul, hcrossSelf]
  simp only [smul_eq_mul, mul_zero, zero_add]

private theorem hAminusAt2566 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        (∀ z : Real × Real, cross z z = 0) → (
        let qline : Real × Real := (-u.2, u.1)
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        ∀ (x0 : ℝ × ℝ), ∀ (t0 : ℝ), (x0-v = t0 • a) → (∀ (t : ℝ),
        let ym := x0 + t • (-qside)
        cross a (ym-v) = -(t * cross a qside)))) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u hcrossSelf qline qside x0 t0 hx0form t ym
  have he : ym-v = t0 • a + t • (-qside) := by rw [← hx0form]; dsimp [ym]; abel
  rw [he, (hcrossLinear a).map_add, (hcrossLinear a).map_smul,
    (hcrossLinear a).map_smul, hcrossSelf, (hcrossLinear a).map_neg]
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg]

private theorem hdetformulaAt2571 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let a := p.vertex (i + 1) - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        ∀ y : Real × Real, P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), y] = cross
            a (y-v) ) := by
  classical
  intro n p i v a cross y
  simp [P3381T1TriangleDeterminant, cross, a, v]
  ring

private theorem hdetpAt2576 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        (0 < cross a qside) → (∀ (x0 : ℝ × ℝ), ∀ (s : ℝ), ((0 : ℝ) < s) → (
        let yp := x0 + s • qside
        (cross a (yp-v) = s * cross a qside) → ((∀ y : Real × Real, P3381T1TriangleDeterminant
            ![p.vertex i, p.vertex (i+1), y] = cross a (y-v)) → (0 < P3381T1TriangleDeterminant
            ![p.vertex i, p.vertex (i+1), yp])))) ) := by
  classical
  intro n p i v prev a b cross u qline qside hqa x0 s hs yp hAplus hdetformula
  rw [hdetformula, hAplus]
  exact mul_pos hs hqa

private theorem hdetmAt2579 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        (0 < cross a qside) → (∀ (x0 : ℝ × ℝ), ∀ (t : ℝ), ((0 : ℝ) < t) → (
        let ym := x0 + t • (-qside)
        (cross a (ym-v) = -(t * cross a qside)) → ((∀ y : Real × Real,
            P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), y] = cross a (y-v)) →
            (P3381T1TriangleDeterminant ![p.vertex i, p.vertex (i+1), ym] < 0)))) ) := by
  classical
  intro n p i v prev a b cross u qline qside hqa x0 t ht ym hAminus hdetformula
  rw [hdetformula, hAminus]
  exact neg_neg_of_pos (mul_pos ht hqa)

private theorem hUplus :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        (cross u a = 0) → (
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        ∀ (x0 : ℝ × ℝ), ∀ (t0 : ℝ), (x0-v = t0 • a) → (∀ (s : ℝ),
        let yp := x0 + s • qside
        cross u (yp-v) = s * cross u qside))) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u qline hcrossua qside x0 t0 hx0form s yp
  have he : yp-v = t0 • a + s • qside := by rw [← hx0form]; dsimp [yp]; abel
  rw [he, (hcrossLinear u).map_add, (hcrossLinear u).map_smul,
    (hcrossLinear u).map_smul, hcrossua]
  simp only [smul_eq_mul, mul_zero, zero_add]

private theorem hUminusAt2589 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let v := p.vertex i
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        (∀ u : Real × Real, IsLinearMap Real (cross u)) → (
        let u := if 0 < cross a b then a else b
        let qline : Real × Real := (-u.2, u.1)
        (cross u a = 0) → (
        let qside : Real × Real := if 0 < cross a qline then qline else -qline
        ∀ (x0 : ℝ × ℝ), ∀ (t0 : ℝ), (x0-v = t0 • a) → (∀ (t : ℝ),
        let ym := x0 + t • (-qside)
        cross u (ym-v) = -(t * cross u qside)))) ) := by
  classical
  intro n p i v prev a b cross hcrossLinear u qline hcrossua qside x0 t0 hx0form t ym
  have he : ym-v = t0 • a + t • (-qside) := by rw [← hx0form]; dsimp [ym]; abel
  rw [he, (hcrossLinear u).map_add, (hcrossLinear u).map_smul,
    (hcrossLinear u).map_smul, hcrossua, (hcrossLinear u).map_neg]
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg]

private theorem hPconstant :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        (∀ S : Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x ∈ S, ∀ y ∈ S, (x ∈ O
            ↔ y ∈ O)) → (
        let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
        (∀ x, x ∈ Lp → x ∉ C) → ((IsPathConnected Lp) → (∀ (xP : ℝ × ℝ), (xP ∈ Lp) → (∀ x, x ∈ Lp
            → (x ∈ O ↔ xP ∈ O))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u hconstOn Lp hLpoff hLppath xP hxP x hx
  exact hconstOn Lp hLppath.isConnected (fun y hy => hLpoff y hy) x hx xP hxP

private theorem hMconstant :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        let v := p.vertex i
        ∀ (rK : ℝ),
        let prev : Fin (n + 3) :=
          if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
        let a := p.vertex (i + 1) - v
        let b := p.vertex prev - v
        let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
        let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
          (dist v (p.vertex prev) / 2))
        let u := if 0 < cross a b then a else b
        (∀ S : Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x ∈ S, ∀ y ∈ S, (x ∈ O
            ↔ y ∈ O)) → (
        let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
        (∀ x, x ∈ Lm → x ∉ C) → ((IsPathConnected Lm) → (∀ (xM : ℝ × ℝ), (xM ∈ Lm) → (∀ x, x ∈ Lm
            → (x ∈ O ↔ xM ∈ O))))) ) := by
  classical
  intro n p i O C v rK prev a b cross r u hconstOn Lm hLmoff hLmpath xM hxM x hx
  exact hconstOn Lm hLmpath.isConnected (fun y hy => hLmoff y hy) x hx xM hxM

end VertexSectorDetails

theorem P3597T1VertexSectors {n : Nat} (p : P3381T1PolygonBoundary n)
    (i : Fin (n + 3)) :
    ∃ r : Real, 0 < r ∧
      IsPathConnected (Metric.ball (p.vertex i) r ∩ P3544T1RayParity p) ∧
      IsPathConnected (Metric.ball (p.vertex i) r \
        (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p)) ∧
      p.vertex i ∈ closure (P3544T1RayParity p) ∧
      p.vertex i ∈ closure
        (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p)ᶜ := by
-- BODY
  classical
  let O := P3544T1RayParity p
  let C := P3544T1BoundaryCarrier p
  let v := p.vertex i
  let J : Set (Fin (n + 3)) := {j | j ≠ i ∧ j + 1 ≠ i}
  let K : Set (Real × Real) := ⋃ j ∈ J,
    segment Real (p.vertex j) (p.vertex (j + 1))
  have hvKopen : IsOpen Kᶜ := (VertexSectorDetails.hKcompact n p i
      (VertexSectorDetails.hsegcompact n p)).isClosed.isOpen_compl
  obtain ⟨rK, hrK, hballK⟩ := Metric.isOpen_iff.mp hvKopen v (VertexSectorProof.hvnot n p i)
  let prev : Fin (n + 3) :=
    if i.val = 0 then ⟨n + 2, by omega⟩ else ⟨i.val - 1, by omega⟩
  have hprev := VertexSectorDetails.hprev n i
  have haddne : ∀ j : Fin (n + 3), j + 1 ≠ j := VertexSectorProof.haddne n
  have hprevne := VertexSectorDetails.hprevne n i hprev haddne
  have hnextne : i + 1 ≠ i := haddne i
  have hnextVertex := VertexSectorDetails.hnextVertex n p i hnextne
  have hprevVertex := VertexSectorDetails.hprevVertex n p i hprevne
  let a := p.vertex (i + 1) - v
  let b := p.vertex prev - v
  have ha : a ≠ 0 := sub_ne_zero.mpr hnextVertex
  have hb : b ≠ 0 := sub_ne_zero.mpr hprevVertex
  let cross (u z : Real × Real) : Real := u.1 * z.2 - u.2 * z.1
  have hcrossLinear := VertexSectorDetails.hcrossLinear
  have hcrosszero : ∀ x z : Real × Real, x ≠ 0 → cross x z = 0 →
      ∃ c : Real, z = c • x := VertexSectorProof.hcrosszero
  have hdistA : 0 < dist v (p.vertex (i + 1)) := dist_pos.mpr hnextVertex.symm
  have hdistB : 0 < dist v (p.vertex prev) := dist_pos.mpr hprevVertex.symm
  let r := min rK (min (dist v (p.vertex (i + 1)) / 2)
    (dist v (p.vertex prev) / 2))
  have hr := VertexSectorDetails.hr n p i rK hrK hdistA hdistB
  have hrKle : r ≤ rK := min_le_left _ _
  have hrAle : r ≤ dist v (p.vertex (i + 1)) / 2 := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hrBle : r ≤ dist v (p.vertex prev) / 2 := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hlineMap := AffineLineMapProperties.coordinates
  have hsegA := VertexSectorProof.hsegA n p i hlineMap
  have hdistRadial := VertexSectorDetails.hdistRadial n p i
  have hnoPosMultiple := VertexSectorProof.hnoPosMultiple n p i
      hprev hprevne hnextVertex hlineMap
  have happroach := VertexSectorProof.happroach n p i hdistA hlineMap hdistRadial
  have hvOdd := VertexSectorProof.hvOdd n p i happroach
  have hvEven := VertexSectorProof.hvEven n p i happroach
  let u := if 0 < cross a b then a else b
  let w := if 0 < cross a b then b else a
  have hdetuw := VertexSectorProof.hdetuw n p i
  have hcarrierUW := VertexSectorProof.hcarrierUW n p i rK
            (VertexSectorProof.hcarrierRays n p i rK (VertexSectorProof.hcarrierLocal n p i rK
            hballK hprev (VertexSectorProof.haddinj n) hrKle) hsegA (VertexSectorProof.hsegB n
            p i hlineMap) (VertexSectorProof.hRayA n p i rK hdistA hrAle hlineMap hdistRadial)
            (VertexSectorProof.hRayB n p i rK hdistB hrBle hlineMap hdistRadial))
  have hconstOn := VertexSectorProof.hconstOn n p
          (VertexSectorProof.hlocal n p (VertexSectorProof.hgeneric n p)
              (VertexSectorProof.hparity n p))
  have hsmallScale := VertexSectorProof.hsmallScale
  let N : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
    0 < cross u (x - v) ∧ cross w (x - v) < 0}
  let W : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧
    (cross u (x - v) < 0 ∨ 0 < cross w (x - v))}
  have hNandW := VertexSectorProof.hNandW
      n p i rK hcrossLinear hr hsmallScale
  have hu0 := VertexSectorDetails.hu0 n p i ha hb
  have hw0 := VertexSectorDetails.hw0 n p i ha hb
  have hswapuw := VertexSectorDetails.hswapuw n p i
  have hcrossSelf := VertexSectorDetails.hcrossSelf
  have hNoff := VertexSectorProof.hNoff n p i rK hcrossLinear
      hcarrierUW hcrossSelf
  have hWoff := VertexSectorProof.hWoff n p i rK hcrossLinear
      hdetuw hcarrierUW hswapuw hcrossSelf
  have hcover := VertexSectorProof.hcover n p i rK
          (VertexSectorProof.hzeroUNegW n p i rK hcrossLinear hcrosszero hcarrierUW hu0 hswapuw)
          (VertexSectorProof.hzeroWPosU n p i rK hcrossLinear hcrosszero hcarrierUW hw0)
              (VertexSectorProof.hzeroBoth n p i rK hcrossLinear hcrosszero hcarrierUW hu0 hswapuw)
  rcases hdetuw with hD | hDzero
  · obtain ⟨xN, hxN, xW, hxW, hOpp⟩ := (VertexSectorDetails.hsectorOpp n p i rK hrK ha
      hcrossLinear hdistA hdistB hr hlineMap hdistRadial hsmallScale hcrossSelf) hD
    have hNpath := (hNandW hD).1
    have hWpath := (hNandW hD).2
    have hNconstant := VertexSectorDetails.hNconstant n p i rK
        hconstOn hNoff xN hxN hNpath
    have hWconstant := VertexSectorDetails.hWconstant n p i rK
        hconstOn hWoff xW hxW hWpath
    have hOoff := VertexSectorDetails.hOoffAt2413 n p
    by_cases hn : xN ∈ O
    · have hOddEq : Metric.ball v r ∩ O = N := VertexSectorProof.hOddEqAt1181 n p i rK hcover hD
        xN xW hOpp hNconstant hWconstant hOoff hn
      have hEvenEq : Metric.ball v r \ (O ∪ C) = W := VertexSectorProof.hEvenEqAt1192 n p i rK
          hWoff hcover hD xN xW hOpp hNconstant hWconstant hn
      refine ⟨r, hr, ?_, ?_, hvOdd, hvEven⟩
      · rw [hOddEq]
        exact hNpath
      · rw [hEvenEq]
        exact hWpath
    · have hOddEq : Metric.ball v r ∩ O = W := VertexSectorProof.hOddEqAt1218 n p i rK hcover hD
        xN xW hOpp hNconstant hWconstant hOoff hn
      have hEvenEq : Metric.ball v r \ (O ∪ C) = N := VertexSectorProof.hEvenEqAt1232 n p i rK
          hNoff hcover hD xN xW hOpp hNconstant hWconstant hn
      refine ⟨r, hr, ?_, ?_, hvOdd, hvEven⟩
      · rw [hOddEq]
        exact hWpath
      · rw [hEvenEq]
        exact hNpath
  · have habzero : cross a b = 0 := VertexSectorDetails.habzero n p i hDzero
    obtain ⟨c, hcw⟩ := hcrosszero u w hu0 hDzero
    have hcne := VertexSectorDetails.hcne n p i hw0 c hcw
    have hcarrierZero := VertexSectorProof.hcarrierZero n p i rK hcrossLinear hcarrierUW
            hcrossSelf c hcw
    let Lp : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ 0 < cross u (x-v)}
    let Lm : Set (Real × Real) := {x | x ∈ Metric.ball v r ∧ cross u (x-v) < 0}
    have hLpoff := VertexSectorDetails.hLpoff n p i rK hcarrierZero
    have hLmoff := VertexSectorDetails.hLmoff n p i rK hcarrierZero
    have hLcover := VertexSectorDetails.hLcover
        n p i rK (VertexSectorProof.hlineCarrier n p i rK hcrosszero hcarrierUW hu0 c hcw hcne
            (VertexSectorProof.hcneg n p i hnoPosMultiple c hcw hcne))
    let HP : Set (Real × Real) := {z | 0 < cross u z}
    let HM : Set (Real × Real) := {z | cross u z < 0}
    have hconvP : Convex Real HP := convex_halfSpace_gt (hcrossLinear u) 0
    have hconvM : Convex Real HM := convex_halfSpace_lt (hcrossLinear u) 0
    have hpreP : Convex Real ((fun x : Real × Real => x + (-v)) ⁻¹' HP) :=
      hconvP.translate_preimage_left (-v)
    have hpreM : Convex Real ((fun x : Real × Real => x + (-v)) ⁻¹' HM) :=
      hconvM.translate_preimage_left (-v)
    let qline : Real × Real := (-u.2, u.1)
    have hqu : 0 < cross u qline := VertexSectorProof.hqu n p i ha hb
    obtain ⟨tp, htp, htpball⟩ := hsmallScale qline r hr
    obtain ⟨tm, htm, htmball⟩ := hsmallScale (-qline) r hr
    have htranslate : ∀ z : Real × Real, z ∈ Metric.ball (0, 0) r →
        v + z ∈ Metric.ball v r := VertexSectorProof.htranslate n p i rK
    let xp := v + tp • qline
    let xm := v + (-tm) • qline
    have hxpball : xp ∈ Metric.ball v r := by
      exact htranslate (tp • qline) htpball
    have hxmball : xm ∈ Metric.ball v r := by
      exact htranslate ((-tm) • qline) (by simpa using htmball)
    have hxpLp : xp ∈ Lp := ⟨hxpball, (VertexSectorDetails.hxpdet n p i hcrossLinear hqu tp htp)⟩
    have hxmLm : xm ∈ Lm := ⟨hxmball, (VertexSectorProof.hxmdet n p i hcrossLinear hqu tm htm)⟩
    have hLppath : IsPathConnected Lp := (VertexSectorDetails.hLpconv n p i rK
        hpreP).isPathConnected ⟨xp, hxpLp⟩
    have hLmpath : IsPathConnected Lm := (VertexSectorDetails.hLmconv n p i rK
        hpreM).isPathConnected ⟨xm, hxmLm⟩
    have hcrossua := VertexSectorDetails.hcrossua n p i hcrossSelf hDzero
    let qside : Real × Real := if 0 < cross a qline then qline else -qline
    have hqa := VertexSectorDetails.hqaAt2526 n p i hcrossLinear
        (VertexSectorDetails.hcrossaQ n p i ha hcrossLinear hcrosszero hqu hcrossua)
    obtain ⟨x0, hx0open, hx0dist⟩ := happroach r hr
    have hx0seg : x0 ∈ segment Real v (p.vertex (i+1)) :=
      openSegment_subset_segment Real v (p.vertex (i+1)) hx0open
    obtain ⟨t0, ht0, hx0eq⟩ := (hsegA x0).mp hx0seg
    have hx0form : x0-v = t0 • a := by rw [hx0eq]; abel
    obtain ⟨rS, hrS, hside, _, _⟩ := P3597T1SideCrossing p i x0 hx0open
    let U : Set (Real × Real) := Metric.ball x0 rS ∩ Metric.ball v r
    have hx0U : x0 ∈ U := ⟨Metric.mem_ball_self hrS, (VertexSectorDetails.hx0ballAt2541 n p i rK
        hr x0 hx0dist)⟩
    obtain ⟨δ, hδ, hballU⟩ := Metric.isOpen_iff.mp (Metric.isOpen_ball.inter Metric.isOpen_ball)
        x0 hx0U
    obtain ⟨s, hs, hsmall⟩ := hsmallScale qside δ hδ
    obtain ⟨t, ht, hsmallNeg⟩ := hsmallScale (-qside) δ hδ
    have htranslateAt := VertexSectorProof.htranslateAt x0 δ
    let yp := x0 + s • qside
    let ym := x0 + t • (-qside)
    have hypU : yp ∈ U := hballU (by simpa [yp] using htranslateAt (s • qside) hsmall)
    have hymU : ym ∈ U := hballU (by simpa [ym] using htranslateAt (t • (-qside)) hsmallNeg)
    have hdetformula := VertexSectorDetails.hdetformulaAt2571 n p i
    have hOpp : (yp ∈ O ↔ ym ∉ O) := VertexSectorProof.hOppAt1494 n p i rK x0 rS hside s t hypU
        hymU (VertexSectorDetails.hdetpAt2576 n p i hqa x0 s hs (VertexSectorDetails.hAplusAt2561
            n p i hcrossLinear hcrossSelf x0 t0 hx0form s) hdetformula)
            (VertexSectorDetails.hdetmAt2579 n p i hqa x0 t ht (VertexSectorDetails.hAminusAt2566
            n p i hcrossLinear hcrossSelf x0 t0 hx0form t) hdetformula)
    obtain ⟨xP, hxP, xM, hxM, hOpp⟩ := (VertexSectorProof.hLopp n p i rK
        (VertexSectorDetails.hcrossuQ n p i hcrossLinear hqu) x0 rS s hs t ht hypU hymU hOpp
        (VertexSectorDetails.hUplus n p i hcrossLinear hcrossua x0 t0 hx0form s)
        (VertexSectorDetails.hUminusAt2589 n p i hcrossLinear hcrossua x0 t0 hx0form t))
    have hPconstant := VertexSectorDetails.hPconstant n p i rK
        hconstOn hLpoff hLppath xP hxP
    have hMconstant := VertexSectorDetails.hMconstant n p i rK
        hconstOn hLmoff hLmpath xM hxM
    have hOoff := VertexSectorDetails.hOoffAt2413 n p
    by_cases hn : xP ∈ O
    · have hOddEq : Metric.ball v r ∩ O = Lp := VertexSectorProof.hOddEqAt1554 n p i rK hLcover
        xP xM hOpp hPconstant hMconstant hOoff hn
      have hEvenEq : Metric.ball v r \ (O ∪ C) = Lm := VertexSectorProof.hEvenEqAt1565 n p i rK
          hLmoff hLcover xP xM hOpp hPconstant hMconstant hn
      refine ⟨r, hr, ?_, ?_, hvOdd, hvEven⟩
      · rw [hOddEq]
        exact hLppath
      · rw [hEvenEq]
        exact hLmpath
    · have hOddEq : Metric.ball v r ∩ O = Lm := VertexSectorProof.hOddEqAt1591 n p i rK hLcover
        xP xM hOpp hPconstant hMconstant hOoff hn
      have hEvenEq : Metric.ball v r \ (O ∪ C) = Lp := VertexSectorProof.hEvenEqAt1605 n p i rK
          hLpoff hLcover xP xM hOpp hPconstant hMconstant hn
      refine ⟨r, hr, ?_, ?_, hvOdd, hvEven⟩
      · rw [hOddEq]
        exact hLmpath
      · rw [hEvenEq]
        exact hLppath

end ApollonianSuperharmonic

end
