/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Order.Interval.Set.Infinite

public import LeanPool.ApollonianSuperharmonic.P3650T1ExposedCorner
public import LeanPool.ApollonianSuperharmonic.P3544T1LocalParity

-- [TABLET NODE: P3650T1ExposedCornerExists]

/-!
# P3650T1ExposedCornerExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ExposedCornerGeometry

private theorem hdistinct :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        (q ∉ Set.range f) → (
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        Function.Injective (ell ∘ v))) := by
  classical
  intro n p v f hqexists q hq ell i j hij
  have heq : (v i).1 + q * (v i).2 = (v j).1 + q * (v j).2 := hij
  have hy : (v i).2 = (v j).2 := by
    by_contra hne
    have hden : (v i).2 - (v j).2 ≠ 0 := sub_ne_zero.mpr hne
    have hratio : q = ((v j).1 - (v i).1) / ((v i).2 - (v j).2) := by
      apply (eq_div_iff hden).2
      nlinarith [heq]
    apply hq
    exact ⟨(i, j), by simp [f, v, hratio]⟩
  have hx : (v i).1 = (v j).1 := by rw [hy] at heq; linarith
  exact p.injective (Prod.ext hx hy)

private theorem hstrict :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        (Function.Injective (ell ∘ v)) → (∀ (b : Fin (n + (3 : ℕ))), (∀ x' ∈ Finset.univ, (ell :
            ℝ × ℝ → ℝ) (v x') ≤ (ell : ℝ × ℝ → ℝ) (v b)) → (∀ i : Fin (n + 3), i ≠ b → ell (v i)
            < ell (v b))) ) := by
  classical
  intro n p v f hqexists q ell hdistinct b hmax i hib
  have hle := hmax i (Finset.mem_univ i)
  exact lt_of_le_of_ne hle (fun heq => hib (hdistinct heq))

private theorem hnextne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (b : Fin (n + (3 : ℕ))), b + 1 ≠ b ) := by
  classical
  intro n b h
  have hv := congrArg Fin.val h
  simp only [Fin.val_add, Fin.val_one] at hv
  by_cases hlt : b.val + 1 < n + 3
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : b.val + 1 = n + 3 := by omega
    rw [heq] at hv
    simp at hv
    omega

private theorem hprevne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (b : Fin (n + (3 : ℕ))), (b - 1 + 1 = b) → ((b + 1 ≠ b) → (b - 1 ≠ b)) )
            := by
  classical
  intro n b hprev hnextne heq
  have hh := congrArg (fun j : Fin (n + 3) => j + 1) heq
  rw [hprev] at hh
  exact hnextne hh.symm

private theorem haB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))), (b - 1 ≠ b) → (
        let B := v b
        let a := v (b - 1)
        a ≠ B) ) := by
  classical
  intro n p v b hprevne B a heq
  exact hprevne (p.injective (by simpa [a, B, v] using heq))

private theorem hcB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))), (b + 1 ≠ b) → (
        let B := v b
        let c := v (b + 1)
        c ≠ B) ) := by
  classical
  intro n p v b hnextne B c heq
  exact hnextne (p.injective (by simpa [c, B, v] using heq))

private theorem hellu :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        (∀ i : Fin (n + 3), i ≠ b → ell (v i) < ell (v b)) → ((b - 1 ≠ b) → (
        let B := v b
        let a := v (b - 1)
        let u : Real × Real := a - B
        ell u < 0)) ) := by
  classical
  intro n p v f hqexists q b ell hstrict hprevne B a u
  have hh := hstrict (b - 1) hprevne
  calc
    ell u = ell (a - B) := rfl
    _ = ell a - ell B := map_sub ell a B
    _ < 0 := by simpa [a, B, v] using hh

private theorem hellw :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let c := v (b + 1)
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        (∀ i : Fin (n + 3), i ≠ b → ell (v i) < ell (v b)) → ((b + 1 ≠ b) → (
        let B := v b
        let w : Real × Real := c - B
        ell w < 0)) ) := by
  classical
  intro n p v f hqexists q b c ell hstrict hnextne B w
  have hh := hstrict (b + 1) hnextne
  calc
    ell w = ell (c - B) := rfl
    _ = ell c - ell B := map_sub ell c B
    _ < 0 := by simpa [c, B, v] using hh


private theorem hcrosszero :
    (by
      classical
      exact
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ x y : Real × Real, x ≠ 0 → cross x y = 0 → ∃ t : Real, y = t • x ) := by
  classical
  intro cross x y hx hxy
  by_cases hx1 : x.1 = 0
  · have hx2 : x.2 ≠ 0 := by
      intro h
      apply hx
      exact Prod.ext hx1 h
    have hy1 : y.1 = 0 := by
      dsimp [cross] at hxy
      rw [hx1] at hxy
      have hprod : x.2 * y.1 = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with h | h
      · exact (hx2 h).elim
      · exact h
    refine ⟨y.2 / x.2, ?_⟩
    ext
    · simp [hx1, hy1]
    · simp
      field_simp
  · refine ⟨y.1 / x.1, ?_⟩
    have hdet : x.1 * y.2 = x.2 * y.1 := by
      dsimp [cross] at hxy
      linarith
    ext
    · simp
      field_simp
    · simp
      field_simp
      nlinarith [hdet]

private theorem hdetAt218 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let c := v (b + 1)
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        (b - 1 + 1 = b) → ((b - 1 ≠ b) → (
        let B := v b
        let a := v (b - 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        (u ≠ 0) → ((w ≠ 0) → ((ell u < 0) → ((ell w < 0) → ((∀ x y : Real × Real, ∀ t : Real,
            AffineMap.lineMap x y t = x + t • (y - x)) → (
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (∀ x y : Real × Real, x ≠ 0 → cross x y = 0 → ∃ t : Real, y = t • x) → (cross u w ≠
            0)))))))) ) := by
  classical
  intro n p v f hqexists q b c ell hprev hprevne B a u w hu hw hellu hellw hlineMap cross
      hcrosszero hzero
  obtain ⟨t, htw⟩ := hcrosszero u w hu hzero
  have hmap : ell w = t * ell u := by
    rw [htw, map_smul]
    simp only [smul_eq_mul]
  have htpos : 0 < t := by nlinarith [hellu, hellw, hmap]
  let s := 1 / (2 * t + 2)
  have hs : 0 < s := by dsimp [s]; positivity
  have hts : 0 < t * s := mul_pos htpos hs
  have htslt : t * s < 1 := by
    dsimp [s]
    have hden : 0 < 2 * t + 2 := by positivity
    rw [show t * (1 / (2 * t + 2)) = t / (2 * t + 2) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hslt : s < 1 := by
    dsimp [s]
    have hden : 0 < 2 * t + 2 := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith
  let z : Real × Real := B + s • w
  have hzw : z = B + (t * s) • u := by
    dsimp [z]
    rw [htw, smul_smul]
    congr 1
    ring
  have hseg₁ : z ∈ segment Real B c := by
    have hh := lineMap_mem_segment Real B c (show s ∈ Set.Icc 0 1 from ⟨hs.le, hslt.le⟩)
    rw [hlineMap] at hh
    simpa [z, w, c, B] using hh
  have hseg₂ : z ∈ segment Real B a := by
    have hh := lineMap_mem_segment Real B a
      (show t * s ∈ Set.Icc 0 1 from ⟨hts.le, htslt.le⟩)
    rw [hlineMap] at hh
    rw [hzw]
    simpa [u] using hh
  have hinter : z ∈ segment Real a B ∩ segment Real B c := by
    have hseg₂' : z ∈ segment Real a B := by
      rw [← segment_symm Real B a]
      exact hseg₂
    exact ⟨hseg₂', hseg₁⟩
  have hlaw := p.edge_intersection (b - 1) b hprevne
  have hinter' : z ∈ segment Real (v (b - 1)) (v ((b - 1) + 1)) ∩
      segment Real (v b) (v (b + 1)) := by
    simpa [a, B, c, v, hprev] using hinter
  rw [hlaw] at hinter'
  have hend : (z = a ∨ z = B) ∧ (z = B ∨ z = c) := by
    simpa [a, B, c, v, hprev] using hinter'
  have hzneB : z ≠ B := by
    intro hz
    have hmul : s • w = 0 := by
      have hh := congrArg (fun x : Real × Real => x - B) hz
      simpa [z] using hh
    rcases (smul_eq_zero.mp hmul) with hs0 | hw0
    · exact (ne_of_gt hs) hs0
    · exact hw hw0
  have hzneC : z ≠ c := by
    intro hz
    have hmul : (s - 1) • w = 0 := by
      have hh := congrArg (fun x : Real × Real => x - B) hz
      have hh' : s • w = w := by simpa [z, c, w, B] using hh
      calc
        (s - 1) • w = s • w - 1 • w := sub_smul s 1 w
        _ = w - w := by rw [hh', one_smul]
        _ = 0 := sub_self _
    rcases (smul_eq_zero.mp hmul) with hs1 | hw0
    · linarith [hslt]
    · exact hw hw0
  rcases hend.2 with hzB | hzC
  · exact hzneB hzB
  · exact hzneC hzC

private theorem htriangle :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (cross u w ≠ 0) → (P3381T1TriangleDeterminant ![a, B, c] ≠ 0) ) := by
  classical
  intro n p v b B a c u w cross hdet hz
  have hrel : cross u w =
      -P3381T1TriangleDeterminant ![a, B, c] := by
    simp [P3381T1TriangleDeterminant, cross, u, w, a, B, c]
    ring
  have hz' : cross u w = 0 := by
    rw [hrel]
    have hzero : P3381T1TriangleDeterminant ![a, B, c] = 0 := by
      simpa [P3381T1TriangleDeterminant] using hz
    rw [hzero]
    ring
  exact hdet hz'

private theorem hD :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (P3381T1TriangleDeterminant ![a, B, c] ≠ 0) → (
        let D := cross (c - a) (B - a)
        D ≠ 0) ) := by
  classical
  intro n p v b B a c cross htriangle D hzero
  apply htriangle
  have hrel : P3381T1TriangleDeterminant ![a, B, c] = -D := by
    simp [P3381T1TriangleDeterminant, D, cross, a, B, c]
    ring
  rw [hrel, hzero]
  simp

private theorem hFaff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let D := cross (c - a) (B - a)
        let L : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => cross (c - a) x * D⁻¹
            map_add' := by intro x y; simp [cross]; ring
            map_smul' := by intro t x; simp [cross]; ring }
        let F : (Real × Real) → Real := fun x => L (x - a)
        ∀ x : Real × Real, F x = L (x -ᵥ a) +ᵥ F a ) := by
  classical
  intro n p v b B a c cross D L F x
  simp [F]

private theorem hFc :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let D := cross (c - a) (B - a)
        let L : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => cross (c - a) x * D⁻¹
            map_add' := by intro x y; simp [cross]; ring
            map_smul' := by intro t x; simp [cross]; ring }
        let F : (Real × Real) → Real := fun x => L (x - a)
        F c = 0 ) := by
  classical
  intro n p v b B a c cross D L F
  simp only [Prod.fst_sub, Prod.snd_sub, LinearMap.coe_mk, AddHom.coe_mk, mul_eq_zero,
      inv_eq_zero, F, L, cross]
  left
  ring

private theorem hFB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let D := cross (c - a) (B - a)
        (D ≠ 0) → (
        let L : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => cross (c - a) x * D⁻¹
            map_add' := by intro x y; simp [cross]; ring
            map_smul' := by intro t x; simp [cross]; ring }
        let F : (Real × Real) → Real := fun x => L (x - a)
        F B = 1)) := by
  classical
  intro n p v b B a c cross D hD L F
  dsimp [F, L, D]
  rw [mul_inv_cancel₀ hD]

private theorem hsegcompact :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ j : Fin (n + 3), IsCompact (segment Real (v j) (v (j + 1))) ) := by
  classical
  intro n p v j
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

private theorem hKcompact :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))), (∀ j : Fin (n + 3), IsCompact (segment Real (v j) (v (j +
            1)))) → (
        let J : Set (Fin (n + 3)) := {j | j ≠ b ∧ j + 1 ≠ b}
        let K : Set (Real × Real) := ⋃ j ∈ J,
          segment Real (v j) (v (j + 1))
        IsCompact K) ) := by
  classical
  intro n p v b hsegcompact J K
  dsimp [K]
  exact (Set.toFinite J).isCompact_biUnion fun j hj => hsegcompact j

private theorem hBnotK :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let J : Set (Fin (n + 3)) := {j | j ≠ b ∧ j + 1 ≠ b}
        let K : Set (Real × Real) := ⋃ j ∈ J,
          segment Real (v j) (v (j + 1))
        B ∉ K ) := by
  classical
  intro n p v b B J K hBK
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hBK
  obtain ⟨hjJ, hBj⟩ := Set.mem_iUnion.mp hj
  have hleft : B ∈ segment Real (v b) (v (b + 1)) := by
    exact left_mem_segment Real _ _
  have hinter : B ∈ segment Real (v b) (v (b + 1)) ∩
      segment Real (v j) (v (j + 1)) := ⟨hleft, hBj⟩
  rw [p.edge_intersection b j hjJ.1.symm] at hinter
  have hend : (B = v b ∨ B = v (b + 1)) ∧
      (B = v j ∨ B = v (j + 1)) := by simpa using hinter
  rcases hend.2 with hj0 | hj1
  · have heq : b = j := p.injective (by simpa [B, v] using hj0)
    exact hjJ.1 heq.symm
  · have heq : b = j + 1 := p.injective (by simpa [B, v] using hj1)
    exact hjJ.2 heq.symm

private theorem haddinj :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ x y : Fin (n + 3), x + 1 = y + 1 → x = y ) := by
  classical
  intro n x y hxy
  exact add_right_cancel hxy

private theorem hcarrierLocal :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))), (b - 1 + 1 = b) → (
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let C := P3544T1BoundaryCarrier p
        let J : Set (Fin (n + 3)) := {j | j ≠ b ∧ j + 1 ≠ b}
        let K : Set (Real × Real) := ⋃ j ∈ J,
          segment Real (v j) (v (j + 1))
        ∀ (rK : ℝ), (Metric.ball B rK ⊆ Kᶜ) → (
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (r ≤ rK) → ((∀ x y : Fin (n + 3), x + 1 = y + 1 → x = y) → (∀ x : Real × Real, x ∈
            Metric.ball B r → (x ∈ C ↔ x ∈ segment Real B c ∨ x ∈ segment Real a B))))) ) := by
  classical
  intro n p v b hprev B a c C J K rK hballK r hrKle haddinj x hx
  constructor
  · intro hxC
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxC
    by_cases hjb : j = b
    · left
      simpa [hjb, B, c, v] using hj
    · by_cases hjnext : j + 1 = b
      · have hjprev : j = b - 1 := by
          apply haddinj
          rw [hjnext, hprev]
        right
        simpa [hjprev, a, B, v, hprev] using hj
      · have hjJ : j ∈ J := ⟨hjb, hjnext⟩
        have hxK : x ∈ K := Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjJ, hj⟩⟩
        have hxKc : x ∈ Kᶜ := hballK (Metric.ball_subset_ball hrKle hx)
        exact (hxKc hxK).elim
  · rintro (hx | hx)
    · exact Set.mem_iUnion.mpr ⟨b, by simpa [B, c, v] using hx⟩
    · exact Set.mem_iUnion.mpr ⟨b - 1, by
        simpa [a, B, v, hprev] using hx⟩

private theorem hsegParam :
    (by
      classical
      exact
        (∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) → (∀ x y z :
            Real × Real, z ∈ segment Real x y → ∃ t : Real, t ∈ Set.Icc 0 1 ∧ z = x + t • (y -
            x)) ) := by
  classical
  intro hlineMap x y z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  refine ⟨t, ht, ?_⟩
  rw [← hzt, hlineMap]

private theorem hcrossLinear :
    (by
      classical
      exact
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ z : Real × Real, IsLinearMap Real (cross z) ) := by
  classical
  intro cross z
  refine IsLinearMap.mk ?_ ?_
  · intro x y
    dsimp [cross]
    ring
  · intro t x
    dsimp [cross]
    ring

private theorem hcrossSelf :
    (by
      classical
      exact
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ z : Real × Real, cross z z = 0 ) := by
  classical
  intro cross z
  dsimp [cross]
  ring

private theorem hcarrierCross :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ x : Real × Real, x ∈ Metric.ball B r → (x ∈ C ↔ x ∈ segment Real B c ∨ x ∈ segment
            Real a B)) → ((∀ x y z : Real × Real, z ∈ segment Real x y → ∃ t : Real, t ∈ Set.Icc
            0 1 ∧ z = x + t • (y - x)) → ((∀ z : Real × Real, IsLinearMap Real (cross z)) → (∀ x
            : Real × Real, x ∈ Metric.ball B r → x ∈ C → cross u (x - B) = 0 ∨ cross w (x - B) =
            0))) ) := by
  classical
  intro n p v b B a c u w cross C rK r hcarrierLocal hsegParam hcrossLinear x hx hxC
  rcases (hcarrierLocal x hx).mp hxC with hxc | hxa
  · obtain ⟨t, ht, hform⟩ := hsegParam B c x hxc
    right
    have hdiff : x - B = t • w := by
      rw [hform]
      dsimp [w, c, B]
      module
    rw [hdiff, (hcrossLinear w).map_smul]
    change t * cross w w = 0
    rw [show cross w w = 0 by simp [cross]; ring]
    simp
  · obtain ⟨t, ht, hform⟩ := hsegParam a B x hxa
    left
    have hdiff : x - B = (1 - t) • u := by
      rw [hform]
      dsimp [u, a, B]
      module
    rw [hdiff]
    rw [(hcrossLinear u).map_smul]
    change (1 - t) * cross u u = 0
    rw [show cross u u = 0 by simp [cross]; ring]
    simp

private theorem hUV :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (cross w u = -cross u w) → ((0 < cross u w ∨ cross u w < 0) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        0 < cross U V)) ) := by
  classical
  intro n p v b B a c u w cross hswap hpos U V
  rcases hpos with hp | hn
  · simp [U, V, hp]
  · have hnp : ¬ 0 < cross u w := not_lt_of_gt hn
    simpa [U, V, hnp, hswap] using neg_pos.mpr hn

private theorem hdecomp :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (0 < cross U V) → (∀ z : Real × Real, z = (-cross V z / cross U V) • U + (cross U z /
            cross U V) • V) ) := by
  classical
  intro n p v b B a c u w cross U V hUV z
  apply Prod.ext
  · have hcoeff : -cross V z * U.1 + cross U z * V.1 =
        z.1 * cross U V := by dsimp [cross]; ring
    calc
      z.1 = z.1 * (cross U V * (cross U V)⁻¹) := by
        rw [mul_inv_cancel₀ (ne_of_gt hUV)]
        ring
      _ = (-cross V z * U.1 + cross U z * V.1) * (cross U V)⁻¹ := by
        rw [hcoeff]
        ring
      _ = (-cross V z / cross U V) * U.1 +
            (cross U z / cross U V) * V.1 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
  · have hcoeff : -cross V z * U.2 + cross U z * V.2 =
        z.2 * cross U V := by dsimp [cross]; ring
    calc
      z.2 = z.2 * (cross U V * (cross U V)⁻¹) := by
        rw [mul_inv_cancel₀ (ne_of_gt hUV)]
        ring
      _ = (-cross V z * U.2 + cross U z * V.2) * (cross U V)⁻¹ := by
        rw [hcoeff]
        ring
      _ = (-cross V z / cross U V) * U.2 +
            (cross U z / cross U V) * V.2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

private theorem hconeUV :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ((∀ z : Real × Real, IsLinearMap Real (cross z)) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (0 < cross U V) → ((∀ z : Real × Real, z = (-cross V z / cross U V) • U + (cross U z /
            cross U V) • V) → (∀ x : Real × Real, (∃ s t : Real, 0 < s ∧ 0 < t ∧ x = B + s • u +
            t • w) ↔ (0 < cross U (x - B) ∧ cross V (x - B) < 0))))) ) := by
  classical
  intro n p v b B a c u w cross hcrossLinear U V hUV hdecomp x
  constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    by_cases hp : 0 < cross u w
    · have hA : cross U (s • u + t • w) = t * cross U V := by
        rw [show U = u by simp [U, hp], show V = w by simp [V, hp]]
        rw [(hcrossLinear u).map_add, (hcrossLinear u).map_smul,
          (hcrossLinear u).map_smul]
        simp only [smul_eq_mul]
        dsimp [cross]
        ring
      have hB : cross V (s • u + t • w) = -(s * cross U V) := by
        rw [show U = u by simp [U, hp], show V = w by simp [V, hp]]
        rw [(hcrossLinear w).map_add, (hcrossLinear w).map_smul,
          (hcrossLinear w).map_smul]
        simp only [smul_eq_mul]
        dsimp [cross]
        ring
      constructor
      · have hpoint : B + s • u + t • w - B = s • u + t • w := by abel
        rw [hpoint, hA]
        exact mul_pos ht hUV
      · have hpoint : B + s • u + t • w - B = s • u + t • w := by abel
        rw [hpoint, hB]
        exact neg_neg_of_pos (mul_pos hs hUV)
    · have hA : cross U (t • w + s • u) = s * cross U V := by
        rw [show U = w by simp [U, hp], show V = u by simp [V, hp]]
        rw [(hcrossLinear w).map_add, (hcrossLinear w).map_smul,
          (hcrossLinear w).map_smul]
        simp only [smul_eq_mul]
        dsimp [cross]
        ring
      have hB : cross V (t • w + s • u) = -(t * cross U V) := by
        rw [show U = w by simp [U, hp], show V = u by simp [V, hp]]
        rw [(hcrossLinear u).map_add, (hcrossLinear u).map_smul,
          (hcrossLinear u).map_smul]
        simp only [smul_eq_mul]
        dsimp [cross]
        ring
      constructor
      · have he : B + s • u + t • w - B = t • w + s • u := by abel
        rw [he, hA]
        exact mul_pos hs hUV
      · have he : B + s • u + t • w - B = t • w + s • u := by abel
        rw [he, hB]
        exact neg_neg_of_pos (mul_pos ht hUV)
  · rintro ⟨hA, hB⟩
    let s := -cross V (x - B) / cross U V
    let t := cross U (x - B) / cross U V
    have hs : 0 < s := by dsimp [s]; exact div_pos (neg_pos.mpr hB) hUV
    have ht : 0 < t := by dsimp [t]; exact div_pos hA hUV
    have hz' : x - B = s • U + t • V := by simpa [s, t] using hdecomp (x - B)
    have hx : x = B + s • U + t • V := by
      calc
        x = B + (x - B) := by abel
        _ = B + (s • U + t • V) := by rw [hz']
        _ = B + s • U + t • V := by abel
    by_cases hp : 0 < cross u w
    · refine ⟨s, t, hs, ht, ?_⟩
      simpa [U, V, hp, add_assoc] using hx
    · refine ⟨t, s, ht, hs, ?_⟩
      calc
        x = B + s • U + t • V := hx
        _ = B + s • w + t • u := by simp [U, V, hp]
        _ = B + t • u + s • w := by abel

private theorem hsmallScale :
    (by
      classical
      exact
        ∀ z : Real × Real, ∀ δ : Real, 0 < δ → ∃ t : Real, 0 < t ∧ t • z ∈ Metric.ball (0 : Real
            × Real) δ ) := by
  classical
  intro z δ hδ
  let t := δ / (‖z‖ + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hn : ‖t • z‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hd : 0 < ‖z‖ + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith [norm_nonneg z]
  have hmem : t • z ∈ Metric.ball (0 : Real × Real) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (t • z : Real × Real) - 0 = t • z := by ext <;> simp
    rw [he]
    exact hn
  exact ⟨t, ht, hmem⟩

private theorem hconstOn :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        (∀ x ∉ P3544T1BoundaryCarrier p, ∃ (r : ℝ), (0 : ℝ) < r ∧ (Metric.ball x r ⊆
            P3544T1RayParity p ∨ Disjoint (Metric.ball x r) (P3544T1RayParity p))) → (∀ S :
            Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x, x ∈ S → ∀ y, y ∈ S →
            (x ∈ O ↔ y ∈ O)) ) := by
  classical
  intro n p O C hlocal S hconn hSC x hx y hy
  let f : S → Bool := fun z => decide ((z : Real × Real) ∈ O)
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨ρ, hρ, hstable⟩ := hlocal z.1 (hSC z.1 z.2)
    let V : Set S := Subtype.val ⁻¹' Metric.ball z.1 ρ
    refine ⟨V, Metric.isOpen_ball.preimage continuous_subtype_val,
      Metric.mem_ball_self hρ, ?_⟩
    intro z' hz'
    have hzball : (z' : Real × Real) ∈ Metric.ball z.1 ρ := hz'
    have heq : decide ((z' : Real × Real) ∈ O) = decide (z.1 ∈ O) := by
      rcases hstable with hsub | hdis
      · have hzO : z.1 ∈ O := hsub (Metric.mem_ball_self hρ)
        have hz'O : (z' : Real × Real) ∈ O := hsub hzball
        simp [hzO, hz'O]
      · have hzO : z.1 ∉ O := by
          intro hmem
          exact (Set.disjoint_left.mp hdis (Metric.mem_ball_self hρ)) hmem
        have hz'O : (z' : Real × Real) ∉ O := by
          intro hmem
          exact (Set.disjoint_left.mp hdis hzball) hmem
        simp [hzO, hz'O]
    simpa [f] using heq
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn.2
  have heq := hf.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  change decide (x ∈ O) = decide (y ∈ O) at heq
  by_cases hxo : x ∈ O <;> by_cases hyo : y ∈ O <;> simp [hxo, hyo] at heq ⊢

private theorem hNconvex :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ z : Real × Real, IsLinearMap Real (cross z)) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        let N0 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧
          0 < cross U z ∧ cross V z < 0}
        Convex Real N0) ) := by
  classical
  intro n p v b B a c u w cross rK r hcrossLinear U V N0
  exact (convex_ball 0 r).inter
    ((convex_halfSpace_gt (hcrossLinear U) 0).inter
      (convex_halfSpace_lt (hcrossLinear V) 0))

private theorem hN0ne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ z : Real × Real, IsLinearMap Real (cross z)) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (0 < cross U V) → (
        let N0 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧
          0 < cross U z ∧ cross V z < 0}
        let z0 := U + V
        (cross U z0 = cross U V) → ((cross V z0 = -cross U V) → (∀ (τ : ℝ), ((0 : ℝ) < τ) → ((τ •
            z0 ∈ Metric.ball (0 : ℝ × ℝ) r) → (N0.Nonempty)))))) ) := by
  classical
  intro n p v b B a c u w cross rK r hcrossLinear U V hUV N0 z0 hz0U hz0V τ hτ hτball
  refine ⟨τ • z0, ?_, ?_, ?_⟩
  · exact hτball
  · rw [(hcrossLinear U).map_smul]
    rw [hz0U]
    exact mul_pos hτ hUV
  · rw [(hcrossLinear V).map_smul]
    rw [hz0V]
    change τ * (-cross U V) < 0
    exact mul_neg_of_pos_of_neg hτ (neg_neg_of_pos hUV)

private theorem hτnegBall :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        let z0 := U + V
        ∀ (τ : ℝ), (τ • z0 ∈ Metric.ball (0 : ℝ × ℝ) r) → (-(τ • z0) ∈ Metric.ball (0 : Real ×
            Real) r) ) := by
  classical
  intro n p v b B a c u w cross rK r U V z0 τ hτball
  have hh := hτball
  rw [Metric.mem_ball, dist_eq_norm] at hh ⊢
  have he : (τ • z0 : Real × Real) - 0 = τ • z0 := by ext <;> simp
  have he' : (-(τ • z0) : Real × Real) - 0 = -(τ • z0) := by ext <;> simp
  rw [he] at hh
  rw [he']
  simpa [norm_neg] using hh

private theorem hnegU :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (∀ z : Real × Real, IsLinearMap Real (cross z)) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (0 < cross U V) → (
        let z0 := U + V
        (cross U z0 = cross U V) → (∀ (τ : ℝ), ((0 : ℝ) < τ) → (cross U (-(τ • z0)) < 0)))) ) := by
  classical
  intro n p v b B a c u w cross hcrossLinear U V hUV z0 hz0U τ hτ
  rw [(hcrossLinear U).map_neg, (hcrossLinear U).map_smul, hz0U]
  change -(τ * cross U V) < 0
  exact neg_neg_of_pos (mul_pos hτ hUV)

private theorem hposV :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (∀ z : Real × Real, IsLinearMap Real (cross z)) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (0 < cross U V) → (
        let z0 := U + V
        (cross V z0 = -cross U V) → (∀ (τ : ℝ), ((0 : ℝ) < τ) → (0 < cross V (-(τ • z0)))))) ) := by
  classical
  intro n p v b B a c u w cross hcrossLinear U V hUV z0 hz0V τ hτ
  rw [(hcrossLinear V).map_neg, (hcrossLinear V).map_smul, hz0V]
  change 0 < - (τ * -cross U V)
  nlinarith [mul_pos hτ hUV]

private theorem himageN :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        let N0 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧
          0 < cross U z ∧ cross V z < 0}
        let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          0 < cross U (x - B) ∧ cross V (x - B) < 0}
        (fun z : Real × Real => B + z) '' N0 = N ) := by
  classical
  intro n p v b B a c u w cross rK r U V N0 N
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨hzball, hzu, hzw⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm] at hzball ⊢
      have he : (B + z : Real × Real) - B = z := by abel
      rw [he]
      simpa using hzball
    · have he : (B + z : Real × Real) - B = z := by abel
      rw [he]
      exact hzu
    · have he : (B + z : Real × Real) - B = z := by abel
      rw [he]
      exact hzw
  · rintro ⟨hxball, hxu, hxw⟩
    refine ⟨x - B, ?_, by abel⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm] at hxball ⊢
      have he : (x - B : Real × Real) - 0 = x - B := by ext <;> simp
      rw [he]
      exact hxball
    · exact hxu
    · exact hxw

private theorem himageW :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        let W1 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧ cross U z < 0}
        let W2 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧ 0 < cross V z}
        let W0 : Set (Real × Real) := W1 ∪ W2
        let W : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          (cross U (x - B) < 0 ∨ 0 < cross V (x - B))}
        (fun z : Real × Real => B + z) '' W0 = W ) := by
  classical
  intro n p v b B a c u w cross rK r U V W1 W2 W0 W
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · rcases hz with ⟨hzball, hzu⟩
      refine ⟨?_, Or.inl ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hzball ⊢
        have he : (B + z : Real × Real) - B = z := by abel
        rw [he]
        simpa using hzball
      · have he : (B + z : Real × Real) - B = z := by abel
        rw [he]
        exact hzu
    · rcases hz with ⟨hzball, hzw⟩
      refine ⟨?_, Or.inr ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hzball ⊢
        have he : (B + z : Real × Real) - B = z := by abel
        rw [he]
        simpa using hzball
      · have he : (B + z : Real × Real) - B = z := by abel
        rw [he]
        exact hzw
  · rintro ⟨hxball, hsign⟩
    refine ⟨x - B, ?_, by abel⟩
    have hx0 : x - B ∈ Metric.ball (0 : Real × Real) r := by
      rw [Metric.mem_ball, dist_eq_norm] at hxball ⊢
      have he : (x - B : Real × Real) - 0 = x - B := by ext <;> simp
      rw [he]
      exact hxball
    rcases hsign with hsign | hsign
    · exact Or.inl ⟨hx0, hsign⟩
    · exact Or.inr ⟨hx0, hsign⟩

private theorem hsegmentHeight :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        (∀ x' ∈ Finset.univ, (ell : ℝ × ℝ → ℝ) (v x') ≤ (ell : ℝ × ℝ → ℝ) (v b)) → (
        let B := v b
        (∀ x y z : Real × Real, z ∈ segment Real x y → ∃ t : Real, t ∈ Set.Icc 0 1 ∧ z = x + t •
            (y - x)) → (∀ i : Fin (n + 3), ∀ x : Real × Real, x ∈ segment Real (v i) (v (i + 1))
            → ell x ≤ ell B)) ) := by
  classical
  intro n p v f hqexists q b ell hmax B hsegParam i x hx
  obtain ⟨t, ht, hform⟩ := hsegParam (v i) (v (i + 1)) x hx
  have hvalue : ell x = (1 - t) * ell (v i) + t * ell (v (i + 1)) := by
    rw [hform, map_add, map_smul, map_sub]
    simp only [smul_eq_mul]
    ring
  have hi := hmax i (Finset.mem_univ i)
  have hinext := hmax (i + 1) (Finset.mem_univ (i + 1))
  calc
    ell x = (1 - t) * ell (v i) + t * ell (v (i + 1)) := hvalue
    _ ≤ (1 - t) * ell B + t * ell B := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr ht.2)
      · exact mul_le_mul_of_nonneg_left hinext ht.1
    _ = ell B := by ring

private theorem hellCarrier :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let c := v (b + 1)
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        (b - 1 + 1 = b) → (
        let B := v b
        let a := v (b - 1)
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ x : Real × Real, x ∈ Metric.ball B r → (x ∈ C ↔ x ∈ segment Real B c ∨ x ∈ segment
            Real a B)) → ((∀ i : Fin (n + 3), ∀ x : Real × Real, x ∈ segment Real (v i) (v (i +
            1)) → ell x ≤ ell B) → (∀ x : Real × Real, x ∈ Metric.ball B r → x ∈ C → ell x ≤ ell
            B))) ) := by
  classical
  intro n p v f hqexists q b c ell hprev B a C rK r hcarrierLocal hsegmentHeight x hx hxC
  rcases (hcarrierLocal x hx).mp hxC with hxc | hxa
  · exact hsegmentHeight b x (by simpa [B, c, v] using hxc)
  · have hprevseg : x ∈ segment Real (v (b - 1)) (v ((b - 1) + 1)) := by
      simpa [a, B, v, hprev] using hxa
    exact hsegmentHeight (b - 1) x hprevseg

private theorem hradialDist :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        ∀ d : Real × Real, ∀ t : Real, 0 ≤ t → dist (B + t • d) B = t * dist (B + d) B ) := by
  classical
  intro n p v b B d t ht
  rw [dist_eq_norm, dist_eq_norm]
  have he : B + t • d - B = t • d := by abel
  have he' : B + d - B = d := by abel
  rw [he, he', norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

private theorem hUendpoint :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let U := if 0 < cross u w then u else w
        B + U = a ∨ B + U = c ) := by
  classical
  intro n p v b B a c u w cross U
  by_cases hp : 0 < cross u w
  · left
    simp [U, hp, B, a, u]
  · right
    simp [U, hp, B, c, w]

private theorem hVendpoint :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let V := if 0 < cross u w then w else u
        B + V = a ∨ B + V = c ) := by
  classical
  intro n p v b B a c u w cross V
  by_cases hp : 0 < cross u w
  · right
    simp [V, hp, B, c, w]
  · left
    simp [V, hp, B, a, u]

private theorem hUdist :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (r < dist B a) → ((r < dist B c) → (
        let U := if 0 < cross u w then u else w
        (B + U = a ∨ B + U = c) → (r < dist (B + U) B))) ) := by
  classical
  intro n p v b B a c u w cross rK r hrA hrC U hUendpoint
  rcases hUendpoint with h | h
  · rw [h, dist_comm]
    exact hrA
  · rw [h, dist_comm]
    exact hrC

private theorem hVdist :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (r < dist B a) → ((r < dist B c) → (
        let V := if 0 < cross u w then w else u
        (B + V = a ∨ B + V = c) → (r < dist (B + V) B))) ) := by
  classical
  intro n p v b B a c u w cross rK r hrA hrC V hVendpoint
  rcases hVendpoint with h | h
  · rw [h, dist_comm]
    exact hrA
  · rw [h, dist_comm]
    exact hrC

private theorem haxisU :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        (∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) → (
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (0 < r) → ((∀ x : Real × Real, x ∈ Metric.ball B r → (x ∈ C ↔ x ∈ segment Real B c ∨ x ∈
            segment Real a B)) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (0 < cross U V) → ((∀ z : Real × Real, z = (-cross V z / cross U V) • U + (cross U z /
            cross U V) • V) → ((∀ d : Real × Real, ∀ t : Real, 0 ≤ t → dist (B + t • d) B = t *
            dist (B + d) B) → ((B + U = a ∨ B + U = c) → ((r < dist (B + U) B) → (∀ x : Real ×
            Real, x ∈ Metric.ball B r → cross U (x - B) = 0 → cross V (x - B) ≤ 0 → x ∈ C))))))))
            ) := by
  classical
  intro n p v b B a c u w hlineMap cross C rK r hr hcarrierLocal U V hUV hdecomp hradialDist
      hUendpoint hUdist x hx hzero hle
  let z := x - B
  let s := -cross V z / cross U V
  have hz : z = s • U := by
    have hh := hdecomp z
    have hzero' : cross U z = 0 := by simpa [z] using hzero
    rw [hzero'] at hh
    simp only [zero_div, zero_smul, add_zero] at hh
    simpa [s] using hh
  have hs : 0 ≤ s := by dsimp [s]; exact div_nonneg (neg_nonneg.mpr hle) hUV.le
  have hslt : s < 1 := by
    by_contra hnot
    have hge : 1 ≤ s := le_of_not_gt hnot
    have hdistx : dist x B < r := Metric.mem_ball.mp hx
    have heq : x = B + s • U := by
      calc
        x = B + (x-B) := by abel
        _ = B + s • U := congrArg (fun z : Real × Real => B + z) (by simpa [z] using hz)
    rw [heq, hradialDist U s hs] at hdistx
    have hmul0 := mul_le_mul_of_nonneg_right hge
      (le_of_lt (lt_trans hr hUdist))
    have hmul : dist (B + U) B ≤ s * dist (B + U) B := by
      simpa only [one_mul] using hmul0
    exact (not_lt_of_ge (le_of_lt hUdist)) (lt_of_le_of_lt hmul hdistx)
  have hseg : x ∈ segment Real B (B + U) := by
    have hh := lineMap_mem_segment Real B (B + U)
      (show s ∈ Set.Icc 0 1 from ⟨hs, hslt.le⟩)
    rw [hlineMap] at hh
    have heq : B + s • ((B + U) - B) = B + s • U := by congr 1; abel
    rw [heq] at hh
    have hxform : x = B + s • U := by
      calc
        x = B + (x-B) := by abel
        _ = B + s • U := congrArg (fun z : Real × Real => B + z) (by simpa [z] using hz)
    rw [hxform]
    exact hh
  rcases hUendpoint with h | h
  · have hseg' : x ∈ segment Real a B := by
      rw [← segment_symm Real B a]
      simpa [h] using hseg
    exact (hcarrierLocal x hx).mpr (Or.inr (by simpa [a, B] using hseg'))
  · rw [h] at hseg
    exact (hcarrierLocal x hx).mpr (Or.inl (by simpa [c, B] using hseg))

private theorem haxisV :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        (∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) → (
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (0 < r) → ((∀ x : Real × Real, x ∈ Metric.ball B r → (x ∈ C ↔ x ∈ segment Real B c ∨ x ∈
            segment Real a B)) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (0 < cross U V) → ((∀ z : Real × Real, z = (-cross V z / cross U V) • U + (cross U z /
            cross U V) • V) → ((∀ d : Real × Real, ∀ t : Real, 0 ≤ t → dist (B + t • d) B = t *
            dist (B + d) B) → ((B + V = a ∨ B + V = c) → ((r < dist (B + V) B) → (∀ x : Real ×
            Real, x ∈ Metric.ball B r → cross V (x - B) = 0 → 0 ≤ cross U (x - B) → x ∈ C))))))))
            ) := by
  classical
  intro n p v b B a c u w hlineMap cross C rK r hr hcarrierLocal U V hUV hdecomp hradialDist
      hVendpoint hVdist x hx hzero hle
  let z := x - B
  let t := cross U z / cross U V
  have hz : z = t • V := by
    have hh := hdecomp z
    have hzero' : cross V z = 0 := by simpa [z] using hzero
    rw [hzero'] at hh
    simp only [neg_zero, zero_div, zero_smul, zero_add] at hh
    simpa [t] using hh
  have ht : 0 ≤ t := by dsimp [t]; exact div_nonneg hle hUV.le
  have htlt : t < 1 := by
    by_contra hnot
    have hge : 1 ≤ t := le_of_not_gt hnot
    have hdistx : dist x B < r := Metric.mem_ball.mp hx
    have heq : x = B + t • V := by
      calc
        x = B + (x-B) := by abel
        _ = B + t • V := congrArg (fun z : Real × Real => B + z) (by simpa [z] using hz)
    rw [heq, hradialDist V t ht] at hdistx
    have hmul0 := mul_le_mul_of_nonneg_right hge
      (le_of_lt (lt_trans hr hVdist))
    have hmul : dist (B + V) B ≤ t * dist (B + V) B := by
      simpa only [one_mul] using hmul0
    exact (not_lt_of_ge (le_of_lt hVdist)) (lt_of_le_of_lt hmul hdistx)
  have hseg : x ∈ segment Real B (B + V) := by
    have hh := lineMap_mem_segment Real B (B + V)
      (show t ∈ Set.Icc 0 1 from ⟨ht, htlt.le⟩)
    rw [hlineMap] at hh
    have heq : B + t • ((B + V) - B) = B + t • V := by congr 1; abel
    rw [heq] at hh
    have hxform : x = B + t • V := by
      calc
        x = B + (x-B) := by abel
        _ = B + t • V := congrArg (fun z : Real × Real => B + z) (by simpa [z] using hz)
    rw [hxform]
    exact hh
  rcases hVendpoint with h | h
  · have hseg' : x ∈ segment Real a B := by
      rw [← segment_symm Real B a]
      simpa [h] using hseg
    exact (hcarrierLocal x hx).mpr (Or.inr (by simpa [a, B] using hseg'))
  · rw [h] at hseg
    exact (hcarrierLocal x hx).mpr (Or.inl (by simpa [c, B] using hseg))

private theorem hcarrierSigns :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (cross u w ≠ 0) → (
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ x : Real × Real, x ∈ Metric.ball B r → (x ∈ C ↔ x ∈ segment Real B c ∨ x ∈ segment
            Real a B)) → ((∀ x y z : Real × Real, z ∈ segment Real x y → ∃ t : Real, t ∈ Set.Icc
            0 1 ∧ z = x + t • (y - x)) → ((∀ z : Real × Real, IsLinearMap Real (cross z)) → ((∀ z
            : Real × Real, cross z z = 0) → ((cross w u = -cross u w) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        ∀ x, x ∈ Metric.ball B r → x ∈ C → 0 ≤ cross U (x-B) ∧ cross V (x-B) ≤ 0)))))) ) := by
  classical
  intro n p v b B a c u w cross hdet C rK r hcarrierLocal hsegParam hcrossLinear hcrossSelf hswap
      U V x hx hxC
  rcases (hcarrierLocal x hx).mp hxC with hxc | hxa
  · obtain ⟨t, ht, hform⟩ := hsegParam B c x hxc
    have hdiff : x-B = t • w := by rw [hform]; dsimp [w, c, B]; module
    by_cases hp : 0 < cross u w
    · constructor
      · rw [show U = u by simp [U, hp], hdiff, (hcrossLinear u).map_smul]
        change 0 ≤ t * cross u w
        exact mul_nonneg ht.1 hp.le
      · rw [show V = w by simp [V, hp], hdiff, (hcrossLinear w).map_smul]
        rw [hcrossSelf]
        simp
    · have hn : cross u w < 0 := lt_of_le_of_ne (le_of_not_gt hp) hdet
      constructor
      · rw [show U = w by simp [U, hp], hdiff, (hcrossLinear w).map_smul]
        rw [hcrossSelf]
        simp
      · rw [show V = u by simp [V, hp], hdiff, (hcrossLinear u).map_smul]
        change t * cross u w ≤ 0
        exact mul_nonpos_of_nonneg_of_nonpos ht.1 hn.le
  · obtain ⟨t, ht, hform⟩ := hsegParam a B x hxa
    have hdiff : x-B = (1-t) • u := by rw [hform]; dsimp [u, a, B]; module
    have hcoef : 0 ≤ 1-t := by linarith [ht.2]
    by_cases hp : 0 < cross u w
    · constructor
      · rw [show U = u by simp [U, hp], hdiff, (hcrossLinear u).map_smul]
        change 0 ≤ (1-t) * cross u u
        rw [hcrossSelf]
        simp
      · rw [show V = w by simp [V, hp], hdiff, (hcrossLinear w).map_smul]
        change (1-t) * cross w u ≤ 0
        rw [hswap]
        exact mul_nonpos_of_nonneg_of_nonpos hcoef (neg_nonpos.mpr hp.le)
    · have hn : cross u w < 0 := lt_of_le_of_ne (le_of_not_gt hp) hdet
      constructor
      · rw [show U = w by simp [U, hp], hdiff, (hcrossLinear w).map_smul]
        change (1-t) * cross w u ≥ 0
        rw [hswap]
        exact mul_nonneg hcoef (neg_nonneg.mpr hn.le)
      · rw [show V = u by simp [V, hp], hdiff, (hcrossLinear u).map_smul]
        rw [hcrossSelf]
        simp

private theorem hNoff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ x : Real × Real, x ∈ Metric.ball B r → x ∈ C → cross u (x - B) = 0 ∨ cross w (x - B) =
            0) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          0 < cross U (x - B) ∧ cross V (x - B) < 0}
        ∀ x, x ∈ N → x ∉ C) ) := by
  classical
  intro n p v b B a c u w cross C rK r hcarrierCross U V N x hx hc
  by_cases hp : 0 < cross u w
  · rcases hcarrierCross x hx.1 hc with hu0 | hw0
    · exact (ne_of_gt hx.2.1) (by simpa [U, hp] using hu0)
    · exact (ne_of_lt hx.2.2) (by simpa [V, hp] using hw0)
  · rcases hcarrierCross x hx.1 hc with hu0 | hw0
    · exact (ne_of_lt hx.2.2) (by simpa [V, hp] using hu0)
    · exact (ne_of_gt hx.2.1) (by simpa [U, hp] using hw0)

private theorem hcover :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          0 < cross U (x - B) ∧ cross V (x - B) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          (cross U (x - B) < 0 ∨ 0 < cross V (x - B))}
        (∀ x : Real × Real, x ∈ Metric.ball B r → cross U (x - B) = 0 → cross V (x - B) ≤ 0 → x ∈
            C) → ((∀ x : Real × Real, x ∈ Metric.ball B r → cross V (x - B) = 0 → 0 ≤ cross U (x
            - B) → x ∈ C) → (∀ x, x ∈ Metric.ball B r → x ∉ C → x ∈ N ∨ x ∈ W)) ) := by
  classical
  intro n p v b B a c u w cross C rK r U V N W haxisU haxisV x hx hxC
  by_cases hu : cross U (x-B) < 0
  · exact Or.inr ⟨hx, Or.inl hu⟩
  · by_cases hv : 0 < cross V (x-B)
    · exact Or.inr ⟨hx, Or.inr hv⟩
    · have hu' : 0 ≤ cross U (x-B) := le_of_not_gt hu
      have hv' : cross V (x-B) ≤ 0 := le_of_not_gt hv
      by_cases hu0 : cross U (x-B) = 0
      · exact False.elim (hxC (haxisU x hx hu0 hv'))
      · have huPos : 0 < cross U (x-B) := lt_of_le_of_ne hu' (Ne.symm hu0)
        by_cases hv0 : cross V (x-B) = 0
        · exact False.elim (hxC (haxisV x hx hv0 hu'))
        · have hvNeg : cross V (x-B) < 0 := lt_of_le_of_ne hv' hv0
          exact Or.inl ⟨hx, huPos, hvNeg⟩

private theorem hconeHeight :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let c := v (b + 1)
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        let B := v b
        let a := v (b - 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        (ell u < 0) → ((ell w < 0) → (∀ x : Real × Real, (∃ s t : Real, 0 < s ∧ 0 < t ∧ x = B + s
            • u + t • w) → ell x < ell B)) ) := by
  classical
  intro n p v f hqexists q b c ell B a u w hellu hellw x hx
  obtain ⟨s, t, hs, ht, rfl⟩ := hx
  have hcalc : ell (B + s • u + t • w) = ell B + s * ell u + t * ell w := by
    rw [map_add, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
  rw [hcalc]
  have hsneg : s * ell u < 0 := mul_neg_of_pos_of_neg hs hellu
  have htneg : t * ell w < 0 := mul_neg_of_pos_of_neg ht hellw
  calc
    ell B + s * ell u + t * ell w = ell B + (s * ell u + t * ell w) := by ring
    _ < ell B := by
      have hsum : s * ell u + t * ell w < 0 := add_neg_of_neg_of_nonpos hsneg htneg.le
      simpa using add_lt_add_left hsum (ell B)

private theorem translateBall (B z : ℝ × ℝ) (r : ℝ)
    (hz : z ∈ Metric.ball (0 : ℝ × ℝ) r) : B + z ∈ Metric.ball B r := by
  have he : dist (B + z) B = dist z (0 : ℝ × ℝ) := by
    calc
      dist (B + z) B = dist (B + z) (B + (0 : ℝ × ℝ)) := by simp
      _ = dist z 0 := dist_add_left B z 0
  rw [Metric.mem_ball, he]
  exact hz

private theorem hyheight :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        ((0 : ℝ) < ε) → (ell B < ell y) ) := by
  classical
  intro n p v f hqexists q b B e ε y ell hε
  have he : ell e = 1 := by simp [e, ell]
  have hval : ell y = ell B + ε := by
    change ell (B + ε • e) = ell B + ε
    rw [map_add, map_smul, he]
    simp only [smul_eq_mul, mul_one]
  rw [hval]
  linarith

private theorem hYclass :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let c := v (b + 1)
        let B := v b
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        let a := v (b - 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (∀ x : Real × Real, (∃ s t : Real, 0 < s ∧ 0 < t ∧ x = B + s • u + t • w) ↔ (0 < cross U
            (x - B) ∧ cross V (x - B) < 0)) → (
        let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          0 < cross U (x - B) ∧ cross V (x - B) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          (cross U (x - B) < 0 ∨ 0 < cross V (x - B))}
        (∀ x, x ∈ Metric.ball B r → x ∉ C → x ∈ N ∨ x ∈ W) → ((∀ x : Real × Real, (∃ s t : Real,
            0 < s ∧ 0 < t ∧ x = B + s • u + t • w) → ell x < ell B) → ((y ∈ Metric.ball B r) →
            ((ell B < ell y) → ((y ∉ C) → (y ∈ W)))))) ) := by
  classical
  intro n p v f hqexists q b c B e ε y ell a u w cross C rK r U V hconeUV N W hcover hconeHeight
      hyball hyheight hynotC
  rcases hcover y hyball hynotC with hyN | hyW
  · have hlt := hconeHeight y ((hconeUV y).mpr ⟨hyN.2.1, hyN.2.2⟩)
    exact False.elim ((not_lt_of_ge (le_of_lt hlt)) hyheight)
  · exact hyW

private theorem hellD :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        (
        let e : Real × Real := (1, 0)
        (
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        ∀ (d0 : ℝ × ℝ),
        let T := max 0 (-ell d0 + 1)
        ∀ (κ : ℝ), (κ ∈ Set.Ioi T) → (
        let d := d0 + κ • e
        0 < ell d)))) := by
  classical
  intro n p v f hqexists q e ell d0 T κ hκT d
  have heval : ell d = ell d0 + κ := by simp [d, e, ell]; ring
  have hκlarge : -ell d0 + 1 < κ := lt_of_le_of_lt (le_max_right _ _) hκT
  rw [heval]
  linarith

private theorem hdv :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        ∀ (d0 : ℝ × ℝ), (∀ (i : Fin (n + (3 : ℕ))), d0.1 * (p.vertex i - y).2 - d0.2 * (p.vertex
            i - y).1 ≠ (0 : ℝ)) → (
        let badV : Fin (n + 3) → Real := fun i =>
          if (v i - y).2 = 0 then 0 else -cross d0 (v i - y) / (v i - y).2
        let badE : Fin (n + 3) → Real := fun i =>
          if (v (i + 1) - v i).2 = 0 then 0 else
            -cross d0 (v (i + 1) - v i) / (v (i + 1) - v i).2
        ∀ (κ : ℝ), (κ ∉ Set.range badV ∪ Set.range badE) → (
        let d := d0 + κ • e
        ∀ i : Fin (n + 3), cross d (v i - y) ≠ 0)) ) := by
  classical
  intro n p v b B cross e ε y d0 hdv0 badV badE κ hκbad d i
  have hdform : cross d (v i-y) = cross d0 (v i-y) + κ * (v i-y).2 := by
    dsimp [cross, d, e]
    ring
  by_cases hzero : (v i-y).2 = 0
  · rw [hdform]
    simp only [hzero, mul_zero, add_zero]
    simpa [cross] using hdv0 i
  · intro hz
    have hroot : κ = -cross d0 (v i-y) / (v i-y).2 := by
      rw [hdform] at hz
      apply (eq_div_iff hzero).2
      linear_combination hz
    have hmem : κ ∈ Set.range badV := by
      refine ⟨i, ?_⟩
      change (if (v i-y).2 = 0 then 0 else
        -cross d0 (v i-y) / (v i-y).2) = κ
      rw [ite_eq_right hzero]
      exact hroot.symm
    exact hκbad (Set.mem_union_left _ hmem)

private theorem hde :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        ∀ (d0 : ℝ × ℝ), (∀ (i : Fin (n + (3 : ℕ))), d0.1 * (p.vertex (i + (1 : Fin (n + (3 :
            ℕ)))) - p.vertex i).2 - d0.2 * (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            i).1 ≠ (0 : ℝ)) → (
        let badV : Fin (n + 3) → Real := fun i =>
          if (v i - y).2 = 0 then 0 else -cross d0 (v i - y) / (v i - y).2
        let badE : Fin (n + 3) → Real := fun i =>
          if (v (i + 1) - v i).2 = 0 then 0 else
            -cross d0 (v (i + 1) - v i) / (v (i + 1) - v i).2
        ∀ (κ : ℝ), (κ ∉ Set.range badV ∪ Set.range badE) → (
        let d := d0 + κ • e
        ∀ i : Fin (n + 3), cross d (v (i + 1)-v i) ≠ 0)) ) := by
  classical
  intro n p v b B cross e ε y d0 hde0 badV badE κ hκbad d i
  let z := v (i + 1)-v i
  have hdform : cross d z = cross d0 z + κ * z.2 := by
    dsimp [cross, d, e]
    ring
  by_cases hzero : z.2 = 0
  · rw [hdform]
    simp only [hzero, mul_zero, add_zero]
    simpa [cross, z] using hde0 i
  · intro hz
    have hroot : κ = -cross d0 z / z.2 := by
      rw [hdform] at hz
      apply (eq_div_iff hzero).2
      linear_combination hz
    have hmem : κ ∈ Set.range badE := by
      refine ⟨i, ?_⟩
      change (if (v (i + 1) - v i).2 = 0 then 0 else
        -cross d0 (v (i + 1) - v i) / (v (i + 1) - v i).2) = κ
      rw [ite_eq_right (by simpa [z] using hzero)]
      exact hroot.symm
    exact hκbad (Set.mem_union_right _ hmem)

private theorem hhitsEmpty :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        (∀ i : Fin (n + 3), ∀ x : Real × Real, x ∈ segment Real (v i) (v (i + 1)) → ell x ≤ ell
            B) → ((ell B < ell y) → (∀ (d0 : ℝ × ℝ), ∀ (κ : ℝ),
        let d := d0 + κ • e
        (0 < ell d) → (
        let hits : Set (Fin (n + 3)) := {i | ∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (v i)
            (v (i +
            1))}
        hits = ∅))) ) := by
  classical
  intro n p v f hqexists q b B e ε y ell hsegmentHeight hyheight d0 κ d hellD hits
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨t, ht, hseg⟩ := hi
  have hle := hsegmentHeight i (y + t • d) hseg
  have hval : ell (y + t • d) = ell y + t * ell d := by
    rw [map_add, map_smul]
    simp only [smul_eq_mul]
  rw [hval] at hle
  have hpos : 0 < t * ell d := mul_pos ht hellD
  have hgt : ell B < ell y + t * ell d := by linarith
  exact (not_lt_of_ge hle) hgt

private theorem hyEven :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        (∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), x ∉ P3544T1BoundaryCarrier p → (∀ (i : Fin (n + (3 :
            ℕ))), d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (∀ (i : Fin (n
            + (3 : ℕ))), d.1 * (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).2 - d.2 *
            (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).1 ≠ (0 : ℝ)) → (x ∈
            P3544T1RayParity p ↔ {i : Fin (n + (3 : ℕ)) | ∃ (t : ℝ), (0 : ℝ) < t ∧ x + t • d ∈
            segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ)))))}.ncard % (2 : ℕ) = (1
            : ℕ))) → (
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        (y ∉ C) → (∀ (d0 : ℝ × ℝ), ∀ (κ : ℝ),
        let d := d0 + κ • e
        (∀ i : Fin (n + 3), cross d (v i - y) ≠ 0) → ((∀ i : Fin (n + 3), cross d (v (i + 1)-v i)
            ≠ 0) → (
        let hits : Set (Fin (n + 3)) := {i | ∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (v i)
            (v (i +
            1))}
        (hits = ∅) → (y ∉ O))))) ) := by
  classical
  intro n p v b B cross O C hparity e ε y hynotC d0 κ d hdv hde hits hhitsEmpty hyO
  have hpar := (hparity y d hynotC hdv hde).mp hyO
  have hpar' : hits.ncard % 2 = 1 := by simpa [hits, v] using hpar
  simp [hhitsEmpty] at hpar'

private theorem hdistx0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        ∀ (rK : ℝ), (rK > (0 : ℝ)) → ((0 < dist B a) → ((0 < dist B c) → (
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (0 < r) → ((∀ d : Real × Real, ∀ t : Real, 0 ≤ t → dist (B + t • d) B = t * dist (B + d)
            B) → (
        let σ := min (1 / 2) (r / (4 * (dist B a + 1)))
        (0 < σ) → ((σ ≤ r / (4 * (dist B a + 1))) → ((σ < 1) → (
        let x0 := B + σ • u
        (B + u = a) → (dist B x0 < r / 2))))))))) ) := by
  classical
  intro n p v b B a c u rK hrK hdistA hdistC r hr hradialDist σ hσ hσle hσlt x0 hBu
  have hrad : dist B x0 = σ * dist B a := by
    calc
      dist B x0 = dist x0 B := dist_comm _ _
      _ = σ * dist (B + u) B := by
        change dist (B + σ • u) B = σ * dist (B + u) B
        exact hradialDist u σ hσ.le
      _ = σ * dist B a := by rw [hBu, dist_comm]
  rw [hrad]
  have hd0 : 0 ≤ dist B a := dist_nonneg
  calc
    σ * dist B a ≤ (r / (4 * (dist B a + 1))) * dist B a :=
      mul_le_mul_of_nonneg_right hσle hd0
    _ = r / 4 * (dist B a / (dist B a + 1)) := by field_simp
    _ < r / 4 := by
      have hfrac : dist B a / (dist B a + 1) < 1 := by
        rw [div_lt_iff₀ (by positivity)]
        linarith
      simpa only [mul_one] using mul_lt_mul_of_pos_left hfrac (by positivity : 0 < r / 4)
    _ < r / 2 := by linarith

private theorem hx0open :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        (∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x)) → (∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let σ := min (1 / 2) (r / (4 * (dist B a + 1)))
        (0 < σ) → ((σ < 1) → (
        let x0 := B + σ • u
        x0 ∈ openSegment Real a B))) ) := by
  classical
  intro n p v b B a c u hlineMap rK r σ hσ hσlt x0
  have hmem := lineMap_mem_openSegment Real a B
    (show 1 - σ ∈ Set.Ioo 0 1 by constructor <;> linarith [hσ, hσlt])
  rw [hlineMap] at hmem
  have heq : a + (1-σ) • (B-a) = x0 := by
    dsimp [x0, u]
    module
  rw [heq] at hmem
  exact hmem

private theorem hx0ball :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (0 < r) → (
        let σ := min (1 / 2) (r / (4 * (dist B a + 1)))
        let x0 := B + σ • u
        (dist B x0 < r / 2) → (x0 ∈ Metric.ball B r)) ) := by
  classical
  intro n p v b B a c u rK r hr σ x0 hdistx0
  rw [Metric.mem_ball, dist_comm]
  exact lt_trans hdistx0 (by linarith)

private theorem hcrossUq :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (cross u w ≠ 0) → ((∀ z : Real × Real, IsLinearMap Real (cross z)) → (
        let qside : Real × Real := if 0 < cross u w then w else -w
        0 < cross u qside)) ) := by
  classical
  intro n p v b B a c u w cross hdet hcrossLinear qside
  by_cases hp : 0 < cross u w
  · simp [qside, hp]
  · have hn : cross u w < 0 := lt_of_le_of_ne (le_of_not_gt hp) hdet
    rw [show qside = -w by simp [qside, hp], (hcrossLinear u).map_neg]
    exact neg_pos.mpr hn

private theorem hcrossWq :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (∀ z : Real × Real, IsLinearMap Real (cross z)) → ((∀ z : Real × Real, cross z z = 0) → (
        let qside : Real × Real := if 0 < cross u w then w else -w
        cross w qside = 0)) ) := by
  classical
  intro n p v b B a c u w cross hcrossLinear hcrossSelf qside
  by_cases hp : 0 < cross u w
  · rw [show qside = w by simp [qside, hp], hcrossSelf]
  · rw [show qside = -w by simp [qside, hp], (hcrossLinear w).map_neg, hcrossSelf]
    simp

private theorem hηballNeg :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ (δ : ℝ),
        let qside : Real × Real := if 0 < cross u w then w else -w
        ∀ (η : ℝ), (η • qside ∈ Metric.ball (0 : ℝ × ℝ) δ) → (-(η • qside) ∈ Metric.ball (0 :
            Real × Real) δ) ) := by
  classical
  intro n p v b B a c u w cross δ qside η hηball
  rw [Metric.mem_ball, dist_eq_norm]
  have hh : ‖η • qside‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hηball
  simpa only [sub_zero, norm_neg] using hh

private theorem hdetSide :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let u : Real × Real := a - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ∀ z : Real × Real, P3381T1TriangleDeterminant ![a, B, z] = -cross u (z-B) ) := by
  classical
  intro n p v b B a u cross z
  simp [P3381T1TriangleDeterminant, cross, u, a, B]
  ring

private theorem hOpp :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))), (b - 1 + 1 = b) → (
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let O := P3544T1RayParity p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let σ := min (1 / 2) (r / (4 * (dist B a + 1)))
        let x0 := B + σ • u
        ∀ (rS : ℝ), ∀ (sbit : Bool), (∀ y ∈ Metric.ball x0 rS, y ∈ P3544T1RayParity p ↔ if sbit
            = true then (0 : ℝ) < P3381T1TriangleDeterminant ![p.vertex (b - (1 : Fin (n + (3 :
            ℕ)))), p.vertex (b - (1 : Fin (n + (3 : ℕ))) + (1 : Fin (n + (3 : ℕ)))), y] else
            P3381T1TriangleDeterminant ![p.vertex (b - (1 : Fin (n + (3 : ℕ)))), p.vertex (b -
            (1 : Fin (n + (3 : ℕ))) + (1 : Fin (n + (3 : ℕ)))), y] < (0 : ℝ)) → (
        let S := Metric.ball x0 rS ∩ Metric.ball B r
        let qside : Real × Real := if 0 < cross u w then w else -w
        ∀ (η : ℝ),
        let yp := x0 + η • qside
        let ym := x0 - η • qside
        (yp ∈ S) → ((ym ∈ S) → ((P3381T1TriangleDeterminant ![a, B, yp] < 0) → ((0 <
            P3381T1TriangleDeterminant ![a, B, ym]) → ((yp ∈ O ↔ ym ∉ O))))))) ) := by
  classical
  intro n p v b hprev B a c u w cross O rK r σ x0 rS sbit hrule S qside η yp ym hypS hymS
      hdetPlus hdetMinus
  have hpS := hrule yp hypS.1
  have hmS := hrule ym hymS.1
  have hpS' : yp ∈ O ↔ if sbit then 0 < P3381T1TriangleDeterminant ![a, B, yp]
      else P3381T1TriangleDeterminant ![a, B, yp] < 0 := by
    simpa [O, a, B, v, hprev] using hpS
  have hmS' : ym ∈ O ↔ if sbit then 0 < P3381T1TriangleDeterminant ![a, B, ym]
      else P3381T1TriangleDeterminant ![a, B, ym] < 0 := by
    simpa [O, a, B, v, hprev] using hmS
  by_cases hb : sbit
  · have hpiff : yp ∈ O ↔ 0 < P3381T1TriangleDeterminant ![a, B, yp] := by
      simpa only [ite_eq_left hb] using hpS'
    have hmiff : ym ∈ O ↔ 0 < P3381T1TriangleDeterminant ![a, B, ym] := by
      simpa only [ite_eq_left hb] using hmS'
    have hpnot : yp ∉ O := by intro h; exact (not_lt_of_ge (le_of_lt hdetPlus)) (hpiff.mp h)
    have hm : ym ∈ O := hmiff.mpr hdetMinus
    simp [hpnot, hm]
  · have hpiff : yp ∈ O ↔ P3381T1TriangleDeterminant ![a, B, yp] < 0 := by
      simpa only [ite_eq_right hb] using hpS'
    have hmiff : ym ∈ O ↔ P3381T1TriangleDeterminant ![a, B, ym] < 0 := by
      simpa only [ite_eq_right hb] using hmS'
    have hp : yp ∈ O := hpiff.mpr hdetPlus
    have hmnot : ym ∉ O := by intro h; exact (not_lt_of_ge (le_of_lt hdetMinus)) (hmiff.mp h)
    simp [hp, hmnot]

private theorem hNanchor :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        (cross u w ≠ 0) → (
        let O := P3544T1RayParity p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (cross w u = -cross u w) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          0 < cross U (x - B) ∧ cross V (x - B) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          (cross U (x - B) < 0 ∨ 0 < cross V (x - B))}
        (∀ x, x ∈ W → x ∉ O) → (
        let σ := min (1 / 2) (r / (4 * (dist B a + 1)))
        (0 < σ) → (
        let x0 := B + σ • u
        ∀ (rS : ℝ),
        let S := Metric.ball x0 rS ∩ Metric.ball B r
        let qside : Real × Real := if 0 < cross u w then w else -w
        (0 < cross u qside) → (∀ (η : ℝ), ((0 : ℝ) < η) → (
        let yp := x0 + η • qside
        let ym := x0 - η • qside
        (yp ∈ S) → ((ym ∈ S) → ((cross u (yp-B) = η * cross u qside) → ((cross u (ym-B) = -(η *
            cross u qside)) → ((cross w (yp-B) = σ * cross w u) → ((cross w (ym-B) = σ * cross w
            u) → (((yp ∈ O ↔ ym ∉ O)) → (∃ z, z ∈ N ∧ z ∈ O))))))))))))) ) := by
  classical
  intro n p v b B a c u w cross hdet O rK r hswap U V N W hWeven σ hσ x0 rS S qside hcrossUq η hη
      yp ym hypS hymS hcrossUplus hcrossUminus hcrossWplus hcrossWminus hOpp
  by_cases hp : 0 < cross u w
  · have hNp : yp ∈ N := by
      refine ⟨hypS.2, ?_, ?_⟩
      · simpa [U, hp] using (show 0 < cross u (yp-B) from by
          rw [hcrossUplus]
          exact mul_pos hη hcrossUq)
      · have hneg : cross w u < 0 := by rw [hswap]; linarith
        simpa [V, hp] using (show cross w (yp-B) < 0 from by
          rw [hcrossWplus]
          exact mul_neg_of_pos_of_neg hσ hneg)
    have hWm : ym ∈ W := by
      refine ⟨hymS.2, Or.inl ?_⟩
      simpa [U, hp] using (show cross u (ym-B) < 0 from by
        rw [hcrossUminus]
        exact neg_neg_of_pos (mul_pos hη hcrossUq))
    have hymnot := hWeven ym hWm
    exact ⟨yp, hNp, hOpp.mpr hymnot⟩
  · have hn : cross u w < 0 := lt_of_le_of_ne (le_of_not_gt hp) hdet
    have hNu : ym ∈ N := by
      refine ⟨hymS.2, ?_, ?_⟩
      · have hpos : 0 < cross w u := by rw [hswap]; exact neg_pos.mpr hn
        simpa [U, hp] using (show 0 < cross w (ym-B) from by
          rw [hcrossWminus]
          exact mul_pos hσ hpos)
      · simpa [V, hp] using (show cross u (ym-B) < 0 from by
          rw [hcrossUminus]
          exact neg_neg_of_pos (mul_pos hη hcrossUq))
    have hWp : yp ∈ W := by
      refine ⟨hypS.2, Or.inr ?_⟩
      simpa [V, hp] using (show 0 < cross u (yp-B) from by
        rw [hcrossUplus]
        exact mul_pos hη hcrossUq)
    have hypnot := hWeven yp hWp
    have hymO : ym ∈ O := by
      by_contra hm
      exact hypnot (hOpp.mpr hm)
    exact ⟨ym, hNu, hymO⟩

private theorem hLocalCone :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))),
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (∀ x : Real × Real, (∃ s t : Real, 0 < s ∧ 0 < t ∧ x = B + s • u + t • w) ↔ (0 < cross U
            (x - B) ∧ cross V (x - B) < 0)) → (
        let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          0 < cross U (x - B) ∧ cross V (x - B) < 0}
        let W : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          (cross U (x - B) < 0 ∨ 0 < cross V (x - B))}
        (∀ x, x ∈ Metric.ball B r → x ∉ C → x ∈ N ∨ x ∈ W) → ((∀ x, x ∈ W → x ∉ O) → ((∀ x, x ∈ N
            → x ∈ O) → (∀ x : Real × Real, x ∈ Metric.ball B r → (x ∈ O ↔ ∃ s t : Real, 0 < s ∧ 0
            < t ∧ x = B + s • u + t • w))))) ) := by
  classical
  intro n p v b B a c u w cross O C rK r U V hconeUV N W hcover hWeven hNodd x hx
  constructor
  · intro hxO
    have hxC : x ∉ C := by
      change x ∉ C ∧ _ at hxO
      exact hxO.1
    rcases hcover x hx hxC with hxN | hxW
    · exact (hconeUV x).mpr ⟨hxN.2.1, hxN.2.2⟩
    · exact False.elim (hWeven x hxW hxO)
  · intro hxcone
    have hsign := (hconeUV x).mp hxcone
    exact hNodd x ⟨hx, hsign.1, hsign.2⟩

end ExposedCornerGeometry

namespace ExposedCornerAssembly

private theorem hynotC :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f), ∀ (b : Fin (n + (3 : ℕ))), (b - 1 + 1 = b) → (
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 : Fin
            (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 :
            ℕ))))) / (2 : ℝ)))), x ∈ P3544T1BoundaryCarrier p ↔ x ∈ segment ℝ (p.vertex b)
            (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) ∨ x ∈ segment ℝ (p.vertex (b - (1 : Fin (n +
            (3 : ℕ))))) (p.vertex b)) → ((∀ (i : Fin (n + (3 : ℕ))), ∀ x ∈ segment ℝ (p.vertex i)
            (p.vertex (i + (1 : Fin (n + (3 : ℕ))))), ((fun (x : ℝ × ℝ) => x.1 +
            Classical.choose hqexists * x.2) : ℝ × ℝ → ℝ) x ≤ ((fun (x : ℝ × ℝ) => x.1 +
                Classical.choose hqexists * x.2) : ℝ × ℝ → ℝ) (p.vertex b)) → (
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        (y ∈ Metric.ball B r) → ((((fun (x : ℝ × ℝ) => x.1 + Classical.choose hqexists
            * x.2) : ℝ × ℝ → ℝ) (p.vertex b) < ((fun (x
            : ℝ × ℝ) => x.1 + Classical.choose hqexists * x.2) :
            ℝ × ℝ → ℝ) (p.vertex b + ε • ((1 : ℝ), (0 : ℝ)))) → (p.vertex b + ε • ((1 : ℝ), (0 :
            ℝ)) ∉ P3544T1BoundaryCarrier p))))) ) := by
  classical
  intro n p v f hqexists b hprev B a c rK r hcarrierLocal hsegmentHeight e ε y hyball hyheight
  exact (show
      y ∉ (P3544T1BoundaryCarrier p)
    from by
      classical
      intro hyC
      have hle := ((ExposedCornerGeometry.hellCarrier n p hqexists b hprev rK hcarrierLocal
          hsegmentHeight)) y hyball hyC
      exact (not_lt_of_ge hle) hyheight)

private theorem hWeven :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
          ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
        ∀ (hqexists : ∃ q : Real, q ∉ Set.range f),
        let q := Classical.choose hqexists
        ∀ (b : Fin (n + (3 : ℕ))),
        let c := v (b + 1)
        let B := v b
        let e : Real × Real := (1, 0)
        ∀ (ε : ℝ),
        let y : Real × Real := B + ε • e
        let ell : (Real × Real) →ₗ[Real] Real :=
          { toFun := fun x => x.1 + q * x.2
            map_add' := by intro x y; simp; ring
            map_smul' := by intro c x; simp; ring }
        let a := v (b - 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        (
        let B := p.vertex b;
        let a := p.vertex (b - (1 : Fin (n + (3 : ℕ))));
        let u := a - B; ((fun (x : ℝ × ℝ) => x.1 + Classical.choose hqexists * x.2) : ℝ × ℝ → ℝ)
            u < (0 : ℝ)) → ((
        let B := p.vertex b;
        let w := p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - B; ((fun (x : ℝ × ℝ) => x.1 +
            Classical.choose hqexists * x.2) : ℝ × ℝ → ℝ) w < (0
            : ℝ)) → (
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ((fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) ≠ (0 : ℝ)) → ((∀ (x
            : ℝ × ℝ), ∀ (d : ℝ × ℝ), x ∉ P3544T1BoundaryCarrier p → (∀ (i : Fin (n + (3 : ℕ))),
            d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (∀ (i : Fin (n + (3
            : ℕ))), d.1 * (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).2 - d.2 *
            (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).1 ≠ (0 : ℝ)) → (x ∈
            P3544T1RayParity p ↔ {i : Fin (n + (3 : ℕ)) | ∃ (t : ℝ), (0 : ℝ) < t ∧ x + t • d ∈
            segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ)))))}.ncard % (2 : ℕ) = (1
            : ℕ))) → (∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 : Fin
            (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 :
            ℕ))))) / (2 : ℝ)))), x ∈ P3544T1BoundaryCarrier p ↔ x ∈ segment ℝ (p.vertex b)
            (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) ∨ x ∈ segment ℝ (p.vertex (b - (1 : Fin (n +
            (3 : ℕ))))) (p.vertex b)) → ((∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (z : ℝ × ℝ), z ∈
            segment ℝ x y → ∃ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), z = x + t • (y - x)) → ((
        let cross := fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1; ∀ (z : ℝ × ℝ), IsLinearMap ℝ
            (cross z)) → ((
        let cross := fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1; ∀ (z : ℝ × ℝ), cross z z = (0 :
            ℝ)) → ((cross w u = -cross u w) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (∀ (x : ℝ × ℝ), (∃ (s : ℝ) (t : ℝ), (0 : ℝ) < s ∧ (0 : ℝ) < t ∧ x = p.vertex b + s •
            (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) + t • (p.vertex (b + (1 : Fin
            (n + (3 : ℕ)))) - p.vertex b)) ↔ (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 *
            y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) then p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b + (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b) ∧ (fun (x y : ℝ × ℝ) => x.1 * y.2
            - x.2 * y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b
            - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b
            - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b) < (0 : ℝ)) → ((∀ (S : Set
            (ℝ × ℝ)), IsConnected S → (∀ x ∈ S, x ∉ P3544T1BoundaryCarrier p) → ∀ x ∈ S, ∀ y ∈
            S, x ∈ P3544T1RayParity p ↔ y ∈ P3544T1RayParity p) → (
        let W : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          (cross U (x - B) < 0 ∨ 0 < cross V (x - B))}
        (IsPathConnected W) → ((∀ (i : Fin (n + (3 : ℕ))), ∀ x ∈ segment ℝ (p.vertex i) (p.vertex
            (i + (1 : Fin (n + (3 : ℕ))))), ((fun (x : ℝ × ℝ) => x.1 + Classical.choose
            hqexists * x.2) : ℝ × ℝ → ℝ) x ≤ ((fun (x :
            ℝ × ℝ) => x.1 + Classical.choose hqexists * x.2) : ℝ
            × ℝ → ℝ) (p.vertex b)) → ((∀ x ∈ Metric.ball (p.vertex b) (min rK (min (dist
            (p.vertex b) (p.vertex (b - (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b)
            (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)))), x ∉ P3544T1BoundaryCarrier p
            → x ∈ {x : ℝ × ℝ | x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b)
            (p.vertex (b - (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b +
            (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)))) ∧ (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 -
            x.2 * y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b -
            (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) then p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b
            + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b) ∧ (fun (x y : ℝ × ℝ) => x.1
            * y.2 - x.2 * y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1)
            (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3
            : ℕ)))) - p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else
            p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b) < (0 : ℝ)} ∨ x
            ∈ {x : ℝ × ℝ | x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex
            (b - (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin
            (n + (3 : ℕ))))) / (2 : ℝ)))) ∧ ((fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (if (0
            : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 :
            ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then
            p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b + (1 : Fin (n +
            (3 : ℕ)))) - p.vertex b) (x - p.vertex b) < (0 : ℝ) ∨ (0 : ℝ) < (fun (x y : ℝ × ℝ) =>
            x.1 * y.2 - x.2 * y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1)
            (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3
            : ℕ)))) - p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else
            p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b))}) → ((y ∈
            Metric.ball B r) → ((((fun (x : ℝ × ℝ) => x.1 + Classical.choose hqexists *
            x.2) : ℝ × ℝ → ℝ) (p.vertex b) < ((fun (x :
            ℝ × ℝ) => x.1 + Classical.choose hqexists * x.2) : ℝ
            × ℝ → ℝ) (p.vertex b + ε • ((1 : ℝ), (0 : ℝ)))) → ((p.vertex b + ε • ((1 : ℝ), (0 :
            ℝ)) ∉ P3544T1BoundaryCarrier p) → (∀ (d0 : ℝ × ℝ), (∀ (i : Fin (n + (3 : ℕ))), d0.1
            * (p.vertex i - y).2 - d0.2 * (p.vertex i - y).1 ≠ (0 : ℝ)) → ((∀ (i : Fin (n + (3 :
            ℕ))), d0.1 * (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).2 - d0.2 *
            (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).1 ≠ (0 : ℝ)) → (
        let badV : Fin (n + 3) → Real := fun i =>
          if (v i - y).2 = 0 then 0 else -cross d0 (v i - y) / (v i - y).2
        let badE : Fin (n + 3) → Real := fun i =>
          if (v (i + 1) - v i).2 = 0 then 0 else
            -cross d0 (v (i + 1) - v i) / (v (i + 1) - v i).2
        let T := max 0 (-ell d0 + 1)
        ∀ (κ : ℝ), (κ ∈ Set.Ioi T) → ((κ ∉ Set.range badV ∪ Set.range badE) → (∀ x ∈ {x : ℝ × ℝ |
            x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 : Fin
            (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 :
            ℕ))))) / (2 : ℝ)))) ∧ ((fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (if (0 : ℝ) <
            (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ))))
            - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then p.vertex (b
            - (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) (x - p.vertex b) < (0 : ℝ) ∨ (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 -
            x.2 * y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b -
            (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b
            - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b))}, x ∉ P3544T1RayParity
            p))))))))))))))))))))) ) := by
  classical
  intro n p v f hqexists q b c B e ε y ell a u w hellu hellw cross hdet hparity rK r
      hcarrierLocal hsegParam hcrossLinear hcrossSelf hswap U V hconeUV hconstOn W hWpc
      hsegmentHeight hcover hyball hyheight hynotC d0 hdv0 hde0 badV badE T κ hκT hκbad
  have hWoff : ∀ x, x ∈ W → x ∉ P3544T1BoundaryCarrier p := by
    classical
    intro x hx hc
    have hs := ((ExposedCornerGeometry.hcarrierSigns n p b hdet rK hcarrierLocal hsegParam
          hcrossLinear hcrossSelf hswap)) x hx.1 hc
    rcases hx.2 with hn | hp
    · exact (not_lt_of_ge hs.1) hn
    · exact (not_lt_of_ge hs.2) hp
  have hyW := ExposedCornerGeometry.hYclass n p hqexists b ε rK
      hconeUV hcover (ExposedCornerGeometry.hconeHeight n p hqexists b hellu hellw) hyball
      hyheight hynotC
  have hyEven := ExposedCornerGeometry.hyEven n p b hparity ε hynotC d0 κ
      (ExposedCornerGeometry.hdv n p b ε d0 hdv0 κ hκbad) (ExposedCornerGeometry.hde n p b ε d0
      hde0 κ hκbad) (ExposedCornerGeometry.hhitsEmpty n p hqexists b ε hsegmentHeight hyheight d0
      κ (ExposedCornerGeometry.hellD n p hqexists d0 κ hκT))
  intro x hx hxO
  exact hyEven ((hconstOn W hWpc.isConnected hWoff y hyW x hx).mpr hxO)

private theorem hLocalCone :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let v := p.vertex
        ∀ (b : Fin (n + (3 : ℕ))), (b - 1 + 1 = b) → (
        let B := v b
        let a := v (b - 1)
        let c := v (b + 1)
        let u : Real × Real := a - B
        let w : Real × Real := c - B
        let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
        ((fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) ≠ (0 : ℝ)) → (
        let O := P3544T1RayParity p
        ∀ (rK : ℝ),
        let r := min rK (min (dist B a / 2) (dist B c / 2))
        (∀ x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 : Fin
            (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 :
            ℕ))))) / (2 : ℝ)))), x ∈ P3544T1BoundaryCarrier p ↔ x ∈ segment ℝ (p.vertex b)
            (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) ∨ x ∈ segment ℝ (p.vertex (b - (1 : Fin (n +
            (3 : ℕ))))) (p.vertex b)) → ((∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (z : ℝ × ℝ), z ∈
            segment ℝ x y → ∃ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), z = x + t • (y - x)) → ((
        let cross := fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1; ∀ (z : ℝ × ℝ), IsLinearMap ℝ
            (cross z)) → ((cross w u = -cross u w) → (
        let U := if 0 < cross u w then u else w
        let V := if 0 < cross u w then w else u
        (∀ (x : ℝ × ℝ), (∃ (s : ℝ) (t : ℝ), (0 : ℝ) < s ∧ (0 : ℝ) < t ∧ x = p.vertex b + s •
            (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) + t • (p.vertex (b + (1 : Fin
            (n + (3 : ℕ)))) - p.vertex b)) ↔ (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 *
            y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) then p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b + (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b) ∧ (fun (x y : ℝ × ℝ) => x.1 * y.2
            - x.2 * y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b
            - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b
            - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b) < (0 : ℝ)) → ((∀ (S : Set
            (ℝ × ℝ)), IsConnected S → (∀ x ∈ S, x ∉ P3544T1BoundaryCarrier p) → ∀ x ∈ S, ∀ y ∈
            S, x ∈ P3544T1RayParity p ↔ y ∈ P3544T1RayParity p) → (
        let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
          0 < cross U (x - B) ∧ cross V (x - B) < 0}
        (IsPathConnected N) → ((∀ x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b)
            (p.vertex (b - (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b +
            (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)))), x ∉ P3544T1BoundaryCarrier p → x ∈ {x : ℝ ×
            ℝ | x ∈ Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 :
            Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 :
            ℕ))))) / (2 : ℝ)))) ∧ (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (if (0 :
            ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 :
            ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then
            p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b + (1 : Fin (n +
            (3 : ℕ)))) - p.vertex b) (x - p.vertex b) ∧ (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 *
            y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b) < (0 : ℝ)} ∨ x ∈ {x : ℝ × ℝ | x ∈
            Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 : Fin (n +
            (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) /
            (2 : ℝ)))) ∧ ((fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (if (0 : ℝ) < (fun (x y :
            ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then p.vertex (b - (1 : Fin
            (n + (3 : ℕ)))) - p.vertex b else p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) (x - p.vertex b) < (0 : ℝ) ∨ (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 *
            y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b))}) → ((∀ x ∈ {x : ℝ × ℝ | x ∈
            Metric.ball (p.vertex b) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 : Fin (n +
            (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) /
            (2 : ℝ)))) ∧ ((fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (if (0 : ℝ) < (fun (x y :
            ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then p.vertex (b - (1 : Fin
            (n + (3 : ℕ)))) - p.vertex b else p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) (x - p.vertex b) < (0 : ℝ) ∨ (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 *
            y.1) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (x - p.vertex b))}, x ∉ P3544T1RayParity p) → (
        let σ := min (1 / 2) (r / (4 * (dist B a + 1)))
        (0 < σ) → (
        let x0 := B + σ • u
        ∀ (rS : ℝ), ∀ (sbit : Bool), (∀ y ∈ Metric.ball x0 rS, y ∈ P3544T1RayParity p ↔ if sbit
            = true then (0 : ℝ) < P3381T1TriangleDeterminant ![p.vertex (b - (1 : Fin (n + (3 :
            ℕ)))), p.vertex (b - (1 : Fin (n + (3 : ℕ))) + (1 : Fin (n + (3 : ℕ)))), y] else
            P3381T1TriangleDeterminant ![p.vertex (b - (1 : Fin (n + (3 : ℕ)))), p.vertex (b -
            (1 : Fin (n + (3 : ℕ))) + (1 : Fin (n + (3 : ℕ)))), y] < (0 : ℝ)) → (
        let S := Metric.ball x0 rS ∩ Metric.ball B r
        let qside : Real × Real := if 0 < cross u w then w else -w
        (
        let qside := if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1
            : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else -(p.vertex
            (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b); (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 *
            y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) qside) → ((
        let qside := if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1
            : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else -(p.vertex
            (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b); (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 *
            y.1) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) qside = (0 : ℝ)) → (∀ (η :
            ℝ), ((0 : ℝ) < η) → (
        let yp := x0 + η • qside
        let ym := x0 - η • qside
        (yp ∈ S) → ((
        let ym := p.vertex b + min (1 / 2 : ℝ) (min rK (min (dist (p.vertex b) (p.vertex (b - (1
            : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3
            : ℕ))))) / (2 : ℝ))) / ((4 : ℝ) * (dist (p.vertex b) (p.vertex (b - (1 : Fin (n + (3
            : ℕ))))) + (1 : ℝ)))) • (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) - η •
            if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n
            + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then
            p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else -(p.vertex (b + (1 : Fin (n
            + (3 : ℕ)))) - p.vertex b); ym ∈ Metric.ball (p.vertex b + min (1 / 2 : ℝ) (min rK
            (min (dist (p.vertex b) (p.vertex (b - (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist
            (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ))) / ((4 : ℝ) * (dist
            (p.vertex b) (p.vertex (b - (1 : Fin (n + (3 : ℕ))))) + (1 : ℝ)))) • (p.vertex (b -
            (1 : Fin (n + (3 : ℕ)))) - p.vertex b)) rS ∩ Metric.ball (p.vertex b) (min rK (min
            (dist (p.vertex b) (p.vertex (b - (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist
            (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ))))) → ((yp - B = σ •
            u + η • qside) → ((ym - B = σ • u - η • qside) → (((fun (x y : ℝ × ℝ) => x.1 * y.2 -
            x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) ((p.vertex b + min
            (1 / 2 : ℝ) (min rK (min (dist (p.vertex b) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))))
            / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ))) /
            ((4 : ℝ) * (dist (p.vertex b) (p.vertex (b - (1 : Fin (n + (3 : ℕ))))) + (1 : ℝ)))) •
            (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) + η • if (0 : ℝ) < (fun (x y :
            ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then p.vertex (b + (1 : Fin
            (n + (3 : ℕ)))) - p.vertex b else -(p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b)) - p.vertex b) = η * (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b -
            (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2
            - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1
            : Fin (n + (3 : ℕ)))) - p.vertex b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b else -(p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b))) → (((fun (x
            y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) -
            p.vertex b) ((p.vertex b + min (1 / 2 : ℝ) (min rK (min (dist (p.vertex b) (p.vertex
            (b - (1 : Fin (n + (3 : ℕ))))) / (2 : ℝ)) (dist (p.vertex b) (p.vertex (b + (1 : Fin
            (n + (3 : ℕ))))) / (2 : ℝ))) / ((4 : ℝ) * (dist (p.vertex b) (p.vertex (b - (1 : Fin
            (n + (3 : ℕ))))) + (1 : ℝ)))) • (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b)
            - η • if (0 : ℝ) < (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            b) then p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else -(p.vertex (b + (1 :
            Fin (n + (3 : ℕ)))) - p.vertex b)) - p.vertex b) = -(η * (fun (x y : ℝ × ℝ) => x.1 *
            y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ)))) - p.vertex b) (if (0 : ℝ) <
            (fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1) (p.vertex (b - (1 : Fin (n + (3 : ℕ))))
            - p.vertex b) (p.vertex (b + (1 : Fin (n + (3 : ℕ)))) - p.vertex b) then p.vertex (b
            + (1 : Fin (n + (3 : ℕ)))) - p.vertex b else -(p.vertex (b + (1 : Fin (n + (3 : ℕ))))
            - p.vertex b)))) → ((
        let B := p.vertex b;
        let a := p.vertex (b - (1 : Fin (n + (3 : ℕ))));
        let u := a - B;
        let cross := fun (x y : ℝ × ℝ) => x.1 * y.2 - x.2 * y.1; ∀ (z : ℝ × ℝ),
            P3381T1TriangleDeterminant ![a, B, z] = -cross u (z - B)) → (∀ x : Real × Real, x ∈
            Metric.ball B r → (x ∈ O ↔ ∃ s t : Real, 0 < s ∧ 0 < t ∧ x = B + s • u + t •
            w)))))))))))))))))))))))) ) := by
  classical
  intro n p v b hprev B a c u w cross hdet O rK r hcarrierLocal hsegParam hcrossLinear hswap U V
      hconeUV hconstOn N hNpc hcover hWeven σ hσ x0 rS sbit hrule S qside hcrossUq hcrossWq η hη
      yp ym hypS hymS hyplus hyminus hcrossUplus hcrossUminus hdetSide
  exact ExposedCornerGeometry.hLocalCone n p b rK hconeUV hcover hWeven
              ((show
                  ∀ x, x ∈ N → x ∈ O
                from by
                  classical
                  obtain ⟨z, hzN, hzO⟩ := ((ExposedCornerGeometry.hNanchor n p b hdet rK hswap
                      hWeven hσ rS
                                hcrossUq η hη hypS hymS hcrossUplus hcrossUminus ((show
                                    cross w (yp-B) = σ * cross w u
                                  from by
                                    classical
                                    change (∀ z, IsLinearMap ℝ (cross z)) at hcrossLinear
                                    change cross w qside = 0 at hcrossWq
                                    rw [hyplus, (hcrossLinear w).map_add, (hcrossLinear w).map_smul,
                                      (hcrossLinear w).map_smul, hcrossWq]
                                    simp only [smul_eq_mul, mul_zero, add_zero])) ((show
                                        cross w (ym-B) = σ * cross w u
                                      from by
                                        classical
                                        change (∀ z : Real × Real, IsLinearMap Real (cross z))
                                            at hcrossLinear
                                        change cross w qside = 0 at hcrossWq
                                        rw [hyminus, (hcrossLinear w).map_sub, (hcrossLinear
                                            w).map_smul,
                                          (hcrossLinear w).map_smul, hcrossWq]
                                        simp only [smul_eq_mul, mul_zero, sub_zero]))
                                            (ExposedCornerGeometry.hOpp n p b hprev rK rS
                                sbit hrule η hypS hymS ((show
                                    P3381T1TriangleDeterminant ![a, B, yp] < 0
                                  from by
                                    classical
                                    rw [hdetSide, hcrossUplus]
                                    exact neg_neg_of_pos (mul_pos hη hcrossUq))) ((show
                                        0 < P3381T1TriangleDeterminant ![a, B, ym]
                                      from by
                                        classical
                                        rw [hdetSide, hcrossUminus]
                                        exact neg_pos.mpr (neg_neg_of_pos (mul_pos hη
                                            hcrossUq)))))))
                  intro x hx
                  have hsame := hconstOn N hNpc.isConnected ((ExposedCornerGeometry.hNoff n
                                p b rK (ExposedCornerGeometry.hcarrierCross n p b rK
                                    hcarrierLocal hsegParam
                                hcrossLinear))) x hx z hzN
                  exact hsame.mpr hzO))

end ExposedCornerAssembly

theorem P3650T1ExposedCornerExists {n : Nat} (p : P3381T1PolygonBoundary n) :
    Nonempty (P3650T1ExposedCorner p) := by
-- BODY
  classical
  let v := p.vertex
  let f : Fin (n + 3) × Fin (n + 3) → Real := fun ij =>
    ((v ij.2).1 - (v ij.1).1) / ((v ij.1).2 - (v ij.2).2)
  have hqexists : ∃ q : Real, q ∉ Set.range f :=
    Set.finite_range f |>.exists_notMem
  let q := Classical.choose hqexists
  let ell : (Real × Real) →ₗ[Real] Real :=
    { toFun := fun x => x.1 + q * x.2
      map_add' := by intro x y; simp; ring
      map_smul' := by intro c x; simp; ring }
  have hdistinct := ExposedCornerGeometry.hdistinct n p hqexists (Classical.choose_spec hqexists)
  obtain ⟨b, hb, hmax⟩ := Finset.univ.exists_max_image
    (fun i : Fin (n + 3) => ell (v i)) (Finset.univ_nonempty)
  have hstrict := ExposedCornerGeometry.hstrict n p hqexists hdistinct b hmax
  have hprev : b - 1 + 1 = b := by simp
  have hnextne := ExposedCornerGeometry.hnextne n b
  have hprevne := ExposedCornerGeometry.hprevne n b hprev hnextne
  let B := v b
  let a := v (b - 1)
  let c := v (b + 1)
  let u : Real × Real := a - B
  let w : Real × Real := c - B
  have haB := ExposedCornerGeometry.haB n p b hprevne
  have hcB := ExposedCornerGeometry.hcB n p b hnextne
  have hu : u ≠ 0 := sub_ne_zero.mpr haB
  have hw : w ≠ 0 := sub_ne_zero.mpr hcB
  have hellu := ExposedCornerGeometry.hellu n p hqexists b hstrict hprevne
  have hellw := ExposedCornerGeometry.hellw n p hqexists b hstrict hnextne
  have hlineMap := AffineLineMapProperties.coordinates
  let cross (x y : Real × Real) : Real := x.1 * y.2 - x.2 * y.1
  have hdet := ExposedCornerGeometry.hdetAt218 n p hqexists b hprev hprevne hu hw hellu hellw
      hlineMap (ExposedCornerGeometry.hcrosszero)
  have htriangle : P3381T1TriangleDeterminant ![a, B, c] ≠ 0 := ExposedCornerGeometry.htriangle
      n p b hdet
  let D := cross (c - a) (B - a)
  let L : (Real × Real) →ₗ[Real] Real :=
    { toFun := fun x => cross (c - a) x * D⁻¹
      map_add' := by intro x y; simp [cross]; ring
      map_smul' := by intro t x; simp [cross]; ring }
  let F : (Real × Real) → Real := fun x => L (x - a)
  let height : (Real × Real) →ᵃ[Real] Real := AffineMap.mk' F L a (ExposedCornerGeometry.hFaff n
      p b)
  have hFa : F a = 0 := by simp [F, L, cross]
  have hFc : F c = 0 := ExposedCornerGeometry.hFc n p b
  have hFB : F B = 1 := ExposedCornerGeometry.hFB n p b (ExposedCornerGeometry.hD n p b htriangle)
  have hheightPrev : height a = 0 := by simpa [height] using hFa
  have hheightTop : height B = 1 := by simpa [height] using hFB
  have hheightNext : height c = 0 := by simpa [height] using hFc
  let O := P3544T1RayParity p
  rcases P3544T1LocalParity p with
    ⟨_, _, _, _, hlocal, hgeneric, hparity, _, hsides⟩
  let J : Set (Fin (n + 3)) := {j | j ≠ b ∧ j + 1 ≠ b}
  let K : Set (Real × Real) := ⋃ j ∈ J,
    segment Real (v j) (v (j + 1))
  have hKopen : IsOpen Kᶜ := (ExposedCornerGeometry.hKcompact n p b
      (ExposedCornerGeometry.hsegcompact n p)).isClosed.isOpen_compl
  obtain ⟨rK, hrK, hballK⟩ := Metric.isOpen_iff.mp hKopen B (ExposedCornerGeometry.hBnotK n p b)
  have hdistA : 0 < dist B a := dist_pos.mpr haB.symm
  have hdistC : 0 < dist B c := dist_pos.mpr hcB.symm
  let r := min rK (min (dist B a / 2) (dist B c / 2))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrKle : r ≤ rK := min_le_left _ _
  have hrAle : r ≤ dist B a / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrCle : r ≤ dist B c / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hrA : r < dist B a := lt_of_le_of_lt hrAle (half_lt_self hdistA)
  have hrC : r < dist B c := lt_of_le_of_lt hrCle (half_lt_self hdistC)
  have hcarrierLocal := ExposedCornerGeometry.hcarrierLocal n p b hprev rK hballK hrKle
      (ExposedCornerGeometry.haddinj n)
  have hsegParam := ExposedCornerGeometry.hsegParam hlineMap
  have hcrossLinear : ∀ z, IsLinearMap ℝ (cross z) := ExposedCornerGeometry.hcrossLinear
  have hcrossSelf : ∀ z, cross z z = 0 := ExposedCornerGeometry.hcrossSelf
  have hswap : cross w u = -cross u w := by dsimp [cross]; ring
  have hpos : 0 < cross u w ∨ cross u w < 0 := lt_or_gt_of_ne hdet.symm
  let U := if 0 < cross u w then u else w
  let V := if 0 < cross u w then w else u
  have hUV := ExposedCornerGeometry.hUV n p b hswap hpos
  have hdecomp := ExposedCornerGeometry.hdecomp n p b hUV
  have hconeUV := ExposedCornerGeometry.hconeUV n p b hcrossLinear hUV hdecomp
  have hconstOn := ExposedCornerGeometry.hconstOn n p hlocal
  let N0 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧
    0 < cross U z ∧ cross V z < 0}
  let W1 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧ cross U z < 0}
  let W2 : Set (Real × Real) := {z | z ∈ Metric.ball 0 r ∧ 0 < cross V z}
  let W0 : Set (Real × Real) := W1 ∪ W2
  let z0 := U + V
  have hz0U : cross U z0 = cross U V := by dsimp [z0]; dsimp [cross]; ring
  have hz0V : cross V z0 = -cross U V := by dsimp [z0]; dsimp [cross]; ring
  obtain ⟨τ, hτ, hτball⟩ := ExposedCornerGeometry.hsmallScale z0 r hr
  have hN0pc : IsPathConnected N0 := by
    exact (ExposedCornerGeometry.hNconvex n p b rK
        hcrossLinear).isPathConnected (ExposedCornerGeometry.hN0ne n p b rK hcrossLinear hUV hz0U
        hz0V τ hτ hτball)
  have hW1convex : Convex Real W1 :=
    (convex_ball 0 r).inter (convex_halfSpace_lt (hcrossLinear U) 0)
  have hW2convex : Convex Real W2 :=
    (convex_ball 0 r).inter (convex_halfSpace_gt (hcrossLinear V) 0)
  have hτnegBall := ExposedCornerGeometry.hτnegBall n p b rK τ hτball
  have hnegU := ExposedCornerGeometry.hnegU n p b hcrossLinear hUV hz0U τ hτ
  have hposV := ExposedCornerGeometry.hposV n p b hcrossLinear hUV hz0V τ hτ
  have hW1ne : W1.Nonempty := ⟨-(τ • z0), hτnegBall, hnegU⟩
  have hW2ne : W2.Nonempty := ⟨-(τ • z0), hτnegBall, hposV⟩
  have hWoverlap : (W1 ∩ W2).Nonempty :=
    ⟨-(τ • z0), ⟨hτnegBall, hnegU⟩, ⟨hτnegBall, hposV⟩⟩
  have hW0pc : IsPathConnected W0 :=
    (hW1convex.isPathConnected hW1ne).union
      (hW2convex.isPathConnected hW2ne) hWoverlap
  let N : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
    0 < cross U (x - B) ∧ cross V (x - B) < 0}
  let W : Set (Real × Real) := {x | x ∈ Metric.ball B r ∧
    (cross U (x - B) < 0 ∨ 0 < cross V (x - B))}
  have himageN : (fun z : Real × Real => B + z) '' N0 = N  := ExposedCornerGeometry.himageN n p b rK
  have himageW : (fun z : Real × Real => B + z) '' W0 = W  := ExposedCornerGeometry.himageW n p b rK
  have hNpc : IsPathConnected N :=
    himageN ▸ hN0pc.image (continuous_const.add continuous_id)
  have hWpc : IsPathConnected W :=
    himageW ▸ hW0pc.image (continuous_const.add continuous_id)
  have hsegmentHeight := ExposedCornerGeometry.hsegmentHeight n p hqexists b hmax hsegParam
  have hradialDist := ExposedCornerGeometry.hradialDist n p b
  have hUendpoint := ExposedCornerGeometry.hUendpoint n p b
  have hVendpoint := ExposedCornerGeometry.hVendpoint n p b
  have haxisU := ExposedCornerGeometry.haxisU n p b hlineMap rK hr hcarrierLocal hUV
    hdecomp hradialDist hUendpoint
    (ExposedCornerGeometry.hUdist n p b rK hrA hrC hUendpoint)
  have haxisV := ExposedCornerGeometry.haxisV n p b hlineMap rK hr hcarrierLocal hUV
    hdecomp hradialDist hVendpoint
    (ExposedCornerGeometry.hVdist n p b rK hrA hrC hVendpoint)
  have hcover := ExposedCornerGeometry.hcover n p b rK haxisU haxisV
  let e : Real × Real := (1, 0)
  obtain ⟨ε, hε, hεball⟩ := ExposedCornerGeometry.hsmallScale e r hr
  let y : Real × Real := B + ε • e
  have hyball := ExposedCornerGeometry.translateBall B (ε • e) r hεball
  have hyheight := ExposedCornerGeometry.hyheight n p hqexists b ε hε
  have hynotC := ExposedCornerAssembly.hynotC n p hqexists b hprev rK hcarrierLocal
      hsegmentHeight ε hyball hyheight
  obtain ⟨d0, hdv0, hde0⟩ := hgeneric y hynotC
  let badV : Fin (n + 3) → Real := fun i =>
    if (v i - y).2 = 0 then 0 else -cross d0 (v i - y) / (v i - y).2
  let badE : Fin (n + 3) → Real := fun i =>
    if (v (i + 1) - v i).2 = 0 then 0 else
      -cross d0 (v (i + 1) - v i) / (v (i + 1) - v i).2
  let T := max 0 (-ell d0 + 1)
  have hbadfinite : (Set.range badV ∪ Set.range badE).Finite :=
    (Set.finite_range badV).union (Set.finite_range badE)
  obtain ⟨κ, hκT, hκbad⟩ := (Set.Ioi_infinite T).exists_notMem_finite hbadfinite
  have hWeven := ExposedCornerAssembly.hWeven n p hqexists b ε hellu hellw hdet hparity rK
      hcarrierLocal hsegParam hcrossLinear hcrossSelf hswap hconeUV hconstOn hWpc hsegmentHeight
      hcover hyball hyheight hynotC d0 hdv0 hde0 κ hκT hκbad
  let σ := min (1 / 2) (r / (4 * (dist B a + 1)))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσle : σ ≤ r / (4 * (dist B a + 1)) := min_le_right _ _
  have hσlt : σ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let x0 := B + σ • u
  have hBu : B + u = a := by dsimp [u, a, B]; abel
  have hx0open : x0 ∈ openSegment Real a B := ExposedCornerGeometry.hx0open n p b hlineMap rK hσ
      hσlt
  have hx0prev : x0 ∈ openSegment Real (v (b - 1)) (v ((b - 1) + 1)) := by
    simpa [a, B, v, hprev] using hx0open
  obtain ⟨rS, hrS, sbit, hrule⟩ := hsides (b - 1) x0 hx0prev
  let S := Metric.ball x0 rS ∩ Metric.ball B r
  have hx0S : x0 ∈ S := ⟨Metric.mem_ball_self hrS, (ExposedCornerGeometry.hx0ball n p b rK hr
      (ExposedCornerGeometry.hdistx0 n p b rK hrK hdistA hdistC hr hradialDist hσ hσle hσlt hBu))⟩
  obtain ⟨δ, hδ, hballS⟩ := Metric.isOpen_iff.mp (Metric.isOpen_ball.inter Metric.isOpen_ball) x0
      hx0S
  let qside : Real × Real := if 0 < cross u w then w else -w
  have hcrossUq := ExposedCornerGeometry.hcrossUq n p b hdet hcrossLinear
  have hcrossWq := ExposedCornerGeometry.hcrossWq n p b hcrossLinear hcrossSelf
  obtain ⟨η, hη, hηball⟩ := ExposedCornerGeometry.hsmallScale qside δ hδ
  let yp := x0 + η • qside
  let ym := x0 - η • qside
  have hypS : yp ∈ S :=
    hballS (ExposedCornerGeometry.translateBall x0 (η • qside) δ hηball)
  have hymS : ym ∈ S := by
    have hh := ExposedCornerGeometry.translateBall x0 (-(η • qside)) δ
      (ExposedCornerGeometry.hηballNeg n p b δ η hηball)
    simpa [ym, S, x0, σ, u, a, B, c, v, r, sub_eq_add_neg] using hballS hh
  have hyplus : yp - B = σ • u + η • qside := by dsimp [yp, x0]; abel
  have hyminus : ym - B = σ • u - η • qside := by dsimp [ym, x0]; abel
  have hcrossUplus : cross u (yp - B) = η * cross u qside := by
    rw [hyplus, (hcrossLinear u).map_add, (hcrossLinear u).map_smul,
      (hcrossLinear u).map_smul, hcrossSelf]
    simp only [smul_eq_mul, mul_zero, zero_add]
  have hcrossUminus : cross u (ym - B) = -(η * cross u qside) := by
    rw [hyminus, (hcrossLinear u).map_sub, (hcrossLinear u).map_smul,
      (hcrossLinear u).map_smul, hcrossSelf]
    simp only [smul_eq_mul, mul_zero, zero_sub]
  have hdetSide := ExposedCornerGeometry.hdetSide n p b
  have hLocalCone : ∀ x : Real × Real, x ∈ Metric.ball B r →
      (x ∈ O ↔ ∃ s t : Real, 0 < s ∧ 0 < t ∧ x = B + s • u + t • w) :=
          ExposedCornerAssembly.hLocalCone n p b hprev hdet rK hcarrierLocal hsegParam
          hcrossLinear hswap hconeUV hconstOn hNpc hcover hWeven hσ rS sbit hrule hcrossUq
          hcrossWq η hη hypS hymS hyplus hyminus hcrossUplus hcrossUminus hdetSide
  refine ⟨⟨b, ell, hdistinct, hstrict, ?_, height, hheightPrev,
    hheightTop, hheightNext, ?_⟩⟩
  · simpa [a, B, c, v] using htriangle
  · refine ⟨r, hr, ?_⟩
    intro x hx
    simpa [O, a, B, c, u, w, v] using hLocalCone x hx

end ApollonianSuperharmonic

end
