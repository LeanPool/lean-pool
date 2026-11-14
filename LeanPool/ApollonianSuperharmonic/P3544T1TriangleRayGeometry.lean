/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3544T1LocalParity

-- [TABLET NODE: P3544T1TriangleRayGeometry]

/-!
# P3544T1TriangleRayGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TriangleRayIntersections

private theorem habAt122 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        a ≠ b ) := by
  classical
  intro p a b h
  exact (by decide : (0 : Fin 3) ≠ 1) (p.injective h)

private theorem hac :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let c : Real × Real := p.vertex 2
        a ≠ c ) := by
  classical
  intro p a c h
  exact (by decide : (0 : Fin 3) ≠ 2) (p.injective h)

private theorem hbcAt128 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        b ≠ c ) := by
  classical
  intro p b c h
  exact (by decide : (1 : Fin 3) ≠ 2) (p.injective h)

private theorem hu :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        (a ≠ b) → (b - a ≠ (0, 0)) ) := by
  classical
  intro p a b hab h
  apply hab
  apply Prod.ext
  · have hh := congrArg Prod.fst h
    simp at hh
    dsimp [a, b] at hh ⊢
    linarith
  · have hh := congrArg Prod.snd h
    simp at hh
    dsimp [a, b] at hh ⊢
    linarith

private theorem hDne :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        (a ≠ b) → ((a ≠ c) → ((b ≠ c) → ((b - a ≠ (0, 0)) → (P3381T1TriangleDeterminant
            p.vertex ≠ 0)))) ) := by
  classical
  intro p a b c hab hac hbc hu hD
  have hdet0 : (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2 = 0 := by
    simpa [P3381T1TriangleDeterminant, a, b, c] using hD
  have hcol : ∃ t : Real, c - a = t • (b - a) := by
    by_cases hx : b.1 - a.1 = 0
    · have hy : b.2 - a.2 ≠ 0 := by
        intro hy
        apply hu
        apply Prod.ext <;> simp [hx, hy]
      change (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) = 0 at hdet0
      rw [hx] at hdet0
      have hc0 : c.1 - a.1 = 0 := by
        have hm : (c.1 - a.1) * (b.2 - a.2) = 0 := by nlinarith
        exact (mul_eq_zero.mp hm).resolve_right hy
      refine ⟨(c - a).2 / (b - a).2, ?_⟩
      apply Prod.ext
      · change c.1 - a.1 = ((c.2 - a.2) / (b.2 - a.2)) * (b.1 - a.1)
        simp [hx, hc0]
      · change c.2 - a.2 = ((c.2 - a.2) / (b.2 - a.2)) * (b.2 - a.2)
        field_simp
    · have hy : b.1 - a.1 ≠ 0 := hx
      change (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) = 0 at hdet0
      refine ⟨(c - a).1 / (b - a).1, ?_⟩
      apply Prod.ext
      · change c.1 - a.1 = ((c.1 - a.1) / (b.1 - a.1)) * (b.1 - a.1)
        field_simp
      · change c.2 - a.2 = ((c.1 - a.1) / (b.1 - a.1)) * (b.2 - a.2)
        have hm : (b.1 - a.1) * (c.2 - a.2) = (c.1 - a.1) * (b.2 - a.2) := by linarith
        field_simp
        nlinarith
  obtain ⟨t, ht⟩ := hcol
  have ht0 : t ≠ 0 := by
    intro ht0
    have : c - a = (0 : Real) • (b - a) := by simpa [ht0] using ht
    apply hac
    have := congrArg (fun z : Real × Real => z + a) this
    have heq : c = a := by simpa using this
    exact heq.symm
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hbc
    have : c - a = (1 : Real) • (b - a) := by simpa [ht1] using ht
    have := congrArg (fun z : Real × Real => z + a) this
    have heq : c = b := by simpa using this
    exact heq.symm
  have hcform : c = (1 - t) • a + t • b := by
    have htx : c.1 - a.1 = t * (b.1 - a.1) := by
      have hh := congrArg Prod.fst ht
      simpa using hh
    have hty : c.2 - a.2 = t * (b.2 - a.2) := by
      have hh := congrArg Prod.snd ht
      simpa using hh
    ext <;> simp [smul_eq_mul] <;> nlinarith [htx, hty]
  rcases lt_trichotomy t 0 with htneg | htzero | htpos
  · have hseg : a ∈ segment Real b c := by
      rw [segment_eq_image]
      have hden : 0 < 1 - t := by linarith
      refine ⟨1 / (1 - t), ?_, ?_⟩
      · constructor
        · exact le_of_lt (div_pos (by norm_num) hden)
        · rw [div_le_one hden]
          linarith
      · rw [hcform]
        ext <;> simp [smul_eq_mul] <;> field_simp <;> ring
    have hpair := p.edge_intersection 1 2 (by decide)
    have hca : a ∈ segment Real c a := by
      rw [segment_eq_image]
      refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp []
    have : a ∈ segment Real b c ∩ segment Real c a := ⟨hseg, hca⟩
    have hpair' : segment Real b c ∩ segment Real c a =
        {x | (x = b ∨ x = c) ∧ (x = c ∨ x = a)} := by
      simpa [a, b, c] using hpair
    rw [hpair'] at this
    have hs := this
    simp only [Set.mem_ofPred_eq] at hs
    rcases hs.1 with h | h
    · exact hab h
    · exact hac h
  · exact (ht0 htzero).elim
  · rcases lt_trichotomy t 1 with htlt | hteq | htgt
    · have hcs : c ∈ segment Real a b := by
        rw [segment_eq_image]
        refine ⟨t, ⟨le_of_lt htpos, le_of_lt htlt⟩, ?_⟩
        rw [hcform]
      have hcb : c ∈ segment Real b c := by
        rw [segment_eq_image]
        refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
        simp []
      have hpair : segment Real a b ∩ segment Real b c =
          {x | (x = a ∨ x = b) ∧ (x = b ∨ x = c)} := by
        simpa [a, b, c] using p.edge_intersection 0 1 (by decide)
      have hi : c ∈ segment Real a b ∩ segment Real b c := ⟨hcs, hcb⟩
      rw [hpair] at hi
      simp only [Set.mem_ofPred_eq] at hi
      rcases hi.1 with h | h
      · exact hac h.symm
      · exact hbc h.symm
    · exact (ht1 hteq).elim
    · have hpair := p.edge_intersection 0 2 (by decide)
      have hpair' : segment Real a b ∩ segment Real c a =
          {x | (x = a ∨ x = b) ∧ (x = c ∨ x = a)} := by
        simpa [a, b, c] using hpair
      have hbca : b ∈ segment Real c a := by
        rw [segment_eq_image]
        refine ⟨(t - 1) / t, ?_, ?_⟩
        · constructor
          · exact div_nonneg (by linarith) (le_of_lt htpos)
          · rw [div_le_one htpos]
            linarith
        · rw [hcform]
          ext <;> simp [smul_eq_mul] <;> field_simp <;> ring
      have habseg : b ∈ segment Real a b := by
        rw [segment_eq_image]
        refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
        simp []
      have : b ∈ segment Real a b ∩ segment Real c a := ⟨habseg, hbca⟩
      rw [hpair'] at this
      have hs := this
      simp only [Set.mem_ofPred_eq] at hs
      rcases hs.2 with h | h
      · exact hbc h
      · exact hab h.symm

private theorem hsum :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        ∀ x, alpha x + beta x + gamma x = 1 ) := by
  classical
  intro p a b c D beta gamma alpha x
  simp [alpha]
  ring

private theorem hrec :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        ∀ x, x = alpha x • a + beta x • b + gamma x • c) ) := by
  classical
  intro p a b c D hDneq beta gamma alpha x
  dsimp [alpha, beta, gamma]
  ext <;> simp [smul_eq_mul]
  · field_simp [hDneq]
    simp [D]
    ring
  · field_simp [hDneq]
    simp [D]
    ring

private theorem hbeta_affine :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        ∀ x, ∀ y, ∀ s, ∀ t, s + t = 1 → beta (s • x + t • y) = s * beta x + t * beta y) ) := by
  classical
  intro p a b c D hDneq beta x y s t hst
  have hsub : s • x + t • y - a = s • (x - a) + t • (y - a) := by
    ext <;> simp [smul_eq_mul]
    · linear_combination a.1 * hst
    · linear_combination a.2 * hst
  change (((s • x + t • y - a).1 * (c - a).2 -
    (s • x + t • y - a).2 * (c - a).1) / D) =
    s * (((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D) +
    t * (((y - a).1 * (c - a).2 - (y - a).2 * (c - a).1) / D)
  rw [hsub]
  simp [smul_eq_mul]
  field_simp [hDneq]
  ring

private theorem hgamma_affine :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        ∀ x, ∀ y, ∀ s, ∀ t, s + t = 1 → gamma (s • x + t • y) = s * gamma x + t * gamma y) ) := by
  classical
  intro p a b c D hDneq gamma x y s t hst
  have hsub : s • x + t • y - a = s • (x - a) + t • (y - a) := by
    ext <;> simp [smul_eq_mul]
    · linear_combination a.1 * hst
    · linear_combination a.2 * hst
  change (((b - a).1 * (s • x + t • y - a).2 -
    (b - a).2 * (s • x + t • y - a).1) / D) =
    s * (((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D) +
    t * (((b - a).1 * (y - a).2 - (b - a).2 * (y - a).1) / D)
  rw [hsub]
  simp [smul_eq_mul]
  field_simp [hDneq]
  ring

private theorem halpha_affine :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        (∀ x, ∀ y, ∀ s, ∀ t, s + t = 1 → beta (s • x + t • y) = s * beta x + t * beta y) → ((∀ x,
            ∀ y, ∀ s, ∀ t, s + t = 1 → gamma (s • x + t • y) = s * gamma x + t * gamma y) → (∀ x,
            ∀ y, ∀ s, ∀ t, s + t = 1 → alpha (s • x + t • y) = s * alpha x + t * alpha y)) ) := by
  classical
  intro p a b c D beta gamma alpha hbeta_affine hgamma_affine x y s t hst
  simp [alpha, hbeta_affine x y s t hst, hgamma_affine x y s t hst]
  nlinarith [hst]

private theorem hCsubset :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (Convex Real K) → (P3544T1BoundaryCarrier p ⊆ K) ) := by
  classical
  intro p K hKconv x hx
  change x ∈ ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)) at hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
  have hpi : p.vertex i ∈ K := by
    change p.vertex i ∈ convexHull Real (Set.range p.vertex)
    exact subset_convexHull Real (Set.range p.vertex) ⟨i, rfl⟩
  have hpn : p.vertex (i + 1) ∈ K := by
    change p.vertex (i + 1) ∈ convexHull Real (Set.range p.vertex)
    exact subset_convexHull Real (Set.range p.vertex) ⟨i + 1, rfl⟩
  exact hKconv.segment_subset hpi hpn hi

private theorem hβb :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        beta b = 1) ) := by
  classical
  intro p a b c D hDneq beta
  dsimp [beta]
  field_simp [hDneq]
  simp [D]
  ring

private theorem hγb :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        gamma b = 0) ) := by
  classical
  intro p a b c D hDneq gamma
  dsimp [gamma]
  field_simp [hDneq]
  ring

private theorem hβc :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        beta c = 0) ) := by
  classical
  intro p a b c D hDneq beta
  dsimp [beta]
  field_simp [hDneq]
  ring

private abbrev hγc :=
  ApollonianSuperharmonic.TriangleRayIntersections.hβb

private theorem hSconv :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        (∀ x, ∀ y, ∀ s, ∀ t, s + t = 1 → beta (s • x + t • y) = s * beta x + t * beta y) → ((∀ x,
            ∀ y, ∀ s, ∀ t, s + t = 1 → gamma (s • x + t • y) = s * gamma x + t * gamma y) → ((∀
            x, ∀ y, ∀ s, ∀ t, s + t = 1 → alpha (s • x + t • y) = s * alpha x + t * alpha y) → (
        let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
        Convex Real S))) ) := by
  classical
  intro p a b c D beta gamma alpha hbeta_affine hgamma_affine halpha_affine S x hx y hy r s hr hs
      hrs
  change 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x at hx
  change 0 ≤ alpha y ∧ 0 ≤ beta y ∧ 0 ≤ gamma y at hy
  change 0 ≤ alpha (r • x + s • y) ∧ 0 ≤ beta (r • x + s • y) ∧
    0 ≤ gamma (r • x + s • y)
  rw [halpha_affine x y r s hrs, hbeta_affine x y r s hrs,
    hgamma_affine x y r s hrs]
  exact ⟨add_nonneg (mul_nonneg hr hx.1) (mul_nonneg hs hy.1),
    add_nonneg (mul_nonneg hr hx.2.1) (mul_nonneg hs hy.2.1),
    add_nonneg (mul_nonneg hr hx.2.2) (mul_nonneg hs hy.2.2)⟩

private theorem hKsubS :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (beta a = 0) → ((gamma a = 0) → ((beta b = 1) → ((gamma b = 0) → ((beta c = 0) → ((gamma
            c = 1) → ((alpha a = 1) → ((alpha b = 0) → ((alpha c = 0) → (
        let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
        (Convex Real S) → (K ⊆ S)))))))))) ) := by
  classical
  intro p a b c D beta gamma alpha K hβa hγa hβb hγb hβc hγc hαa hαb hαc S hSconv
  apply convexHull_min
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · change 0 ≤ alpha a ∧ 0 ≤ beta a ∧ 0 ≤ gamma a
      simp [hαa, hβa, hγa]
    · change 0 ≤ alpha b ∧ 0 ≤ beta b ∧ 0 ≤ gamma b
      simp [hαb, hβb, hγb]
    · change 0 ≤ alpha c ∧ 0 ≤ beta c ∧ 0 ≤ gamma c
      simp [hαc, hβc, hγc]
  · exact hSconv

private theorem hSsubK :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        (∀ x, x = alpha x • a + beta x • b + gamma x • c) → (
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
        S ⊆ K) ) := by
  classical
  intro p a b c D beta gamma alpha hrec K S x hx
  change 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x at hx
  have hw0 : ∀ i : Fin 3,
      0 ≤ if i = 0 then alpha x else if i = 1 then beta x else gamma x := by
    intro i
    fin_cases i <;> simp [hx.1, hx.2.1, hx.2.2]
  have hwsum : (∑ i : Fin 3,
      if i = 0 then alpha x else if i = 1 then beta x else gamma x) = 1 := by
    simp [Fin.sum_univ_succ]
    linarith [hsum p x]
  have hz : ∀ i : Fin 3, p.vertex i ∈ Set.range p.vertex := by
    intro i
    exact ⟨i, rfl⟩
  have hcomb : (∑ i : Fin 3,
      (if i = 0 then alpha x else if i = 1 then beta x else gamma x) • p.vertex i) = x := by
    simp [Fin.sum_univ_succ]
    simpa [add_assoc] using (hrec x).symm
  have hxK : x ∈ convexHull Real (Set.range p.vertex) :=
    mem_convexHull_of_exists_fintype
      (fun i : Fin 3 => if i = 0 then alpha x else if i = 1 then beta x else gamma x)
      p.vertex hw0 hwsum hz hcomb
  simpa [K] using hxK

private theorem hSpath :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        (∀ x, ∀ y, ∀ s, ∀ t, s + t = 1 → beta (s • x + t • y) = s * beta x + t * beta y) → ((∀ x,
            ∀ y, ∀ s, ∀ t, s + t = 1 → gamma (s • x + t • y) = s * gamma x + t * gamma y) → ((∀
            x, ∀ y, ∀ s, ∀ t, s + t = 1 → alpha (s • x + t • y) = s * alpha x + t * alpha y) →
            ((beta a = 0) → ((gamma a = 0) → ((beta b = 1) → ((gamma b = 0) → ((beta c = 0) →
            ((gamma c = 1) → (IsPathConnected {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma
            x}))))))))) ) := by
  classical
  intro p a b c D beta gamma alpha hbeta_affine hgamma_affine halpha_affine hβa hγa hβb hγb hβc hγc
  apply (Convex.isPathConnected ?_ ?_)
  · intro x hx y hy r s hr hs hrs
    change 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x at hx
    change 0 < alpha y ∧ 0 < beta y ∧ 0 < gamma y at hy
    change 0 < alpha (r • x + s • y) ∧ 0 < beta (r • x + s • y) ∧
      0 < gamma (r • x + s • y)
    rw [halpha_affine x y r s hrs, hbeta_affine x y r s hrs,
      hgamma_affine x y r s hrs]
    have hweighted : ∀ u v : Real, 0 < u → 0 < v →
        0 ≤ r → 0 ≤ s → r + s = 1 → 0 < r * u + s * v := by
      intro u v hu hv hr hs hrs
      by_cases hr0 : r = 0
      · have hspos : 0 < s := by linarith
        nlinarith [mul_pos hspos hv]
      · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
        nlinarith [mul_pos hrpos hu]
    refine ⟨hweighted _ _ hx.1 hy.1 hr hs hrs, ?_⟩
    exact ⟨hweighted _ _ hx.2.1 hy.2.1 hr hs hrs,
      hweighted _ _ hx.2.2 hy.2.2 hr hs hrs⟩
  · refine ⟨((1 : Real) / 3) • a + ((1 : Real) / 3) • b +
      ((1 : Real) / 3) • c, ?_⟩
    let m : Real × Real := ((1 : Real) / 2) • a + ((1 : Real) / 2) • b
    let z : Real × Real := ((1 : Real) / 3) • a + ((1 : Real) / 3) • b +
      ((1 : Real) / 3) • c
    have hma : beta m = 1 / 2 := by
      calc
        beta m = beta (((1 : Real) / 2) • a + ((1 : Real) / 2) • b) := rfl
        _ = (1 / 2) * beta a + (1 / 2) * beta b :=
          hbeta_affine a b (1 / 2) (1 / 2) (by norm_num)
        _ = 1 / 2 := by rw [hβa, hβb]; norm_num
    have hmg : gamma m = 0 := by
      calc
        gamma m = gamma (((1 : Real) / 2) • a + ((1 : Real) / 2) • b) := rfl
        _ = (1 / 2) * gamma a + (1 / 2) * gamma b :=
          hgamma_affine a b (1 / 2) (1 / 2) (by norm_num)
        _ = 0 := by rw [hγa, hγb]; norm_num
    have hza : z = ((2 : Real) / 3) • m + ((1 : Real) / 3) • c := by
      dsimp [z, m]
      ext <;> simp [smul_eq_mul] <;> ring
    have hbz : beta z = 1 / 3 := by
      calc
        beta z = beta (((2 : Real) / 3) • m + ((1 : Real) / 3) • c) := congrArg beta hza
        _ = (2 / 3) * beta m + (1 / 3) * beta c :=
          hbeta_affine m c (2 / 3) (1 / 3) (by norm_num)
        _ = 1 / 3 := by rw [hma, hβc]; norm_num
    have hgz : gamma z = 1 / 3 := by
      calc
        gamma z = gamma (((2 : Real) / 3) • m + ((1 : Real) / 3) • c) := congrArg gamma hza
        _ = (2 / 3) * gamma m + (1 / 3) * gamma c :=
          hgamma_affine m c (2 / 3) (1 / 3) (by norm_num)
        _ = 1 / 3 := by rw [hmg, hγc]; norm_num
    have haz : alpha z = 1 / 3 := by
      dsimp [alpha]
      rw [hbz, hgz]
      norm_num
    simp only [Set.mem_ofPred_eq]
    have hzstrict : 0 < alpha z ∧ 0 < beta z ∧ 0 < gamma z := by
      rw [haz, hbz, hgz]
      norm_num
    simpa [z] using hzstrict

private theorem hKdecomp :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        (∀ x, x = alpha x • a + beta x • b + gamma x • c) → (
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (P3544T1BoundaryCarrier p ⊆ K) → (
        let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
        (K ⊆ S) → ((S ⊆ K) → (K = {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x} ∪
            P3544T1BoundaryCarrier p)))) ) := by
  classical
  intro p a b c D beta gamma alpha hrec K hCsubset S hKsubS hSsubK
  have hzeroA : ∀ x, alpha x = 0 → 0 ≤ beta x → 0 ≤ gamma x →
      x ∈ P3544T1BoundaryCarrier p := by
    intro x hα hβ hγ
    have hbc : beta x + gamma x = 1 := by linarith [hsum p x]
    have heq : x = (1 - gamma x) • b + gamma x • c := by
      calc
        x = alpha x • a + beta x • b + gamma x • c := hrec x
        _ = (1 - gamma x) • b + gamma x • c := by
          rw [hα, show beta x = 1 - gamma x by linarith [hbc]]
          module
    have hseg : x ∈ segment Real b c := by
      rw [segment_eq_image]
      refine ⟨gamma x, ⟨hγ, ?_⟩, heq.symm⟩
      linarith
    change x ∈ ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    simpa [b, c] using hseg
  have hzeroB : ∀ x, beta x = 0 → 0 ≤ alpha x → 0 ≤ gamma x →
      x ∈ P3544T1BoundaryCarrier p := by
    intro x hβ hα hγ
    have hca : alpha x + gamma x = 1 := by linarith [hsum p x]
    have heq : x = (1 - alpha x) • c + alpha x • a := by
      calc
        x = alpha x • a + beta x • b + gamma x • c := hrec x
        _ = (1 - alpha x) • c + alpha x • a := by
          rw [hβ, show gamma x = 1 - alpha x by linarith [hca]]
          module
    have hseg : x ∈ segment Real c a := by
      rw [segment_eq_image]
      refine ⟨alpha x, ⟨hα, ?_⟩, heq.symm⟩
      linarith
    change x ∈ ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
    refine Set.mem_iUnion.mpr ⟨2, ?_⟩
    simpa [a, c] using hseg
  have hzeroC : ∀ x, gamma x = 0 → 0 ≤ alpha x → 0 ≤ beta x →
      x ∈ P3544T1BoundaryCarrier p := by
    intro x hγ hα hβ
    have hab : alpha x + beta x = 1 := by linarith [hsum p x]
    have heq : x = (1 - beta x) • a + beta x • b := by
      calc
        x = alpha x • a + beta x • b + gamma x • c := hrec x
        _ = (1 - beta x) • a + beta x • b := by
          rw [hγ, show alpha x = 1 - beta x by linarith [hab]]
          module
    have hseg : x ∈ segment Real a b := by
      rw [segment_eq_image]
      refine ⟨beta x, ⟨hβ, ?_⟩, heq.symm⟩
      linarith
    change x ∈ ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
    exact Set.mem_iUnion.mpr ⟨0, by simpa [a, b] using hseg⟩
  ext x
  constructor
  · intro hx
    have hsx := hKsubS hx
    change 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x at hsx
    by_cases hα : alpha x = 0
    · right
      exact hzeroA x hα hsx.2.1 hsx.2.2
    by_cases hβ : beta x = 0
    · right
      exact hzeroB x hβ hsx.1 hsx.2.2
    by_cases hγ : gamma x = 0
    · right
      exact hzeroC x hγ hsx.1 hsx.2.1
    · left
      exact ⟨lt_of_le_of_ne hsx.1 (Ne.symm hα),
        lt_of_le_of_ne hsx.2.1 (Ne.symm hβ),
        lt_of_le_of_ne hsx.2.2 (Ne.symm hγ)⟩
  · rintro (hx | hx)
    · apply hSsubK
      change 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x
      exact ⟨le_of_lt hx.1, le_of_lt hx.2.1, le_of_lt hx.2.2⟩
    · exact hCsubset hx

private theorem hmuA_neg :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        ∀ (d : ℝ × ℝ), muA (-d) = -muA d ) := by
  classical
  intro p a b c D muB muC muA d
  simp [muA, muB, muC]
  ring

private theorem hmuB_neg :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        ∀ (d : ℝ × ℝ), muB (-d) = -muB d ) := by
  classical
  intro p a b c D muB d
  simp [muB]
  ring

private theorem hmuC_neg :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        ∀ (d : ℝ × ℝ), muC (-d) = -muC d ) := by
  classical
  intro p a b c D muC d
  simp [muC]
  ring

private theorem hbeta_ray :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        ∀ x, ∀ d, ∀ t, beta (x + t • d) = beta x + t * muB d) ) := by
  classical
  intro p a b c D hDneq beta muB x d t
  dsimp [beta, muB]
  field_simp [hDneq]
  ring

private theorem hgamma_ray :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        ∀ x, ∀ d, ∀ t, gamma (x + t • d) = gamma x + t * muC d) ) := by
  classical
  intro p a b c D hDneq gamma muC x d t
  dsimp [gamma, muC]
  field_simp [hDneq]
  ring

private theorem halpha_ray :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        (∀ x, ∀ d, ∀ t, beta (x + t • d) = beta x + t * muB d) → ((∀ x, ∀ d, ∀ t, gamma (x + t •
            d) = gamma x + t * muC d) → (∀ x, ∀ d, ∀ t, alpha (x + t • d) = alpha x + t * muA d))
            ) := by
  classical
  intro p a b c D beta gamma alpha muB muC muA hbeta_ray hgamma_ray x d t
  dsimp [alpha, muA]
  rw [hbeta_ray, hgamma_ray]
  ring

private theorem hxC :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (P3544T1BoundaryCarrier p ⊆ K) → (∀ (x : ℝ × ℝ), (x ∉ K) → (x ∉
            P3544T1BoundaryCarrier p)) ) := by
  classical
  intro p K hCsubset x hxK hxC
  exact hxK (hCsubset hxC)

private theorem hmuAt597 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        ∀ (d : ℝ × ℝ), (d.1 * (c - b).2 - d.2 * (c - b).1 ≠ 0) → (muA d ≠ 0)) ) := by
  classical
  intro p a b c D hDneq muB muC muA d hcross hmu
  apply hcross
  dsimp [muA, muB, muC] at hmu
  field_simp [hDneq] at hmu
  have hcrossEq : d.1 * (c - b).2 - d.2 * (c - b).1 =
      d.1 * (c.2 - a.2) - d.2 * (c.1 - a.1) +
        -(d.1 * (b.2 - a.2) - d.2 * (b.1 - a.1)) := by
    dsimp [a, b, c]
    ring
  rw [hcrossEq]
  nlinarith [hmu]

private theorem hmu'At610 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        (∀ (d : Real × Real), muA (-d) = -muA d) → (∀ (d : ℝ × ℝ), (muA d ≠ 0) → (
        let d' : Real × Real := if 0 < muA d then -d else d
        muA d' < 0)) ) := by
  classical
  intro p a b c D muB muC muA hmuA_neg d hmu d'
  by_cases hpos : 0 < muA d
  · simp only [d', ite_eq_left hpos]
    rw [hmuA_neg]
    linarith
  · have hneg : muA d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hmu
    simpa [d', hpos] using hneg

private theorem hdv'At617 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), (∀ (i : Fin ((0 : ℕ) + (3 : ℕ))), d.1 * (p.vertex i - x).2
            - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (
        let d' : Real × Real := if 0 < muA d then -d else d
        ∀ i, d'.1 * (p.vertex i - x).2 - d'.2 * (p.vertex i - x).1 ≠ 0) ) := by
  classical
  intro p a b c D muB muC muA x d hdv d' i
  by_cases hpos : 0 < muA d
  · have heq : d'.1 * (p.vertex i - x).2 - d'.2 * (p.vertex i - x).1 =
        -(d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1) := by
      simp only [d', ite_eq_left hpos]
      change (-d.1) * (p.vertex i - x).2 - (-d.2) * (p.vertex i - x).1 =
        -(d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1)
      ring
    rw [heq]
    exact fun hz => hdv i (by linarith [hz])
  · simpa [d', hpos] using hdv i

private theorem hde'At630 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        ∀ (d : ℝ × ℝ), (∀ (i : Fin ((0 : ℕ) + (3 : ℕ))), d.1 * (p.vertex (i + (1 : Fin ((0 : ℕ) +
            (3 : ℕ)))) - p.vertex i).2 - d.2 * (p.vertex (i + (1 : Fin ((0 : ℕ) + (3 : ℕ)))) -
            p.vertex i).1 ≠ (0 : ℝ)) → (
        let d' : Real × Real := if 0 < muA d then -d else d
        ∀ i, d'.1 * (p.vertex (i + 1) - p.vertex i).2 - d'.2 * (p.vertex (i + 1) - p.vertex i).1
            ≠ 0) ) := by
  classical
  intro p a b c D muB muC muA d hde d' i
  by_cases hpos : 0 < muA d
  · have heq : d'.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d'.2 * (p.vertex (i + 1) - p.vertex i).1 =
        -(d.1 * (p.vertex (i + 1) - p.vertex i).2 -
          d.2 * (p.vertex (i + 1) - p.vertex i).1) := by
      simp only [d', ite_eq_left hpos]
      change (-d.1) * (p.vertex (i + 1) - p.vertex i).2 -
        (-d.2) * (p.vertex (i + 1) - p.vertex i).1 =
        -(d.1 * (p.vertex (i + 1) - p.vertex i).2 -
          d.2 * (p.vertex (i + 1) - p.vertex i).1)
      ring
    rw [heq]
    exact fun hz => hde i (by linarith [hz])
  · simpa [d', hpos] using hde i

private theorem hnoAt647 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (P3544T1BoundaryCarrier p ⊆ K) → (
        let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
        (K ⊆ S) → (
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        (∀ x, ∀ d, ∀ t, alpha (x + t • d) = alpha x + t * muA d) → (∀ (x : ℝ × ℝ), (¬(0 : ℝ) ≤
            alpha x) → (∀ (d : ℝ × ℝ),
        let d' : Real × Real := if 0 < muA d then -d else d
        (muA d' < 0) → (∀ i : Fin 3, ¬ ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real (p.vertex i)
            (p.vertex (i + 1))))))) ) := by
  classical
  intro p a b c D beta gamma alpha K hCsubset S hKsubS muB muC muA halpha_ray x hαneg d d' hmu' i hi
  rcases hi with ⟨t, ht, hseg⟩
  have hyC : x + t • d' ∈ P3544T1BoundaryCarrier p := by
    change x + t • d' ∈ ⋃ j, segment Real (p.vertex j) (p.vertex (j + 1))
    exact Set.mem_iUnion.mpr ⟨i, hseg⟩
  have hyS := hKsubS (hCsubset hyC)
  change 0 ≤ alpha (x + t • d') ∧ 0 ≤ beta (x + t • d') ∧
    0 ≤ gamma (x + t • d') at hyS
  have : alpha (x + t • d') < 0 := by
    rw [halpha_ray]
    have hm := mul_neg_of_pos_of_neg ht hmu'
    linarith
  exact (not_lt_of_ge hyS.1) this

private theorem hcount0At662 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ),
        let d' : Real × Real := if 0 < muA d then -d else d
        (∀ i : Fin 3, ¬ ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i +
            1))) → (Set.ncard {i : Fin 3 | ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real
            (p.vertex i) (p.vertex (i + 1))} = 0) ) := by
  classical
  intro p a b c D muB muC muA x d d' hno
  have hset : {i : Fin 3 | ∃ t : Real, 0 < t ∧
      x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i + 1))} = ∅ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact hno i
  simp [hset]

private theorem hmuAt678 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        ∀ (d : ℝ × ℝ), (d.1 * (a - c).2 - d.2 * (a - c).1 ≠ 0) → (muB d ≠ 0)) ) := by
  classical
  intro p a b c D hDneq muB d hcross hm
  dsimp [muB] at hm
  field_simp [hDneq] at hm
  have hc0 : d.1 * (c.2 - a.2) - d.2 * (c.1 - a.1) = 0 := by
    simpa using hm
  have heq : d.1 * (a - c).2 - d.2 * (a - c).1 =
      -(d.1 * (c - a).2 - d.2 * (c - a).1) := by
    dsimp [a, c]
    ring
  apply hcross
  rw [heq]
  change -(d.1 * (c.2 - a.2) - d.2 * (c.1 - a.1)) = 0
  rw [hc0]
  simp

private theorem hmu'At694 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        (∀ (d : Real × Real), muB (-d) = -muB d) → (∀ (d : ℝ × ℝ), (muB d ≠ 0) → (
        let d' : Real × Real := if 0 < muB d then -d else d
        muB d' < 0)) ) := by
  classical
  intro p a b c D muB hmuB_neg d hmu d'
  by_cases hpos : 0 < muB d
  · simp only [d', ite_eq_left hpos]
    rw [hmuB_neg]
    linarith
  · have hneg : muB d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hmu
    simpa [d', hpos] using hneg

private theorem hdv'At701 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), (∀ (i : Fin ((0 : ℕ) + (3 : ℕ))), d.1 * (p.vertex i - x).2
            - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (
        let d' : Real × Real := if 0 < muB d then -d else d
        ∀ i, d'.1 * (p.vertex i - x).2 - d'.2 * (p.vertex i - x).1 ≠ 0) ) := by
  classical
  intro p a b c D muB x d hdv d' i
  by_cases hpos : 0 < muB d
  · have heq : d'.1 * (p.vertex i - x).2 - d'.2 * (p.vertex i - x).1 =
        -(d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1) := by
      simp only [d', ite_eq_left hpos]
      change (-d.1) * (p.vertex i - x).2 - (-d.2) * (p.vertex i - x).1 =
        -(d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1)
      ring
    rw [heq]
    exact fun hz => hdv i (by linarith [hz])
  · simpa [d', hpos] using hdv i

private theorem hde'At714 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        ∀ (d : ℝ × ℝ), (∀ (i : Fin ((0 : ℕ) + (3 : ℕ))), d.1 * (p.vertex (i + (1 : Fin ((0 : ℕ) +
            (3 : ℕ)))) - p.vertex i).2 - d.2 * (p.vertex (i + (1 : Fin ((0 : ℕ) + (3 : ℕ)))) -
            p.vertex i).1 ≠ (0 : ℝ)) → (
        let d' : Real × Real := if 0 < muB d then -d else d
        ∀ i, d'.1 * (p.vertex (i + 1) - p.vertex i).2 - d'.2 * (p.vertex (i + 1) - p.vertex i).1
            ≠ 0) ) := by
  classical
  intro p a b c D muB d hde d' i
  by_cases hpos : 0 < muB d
  · have heq : d'.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d'.2 * (p.vertex (i + 1) - p.vertex i).1 =
        -(d.1 * (p.vertex (i + 1) - p.vertex i).2 -
          d.2 * (p.vertex (i + 1) - p.vertex i).1) := by
      simp only [d', ite_eq_left hpos]
      change (-d.1) * (p.vertex (i + 1) - p.vertex i).2 -
        (-d.2) * (p.vertex (i + 1) - p.vertex i).1 =
        -(d.1 * (p.vertex (i + 1) - p.vertex i).2 -
          d.2 * (p.vertex (i + 1) - p.vertex i).1)
      ring
    rw [heq]
    exact fun hz => hde i (by linarith [hz])
  · simpa [d', hpos] using hde i

private theorem hnoAt731 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (P3544T1BoundaryCarrier p ⊆ K) → (
        let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
        (K ⊆ S) → (
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        (∀ x, ∀ d, ∀ t, beta (x + t • d) = beta x + t * muB d) → (∀ (x : ℝ × ℝ), (¬(0 : ℝ) ≤ beta
            x) → (∀ (d : ℝ × ℝ),
        let d' : Real × Real := if 0 < muB d then -d else d
        (muB d' < 0) → (∀ i : Fin 3, ¬ ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real (p.vertex i)
            (p.vertex (i + 1))))))) ) := by
  classical
  intro p a b c D beta gamma alpha K hCsubset S hKsubS muB hbeta_ray x hβneg d d' hmu' i hi
  rcases hi with ⟨t, ht, hseg⟩
  have hyC : x + t • d' ∈ P3544T1BoundaryCarrier p := by
    change x + t • d' ∈ ⋃ j, segment Real (p.vertex j) (p.vertex (j + 1))
    exact Set.mem_iUnion.mpr ⟨i, hseg⟩
  have hyS := hKsubS (hCsubset hyC)
  change 0 ≤ alpha (x + t • d') ∧ 0 ≤ beta (x + t • d') ∧
    0 ≤ gamma (x + t • d') at hyS
  have : beta (x + t • d') < 0 := by
    rw [hbeta_ray]
    have hm := mul_neg_of_pos_of_neg ht hmu'
    linarith
  exact (not_lt_of_ge hyS.2.1) this

private theorem hcount0At746 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muB : (Real × Real) → Real := fun d =>
          (d.1 * (c - a).2 - d.2 * (c - a).1) / D
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ),
        let d' : Real × Real := if 0 < muB d then -d else d
        (∀ i : Fin 3, ¬ ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i +
            1))) → (Set.ncard {i : Fin 3 | ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real
            (p.vertex i) (p.vertex (i + 1))} = 0) ) := by
  classical
  intro p a b c D muB x d d' hno
  have hset : {i : Fin 3 | ∃ t : Real, 0 < t ∧
      x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i + 1))} = ∅ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact hno i
  simp [hset]

private theorem hmuAt761 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        (D ≠ 0) → (
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        ∀ (d : ℝ × ℝ), (d.1 * (b - a).2 - d.2 * (b - a).1 ≠ 0) → (muC d ≠ 0)) ) := by
  classical
  intro p a b c D hDneq muC d hcross hm
  dsimp [muC] at hm
  field_simp [hDneq] at hm
  have hab0 : d.1 * (b - a).2 - d.2 * (b - a).1 = 0 := by
    have hm' := hm
    simp only [mul_zero] at hm'
    exact neg_eq_zero.mp hm'
  exact hcross hab0

private theorem hmu'At771 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        (∀ (d : Real × Real), muC (-d) = -muC d) → (∀ (d : ℝ × ℝ), (muC d ≠ 0) → (
        let d' : Real × Real := if 0 < muC d then -d else d
        muC d' < 0)) ) := by
  classical
  intro p a b c D muC hmuC_neg d hmu d'
  by_cases hpos : 0 < muC d
  · simp only [d', ite_eq_left hpos]
    rw [hmuC_neg]
    linarith
  · have hneg : muC d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hmu
    simpa [d', hpos] using hneg

private theorem hdv'At778 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), (∀ (i : Fin ((0 : ℕ) + (3 : ℕ))), d.1 * (p.vertex i - x).2
            - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (
        let d' : Real × Real := if 0 < muC d then -d else d
        ∀ i, d'.1 * (p.vertex i - x).2 - d'.2 * (p.vertex i - x).1 ≠ 0) ) := by
  classical
  intro p a b c D muC x d hdv d' i
  by_cases hpos : 0 < muC d
  · have heq : d'.1 * (p.vertex i - x).2 - d'.2 * (p.vertex i - x).1 =
        -(d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1) := by
      simp only [d', ite_eq_left hpos]
      change (-d.1) * (p.vertex i - x).2 - (-d.2) * (p.vertex i - x).1 =
        -(d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1)
      ring
    rw [heq]
    exact fun hz => hdv i (by linarith [hz])
  · simpa [d', hpos] using hdv i

private theorem hde'At791 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        ∀ (d : ℝ × ℝ), (∀ (i : Fin ((0 : ℕ) + (3 : ℕ))), d.1 * (p.vertex (i + (1 : Fin ((0 : ℕ) +
            (3 : ℕ)))) - p.vertex i).2 - d.2 * (p.vertex (i + (1 : Fin ((0 : ℕ) + (3 : ℕ)))) -
            p.vertex i).1 ≠ (0 : ℝ)) → (
        let d' : Real × Real := if 0 < muC d then -d else d
        ∀ i, d'.1 * (p.vertex (i + 1) - p.vertex i).2 - d'.2 * (p.vertex (i + 1) - p.vertex i).1
            ≠ 0) ) := by
  classical
  intro p a b c D muC d hde d' i
  by_cases hpos : 0 < muC d
  · have heq : d'.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d'.2 * (p.vertex (i + 1) - p.vertex i).1 =
        -(d.1 * (p.vertex (i + 1) - p.vertex i).2 -
          d.2 * (p.vertex (i + 1) - p.vertex i).1) := by
      simp only [d', ite_eq_left hpos]
      change (-d.1) * (p.vertex (i + 1) - p.vertex i).2 -
        (-d.2) * (p.vertex (i + 1) - p.vertex i).1 =
        -(d.1 * (p.vertex (i + 1) - p.vertex i).2 -
          d.2 * (p.vertex (i + 1) - p.vertex i).1)
      ring
    rw [heq]
    exact fun hz => hde i (by linarith [hz])
  · simpa [d', hpos] using hde i

private theorem hnoAt808 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (P3544T1BoundaryCarrier p ⊆ K) → (
        let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
        (K ⊆ S) → (
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        (∀ x, ∀ d, ∀ t, gamma (x + t • d) = gamma x + t * muC d) → (∀ (x : ℝ × ℝ), (¬(0 : ℝ) ≤
            gamma x) → (∀ (d : ℝ × ℝ),
        let d' : Real × Real := if 0 < muC d then -d else d
        (muC d' < 0) → (∀ i : Fin 3, ¬ ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real (p.vertex i)
            (p.vertex (i + 1))))))) ) := by
  classical
  intro p a b c D beta gamma alpha K hCsubset S hKsubS muC hgamma_ray x hγneg d d' hmu' i hi
  rcases hi with ⟨t, ht, hseg⟩
  have hyC : x + t • d' ∈ P3544T1BoundaryCarrier p := by
    change x + t • d' ∈ ⋃ j, segment Real (p.vertex j) (p.vertex (j + 1))
    exact Set.mem_iUnion.mpr ⟨i, hseg⟩
  have hyS := hKsubS (hCsubset hyC)
  change 0 ≤ alpha (x + t • d') ∧ 0 ≤ beta (x + t • d') ∧
    0 ≤ gamma (x + t • d') at hyS
  have : gamma (x + t • d') < 0 := by
    rw [hgamma_ray]
    have hm := mul_neg_of_pos_of_neg ht hmu'
    linarith
  exact (not_lt_of_ge hyS.2.2) this

private theorem hcount0At823 :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let muC : (Real × Real) → Real := fun d =>
          -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ),
        let d' : Real × Real := if 0 < muC d then -d else d
        (∀ i : Fin 3, ¬ ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i +
            1))) → (Set.ncard {i : Fin 3 | ∃ t : Real, 0 < t ∧ x + t • d' ∈ segment Real
            (p.vertex i) (p.vertex (i + 1))} = 0) ) := by
  classical
  intro p a b c D muC x d d' hno
  have hset : {i : Fin 3 | ∃ t : Real, 0 < t ∧
      x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i + 1))} = ∅ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact hno i
  simp [hset]

private theorem hCdisjH :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        (∀ x, ∀ y, ∀ s, ∀ t, s + t = 1 → beta (s • x + t • y) = s * beta x + t * beta y) → ((∀ x,
            ∀ y, ∀ s, ∀ t, s + t = 1 → gamma (s • x + t • y) = s * gamma x + t * gamma y) → ((∀
            x, ∀ y, ∀ s, ∀ t, s + t = 1 → alpha (s • x + t • y) = s * alpha x + t * alpha y) →
            ((beta a = 0) → ((gamma a = 0) → ((gamma b = 0) → ((beta c = 0) → ((alpha b = 0) →
            ((alpha c = 0) → (
        let H : Set (Real × Real) := {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x}
        ∀ x, x ∈ H → x ∉ P3544T1BoundaryCarrier p))))))))) ) := by
  classical
  intro p a b c D beta gamma alpha hbeta_affine hgamma_affine halpha_affine hβa hγa hγb hβc hαb
      hαc H x hxH hxC
  change x ∈ ⋃ i : Fin 3, segment Real (p.vertex i) (p.vertex (i + 1)) at hxC
  rcases Set.mem_iUnion.mp hxC with ⟨i, hi⟩
  rw [segment_eq_image] at hi
  rcases hi with ⟨t, ht, heq⟩
  fin_cases i
  · have hg := hgamma_affine a b (1 - t) t (by ring)
    rw [hγa, hγb] at hg
    have hz : gamma x = 0 := by rw [← heq]; simpa using hg
    linarith [hxH.2.2]
  · have ha := halpha_affine b c (1 - t) t (by ring)
    rw [hαb, hαc] at ha
    have hz : alpha x = 0 := by rw [← heq]; simpa using ha
    linarith [hxH.1]
  · have hb := hbeta_affine c a (1 - t) t (by ring)
    rw [hβc, hβa] at hb
    have hz : beta x = 0 := by rw [← heq]; simpa using hb
    linarith [hxH.2.1]

private theorem hbeta_cont :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        Continuous beta ) := by
  classical
  intro p a b c D beta
  dsimp [beta]
  fun_prop

private theorem hgamma_cont :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        Continuous gamma ) := by
  classical
  intro p a b c D gamma
  dsimp [gamma]
  fun_prop

private theorem halpha_cont :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        Continuous alpha ) := by
  classical
  intro p a b c D beta gamma alpha
  dsimp [alpha, beta, gamma]
  fun_prop

private theorem hHopen :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        let H : Set (Real × Real) := {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x}
        (Continuous beta) → ((Continuous gamma) → ((Continuous alpha) → (IsOpen H))) ) := by
  classical
  intro p a b c D beta gamma alpha H hbeta_cont hgamma_cont halpha_cont
  have hα : IsOpen {x | 0 < alpha x} := isOpen_lt continuous_const halpha_cont
  have hβ : IsOpen {x | 0 < beta x} := isOpen_lt continuous_const hbeta_cont
  have hγ : IsOpen {x | 0 < gamma x} := isOpen_lt continuous_const hgamma_cont
  simpa [H, Set.ofPred_and] using hα.inter (hβ.inter hγ)

private theorem hHminusOopen :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        (∀ x ∉ P3544T1BoundaryCarrier p, ∃ (r : ℝ), (0 : ℝ) < r ∧ (Metric.ball x r ⊆
            P3544T1RayParity p ∨ Disjoint (Metric.ball x r) (P3544T1RayParity p))) → (
        let H : Set (Real × Real) := {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x}
        (∀ x, x ∈ H → x ∉ P3544T1BoundaryCarrier p) → ((IsOpen H) → (IsOpen (H \
            P3544T1RayParity p)))) ) := by
  classical
  intro p a b c D beta gamma alpha hlocal H hCdisjH hHopen
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨r, hr, hchoice⟩ := hlocal x (hCdisjH x hx.1)
  obtain ⟨s, hs, hballH⟩ := Metric.isOpen_iff.mp hHopen x hx.1
  have hdisj : Disjoint (Metric.ball x r) (P3544T1RayParity p) := by
    rcases hchoice with hball | hdisj
    · exfalso
      have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
      exact hx.2 (hball hxball)
    · exact hdisj
  have hmin : 0 < min r s := by
    rw [lt_min_iff]
    exact ⟨hr, hs⟩
  refine ⟨min r s, hmin, ?_⟩
  intro y hy
  have hy' := Metric.mem_ball.mp hy
  have hyr : dist y x < r := lt_of_lt_of_le hy' (min_le_left _ _)
  have hys : dist y x < s := lt_of_lt_of_le hy' (min_le_right _ _)
  refine ⟨hballH (Metric.mem_ball.mpr hys), ?_⟩
  intro hyO
  exact (Set.disjoint_left.mp hdisj) hyr hyO

private theorem hOsubK :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (∀ x, x ∉ K → x ∉ P3544T1RayParity p) → (P3544T1RayParity p ⊆ K) ) := by
  classical
  intro p K hnotOoutside x hxO
  by_contra hxK
  exact hnotOoutside x hxK hxO

private theorem hOeqH :
    (by
      classical
      exact
        ∀ (p : P3381T1PolygonBoundary 0),
        let a : Real × Real := p.vertex 0
        let b : Real × Real := p.vertex 1
        let c : Real × Real := p.vertex 2
        let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
        let beta : (Real × Real) → Real := fun x =>
          ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
        let gamma : (Real × Real) → Real := fun x =>
          ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
        let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
        let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
        (IsPathConnected {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x}) → ((IsOpen
            (P3544T1RayParity p)) → ((∀ (i : Fin ((0 : ℕ) + (3 : ℕ))), ∃ (r : ℝ), (0 : ℝ) < r ∧
            IsPathConnected (Metric.ball (p.vertex i) r ∩ P3544T1RayParity p) ∧ IsPathConnected
            (Metric.ball (p.vertex i) r \ (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p))) → (
        let H : Set (Real × Real) := {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x}
        (K = H ∪ P3544T1BoundaryCarrier p) → ((IsOpen (H \ P3544T1RayParity p)) →
            ((P3544T1RayParity p ⊆ K) → (P3544T1RayParity p = H)))))) ) := by
  classical
  intro p a b c D beta gamma alpha K hSpath hOpenO hvertex H hKdecompH hHminusOopen hOsubK
  apply Set.Subset.antisymm
  · intro x hxO
    have hxK := hOsubK hxO
    have hxKH : x ∈ H ∨ x ∈ P3544T1BoundaryCarrier p := by
      simpa [hKdecompH] using hxK
    rcases hxKH with hxH | hxC
    · exact hxH
    · exact (hxO.1 hxC).elim
  · intro x hxH
    have hU : IsClopen (Subtype.val ⁻¹' P3544T1RayParity p : Set H) := by
      have hcomp : (Subtype.val ⁻¹' P3544T1RayParity p : Set H)ᶜ =
            Subtype.val ⁻¹' (H \ P3544T1RayParity p) := by
        ext y
        change (↑y ∉ P3544T1RayParity p) ↔
          (↑y ∈ H ∧ ↑y ∉ P3544T1RayParity p)
        exact ⟨fun hy => ⟨y.property, hy⟩, And.right⟩
      have hcompopen : IsOpen ((Subtype.val ⁻¹' P3544T1RayParity p : Set H)ᶜ) := by
        rw [hcomp]
        exact hHminusOopen.preimage continuous_subtype_val
      exact ⟨⟨hcompopen⟩, hOpenO.preimage continuous_subtype_val⟩
    let : PathConnectedSpace H := (isPathConnected_iff_pathConnectedSpace.mp hSpath)
    obtain ⟨r, hr, hnear, _⟩ := hvertex (0 : Fin 3)
    obtain ⟨y, hy⟩ := hnear.nonempty
    have hyO : y ∈ P3544T1RayParity p := hy.2
    have hyK := hOsubK hyO
    have hyKH : y ∈ H ∨ y ∈ P3544T1BoundaryCarrier p := by
      simpa [hKdecompH] using hyK
    have hyH : y ∈ H := by
      rcases hyKH with hyH | hyC
      · exact hyH
      · exact (hyO.1 hyC).elim
    have hnonempty : (Subtype.val ⁻¹' P3544T1RayParity p : Set H).Nonempty :=
      ⟨⟨y, hyH⟩, hyO⟩
    have huniv := hU.eq_univ hnonempty
    have hxO : x ∈ P3544T1RayParity p := by
      have hxmem : (⟨x, hxH⟩ : H) ∈ Subtype.val ⁻¹' P3544T1RayParity p := by
        rw [huniv]
        simp
      exact hxmem
    exact hxO

end TriangleRayIntersections

theorem P3544T1TriangleRayGeometry (p : P3381T1PolygonBoundary 0) :
    P3381T1TriangleDeterminant p.vertex ≠ 0 ∧
    convexHull Real (Set.range p.vertex) =
      P3544T1RayParity p ∪ P3544T1BoundaryCarrier p ∧
    IsPathConnected (P3544T1RayParity p) := by
-- BODY
  let a : Real × Real := p.vertex 0
  let b : Real × Real := p.vertex 1
  let c : Real × Real := p.vertex 2
  have hab := TriangleRayIntersections.habAt122 p
  have hac := TriangleRayIntersections.hac p
  have hbc := TriangleRayIntersections.hbcAt128 p
  have hu := TriangleRayIntersections.hu p hab
  have hDne : P3381T1TriangleDeterminant p.vertex ≠ 0 := TriangleRayIntersections.hDne p hab
      hac hbc hu
  let D : Real := (b - a).1 * (c - a).2 - (c - a).1 * (b - a).2
  have hDneq : D ≠ 0 := by
    simpa [D, P3381T1TriangleDeterminant, a, b, c] using hDne
  let beta : (Real × Real) → Real := fun x =>
    ((x - a).1 * (c - a).2 - (x - a).2 * (c - a).1) / D
  let gamma : (Real × Real) → Real := fun x =>
    ((b - a).1 * (x - a).2 - (b - a).2 * (x - a).1) / D
  let alpha : (Real × Real) → Real := fun x => 1 - beta x - gamma x
  have hrec := TriangleRayIntersections.hrec p hDneq
  have hbeta_affine := TriangleRayIntersections.hbeta_affine p hDneq
  have hgamma_affine := TriangleRayIntersections.hgamma_affine p hDneq
  have halpha_affine := TriangleRayIntersections.halpha_affine p hbeta_affine hgamma_affine
  let K : Set (Real × Real) := convexHull Real (Set.range p.vertex)
  have hKconv : Convex Real K := by
    exact convex_convexHull Real (Set.range p.vertex)
  have hCsubset := TriangleRayIntersections.hCsubset p hKconv
  have hβa : beta a = 0 := by simp [beta]
  have hγa : gamma a = 0 := by simp [gamma]
  have hβb : beta b = 1 := TriangleRayIntersections.hβb p hDneq
  have hγb : gamma b = 0 := TriangleRayIntersections.hγb p hDneq
  have hβc : beta c = 0 := TriangleRayIntersections.hβc p hDneq
  have hγc : gamma c = 1 := TriangleRayIntersections.hγc p hDneq
  have hαa : alpha a = 1 := by dsimp [alpha]; rw [hβa, hγa]; norm_num
  have hαb : alpha b = 0 := by dsimp [alpha]; rw [hβb, hγb]; norm_num
  have hαc : alpha c = 0 := by dsimp [alpha]; rw [hβc, hγc]; norm_num
  let S : Set (Real × Real) := {x | 0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x}
  have hSconv := TriangleRayIntersections.hSconv p hbeta_affine hgamma_affine halpha_affine
  have hKsubS := TriangleRayIntersections.hKsubS p hβa hγa hβb hγb hβc hγc hαa hαb hαc hSconv
  have hSsubK := TriangleRayIntersections.hSsubK p hrec
  have hKS : K = S := Set.Subset.antisymm hKsubS hSsubK
  have hSpath : IsPathConnected {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x} :=
      TriangleRayIntersections.hSpath p hbeta_affine hgamma_affine halpha_affine hβa hγa hβb hγb
      hβc hγc
  have hKdecomp : K = {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x} ∪
      P3544T1BoundaryCarrier p := TriangleRayIntersections.hKdecomp p hrec hCsubset hKsubS hSsubK
  let muB : (Real × Real) → Real := fun d =>
    (d.1 * (c - a).2 - d.2 * (c - a).1) / D
  let muC : (Real × Real) → Real := fun d =>
    -(d.1 * (b - a).2 - d.2 * (b - a).1) / D
  let muA : (Real × Real) → Real := fun d => -(muB d + muC d)
  have hmuA_neg (d : Real × Real) := TriangleRayIntersections.hmuA_neg p d
  have hmuB_neg (d : Real × Real) := TriangleRayIntersections.hmuB_neg p d
  have hmuC_neg (d : Real × Real) := TriangleRayIntersections.hmuC_neg p d
  have hbeta_ray := TriangleRayIntersections.hbeta_ray p hDneq
  have hgamma_ray := TriangleRayIntersections.hgamma_ray p hDneq
  have halpha_ray := TriangleRayIntersections.halpha_ray p hbeta_ray hgamma_ray
  have hLocalParity := P3544T1LocalParity p
  rcases hLocalParity with ⟨_, hOpenO, _, _, hlocal, hgeneric, hchar, hvertex, _⟩
  have hnotOoutside : ∀ x, x ∉ K → x ∉ P3544T1RayParity p := by
    intro x hxK hxO
    have hxC := TriangleRayIntersections.hxC p hCsubset x hxK
    have hxS : x ∉ S := by simpa [hKS] using hxK
    change ¬ (0 ≤ alpha x ∧ 0 ≤ beta x ∧ 0 ≤ gamma x) at hxS
    rcases not_and_or.mp hxS with hαneg | hrest
    · obtain ⟨d, hdv, hde⟩ := hgeneric x hxC
      have hcross : d.1 * (c - b).2 - d.2 * (c - b).1 ≠ 0 := by
        simpa [a, b, c] using hde 1
      have hmu := TriangleRayIntersections.hmuAt597 p hDneq d hcross
      let d' : Real × Real := if 0 < muA d then -d else d
      have hmu' := TriangleRayIntersections.hmu'At610 p hmuA_neg d hmu
      have hdv' := TriangleRayIntersections.hdv'At617 p x d hdv
      have hde' := TriangleRayIntersections.hde'At630 p d hde
      have hno := TriangleRayIntersections.hnoAt647 p hCsubset hKsubS halpha_ray x hαneg d hmu'
      have hcount0 : Set.ncard {i : Fin 3 | ∃ t : Real, 0 < t ∧
          x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i + 1))} = 0 :=
              TriangleRayIntersections.hcount0At662 p x d hno
      have hodd := (hchar x d' hxC hdv' hde').mp hxO
      rw [hcount0] at hodd
      norm_num at hodd
    · rcases not_and_or.mp hrest with hβneg | hγneg
      · obtain ⟨d, hdv, hde⟩ := hgeneric x hxC
        have hcross : d.1 * (a - c).2 - d.2 * (a - c).1 ≠ 0 := by
          simpa [a, b, c] using hde 2
        have hmu := TriangleRayIntersections.hmuAt678 p hDneq d hcross
        let d' : Real × Real := if 0 < muB d then -d else d
        have hmu' := TriangleRayIntersections.hmu'At694 p hmuB_neg d hmu
        have hdv' := TriangleRayIntersections.hdv'At701 p x d hdv
        have hde' := TriangleRayIntersections.hde'At714 p d hde
        have hno := TriangleRayIntersections.hnoAt731 p hCsubset hKsubS hbeta_ray x hβneg d hmu'
        have hcount0 : Set.ncard {i : Fin 3 | ∃ t : Real, 0 < t ∧
            x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i + 1))} = 0 :=
                TriangleRayIntersections.hcount0At746 p x d hno
        have hodd := (hchar x d' hxC hdv' hde').mp hxO
        rw [hcount0] at hodd
        norm_num at hodd
      · obtain ⟨d, hdv, hde⟩ := hgeneric x hxC
        have hcross : d.1 * (b - a).2 - d.2 * (b - a).1 ≠ 0 := by
          simpa [a, b, c] using hde 0
        have hmu := TriangleRayIntersections.hmuAt761 p hDneq d hcross
        let d' : Real × Real := if 0 < muC d then -d else d
        have hmu' := TriangleRayIntersections.hmu'At771 p hmuC_neg d hmu
        have hdv' := TriangleRayIntersections.hdv'At778 p x d hdv
        have hde' := TriangleRayIntersections.hde'At791 p d hde
        have hno := TriangleRayIntersections.hnoAt808 p hCsubset hKsubS hgamma_ray x hγneg d hmu'
        have hcount0 : Set.ncard {i : Fin 3 | ∃ t : Real, 0 < t ∧
            x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i + 1))} = 0 :=
                TriangleRayIntersections.hcount0At823 p x d hno
        have hodd := (hchar x d' hxC hdv' hde').mp hxO
        rw [hcount0] at hodd
        norm_num at hodd
  let H : Set (Real × Real) := {x | 0 < alpha x ∧ 0 < beta x ∧ 0 < gamma x}
  have hKdecompH : K = H ∪ P3544T1BoundaryCarrier p := by
    simpa [H] using hKdecomp
  have hCdisjH := TriangleRayIntersections.hCdisjH p hbeta_affine hgamma_affine halpha_affine hβa
      hγa hγb hβc hαb hαc
  have hbeta_cont := TriangleRayIntersections.hbeta_cont p
  have hgamma_cont := TriangleRayIntersections.hgamma_cont p
  have halpha_cont := TriangleRayIntersections.halpha_cont p
  have hHopen := TriangleRayIntersections.hHopen p hbeta_cont hgamma_cont halpha_cont
  have hHminusOopen := TriangleRayIntersections.hHminusOopen p hlocal hCdisjH hHopen
  have hOsubK := TriangleRayIntersections.hOsubK p hnotOoutside
  have hOeqH : P3544T1RayParity p = H := TriangleRayIntersections.hOeqH p hSpath hOpenO hvertex
      hKdecompH hHminusOopen hOsubK
  refine ⟨hDne, ?_, ?_⟩
  · rw [hOeqH]
    simpa [H] using hKdecomp
  · simpa [hOeqH] using hSpath

end ApollonianSuperharmonic

end
