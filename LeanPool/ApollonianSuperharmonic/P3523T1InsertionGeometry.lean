/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3523T1InsertionIncidence
public import LeanPool.ApollonianSuperharmonic.P3523T1TargetBoundary
public import LeanPool.ApollonianSuperharmonic.P3523T1TargetHull
public import LeanPool.ApollonianSuperharmonic.P3523T1TwoTriangleSplit
public import LeanPool.ApollonianSuperharmonic.P3523T1SplitDeterminants
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


-- [TABLET NODE: P3523T1InsertionGeometry]

/-!
# P3523T1InsertionGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FacialInsertionGeometry

private theorem split_mem :
    (by
      classical
      exact
        ∀ {I : Type}, ∀ [DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d : I),
            ∀ (b : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs, if a
            ∈ F ∧ b ∈ F then G = insert d (F.erase b) ∨ G = insert d (F.erase a) else G = F ) := by
  classical
  intro I typeclassInstance0 fs a d b G
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨F, hF, hG⟩
    refine ⟨F, hF, ?_⟩
    by_cases hab : a ∈ F ∧ b ∈ F
    · simpa [P3523T1BoundaryFaceSplit, hab] using hG
    · simpa [P3523T1BoundaryFaceSplit, hab] using hG
  · rintro ⟨F, hF, hG⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨F, hF, ?_⟩
    by_cases hab : a ∈ F ∧ b ∈ F
    · simpa [P3523T1BoundaryFaceSplit, hab] using hG
    · simpa [P3523T1BoundaryFaceSplit, hab] using hG

private theorem split_mem_cases :
    (by
      classical
      exact
        (∀ {I : Type}, ∀ [DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d : I), ∀ (b
            : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs, if a ∈ F
            ∧ b ∈ F then G = insert d (F.erase b) ∨ G = insert d (F.erase a) else G = F) → (∀
            {I : Type}, ∀ [DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d :
            I), ∀ (b : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs,
            a ∈ F ∧ b ∈ F ∧ (G = insert d (F.erase b) ∨ G = insert d (F.erase a)) ∨ ¬(a ∈ F ∧ b ∈
            F) ∧ G = F) ) := by
  classical
  intro split_mem I typeclassInstance0 fs a d b G
  constructor
  · intro h
    rcases (split_mem fs a d b G).mp h with ⟨F, hF, hbranch⟩
    by_cases hh : a ∈ F ∧ b ∈ F
    · refine ⟨F, hF, Or.inl ⟨hh.1, hh.2, ?_⟩⟩
      exact Eq.mp (ite_eq_left hh) hbranch
    · refine ⟨F, hF, Or.inr ⟨hh, ?_⟩⟩
      exact Eq.mp (ite_eq_right hh) hbranch
  · rintro ⟨F, hF, hbranch⟩
    apply (split_mem fs a d b G).mpr
    refine ⟨F, hF, ?_⟩
    rcases hbranch with ⟨ha, hb, hchildren⟩ | ⟨hh, hsame⟩
    · have hh : a ∈ F ∧ b ∈ F := ⟨ha, hb⟩
      rw [ite_eq_left hh]
      exact hchildren
    · rw [ite_eq_right hh]
      exact hsame

private theorem triangleMatrix_det :
    (by
      classical
      exact
        let triangleMatrix (v : Fin 3 → Real × Real) :
            Matrix (Fin 3) (Fin 3) Real :=
          fun i j => if j = 0 then (v i).1 else if j = 1 then (v i).2 else 1
        ∀ (v : Fin (3 : ℕ) → ℝ × ℝ), P3381T1TriangleDeterminant v = (triangleMatrix v).det ) := by
  classical
  intro triangleMatrix v
  rw [Matrix.det_fin_three]
  simp [triangleMatrix, P3381T1TriangleDeterminant]
  ring

private theorem det_range_transport :
    (by
      classical
      exact
        let triangleMatrix (v : Fin 3 → Real × Real) :
            Matrix (Fin 3) (Fin 3) Real :=
          fun i j => if j = 0 then (v i).1 else if j = 1 then (v i).2 else 1
        (∀ (v : Fin 3 → Real × Real), P3381T1TriangleDeterminant v = (triangleMatrix v).det) →
            (∀ {I : Type}, ∀ (f : Fin (3 : ℕ) → I), ∀ (g : Fin (3 : ℕ) → I), Function.Injective f
            → Function.Injective g → Set.range f = Set.range g → ∀ (v : I → ℝ × ℝ),
            P3381T1TriangleDeterminant (v ∘ f) ≠ (0 : ℝ) ↔ P3381T1TriangleDeterminant (v ∘ g)
            ≠ (0 : ℝ)) ) := by
  classical
  intro triangleMatrix triangleMatrix_det I f g hf hg hr v
  have hmem (i : Fin 3) : f i ∈ Set.range g := by
    rw [← hr]
    exact Set.mem_range_self i
  let eFun : Fin 3 → Fin 3 :=
    fun i => Classical.choose (Set.mem_range.mp (hmem i))
  have heq (i : Fin 3) : g (eFun i) = f i :=
    Classical.choose_spec (Set.mem_range.mp (hmem i))
  have heinj : Function.Injective eFun := by
    intro i j hij
    apply hf
    calc
      f i = g (eFun i) := (heq i).symm
      _ = g (eFun j) := by rw [hij]
      _ = f j := heq j
  have hes : Function.Surjective eFun := Finite.surjective_of_injective heinj
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective eFun ⟨heinj, hes⟩
  have hcomp : v ∘ f = (v ∘ g) ∘ σ := by
    funext i
    change v (f i) = v (g (eFun i))
    exact congrArg v (heq i).symm
  have hdet : P3381T1TriangleDeterminant (v ∘ f) =
      (Equiv.Perm.sign σ : ℤˣ) *
        P3381T1TriangleDeterminant (v ∘ g) := by
    calc
      _ = (triangleMatrix (v ∘ f)).det := triangleMatrix_det _
      _ = (triangleMatrix ((v ∘ g) ∘ σ)).det := by rw [hcomp]
      _ = ((triangleMatrix (v ∘ g)).submatrix σ id).det := by congr 1
      _ = (Equiv.Perm.sign σ : ℤˣ) * (triangleMatrix (v ∘ g)).det := by
        simpa using (Matrix.det_permute σ (triangleMatrix (v ∘ g)))
      _ = _ := by rw [← triangleMatrix_det]
  have hsign : (Equiv.Perm.sign σ : Real) ≠ 0 := by
    have hz : (Equiv.Perm.sign σ : ℤ) ≠ 0 :=
      (Equiv.Perm.sign σ).ne_zero
    exact_mod_cast hz
  rw [hdet]
  constructor
  · intro h
    exact (mul_ne_zero_iff_left hsign).mp h
  · intro h
    exact mul_ne_zero hsign h

private theorem hfaces0 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        c.faces 0 = Finset.univ.image (fun k : Fin t.count => Finset.univ.image (s.start ∘ t.face
            k)) ) := by
  classical
  intro r n q p s X K t c
  simp [c, P3523T1InsertionConstruction]

private theorem initialDet :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀
            {I : Type}, ∀ (f : Fin 3 → I), ∀ (g : Fin 3 → I), (Function.Injective f) →
            ((Function.Injective g) → ((Set.range f = Set.range g) → (∀ (v : I → Real × Real),
            P3381T1TriangleDeterminant (v ∘ f) ≠ 0 ↔ P3381T1TriangleDeterminant (v ∘ g) ≠
            0)))) → (
        let c := P3523T1InsertionConstruction s t
        (c.faces 0 = Finset.univ.image (fun k : Fin t.count => Finset.univ.image (s.start ∘
            t.face k))) → (∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (old : Fin (r + (3 : ℕ)) → ℝ ×
            ℝ), (∀ (i : Fin (r + (3 : ℕ))), v (s.start i) = old i) → (∀ (k : Fin t.count),
            P3381T1TriangleDeterminant (old ∘ t.face k) ≠ (0 : ℝ)) → ∀ F ∈ c.faces (0 : ℕ), ∀
            (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))), Function.Injective g → Set.range g = (↑F : Set
            (Fin (n + (3 : ℕ)))) → P3381T1TriangleDeterminant (v ∘ g) ≠ (0 : ℝ))) ) := by
  classical
  intro r n q p s X K t det_range_transport c hfaces0 v old hstart hcert F hF g hg hgrange
  rw [hfaces0] at hF
  rcases Finset.mem_image.mp hF with ⟨k, -, hF⟩
  have hrange :
      ((Finset.univ.image (s.start ∘ t.face k) : Finset (Fin (n + 3))) :
        Set (Fin (n + 3))) = Set.range (s.start ∘ t.face k) := by
    ext x
    simp [Function.comp_apply]
  have hcanonical : Set.range (s.start ∘ t.face k) = (F : Set _) := by
    rw [← hrange, ← hF]
  have hcanonicalInj : Function.Injective (s.start ∘ t.face k) :=
    s.start_injective.comp (t.face_injective k)
  have htransport := det_range_transport g (s.start ∘ t.face k)
    hg hcanonicalInj (hgrange.trans hcanonical.symm) v
  have hvalues : v ∘ (s.start ∘ t.face k) = old ∘ t.face k := by
    funext i
    simp only [Function.comp_apply]
    rw [hstart]
  exact htransport.mpr (by rw [hvalues]; exact hcert k)

private theorem existsThird :
    (by
      classical
      exact
        ∀ {I : Type}, ∀ [DecidableEq I], ∀ {F : Finset I}, F.card = (3 : ℕ) → ∀ {a : I}, ∀
            {b : I}, a ∈ F → b ∈ F → a ≠ b → ∃ (z : I), a ≠ z ∧ b ≠ z ∧ F = {a, b, z} ) := by
  classical
  intro I typeclassInstance0 F hcard a b ha hb hab
  obtain ⟨x, y, z, hxy, hxz, hyz, hF⟩ := Finset.card_eq_three.mp hcard
  subst F
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with hax | hay | haz
  · subst a
    rcases hb with hbx | hby | hbz
    · exact (hab hbx.symm).elim
    · subst b
      exact ⟨z, hxz, hyz, by ext w; simp⟩
    · subst b
      exact ⟨y, hxy, hyz.symm,
        by ext w; simp [or_comm]⟩
  · subst a
    rcases hb with hbx | hby | hbz
    · subst b
      exact ⟨z, hyz, hxz, by ext w; simp [or_left_comm]⟩
    · exact (hab hby.symm).elim
    · subst b
      exact ⟨x, hxy.symm, hxz.symm,
        by ext w; simp [or_left_comm, or_comm]⟩
  · subst a
    rcases hb with hbx | hby | hbz
    · subst b
      exact ⟨y, hyz.symm, hxy,
        by ext w; simp [or_left_comm, or_comm]⟩
    · subst b
      exact ⟨x, hxz.symm, hxy.symm,
        by ext w; simp [or_left_comm, or_comm]⟩
    · exact (hab hbz.symm).elim

private theorem hstartSource :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (i : Fin (r
            + (3 : ℕ))), p.vertex (s.start i) = q.vertex i ) := by
  classical
  intro r n q p s i
  simpa [s.edge_start, s.parameter_start] using s.vertex_formula (s.start i)

private theorem sourceInterp :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (h
            : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s t).steps.length),
        let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2} ∈
            (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 :
            ℝ) ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
            P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s
            t e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → (
        let c := P3523T1InsertionConstruction s t
        ∀ h, ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
          ∃ u : Real, 0 < u ∧ u < 1 ∧
            p.vertex e.2.1 = (1-u) • p.vertex e.1 + u • p.vertex e.2.2) ) := by
  classical
  intro r n q p s X K t hstep c h hh
  rcases hstep h hh with ⟨_, _, _, _, _, ⟨u, hu0, hu1, hsource, _⟩⟩
  exact ⟨u, hu0, hu1, hsource⟩

private theorem targetInterp :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (h
            : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s t).steps.length),
        let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2} ∈
            (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 :
            ℝ) ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
            P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s
            t e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → (
        let c := P3523T1InsertionConstruction s t
        ∀ h, ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
          ∃ u : Real, 0 < u ∧ u < 1 ∧
            P3523T1InterpolatedTarget s t e.2.1 =
              (1-u) • P3523T1InterpolatedTarget s t e.1 +
                u • P3523T1InterpolatedTarget s t e.2.2) ) := by
  classical
  intro r n q p s X K t hstep c h hh
  rcases hstep h hh with ⟨_, _, _, _, _, ⟨u, hu0, hu1, _, htarget⟩⟩
  exact ⟨u, hu0, hu1, htarget⟩

private theorem tripleInj :
    (by
      classical
      exact
        ∀ {I : Type}, ∀ {a : I}, ∀ {b : I}, ∀ {z : I}, a ≠ b → a ≠ z → b ≠ z → Function.Injective
            ![a, b, z] ) := by
  classical
  intro I a b z hab haz hbz i j hij
  fin_cases i
  · fin_cases j
    · rfl
    · exact (hab (by simpa using hij)).elim
    · exact (haz (by simpa using hij)).elim
  · fin_cases j
    · exact (hab (by simpa using hij.symm)).elim
    · rfl
    · exact (hbz (by simpa using hij)).elim
  · fin_cases j
    · exact (haz (by simpa using hij.symm)).elim
    · exact (hbz (by simpa using hij.symm)).elim
    · rfl

private theorem tripleRange :
    (by
      classical
      exact
        ∀ {I : Type}, ∀ [DecidableEq I], ∀ (a : I), ∀ (b : I), ∀ (z : I), Set.range ![a,
            b, z] = (↑({a, b, z} : Finset _) : Set I) ) := by
  classical
  intro I typeclassInstance0 a b z
  ext x
  simp [or_left_comm, or_comm]

private theorem splitFinsets :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (d : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 :
            ℕ))), ∀ (z : Fin (n + (3 : ℕ))), a ≠ b → a ≠ z → b ≠ z → insert d (({a, b, z} :
                Finset (Fin (n + 3))).erase b)
            = {a, d, z} ∧ insert d (({a, b, z} : Finset (Fin (n + 3))).erase a) = {d, b, z} ) := by
  classical
  intro n a d b z hab haz hbz
  constructor
  · ext x
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro (hd | ⟨hnb, ha | hb | hz⟩)
      · exact Or.inr (Or.inl hd)
      · exact Or.inl ha
      · exact (hnb hb).elim
      · exact Or.inr (Or.inr hz)
    · rintro (ha | hd | hz)
      · exact Or.inr ⟨fun h => hab (ha.symm.trans h), Or.inl ha⟩
      · exact Or.inl hd
      · exact Or.inr ⟨fun h => hbz (h.symm.trans hz), Or.inr (Or.inr hz)⟩
  · ext x
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro (hd | ⟨hna, ha | hb | hz⟩)
      · exact Or.inl hd
      · exact (hna ha).elim
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hz)
    · rintro (hd | hb | hz)
      · exact Or.inl hd
      · exact Or.inr ⟨fun h => hab (h.symm.trans hb), Or.inr (Or.inl hb)⟩
      · exact Or.inr ⟨fun h => haz (h.symm.trans hz), Or.inr (Or.inr hz)⟩

private theorem mapTriple :
    (by
      classical
      exact
        ∀ {I : Type}, ∀ {J : Type}, ∀ (v : I → J), ∀ (a : I), ∀ (b : I), ∀ (z : I), v ∘ ![a, b,
            z] = ![v a, v b, v z] ) := by
  classical
  intro I J v a b z
  funext i
  fin_cases i <;> rfl

private theorem detState :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀
            {I : Type}, ∀ [DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d : I), ∀ (b
            : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs, if a ∈ F
            ∧ b ∈ F then G = insert d (F.erase b) ∨ G = insert d (F.erase a) else G = F) → ((∀
            {I : Type}, ∀ (f : Fin 3 → I), ∀ (g : Fin 3 → I), (Function.Injective f) →
            ((Function.Injective g) → ((Set.range f = Set.range g) → (∀ (v : I → Real × Real),
            P3381T1TriangleDeterminant (v ∘ f) ≠ 0 ↔ P3381T1TriangleDeterminant (v ∘ g) ≠
            0)))) → ((∀ h ≤ (P3523T1InsertionConstruction s t).steps.length, ∀ F ∈
            (P3523T1InsertionConstruction s t).faces h, F.card = (3 : ℕ) ∧ F ⊆
            (P3523T1InsertionConstruction s t).vertices h) → ((∀ (h : ℕ), ∀ (hh : h <
            (P3523T1InsertionConstruction s t).steps.length),
        let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2} ∈
            (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 :
            ℝ) ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
            P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s
            t e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → (
        let c := P3523T1InsertionConstruction s t
        (∀ {I : Type}, ∀ [DecidableEq I], ∀ {F : Finset I}, (F.card = 3) → (∀ {a : I}, ∀ {b : I},
            (a ∈ F) → ((b ∈ F) → ((a ≠ b) → (∃ z, a ≠ z ∧ b ≠ z ∧ F = {a, b, z}))))) → ((∀
            {I : Type}, ∀ {a : I}, ∀ {b : I}, ∀ {z : I}, (a ≠ b) → ((a ≠ z) → ((b ≠ z) →
            (Function.Injective ![a, b, z])))) → ((∀ {I : Type}, ∀ [DecidableEq I], ∀ (a : I), ∀
            (b : I), ∀ (z : I), Set.range ![a, b, z] = (({a, b, z} : Finset I) : Set I)) → ((∀
            {I : Type}, ∀ {J : Type}, ∀ (v : I → J), ∀ (a : I), ∀ (b : I), ∀ (z : I), v ∘ ![a, b,
            z] = ![v a, v b, v z]) → (∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), (∀ (h : ℕ), ∀ (hh : h <
            c.steps.length),
        let e := c.steps.get ⟨h, hh⟩;
          ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ) ∧ v e.2.1 = ((1 : ℝ) - u) • v e.1 + u • v e.2.2) →
        (∀ F ∈ c.faces (0 : ℕ),
            ∀ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))), Function.Injective g →
                Set.range g = (↑F : Set (Fin (n + (3 : ℕ)))) → P3381T1TriangleDeterminant (v ∘
                    g) ≠ (0 : ℝ)) →
          ∀ h ≤ c.steps.length,
            ∀ F ∈ c.faces h,
              ∀ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))), Function.Injective g →
                  Set.range g = (↑F : Set (Fin (n + (3 : ℕ)))) → P3381T1TriangleDeterminant (v
                      ∘ g) ≠ (0 : ℝ))))))))) ) := by
  classical
  intro r n q p s X K t split_mem det_range_transport hfaceShape hstep c existsThird tripleInj
      tripleRange mapTriple v hinterp hinit h
  induction h with
  | zero =>
      intro _ F hF g hg hgrange
      exact hinit F hF g hg hgrange
  | succ h ih =>
      intro hle F hF g hg hgrange
      have hh : h < c.steps.length := by omega
      let e := c.steps.get ⟨h, hh⟩
      rcases hstep h hh with ⟨hab, haV, hbV, hdV, _, _⟩
      have hfacesRec : c.faces (h + 1) =
          P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2 := by
        change (c.steps.take (h + 1)).foldl
          (fun fs e => P3523T1BoundaryFaceSplit fs e.1 e.2.1 e.2.2)
          (Finset.univ.image fun k : Fin t.count =>
            Finset.univ.image (s.start ∘ t.face k)) =
          P3523T1BoundaryFaceSplit
            ((c.steps.take h).foldl
              (fun fs e => P3523T1BoundaryFaceSplit fs e.1 e.2.1 e.2.2)
              (Finset.univ.image fun k : Fin t.count =>
                Finset.univ.image (s.start ∘ t.face k)))
            (c.steps[h].1) (c.steps[h].2.1) (c.steps[h].2.2)
        rw [List.take_succ_eq_append_getElem hh]
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hfacesRec] at hF
      obtain ⟨F₀, hF₀, hbranch⟩ :=
        (split_mem (c.faces h) e.1 e.2.1 e.2.2 F).mp hF
      by_cases hhit : e.1 ∈ F₀ ∧ e.2.2 ∈ F₀
      · have hchildren :
            F = insert e.2.1 (F₀.erase e.2.2) ∨
              F = insert e.2.1 (F₀.erase e.1) := by
          simpa [hhit] using hbranch
        rcases hchildren with hleft | hright
        · have hleFace : h ≤ (P3523T1InsertionConstruction s t).steps.length := by
            have : h ≤ c.steps.length := by omega
            simpa [c] using this
          have hshape := hfaceShape h hleFace F₀ hF₀
          obtain ⟨z, haz, hbz, hF₀eq⟩ :=
            existsThird hshape.1 hhit.1 hhit.2 hab
          have hzV : z ∈ c.vertices h := hshape.2 (by rw [hF₀eq]; simp)
          have had : e.1 ≠ e.2.1 := by
            intro heq
            exact hdV (heq ▸ haV)
          have hzd : z ≠ e.2.1 := by
            intro heq
            exact hdV (heq ▸ hzV)
          have hcanInj := tripleInj had haz hzd.symm
          have hprev := ih (by omega) F₀ hF₀ ![e.1, e.2.2, z]
            (tripleInj hab haz hbz) (by
              rw [hF₀eq]
              exact tripleRange e.1 e.2.2 z)
          have hn : P3381T1TriangleDeterminant ![v e.1, v e.2.2, v z] ≠ 0 := by
            rw [mapTriple v e.1 e.2.2 z] at hprev
            exact hprev
          obtain ⟨u, hu0, hu1, hvalue⟩ := hinterp h hh
          have hsplit := P3523T1SplitDeterminants
            (v e.1) (v e.2.2) (v z) u ⟨hu0, hu1⟩ hn
          have hfinLeft : insert e.2.1 (F₀.erase e.2.2) =
              ({e.1, e.2.1, z} : Finset (Fin (n + 3))) := by
            rw [hF₀eq]
            ext x
            simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
            constructor
            · rintro (hxd | ⟨hxb, hxa | hxb' | hxz⟩)
              · exact Or.inr (Or.inl hxd)
              · exact Or.inl hxa
              · exact (hxb hxb').elim
              · exact Or.inr (Or.inr hxz)
            · rintro (hxa | hxd | hxz)
              · exact Or.inr ⟨fun h => hab (hxa.symm.trans h), Or.inl hxa⟩
              · exact Or.inl hxd
              · exact Or.inr ⟨fun h => hbz (h.symm.trans hxz), Or.inr (Or.inr hxz)⟩
          have hrangeLeft : Set.range ![e.1, e.2.1, z] =
              (F : Set _) := by
            rw [tripleRange, hleft, ← hfinLeft]
          have hcanonicalLeft :
              P3381T1TriangleDeterminant ![v e.1, v e.2.1, v z] ≠ 0 := by
            simpa only [e, ← hvalue] using hsplit.2.2.1
          have htransport := det_range_transport g ![e.1, e.2.1, z]
            hg hcanInj (hgrange.trans hrangeLeft.symm) v
          exact htransport.mpr (by
            rw [mapTriple v e.1 e.2.1 z]
            exact hcanonicalLeft)
        · have hleFace : h ≤ (P3523T1InsertionConstruction s t).steps.length := by
            have : h ≤ c.steps.length := by omega
            simpa [c] using this
          have hshape := hfaceShape h hleFace F₀ hF₀
          obtain ⟨z, haz, hbz, hF₀eq⟩ :=
            existsThird hshape.1 hhit.1 hhit.2 hab
          have hzV : z ∈ c.vertices h := hshape.2 (by rw [hF₀eq]; simp)
          have hbd : e.2.2 ≠ e.2.1 := by
            intro heq
            exact hdV (heq.symm ▸ hbV)
          have hzd : z ≠ e.2.1 := by
            intro heq
            exact hdV (heq ▸ hzV)
          have hprev := ih (by omega) F₀ hF₀ ![e.1, e.2.2, z]
            (tripleInj hab haz hbz) (by rw [hF₀eq]; exact tripleRange _ _ _)
          have hn : P3381T1TriangleDeterminant ![v e.1, v e.2.2, v z] ≠ 0 := by
            rw [mapTriple v e.1 e.2.2 z] at hprev
            exact hprev
          obtain ⟨u, hu0, hu1, hvalue⟩ := hinterp h hh
          have hsplit := P3523T1SplitDeterminants
            (v e.1) (v e.2.2) (v z) u ⟨hu0, hu1⟩ hn
          have hfinRight : insert e.2.1 (F₀.erase e.1) =
              ({e.2.1, e.2.2, z} : Finset (Fin (n + 3))) := by
            rw [hF₀eq]
            ext x
            simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
            constructor
            · rintro (hxd | ⟨hxa, hxa' | hxb | hxz⟩)
              · exact Or.inl hxd
              · exact (hxa hxa').elim
              · exact Or.inr (Or.inl hxb)
              · exact Or.inr (Or.inr hxz)
            · rintro (hxd | hxb | hxz)
              · exact Or.inl hxd
              · exact Or.inr ⟨fun h => hab (h.symm.trans hxb), Or.inr (Or.inl hxb)⟩
              · exact Or.inr ⟨fun h => haz (h.symm.trans hxz), Or.inr (Or.inr hxz)⟩
          have hrangeRight : Set.range ![e.2.1, e.2.2, z] =
              (F : Set _) := by
            rw [tripleRange, hright, ← hfinRight]
          have hcanRightInj := tripleInj hbd.symm hzd.symm hbz
          have hcanonicalRight :
              P3381T1TriangleDeterminant ![v e.2.1, v e.2.2, v z] ≠ 0 := by
            have hvalue' : v e.2.1 = (1-u) • v e.1 + u • v e.2.2 := by
              simpa [e] using hvalue
            have htemp := hsplit.2.2.2
            change P3381T1TriangleDeterminant
              ![(1-u) • v e.1 + u • v e.2.2, v e.2.2, v z] ≠ 0 at htemp
            rw [← hvalue'] at htemp
            exact htemp
          have htransport := det_range_transport g ![e.2.1, e.2.2, z]
            hg hcanRightInj (hgrange.trans hrangeRight.symm) v
          exact htransport.mpr (by
            rw [mapTriple v e.2.1 e.2.2 z]
            exact hcanonicalRight)
      · have hunchanged : F = F₀ := by simpa [hhit] using hbranch
        subst F
        exact ih (by omega) F₀ hF₀ g hg hgrange

private theorem terminalFace :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
            ((Set.range fun (k : Fin ((P3523T1InsertionConstruction s t).faces
            (P3523T1InsertionConstruction s t).steps.length).card) => Set.range
            (P3523T1FaceEnumeration ((P3523T1InsertionConstruction s t).faces
            (P3523T1InsertionConstruction s t).steps.length) k)) = {J : Set (Fin (n + (3 : ℕ)))
            | ∃ F ∈ (P3523T1InsertionConstruction s t).faces (P3523T1InsertionConstruction s
            t).steps.length, (↑F : Set (Fin (n + (3 : ℕ)))) = J}) → (
        let c := P3523T1InsertionConstruction s t
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        ∀ (k : Fin (c.faces c.steps.length).card), ∃ F ∈ c.faces c.steps.length, Set.range (f k)
            = (↑F : Set (Fin (n + (3 : ℕ))))) ) := by
  classical
  intro r n q p s X K t hfaceRange c f k
  have hk : Set.range (f k) ∈ Set.range (fun j => Set.range (f j)) :=
    Set.mem_range_self k
  rw [hfaceRange] at hk
  rcases hk with ⟨F, hF, hEq⟩
  exact ⟨F, by simpa [c] using hF, hEq.symm⟩

private theorem hsourceDet :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (k
            : Fin ((P3523T1InsertionConstruction s t).faces (P3523T1InsertionConstruction s
            t).steps.length).card), Function.Injective (P3523T1FaceEnumeration
            ((P3523T1InsertionConstruction s t).faces (P3523T1InsertionConstruction s
            t).steps.length) k)) → (
        let c := P3523T1InsertionConstruction s t
        (∀ h ≤ c.steps.length, ∀ F ∈ c.faces h, ∀ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))),
            Function.Injective g → Set.range g = (↑F : Set (Fin (n + (3 : ℕ)))) →
            P3381T1TriangleDeterminant (p.vertex ∘ g) ≠ (0 : ℝ)) → (
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        (∀ (k : Fin (c.faces c.steps.length).card), ∃ F ∈ c.faces c.steps.length, Set.range (f k)
            = (F : Set _)) → (∀ k : Fin (c.faces c.steps.length).card,
            P3381T1TriangleDeterminant (p.vertex ∘ f k) ≠ 0))) ) := by
  classical
  intro r n q p s X K t hfaceInj c sourceState f terminalFace k
  obtain ⟨F, hF, hrange⟩ := terminalFace k
  exact sourceState c.steps.length le_rfl F hF (f k) (hfaceInj k) hrange

private theorem htargetDet :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (k
            : Fin ((P3523T1InsertionConstruction s t).faces (P3523T1InsertionConstruction s
            t).steps.length).card), Function.Injective (P3523T1FaceEnumeration
            ((P3523T1InsertionConstruction s t).faces (P3523T1InsertionConstruction s
            t).steps.length) k)) → (
        let c := P3523T1InsertionConstruction s t
        (∀ h ≤ c.steps.length, ∀ F ∈ c.faces h, ∀ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))),
            Function.Injective g → Set.range g = (↑F : Set (Fin (n + (3 : ℕ)))) →
            P3381T1TriangleDeterminant (P3523T1InterpolatedTarget s t ∘ g) ≠ (0 : ℝ)) → (
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        (∀ (k : Fin (c.faces c.steps.length).card), ∃ F ∈ c.faces c.steps.length, Set.range (f k)
            = (F : Set _)) → (∀ k : Fin (c.faces c.steps.length).card,
            P3381T1TriangleDeterminant (P3523T1InterpolatedTarget s t ∘ f k) ≠ 0))) ) := by
  classical
  intro r n q p s X K t hfaceInj c targetState f terminalFace k
  obtain ⟨F, hF, hrange⟩ := terminalFace k
  exact targetState c.steps.length le_rfl F hF (f k) (hfaceInj k) hrange

private theorem imageUnion :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {γ : Type}, ∀ [inst : DecidableEq β], ∀
            (s₀ : Finset α), ∀ (g₀ : α → β), ∀ (P : β → Set γ), ⋃ y ∈ (↑(Finset.image g₀ s₀) :
            Set β), P y = ⋃ x ∈ (↑s₀ : Set α), P (g₀ x) ) := by
  classical
  intro α β γ typeclassInstance1 s₀ g₀ P
  ext z
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hz⟩
    exact ⟨a, ha, hz⟩
  · rintro ⟨a, ha, hz⟩
    exact ⟨g₀ a, ⟨a, ha, rfl⟩, hz⟩

private theorem imageTriple :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n
            + (3 : ℕ))), ∀ (z : Fin (n + (3 : ℕ))), v '' (↑({a, b, z} : Finset _) : Set (Fin (n +
                (3 : ℕ)))) =
            {v a, v b, v z} ) := by
  classical
  intro n v a b z
  ext x
  simp []

private theorem imagePair :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (a : Fin (n + (3 : ℕ))), ∀ (z : Fin (n
            + (3 : ℕ))), v '' (↑({a, z} : Finset _) : Set (Fin (n + (3 : ℕ)))) = {v a, v z} ) := by
  classical
  intro n v a z
  ext x
  simp []

private theorem splitHull :
    (by
      classical
      exact
        ∀ (n : Nat), (∀ (v : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (z : Fin (n + 3)), v '' (({a, b, z} : Finset (Fin (n + 3))) : Set (Fin (n +
            3))) = {v a, v b, v z}) → (∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (a : Fin (n + (3 :
            ℕ))), ∀ (d : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 :
            ℕ))), a ≠ b → a ≠ z → b ≠ z → ∀ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ) → v d = ((1 : ℝ) -
            u) • v a + u • v b → P3381T1TriangleDeterminant ![v a, v b, v z] ≠ (0 : ℝ) →
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, b, z} : Finset _) : Set (Fin
                (n + (3 :
            ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) :
                Set (Fin (n +
            (3 : ℕ))))) ∪ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset
                _) : Set (Fin
            (n + (3 : ℕ)))))) ) := by
  classical
  intro n imageTriple v a d b z hab haz hbz u hu hvalue hdet
  have hgeo := P3523T1TwoTriangleSplit (v a) (v b) (v z) u hu hdet
  have hleft := imageTriple v a d z
  have hright := imageTriple v d b z
  have hold := imageTriple v a b z
  rw [hold, hleft, hright]
  simpa [hvalue] using hgeo.1

private theorem splitGeometry :
    (by
      classical
      exact
        ∀ (n : Nat), (∀ (v : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (z : Fin (n + 3)), v '' (({a, b, z} : Finset (Fin (n + 3))) : Set (Fin (n +
            3))) = {v a, v b, v z}) → (∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (a : Fin (n + (3 :
            ℕ))), ∀ (d : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 :
            ℕ))), a ≠ b → a ≠ z → b ≠ z → ∀ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ) → v d = ((1 : ℝ) -
            u) • v a + u • v b → P3381T1TriangleDeterminant ![v a, v b, v z] ≠ (0 : ℝ) →
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, b, z} : Finset _) : Set (Fin
                (n + (3 :
            ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) :
                Set (Fin (n +
            (3 : ℕ))))) ∪ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset
                _) : Set (Fin
            (n + (3 : ℕ))))) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} :
                Finset _) : Set
            (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z}
                : Finset _)
            : Set (Fin (n + (3 : ℕ))))) = segment ℝ (v d) (v z) ∧ ∀ J ⊆ {v a, v b, v z}, ¬(v a ∈
            J ∧ v b ∈ J) → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset
                _) : Set
            (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) J = (convexHull ℝ
            : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v a, v z}) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ
            × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ :
                Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v b, v z})) ) := by
  classical
  intro n imageTriple v a d b z hab haz hbz u hu hvalue hdet
  have hgeo := P3523T1TwoTriangleSplit (v a) (v b) (v z) u hu hdet
  have hleft := imageTriple v a d z
  have hright := imageTriple v d b z
  have hold := imageTriple v a b z
  constructor
  · rw [hold, hleft, hright]
    simpa [hvalue] using hgeo.1
  constructor
  · rw [hleft, hright]
    simpa [hvalue] using hgeo.2.1
  · intro J hJ hnot
    rcases hgeo.2.2 J hJ hnot with ⟨hl, hr⟩
    constructor
    · rw [hleft]
      simpa [hvalue] using hl
    · rw [hright]
      simpa [hvalue] using hr

private theorem sourceStartImage :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (i
            : Fin (r + 3)), p.vertex (s.start i) = q.vertex i) → (∀ (k : Fin t.count), p.vertex
            '' (↑(Finset.image (s.start ∘ t.face k) Finset.univ) : Set (Fin (n + (3 : ℕ)))) =
            Set.range (q.vertex ∘ t.face k)) ) := by
  classical
  intro r n q p s X K t hstartSource k
  ext x
  simp [Function.comp_apply, hstartSource]

private theorem targetStartImage :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (i
            : Fin (r + (3 : ℕ))), P3523T1InterpolatedTarget s t (s.start i) = t.target i) → (∀
            (k : Fin t.count), P3523T1InterpolatedTarget s t '' (↑(Finset.image (s.start ∘
            t.face k) Finset.univ) : Set (Fin (n + (3 : ℕ)))) = Set.range (t.target ∘ t.face k))
            ) := by
  classical
  intro r n q p s X K t hstartTarget k
  ext x
  simp [Function.comp_apply, hstartTarget]

private theorem startFaceSet :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (k
            : Fin t.count), (↑(Finset.image (s.start ∘ t.face k) Finset.univ) : Set (Fin (n + (3
            : ℕ)))) = s.start '' Set.range (t.face k) ) := by
  classical
  intro r n q p s X K t k
  ext x
  simp [Function.comp_apply]

private theorem sourceStartCommon :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (i
            : Fin (r + 3)), p.vertex (s.start i) = q.vertex i) → ((∀ (k : Fin t.count),
            ((Finset.univ.image (s.start ∘ t.face k) : Finset (Fin (n + 3))) : Set (Fin (n + 3)))
            = s.start '' Set.range (t.face k)) → (∀ (i : Fin t.count), ∀ (j : Fin t.count),
            p.vertex '' ((↑(Finset.image (s.start ∘ t.face i) Finset.univ) : Set (Fin (n + (3 :
            ℕ)))) ∩ (↑(Finset.image (s.start ∘ t.face j) Finset.univ) : Set (Fin (n + (3 : ℕ)))))
            = q.vertex '' (Set.range (t.face i) ∩ Set.range (t.face j)))) ) := by
  classical
  intro r n q p s X K t hstartSource startFaceSet i j
  rw [startFaceSet i, startFaceSet j, ← Set.image_inter s.start_injective]
  rw [Set.image_image]
  ext x
  simp [hstartSource]

private theorem targetStartCommon :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (i
            : Fin (r + (3 : ℕ))), P3523T1InterpolatedTarget s t (s.start i) = t.target i) → ((∀
            (k : Fin t.count), ((Finset.univ.image (s.start ∘ t.face k) : Finset (Fin (n + 3))) :
            Set (Fin (n + 3))) = s.start '' Set.range (t.face k)) → (∀ (i : Fin t.count), ∀ (j :
            Fin t.count), P3523T1InterpolatedTarget s t '' ((↑(Finset.image (s.start ∘ t.face
            i) Finset.univ) : Set (Fin (n + (3 : ℕ)))) ∩ (↑(Finset.image (s.start ∘ t.face j)
            Finset.univ) : Set (Fin (n + (3 : ℕ))))) = t.target '' (Set.range (t.face i) ∩
            Set.range (t.face j)))) ) := by
  classical
  intro r n q p s X K t hstartTarget startFaceSet i j
  rw [startFaceSet i, startFaceSet j, ← Set.image_inter s.start_injective]
  rw [Set.image_image]
  ext x
  simp [hstartTarget]

private theorem sourceBase :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (c.faces 0 = Finset.univ.image (fun k : Fin t.count => Finset.univ.image (s.start ∘
            t.face k))) → (
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        (∀ {α : Type}, ∀ {β : Type}, ∀ {γ : Type}, ∀ [DecidableEq α], ∀ [DecidableEq β], ∀ (s₀ :
            Finset α), ∀ (g₀ : α → β), ∀ (P : β → Set γ), (⋃ y ∈ (s₀.image g₀ : Set β), P y) = ⋃
            x ∈ (s₀ : Set α), P (g₀ x)) → ((∀ (k : Fin t.count), p.vertex '' ((Finset.univ.image
            (s.start ∘ t.face k) : Finset (Fin (n + 3))) : Set (Fin (n + 3))) = Set.range
            (q.vertex ∘ t.face k)) → (faceUnion p.vertex (c.faces 0) = X))) ) := by
  classical
  intro r n q p s X K t c hfaces0 faceUnion imageUnion sourceStartImage
  rw [hfaces0]
  dsimp only [faceUnion]
  rw [imageUnion]
  simp_rw [sourceStartImage]
  simpa using t.source_cover.symm

private theorem targetBase :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (c.faces 0 = Finset.univ.image (fun k : Fin t.count => Finset.univ.image (s.start ∘
            t.face k))) → (
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        (∀ {α : Type}, ∀ {β : Type}, ∀ {γ : Type}, ∀ [DecidableEq α], ∀ [DecidableEq β], ∀ (s₀ :
            Finset α), ∀ (g₀ : α → β), ∀ (P : β → Set γ), (⋃ y ∈ (s₀.image g₀ : Set β), P y) = ⋃
            x ∈ (s₀ : Set α), P (g₀ x)) → ((∀ (k : Fin t.count), (P3523T1InterpolatedTarget s
            t) '' ((Finset.univ.image (s.start ∘ t.face k) : Finset (Fin (n + 3))) : Set (Fin (n
            + 3))) = Set.range (t.target ∘ t.face k)) → (faceUnion (P3523T1InterpolatedTarget s
            t) (c.faces 0) = K))) ) := by
  classical
  intro r n q p s X K t c hfaces0 faceUnion imageUnion targetStartImage
  rw [hfaces0]
  dsimp only [faceUnion]
  rw [imageUnion]
  simp_rw [targetStartImage]
  simpa using t.target_cover.symm

private theorem hfacesRecAt698 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        c.faces (h + 1) = P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2 ) := by
  classical
  intro r n q p s X K t c h hh e
  change (c.steps.take (h + 1)).foldl
    (fun fs e => P3523T1BoundaryFaceSplit fs e.1 e.2.1 e.2.2)
    (Finset.univ.image fun k : Fin t.count =>
      Finset.univ.image (s.start ∘ t.face k)) =
    P3523T1BoundaryFaceSplit
      ((c.steps.take h).foldl
        (fun fs e => P3523T1BoundaryFaceSplit fs e.1 e.2.1 e.2.2)
        (Finset.univ.image fun k : Fin t.count =>
          Finset.univ.image (s.start ∘ t.face k)))
      (c.steps[h].1) (c.steps[h].2.1) (c.steps[h].2.2)
  rw [List.take_succ_eq_append_getElem hh]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem hchildrenAt721 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (G : Finset (Fin (n + (3 : ℕ)))), ∀ (F : Finset (Fin (n + (3 : ℕ)))), (if e.1 ∈ F ∧
            e.2.2 ∈ F then G = insert e.2.1 (F.erase e.2.2) ∨ G = insert e.2.1 (F.erase e.1) else
            G = F) → ((e.1 ∈ F ∧ e.2.2 ∈ F) → (G = insert e.2.1 (F.erase e.2.2) ∨ G = insert
            e.2.1 (F.erase e.1))) ) := by
  classical
  intro r n q p s X K t c h hh e G F hbranch hhit
  simpa [hhit] using hbranch

private theorem hleftFaceAt728 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).1 ≠
            ((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.2) → (∀ (F : Finset (Fin
            (n + (3 : ℕ)))), ∀ (z : Fin (n + (3 : ℕ))), (e.2.2 ≠ z) → ((F = {e.1, e.2.2, z}) →
            (insert e.2.1 (F.erase e.2.2) = ({e.1, e.2.1, z} : Finset (Fin (n + 3)))))) ) := by
  classical
  intro r n q p s X K t c h hh e hab F z hbz hFeq
  rw [hFeq]
  ext y
  simp only [Finset.mem_insert, Finset.mem_erase,
    Finset.mem_singleton]
  constructor
  · rintro (hd | ⟨hne, ha | hb | hz⟩)
    · exact Or.inr (Or.inl hd)
    · exact Or.inl ha
    · exact (hne hb).elim
    · exact Or.inr (Or.inr hz)
  · rintro (ha | hd | hz)
    · exact Or.inr ⟨fun h => hab (ha.symm.trans h), Or.inl ha⟩
    · exact Or.inl hd
    · exact Or.inr ⟨fun h => hbz (h.symm.trans hz), Or.inr (Or.inr hz)⟩

private theorem hrightFaceAt744 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).1 ≠
            ((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.2) → (∀ (F : Finset (Fin
            (n + (3 : ℕ)))), ∀ (z : Fin (n + (3 : ℕ))), (e.1 ≠ z) → ((F = {e.1, e.2.2, z}) →
            (insert e.2.1 (F.erase e.1) = ({e.2.1, e.2.2, z} : Finset (Fin (n + 3)))))) ) := by
  classical
  intro r n q p s X K t c h hh e hab F z haz hFeq
  rw [hFeq]
  ext y
  simp only [Finset.mem_insert, Finset.mem_erase,
    Finset.mem_singleton]
  constructor
  · rintro (hd | ⟨hne, ha | hb | hz⟩)
    · exact Or.inl hd
    · exact (hne ha).elim
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hz)
  · rintro (hd | hb | hz)
    · exact Or.inl hd
    · exact Or.inr ⟨fun h => hab (h.symm.trans hb), Or.inr (Or.inl hb)⟩
    · exact Or.inr ⟨fun h => haz (h.symm.trans hz), Or.inr (Or.inr hz)⟩

private theorem hdet'At762 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ {I : Type}, ∀ {J : Type}, ∀ (v : I → J), ∀ (a : I), ∀ (b : I), ∀ (z : I), v ∘ ![a, b,
            z] = ![v a, v b, v z]) → (∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (h : ℕ), ∀ (hh : h <
            c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (z : Fin (n + (3 : ℕ))), (P3381T1TriangleDeterminant (v ∘ ![e.1, e.2.2, z]) ≠ (0 :
            ℝ)) → (P3381T1TriangleDeterminant ![v e.1, v e.2.2, v z] ≠ 0)) ) := by
  classical
  intro r n q p s X K t c mapTriple v h hh e z hdet
  rw [mapTriple v e.1 e.2.2 z] at hdet
  exact hdet

private theorem hxParent :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (x : ℝ × ℝ), ∀ (G : Finset (Fin (n + (3 : ℕ)))), (x ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set
            (ℝ × ℝ)) (v '' (↑G : Set (Fin (n + (3 : ℕ)))))) → (∀ (F : Finset (Fin (n + (3 :
            ℕ)))), (G = insert e.2.1 (F.erase e.2.2) ∨ G = insert e.2.1 (F.erase e.1)) → (∀ (z :
            Fin (n + (3 : ℕ))), (F = {e.1, e.2.2, z}) → ((insert e.2.1 (F.erase e.2.2) = ({e.1,
            e.2.1, z} : Finset (Fin (n + 3)))) → ((insert e.2.1 (F.erase e.1) = ({e.2.1, e.2.2,
            z} : Finset (Fin (n + 3)))) → (((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑({e.1, e.2.2, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ ×
                ℝ) → Set (ℝ
            × ℝ)) (v '' (↑({e.1, e.2.1, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∪ (convexHull
                ℝ : Set (ℝ ×
            ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.2.1, e.2.2, z} : Finset _) : Set (Fin (n + (3 : ℕ))))))
                → (x ∈
            convexHull Real (v '' (F : Set _)))))))) ) := by
  classical
  intro r n q p s X K t c v h hh e x G hxG F hchildren z hFeq hleftFace hrightFace hgeo
  rcases hchildren with hleft | hright
  · rw [hleft, hleftFace] at hxG
    have : x ∈ convexHull Real (v ''
        (({e.1, e.2.1, z} : Finset (Fin (n + 3))) : Set _)) := hxG
    have hgeo' := hgeo
    rw [← hFeq] at hgeo'
    rw [hgeo']
    exact Or.inl this
  · rw [hright, hrightFace] at hxG
    have : x ∈ convexHull Real (v ''
        (({e.2.1, e.2.2, z} : Finset (Fin (n + 3))) : Set _)) := hxG
    have hgeo' := hgeo
    rw [← hFeq] at hgeo'
    rw [hgeo']
    exact Or.inr this

private theorem hxoldAt785 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (F : Finset (Fin (n + (3 : ℕ)))),
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (h : ℕ), ∀ (x : ℝ × ℝ), (F ∈ c.faces h) → ((x ∈
            convexHull Real (v '' (F : Set _))) → (x ∈ faceUnion v (c.faces h))) ) := by
  classical
  intro r n q p s X K t c F faceUnion v h x hF hxParent
  simp only [faceUnion, Set.mem_iUnion, Finset.mem_coe]
  exact ⟨F, hF, hxParent⟩

private theorem hxoldAt793 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (F : Finset (Fin (n + (3 : ℕ)))),
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (h : ℕ), ∀ (x : ℝ × ℝ), (F ∈ c.faces h) → ((x ∈
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑F : Set (Fin (n + (3 : ℕ)))))) →
            (x ∈ faceUnion v (c.faces h))) ) := by
  classical
  intro r n q p s X K t c F faceUnion v h x hF hxG
  simp only [faceUnion, Set.mem_iUnion, Finset.mem_coe]
  exact ⟨F, hF, hxG⟩

private theorem hchildrenAt804 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀
            {I : Type}, ∀ [DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d : I), ∀ (b
            : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs, if a ∈ F
            ∧ b ∈ F then G = insert d (F.erase b) ∨ G = insert d (F.erase a) else G = F) → (
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (F : Finset (Fin (n + (3 : ℕ)))), (F ∈ c.faces h) → ((e.1 ∈ F ∧ e.2.2 ∈ F) → (insert
            e.2.1 (F.erase e.2.2) ∈ P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2 ∧
            insert e.2.1 (F.erase e.1) ∈ P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1
            e.2.2))) ) := by
  classical
  intro r n q p s X K t split_mem c h hh e F hF hhit
  apply And.intro <;>
    apply (split_mem (c.faces h) e.1 e.2.1 e.2.2 _).mpr
  · exact ⟨F, hF, by simp [hhit]⟩
  · exact ⟨F, hF, by simp [hhit]⟩

private theorem hxSplit :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (x : ℝ × ℝ), ∀ (F : Finset (Fin (n + (3 : ℕ)))), (x ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set
            (ℝ × ℝ)) (v '' (↑F : Set (Fin (n + (3 : ℕ)))))) → (∀ (z : Fin (n + (3 : ℕ))), (F =
            {e.1, e.2.2, z}) → (((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.1, e.2.2,
            z} : Finset _) : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ ×
                ℝ)) (v ''
            (↑({e.1, e.2.1, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∪ (convexHull ℝ : Set (ℝ ×
                ℝ) → Set (ℝ
            × ℝ)) (v '' (↑({e.2.1, e.2.2, z} : Finset _) : Set (Fin (n + (3 : ℕ)))))) → (x ∈
                convexHull Real
            (v '' (({e.1, e.2.1, z} : Finset (Fin (n + 3))) : Set _)) ∪ convexHull Real (v ''
            (({e.2.1, e.2.2, z} : Finset (Fin (n + 3))) : Set _))))) ) := by
  classical
  intro r n q p s X K t c v h hh e x F hxF z hFeq hgeo
  have : x ∈ convexHull Real (v '' (F : Set _)) := hxF
  have hgeo' := hgeo
  rw [← hFeq] at hgeo'
  rw [hgeo'] at this
  exact this

private theorem hunchangedAt874 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀
            {I : Type}, ∀ [DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d : I), ∀ (b
            : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs, if a ∈ F
            ∧ b ∈ F then G = insert d (F.erase b) ∨ G = insert d (F.erase a) else G = F) → (
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (F : Finset (Fin (n + (3 : ℕ)))), (F ∈ c.faces h) → ((¬(e.1 ∈ F ∧ e.2.2 ∈ F)) → (F ∈
            P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2))) ) := by
  classical
  intro r n q p s X K t split_mem c h hh e F hF hhit
  apply (split_mem (c.faces h) e.1 e.2.1 e.2.2 F).mpr
  exact ⟨F, hF, by simp only [hhit, ite_false]⟩

private theorem uniqueEdgeFace :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ h
            ≤ (P3523T1InsertionConstruction s t).steps.length, ∀ (a : Fin (n + (3 : ℕ))), ∀ (b
            : Fin (n + (3 : ℕ))), a ≠ b → {F ∈ (P3523T1InsertionConstruction s t).faces h | a ∈
            F ∧ b ∈ F}.card = if {a, b} ∈ (P3523T1InsertionConstruction s t).boundary h then (1
            : ℕ) else if ∃ F ∈ (P3523T1InsertionConstruction s t).faces h, a ∈ F ∧ b ∈ F then
            (2 : ℕ) else (0 : ℕ)) → (
        let c := P3523T1InsertionConstruction s t
        ∀ h ≤ c.steps.length, ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), a ≠ b → {a,
            b} ∈ c.boundary h → ∀ (F : Finset (Fin (n + (3 : ℕ)))), ∀ (G : Finset (Fin (n + (3 :
            ℕ)))), F ∈ c.faces h → G ∈ c.faces h → a ∈ F → b ∈ F → a ∈ G → b ∈ G → F = G) ) := by
  classical
  intro r n q p s X K t hincidence c h hle a b hab hboundary F G hF hG haF hbF haG hbG
  have hcard := hincidence h hle a b hab
  rw [ite_eq_left hboundary] at hcard
  let S := (c.faces h).filter fun H => a ∈ H ∧ b ∈ H
  have hS : S.card = 1 := by simpa [S] using hcard
  obtain ⟨H, hH⟩ := (Finset.card_eq_one.mp hS)
  have hFm : F ∈ S := by simp [S, hF, haF, hbF]
  have hGm : G ∈ S := by simp [S, hG, haG, hbG]
  have hFU : F = H := by simpa [hH] using hFm
  have hGU : G = H := by simpa [hH] using hGm
  exact hFU.trans hGU.symm

private theorem retainedLeft :
    (by
      classical
      exact
        ∀ (n : Nat), (∀ (v : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (z : Fin (n +
            3)), v '' (({a, z} : Finset (Fin (n + 3))) : Set (Fin (n + 3))) = {v a, v z}) → (∀ (v
            : Fin (n + (3 : ℕ)) → ℝ × ℝ), Function.Injective v → ∀ (a : Fin (n + (3 : ℕ))), ∀ (d
            : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 : ℕ))), a ≠ b → a
            ≠ z → b ≠ z → ∀ (F : Finset (Fin (n + (3 : ℕ)))), ∀ (H : Finset (Fin (n + (3 : ℕ)))),
            F = {a, b, z} → insert d (F.erase b) = {a, d, z} → d ∉ H → ¬(a ∈ H ∧ b ∈ H) →
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑F : Set (Fin (n + (3 : ℕ))))) ∩
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) =
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑F : Set (Fin (n + (3 : ℕ)))) ∩
            (↑H : Set (Fin (n + (3 : ℕ)))))) → ((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑({a, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) →
                Set (ℝ × ℝ))
            (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∪ (convexHull ℝ : Set (ℝ ×
                ℝ) → Set (ℝ
            × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∧ (convexHull ℝ :
                Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull
                ℝ : Set (ℝ ×
            ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) =
                segment ℝ (v d) (v
            z) ∧ ∀ J ⊆ {v a, v b, v z}, ¬(v a ∈ J ∧ v b ∈ J) → (convexHull ℝ : Set (ℝ × ℝ) → Set
            (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ :
                Set (ℝ × ℝ)
            → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v a, v z}) ∧
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin
                (n + (3 :
            ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (J ∩ {v b, v z})) → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑(insert d (F.erase b)) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' ((↑(insert d (F.erase b)) : Set (Fin (n + (3 : ℕ)))) ∩ (↑H : Set
            (Fin (n + (3 : ℕ))))))) ) := by
  classical
  intro n imagePair v vinj a d b z hab haz hbz F H hF hleftFace hdH hnot hpair hgeo
  let J := v '' ((F : Set _) ∩ (H : Set _))
  have hJsub : J ⊆ {v a, v b, v z} := by
    intro y hy
    rcases (Set.mem_image v _ _).mp hy with ⟨x, hx, hxy⟩
    subst y
    rw [hF] at hx
    rcases hx with ⟨hxF, hxH⟩
    change x ∈ ({a, b, z} : Finset (Fin (n + 3))) at hxF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxF
    rcases hxF with ha | hb | hz
    · simp [ha]
    · simp [hb]
    · simp [hz]
  have hJnot : ¬ (v a ∈ J ∧ v b ∈ J) := by
    rintro ⟨⟨x, ⟨hxF, hxH⟩, hxa⟩, ⟨y, ⟨hyF, hyH⟩, hyb⟩⟩
    have hx : x = a := vinj hxa
    have hy : y = b := vinj hyb
    subst x
    subst y
    exact hnot ⟨hxH, hyH⟩
  have hleftRet := (hgeo.2.2 J hJsub hJnot).1
  have hleftFace' : insert d (({a, b, z} : Finset (Fin (n + 3))).erase b) =
      {a, d, z} := by simpa [hF] using hleftFace
  have hlabels : ((F : Set _) ∩ (H : Set _)) ∩
        (({a, z} : Finset (Fin (n + 3))) : Set (Fin (n + 3))) =
      (((insert d (F.erase b) : Finset (Fin (n + 3))) : Set _) ∩
        (H : Set _)) := by
    ext x
    rw [hleftFace, hF]
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, hxH⟩, hpair⟩
      rcases hpair with hxa | hxz
      · exact ⟨Or.inl hxa, hxH⟩
      · exact ⟨Or.inr (Or.inr hxz), hxH⟩
    · rintro ⟨hchild, hxH⟩
      rcases hchild with hxa | hdz
      · exact ⟨⟨Or.inl hxa, hxH⟩, Or.inl hxa⟩
      · rcases hdz with hxd | hxz
        · have hdinH : d ∈ H := by rw [hxd] at hxH; exact hxH
          exact (hdH hdinH).elim
        · exact ⟨⟨Or.inr (Or.inr hxz), hxH⟩,
            Or.inr hxz⟩
  have hJAC : J ∩ {v a, v z} =
      v '' (((F : Set _) ∩ (H : Set _)) ∩
        (({a, z} : Finset (Fin (n + 3))) : Set _)) := by
    dsimp [J]
    rw [← imagePair, ← Set.image_inter vinj]
  have hchildSub :
      convexHull Real (v '' ((insert d (F.erase b) : Finset _) : Set _)) ⊆
        convexHull Real (v '' (F : Set _)) := by
    rw [hleftFace, hF]
    rw [hgeo.1]
    exact Set.subset_union_left
  have hpairJ : convexHull Real (v '' ((F : Set _) ∩ (H : Set _))) =
      convexHull Real J := by rfl
  calc
    _ = (convexHull Real (v '' ((insert d (F.erase b) : Finset _) : Set _)) ∩
          convexHull Real (v '' (F : Set _))) ∩
        convexHull Real (v '' (H : Set _)) := by
          apply Set.ext
          intro x
          simp only [Set.mem_inter_iff]
          constructor
          · rintro ⟨hxL, hxH⟩
            exact ⟨⟨hxL, hchildSub hxL⟩, hxH⟩
          · rintro ⟨⟨hxL, _⟩, hxH⟩
            exact ⟨hxL, hxH⟩
    _ = convexHull Real (v '' ((insert d (F.erase b) : Finset _) : Set _)) ∩
        (convexHull Real (v '' ((F : Set _) ∩ (H : Set _))) ) := by
          rw [Set.inter_assoc, hpair]
    _ = convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∩
        convexHull Real J := by rw [hleftFace, hpairJ]
    _ = convexHull Real (J ∩ {v a, v z}) := hleftRet
    _ = convexHull Real (v '' (((insert d (F.erase b) : Finset _) : Set _) ∩
        (H : Set _))) := by rw [hJAC, hlabels]

private theorem retainedRight :
    (by
      classical
      exact
        ∀ (n : Nat), (∀ (v : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (z : Fin (n +
            3)), v '' (({a, z} : Finset (Fin (n + 3))) : Set (Fin (n + 3))) = {v a, v z}) → (∀ (v
            : Fin (n + (3 : ℕ)) → ℝ × ℝ), Function.Injective v → ∀ (a : Fin (n + (3 : ℕ))), ∀ (d
            : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 : ℕ))), a ≠ b → a
            ≠ z → b ≠ z → ∀ (F : Finset (Fin (n + (3 : ℕ)))), ∀ (H : Finset (Fin (n + (3 : ℕ)))),
            F = {a, b, z} → insert d (F.erase a) = {d, b, z} → d ∉ H → ¬(a ∈ H ∧ b ∈ H) →
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑F : Set (Fin (n + (3 : ℕ))))) ∩
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) =
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑F : Set (Fin (n + (3 : ℕ)))) ∩
            (↑H : Set (Fin (n + (3 : ℕ)))))) → ((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑({a, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) →
                Set (ℝ × ℝ))
            (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∪ (convexHull ℝ : Set (ℝ ×
                ℝ) → Set (ℝ
            × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∧ (convexHull ℝ :
                Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull
                ℝ : Set (ℝ ×
            ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) =
                segment ℝ (v d) (v
            z) ∧ ∀ J ⊆ {v a, v b, v z}, ¬(v a ∈ J ∧ v b ∈ J) → (convexHull ℝ : Set (ℝ × ℝ) → Set
            (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ :
                Set (ℝ × ℝ)
            → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v a, v z}) ∧
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin
                (n + (3 :
            ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (J ∩ {v b, v z})) → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑(insert d (F.erase a)) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' ((↑(insert d (F.erase a)) : Set (Fin (n + (3 : ℕ)))) ∩ (↑H : Set
            (Fin (n + (3 : ℕ))))))) ) := by
  classical
  intro n imagePair v vinj a d b z hab haz hbz F H hF hrightFace hdH hnot hpair hgeo
  let J := v '' ((F : Set _) ∩ (H : Set _))
  have hJsub : J ⊆ {v a, v b, v z} := by
    intro y hy
    rcases (Set.mem_image v _ _).mp hy with ⟨x, hx, hxy⟩
    subst y
    rw [hF] at hx
    rcases hx with ⟨hxF, _⟩
    change x ∈ ({a, b, z} : Finset (Fin (n + 3))) at hxF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxF
    rcases hxF with ha | hb | hz
    · simp [ha]
    · simp [hb]
    · simp [hz]
  have hJnot : ¬ (v a ∈ J ∧ v b ∈ J) := by
    rintro ⟨⟨x, ⟨_, hxH⟩, hxa⟩, ⟨y, ⟨_, hyH⟩, hyb⟩⟩
    have hx : x = a := vinj hxa
    have hy : y = b := vinj hyb
    subst x
    subst y
    exact hnot ⟨hxH, hyH⟩
  have hrightRet := (hgeo.2.2 J hJsub hJnot).2
  have hlabels : ((F : Set _) ∩ (H : Set _)) ∩
        (({b, z} : Finset (Fin (n + 3))) : Set (Fin (n + 3))) =
      (((insert d (F.erase a) : Finset (Fin (n + 3))) : Set _) ∩
        (H : Set _)) := by
    have hrightFace' : insert d (({a, b, z} : Finset (Fin (n + 3))).erase a) =
        {d, b, z} := by simpa [hF] using hrightFace
    ext x
    rw [hrightFace, hF]
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, hxH⟩, hpair⟩
      rcases hpair with hxb | hxz
      · exact ⟨Or.inr (Or.inl hxb), hxH⟩
      · exact ⟨Or.inr (Or.inr hxz), hxH⟩
    · rintro ⟨hchild, hxH⟩
      rcases hchild with hxd | hrem
      · have hdinH : d ∈ H := by rw [hxd] at hxH; exact hxH
        exact (hdH hdinH).elim
      · rcases hrem with hxb | hxz
        · exact ⟨⟨Or.inr (Or.inl hxb), hxH⟩, Or.inl hxb⟩
        · exact ⟨⟨Or.inr (Or.inr hxz), hxH⟩, Or.inr hxz⟩
  have hJBC : J ∩ {v b, v z} =
      v '' (((F : Set _) ∩ (H : Set _)) ∩
        (({b, z} : Finset (Fin (n + 3))) : Set _)) := by
    dsimp [J]
    rw [← imagePair, ← Set.image_inter vinj]
  have hchildSub :
      convexHull Real (v '' ((insert d (F.erase a) : Finset _) : Set _)) ⊆
        convexHull Real (v '' (F : Set _)) := by
    rw [hrightFace, hF]
    rw [hgeo.1]
    exact Set.subset_union_right
  have hpairJ : convexHull Real (v '' ((F : Set _) ∩ (H : Set _))) =
      convexHull Real J := by rfl
  calc
    _ = (convexHull Real (v '' ((insert d (F.erase a) : Finset _) : Set _)) ∩
          convexHull Real (v '' (F : Set _))) ∩
        convexHull Real (v '' (H : Set _)) := by
          apply Set.ext
          intro x
          simp only [Set.mem_inter_iff]
          constructor
          · rintro ⟨hxR, hxH⟩
            exact ⟨⟨hxR, hchildSub hxR⟩, hxH⟩
          · rintro ⟨⟨hxR, _⟩, hxH⟩
            exact ⟨hxR, hxH⟩
    _ = convexHull Real (v '' ((insert d (F.erase a) : Finset _) : Set _)) ∩
        convexHull Real (v '' ((F : Set _) ∩ (H : Set _))) := by
          rw [Set.inter_assoc, hpair]
    _ = convexHull Real (v '' ((insert d (F.erase a) : Finset _) : Set _)) ∩
        convexHull Real J := by rw [hpairJ]
    _ = convexHull Real (J ∩ {v b, v z}) := by
          rw [hrightFace]
          exact hrightRet
    _ = convexHull Real (v '' (((insert d (F.erase a) : Finset _) : Set _) ∩
        (H : Set _))) := by rw [hJBC, hlabels]

private theorem mixedPair :
    (by
      classical
      exact
        ∀ (n : Nat), (∀ (v : Fin (n + 3) → Real × Real), (Function.Injective v) → (∀ (a : Fin (n
            + 3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (z : Fin (n + 3)), (a ≠ b) → ((a ≠
            z) → ((b ≠ z) → (∀ (F : Finset (Fin (n + 3))), ∀ (H : Finset (Fin (n + 3))), (F = {a,
            b, z}) → ((insert d (F.erase b) = {a, d, z}) → ((d ∉ H) → ((¬ (a ∈ H ∧ b ∈ H)) →
            ((convexHull Real (v '' (F : Set _)) ∩ convexHull Real (v '' (H : Set _)) =
            convexHull Real (v '' ((F : Set _) ∩ (H : Set _)))) → ((convexHull Real (v '' (({a,
            b, z} : Finset (Fin (n + 3))) : Set _)) = convexHull Real (v '' (({a, d, z} : Finset
            (Fin (n + 3))) : Set _)) ∪ convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3)))
            : Set _)) ∧ convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∩
            convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3))) : Set _)) = segment Real (v
            d) (v z) ∧ (∀ J : Set (Real × Real), J ⊆ {v a, v b, v z} → ¬ (v a ∈ J ∧ v b ∈ J) →
            convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∩ convexHull Real
            J = convexHull Real (J ∩ {v a, v z}) ∧ convexHull Real (v '' (({d, b, z} : Finset
            (Fin (n + 3))) : Set _)) ∩ convexHull Real J = convexHull Real (J ∩ {v b, v z}))) →
            (convexHull Real (v '' ((insert d (F.erase b) : Finset _) : Set _)) ∩ convexHull Real
            (v '' (H : Set _)) = convexHull Real (v '' (((insert d (F.erase b) : Finset _) : Set
            _) ∩ (H : Set _)))))))))))))) → ((∀ (v : Fin (n + 3) → Real × Real),
            (Function.Injective v) → (∀ (a : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (z : Fin (n + 3)), (a ≠ b) → ((a ≠ z) → ((b ≠ z) → (∀ (F : Finset (Fin (n +
            3))), ∀ (H : Finset (Fin (n + 3))), (F = {a, b, z}) → ((insert d (F.erase a) = {d, b,
            z}) → ((d ∉ H) → ((¬ (a ∈ H ∧ b ∈ H)) → ((convexHull Real (v '' (F : Set _)) ∩
            convexHull Real (v '' (H : Set _)) = convexHull Real (v '' ((F : Set _) ∩ (H : Set
            _)))) → ((convexHull Real (v '' (({a, b, z} : Finset (Fin (n + 3))) : Set _)) =
            convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∪ convexHull Real
            (v '' (({d, b, z} : Finset (Fin (n + 3))) : Set _)) ∧ convexHull Real (v '' (({a, d,
            z} : Finset (Fin (n + 3))) : Set _)) ∩ convexHull Real (v '' (({d, b, z} : Finset
            (Fin (n + 3))) : Set _)) = segment Real (v d) (v z) ∧ (∀ J : Set (Real × Real), J ⊆
            {v a, v b, v z} → ¬ (v a ∈ J ∧ v b ∈ J) → convexHull Real (v '' (({a, d, z} : Finset
            (Fin (n + 3))) : Set _)) ∩ convexHull Real J = convexHull Real (J ∩ {v a, v z}) ∧
            convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3))) : Set _)) ∩ convexHull Real
            J = convexHull Real (J ∩ {v b, v z}))) → (convexHull Real (v '' ((insert d (F.erase
            a) : Finset _) : Set _)) ∩ convexHull Real (v '' (H : Set _)) = convexHull Real (v ''
            (((insert d (F.erase a) : Finset _) : Set _) ∩ (H : Set _)))))))))))))) → (∀ (v : Fin
            (n + (3 : ℕ)) → ℝ × ℝ), Function.Injective v → ∀ (a : Fin (n + (3 : ℕ))), ∀ (d : Fin
            (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 : ℕ))), a ≠ b → a ≠ z →
            b ≠ z → ∀ (F : Finset (Fin (n + (3 : ℕ)))), ∀ (H : Finset (Fin (n + (3 : ℕ)))), F =
            {a, b, z} → insert d (F.erase b) = {a, d, z} → insert d (F.erase a) = {d, b, z} → d ∉
            H → ¬(a ∈ H ∧ b ∈ H) → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑F : Set
            (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set
            (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑F : Set
            (Fin (n + (3 : ℕ)))) ∩ (↑H : Set (Fin (n + (3 : ℕ)))))) → ((convexHull ℝ : Set (ℝ ×
            ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) =
                (convexHull ℝ : Set
            (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∪
                (convexHull ℝ
            : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 :
                ℕ))))) ∧
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin
                (n + (3 :
            ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) :
                Set (Fin (n +
            (3 : ℕ))))) = segment ℝ (v d) (v z) ∧ ∀ J ⊆ {v a, v b, v z}, ¬(v a ∈ J ∧ v b ∈ J) →
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin
                (n + (3 :
            ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (J ∩ {v a, v z}) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) →
                Set (ℝ × ℝ))
            J = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v b, v z})) → (convexHull ℝ :
            Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑(insert d (F.erase b)) : Set (Fin (n + (3 : ℕ)))))
            ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) =
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑(insert d (F.erase b)) : Set (Fin
            (n + (3 : ℕ)))) ∩ (↑H : Set (Fin (n + (3 : ℕ)))))) ∧ (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' (↑(insert d (F.erase a)) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull
            ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ
            : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑(insert d (F.erase a)) : Set (Fin (n + (3 :
            ℕ)))) ∩ (↑H : Set (Fin (n + (3 : ℕ)))))) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            (v '' (↑H : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v
            '' (↑(insert d (F.erase b)) : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ)
            → Set (ℝ × ℝ)) (v '' ((↑H : Set (Fin (n + (3 : ℕ)))) ∩ (↑(insert d (F.erase b)) : Set
            (Fin (n + (3 : ℕ)))))) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set
            (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑(insert d
            (F.erase a)) : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            (v '' ((↑H : Set (Fin (n + (3 : ℕ)))) ∩ (↑(insert d (F.erase a)) : Set (Fin (n + (3 :
            ℕ)))))))) ) := by
  classical
  intro n retainedLeft retainedRight v vinj a d b z hab haz hbz F H hF hleftFace hrightFace hdH
      hnot hpair hgeo
  have hleft := retainedLeft v vinj a d b z hab haz hbz F H hF
    hleftFace hdH hnot hpair hgeo
  have hright := retainedRight v vinj a d b z hab haz hbz F H hF
    hrightFace hdH hnot hpair hgeo
  refine ⟨hleft, hright, ?_, ?_⟩
  · calc
      _ = convexHull Real (v '' ((insert d (F.erase b) : Finset _) : Set _)) ∩
          convexHull Real (v '' (H : Set _)) := Set.inter_comm _ _
      _ = convexHull Real (v '' (((insert d (F.erase b) : Finset _) : Set _) ∩
          (H : Set _))) := hleft
      _ = convexHull Real (v '' ((H : Set _) ∩
          ((insert d (F.erase b) : Finset _) : Set _))) := by rw [Set.inter_comm]
  · calc
      _ = convexHull Real (v '' ((insert d (F.erase a) : Finset _) : Set _)) ∩
          convexHull Real (v '' (H : Set _)) := Set.inter_comm _ _
      _ = convexHull Real (v '' (((insert d (F.erase a) : Finset _) : Set _) ∩
          (H : Set _))) := hright
      _ = convexHull Real (v '' ((H : Set _) ∩
          ((insert d (F.erase a) : Finset _) : Set _))) := by rw [Set.inter_comm]

private theorem splitFacts :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ h
            ≤ (P3523T1InsertionConstruction s t).steps.length, ∀ F ∈
            (P3523T1InsertionConstruction s t).faces h, F.card = (3 : ℕ) ∧ F ⊆
            (P3523T1InsertionConstruction s t).vertices h) → (
        let c := P3523T1InsertionConstruction s t
        (∀ {I : Type}, ∀ [DecidableEq I], ∀ {F : Finset I}, (F.card = 3) → (∀ {a : I}, ∀ {b : I},
            (a ∈ F) → ((b ∈ F) → ((a ≠ b) → (∃ z, a ≠ z ∧ b ≠ z ∧ F = {a, b, z}))))) → ((∀
            {I : Type}, ∀ {a : I}, ∀ {b : I}, ∀ {z : I}, (a ≠ b) → ((a ≠ z) → ((b ≠ z) →
            (Function.Injective ![a, b, z])))) → ((∀ {I : Type}, ∀ [DecidableEq I], ∀ (a : I), ∀
            (b : I), ∀ (z : I), Set.range ![a, b, z] = (({a, b, z} : Finset I) : Set I)) → ((∀ (a
            : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (z : Fin (n + 3)), (a ≠
            b) → ((a ≠ z) → ((b ≠ z) → (insert d (({a, b, z} : Finset (Fin (n + 3))).erase b) =
            {a, d, z} ∧ insert d (({a, b, z} : Finset (Fin (n + 3))).erase a) = {d, b, z})))) →
            ((∀ {I : Type}, ∀ {J : Type}, ∀ (v : I → J), ∀ (a : I), ∀ (b : I), ∀ (z : I), v ∘
            ![a, b, z] = ![v a, v b, v z]) → ((∀ (v : Fin (n + 3) → Real × Real), ∀ (a : Fin (n +
            3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (z : Fin (n + 3)), (a ≠ b) → ((a ≠
            z) → ((b ≠ z) → (∀ (u : Real), (0 < u ∧ u < 1) → ((v d = (1-u) • v a + u • v b) →
            ((P3381T1TriangleDeterminant ![v a, v b, v z] ≠ 0) → (convexHull Real (v '' (({a,
            b, z} : Finset (Fin (n + 3))) : Set _)) = convexHull Real (v '' (({a, d, z} : Finset
            (Fin (n + 3))) : Set _)) ∪ convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3)))
            : Set _)) ∧ convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∩
            convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3))) : Set _)) = segment Real (v
            d) (v z) ∧ (∀ J : Set (Real × Real), J ⊆ {v a, v b, v z} → ¬ (v a ∈ J ∧ v b ∈ J) →
            convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∩ convexHull Real
            J = convexHull Real (J ∩ {v a, v z}) ∧ convexHull Real (v '' (({d, b, z} : Finset
            (Fin (n + 3))) : Set _)) ∩ convexHull Real J = convexHull Real (J ∩ {v b,
            v z}))))))))) → (∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (h : ℕ), ∀ (hh : h <
            c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩;
      ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ) ∧ v e.2.1 = ((1 : ℝ) - u) • v e.1 + u • v e.2.2) → ((∀
          h ≤ c.steps.length, ∀ F ∈ c.faces h, ∀ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))),
          Function.Injective g → Set.range g = (↑F : Set (Fin (n + (3 : ℕ)))) →
          P3381T1TriangleDeterminant (v ∘ g) ≠ (0 : ℝ)) → ((((P3523T1InsertionConstruction s
          t).steps.get ⟨h, hh⟩).1 ≠ ((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.2)
          → ((h ≤ c.steps.length) → (∀ P ∈ c.faces h, e.1 ∈ P ∧ e.2.2 ∈ P → ∃ (z : Fin (n + (3 :
          ℕ))), e.1 ≠ z ∧ e.2.2 ≠ z ∧ P = {e.1, e.2.2, z} ∧ insert e.2.1 (P.erase e.2.2) = {e.1,
          e.2.1, z} ∧ insert e.2.1 (P.erase e.1) = {e.2.1, e.2.2, z} ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u
          < (1 : ℝ) ∧ v e.2.1 = ((1 : ℝ) - u) • v e.1 + u • v e.2.2 ∧ (convexHull ℝ : Set (ℝ × ℝ)
          → Set (ℝ × ℝ)) (v '' (↑({e.1, e.2.2, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) =
              (convexHull ℝ :
          Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.1, e.2.1, z} : Finset _) : Set (Fin (n + (3 :
              ℕ))))) ∪
          (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.2.1, e.2.2, z} : Finset _) : Set
              (Fin (n + (3
          : ℕ))))) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.1, e.2.1, z} : Finset
              _) : Set
          (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.2.1,
          e.2.2, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) = segment ℝ (v e.2.1) (v z) ∧ ∀ J ⊆
              {v e.1,
          v e.2.2, v z}, ¬(v e.1 ∈ J ∧ v e.2.2 ∈ J) → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
          (v '' (↑({e.1, e.2.1, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set
              (ℝ × ℝ) → Set
          (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v e.1, v z}) ∧
          (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.2.1, e.2.2, z} : Finset _) : Set
              (Fin (n + (3
          : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) →
          Set (ℝ × ℝ)) (J ∩ {v e.2.2, v z})))))))))))) ) := by
  classical
  intro r n q p s X K t hfaceShape c existsThird tripleInj tripleRange splitFinsets mapTriple
      splitGeometry v h hh e hinterp hnondeg hab hleFace P hP hhit
  have hshape := hfaceShape h (by simpa [c] using hleFace) P hP
  obtain ⟨z, haz, hbz, hPeq⟩ :=
    existsThird hshape.1 hhit.1 hhit.2 hab
  have hfin := splitFinsets e.1 e.2.1 e.2.2 z hab haz hbz
  have hdet0 := hnondeg h hleFace P hP ![e.1, e.2.2, z]
    (tripleInj hab haz hbz) (by rw [hPeq]; exact tripleRange _ _ _)
  have hdet : P3381T1TriangleDeterminant
      ![v e.1, v e.2.2, v z] ≠ 0 := by
    rw [mapTriple v e.1 e.2.2 z] at hdet0
    exact hdet0
  obtain ⟨u, hu0, hu1, hvalue⟩ := hinterp h hh
  have hgeo := splitGeometry v e.1 e.2.1 e.2.2 z hab haz hbz u
    ⟨hu0, hu1⟩ hvalue hdet
  exact ⟨z, haz, hbz, hPeq, by rw [hPeq]; exact hfin.1,
    by rw [hPeq]; exact hfin.2, u, hu0, hu1, hvalue, hgeo⟩

private theorem hda :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h) → ((e.1 ∈ c.vertices h) → (e.2.1 ≠
            e.1)) ) := by
  classical
  intro r n q p s X K t c h hh e hdV haV0 heq
  exact hdV (heq ▸ haV0)

private theorem hdb :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h) → ((e.2.2 ∈ c.vertices h) → (e.2.1 ≠
            e.2.2)) ) := by
  classical
  intro r n q p s X K t c h hh e hdV hbV0 heq
  exact hdV (heq ▸ hbV0)

private theorem hdz :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h) → (∀ (z : Fin (n + (3 : ℕ))), (z ∈
            c.vertices h) → (e.2.1 ≠ z)) ) := by
  classical
  intro r n q p s X K t c h hh e hdV z hzV0 heq
  exact hdV (heq ▸ hzV0)

private theorem siblingsPair :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).1 ≠
            ((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.2) → (∀ (z : Fin (n + (3 :
            ℕ))), (e.2.2 ≠ z) → (∀ (u : ℝ), (v e.2.1 = ((1 : ℝ) - u) • v e.1 + u • v e.2.2) →
            (((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.1, e.2.2, z} : Finset _) :
                Set (Fin (n +
            (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.1, e.2.1, z} :
                Finset _) :
            Set (Fin (n + (3 : ℕ))))) ∪ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑({e.2.1, e.2.2, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∧ (convexHull ℝ : Set (ℝ
                × ℝ) → Set
            (ℝ × ℝ)) (v '' (↑({e.1, e.2.1, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩
                (convexHull ℝ : Set (ℝ
            × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.2.1, e.2.2, z} : Finset _) : Set (Fin (n + (3 :
                ℕ))))) = segment ℝ
            (v e.2.1) (v z) ∧ ∀ J ⊆ {v e.1, v e.2.2, v z}, ¬(v e.1 ∈ J ∧ v e.2.2 ∈ J) →
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({e.1, e.2.1, z} : Finset _) : Set
                (Fin (n + (3
            : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ)
            → Set (ℝ × ℝ)) (J ∩ {v e.1, v z}) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑({e.2.1, e.2.2, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ
                × ℝ) → Set
            (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v e.2.2, v z})) → (∀ (L
            : Finset (Fin (n + (3 : ℕ)))), ∀ (R : Finset (Fin (n + (3 : ℕ)))), L = {e.1, e.2.1,
            z} → R = {e.2.1, e.2.2, z} → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑L :
            Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑R :
            Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑L :
            Set (Fin (n + (3 : ℕ)))) ∩ (↑R : Set (Fin (n + (3 : ℕ)))))))))) ) := by
  classical
  intro r n q p s X K t c v h hh e hab z hbz u hvalue hgeo L R hL hR
  have hcommon : (L : Set _) ∩ (R : Set _) =
      ({e.2.1, z} : Set (Fin (n + 3))) := by
    rw [hL, hR]
    ext x
    simp only [Set.mem_inter_iff, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hl, hr⟩
      rcases hl with ha | hrest
      · rcases hr with hd | hrest'
        · exact Or.inl hd
        · rcases hrest' with hb | hz
          · exact (hab (ha.symm.trans hb)).elim
          · exact Or.inr hz
      · rcases hrest with hd | hz
        · exact Or.inl hd
        · rcases hr with hd | hrest'
          · exact Or.inl hd
          · rcases hrest' with hb | hz'
            · exact (hbz (hb.symm.trans hz)).elim
            · exact Or.inr hz'
    · rintro (hd | hz)
      · exact ⟨Or.inr (Or.inl hd), Or.inl hd⟩
      · exact ⟨Or.inr (Or.inr hz), Or.inr (Or.inr hz)⟩
  have himage : v '' ({e.2.1, z} : Set (Fin (n + 3))) =
      {v e.2.1, v z} := by
    ext x
    simp [or_comm]
  calc
    _ = segment Real (v e.2.1) (v z) := by
      rw [hL, hR]
      simpa [hvalue] using hgeo.2.1
    _ = convexHull Real (v '' ((L : Set _) ∩ (R : Set _))) := by
      rw [hcommon, himage]
      exact (convexHull_pair (v e.2.1) (v z)).symm

private theorem hnotGactual :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (G : Finset (Fin (n + (3 : ℕ)))), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (G₀ : Finset (Fin (n + (3 : ℕ)))), (¬(e.1 ∈ G₀ ∧ e.2.2 ∈ G₀)) → ((G = G₀) → (¬ (e.1 ∈ G
            ∧ e.2.2 ∈ G))) ) := by
  classical
  intro r n q p s X K t c h G hh e G₀ hnotG hGsame hit
  exact hnotG ⟨hGsame ▸ hit.1, hGsame ▸ hit.2⟩

private theorem hdG :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h) → (∀ (G₀ : Finset (Fin (n + (3 :
            ℕ)))), (G₀ ⊆ (P3523T1InsertionConstruction s t).vertices h) → (e.2.1 ∉ G₀)) ) := by
  classical
  intro r n q p s X K t c h hh e hdV G₀ hG₀subset hd
  exact hdV (hG₀subset hd)

private theorem hdGactual :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (G : Finset (Fin (n + (3 : ℕ)))), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (G₀ : Finset (Fin (n + (3 : ℕ)))), (G = G₀) → ((e.2.1 ∉ G₀) → (e.2.1 ∉ G)) ) := by
  classical
  intro r n q p s X K t c h G hh e G₀ hGsame hdG hd
  exact hdG (hGsame ▸ hd)

private theorem hnotFactual :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (F : Finset (Fin (n + (3 : ℕ)))), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (F₀ : Finset (Fin (n + (3 : ℕ)))), (¬(e.1 ∈ F₀ ∧ e.2.2 ∈ F₀)) → ((F = F₀) → (¬ (e.1 ∈ F
            ∧ e.2.2 ∈ F))) ) := by
  classical
  intro r n q p s X K t c h F hh e F₀ hnotF hFsame hit
  exact hnotF ⟨hFsame ▸ hit.1, hFsame ▸ hit.2⟩

private theorem hdF :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        (((P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩).2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h) → (∀ (F₀ : Finset (Fin (n + (3 :
            ℕ)))), (F₀ ⊆ (P3523T1InsertionConstruction s t).vertices h) → (e.2.1 ∉ F₀)) ) := by
  classical
  intro r n q p s X K t c h hh e hdV F₀ hF₀subset hd
  exact hdV (hF₀subset hd)

private theorem hdFactual :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (F : Finset (Fin (n + (3 : ℕ)))), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∀ (F₀ : Finset (Fin (n + (3 : ℕ)))), (F = F₀) → ((e.2.1 ∉ F₀) → (e.2.1 ∉ F)) ) := by
  classical
  intro r n q p s X K t c h F hh e F₀ hFsame hdF hd
  exact hdF (hFsame ▸ hd)

private theorem enumUnion :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
            ((Set.range fun (k : Fin ((P3523T1InsertionConstruction s t).faces
            (P3523T1InsertionConstruction s t).steps.length).card) => Set.range
            (P3523T1FaceEnumeration ((P3523T1InsertionConstruction s t).faces
            (P3523T1InsertionConstruction s t).steps.length) k)) = {J : Set (Fin (n + (3 : ℕ)))
            | ∃ F ∈ (P3523T1InsertionConstruction s t).faces (P3523T1InsertionConstruction s
            t).steps.length, (↑F : Set (Fin (n + (3 : ℕ)))) = J}) → (
        let c := P3523T1InsertionConstruction s t
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), faceUnion v (c.faces c.steps.length) = ⋃ (k : Fin
            (c.faces c.steps.length).card), (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range
            (v ∘ f k))) ) := by
  classical
  intro r n q p s X K t hfaceRange c f faceUnion v
  have imageRange (k : Fin (c.faces c.steps.length).card) :
      v '' Set.range (f k) = Set.range (v ∘ f k) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨f k i, ⟨i, rfl⟩, hi⟩
  ext x
  simp only [faceUnion, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · rintro ⟨F, hF, hx⟩
    have hFmember : (F : Set (Fin (n + 3))) ∈
        Set.range (fun k : Fin (c.faces c.steps.length).card => Set.range (f k)) := by
      rw [hfaceRange]
      exact ⟨F, hF, rfl⟩
    rcases hFmember with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk] at hx
    simpa [imageRange] using hx
  · rintro ⟨k, hx⟩
    have hKmember : Set.range (f k) ∈
        {J : Set (Fin (n + 3)) |
          ∃ F ∈ c.faces c.steps.length, (F : Set (Fin (n + 3))) = J} := by
      rw [← hfaceRange]
      exact Set.mem_range_self k
    rcases hKmember with ⟨F, hF, hEq⟩
    refine ⟨F, hF, ?_⟩
    rw [hEq]
    simpa [imageRange] using hx

private theorem hsourceCoverage :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        (∀ (v : Fin (n + 3) → Real × Real), faceUnion v (c.faces c.steps.length) = ⋃ k,
            convexHull Real (Set.range (v ∘ f k))) → ((∀ h ≤ c.steps.length, faceUnion p.vertex
            (c.faces h) = X) → (X = ⋃ k, convexHull Real (Set.range (p.vertex ∘ f k)))) ) := by
  classical
  intro r n q p s X K t c f faceUnion enumUnion hsourceCoverState
  calc
    X = faceUnion p.vertex (c.faces c.steps.length) :=
      (hsourceCoverState c.steps.length le_rfl).symm
    _ = ⋃ k, convexHull Real (Set.range (p.vertex ∘ f k)) := enumUnion p.vertex

private theorem htargetCoverage :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        (∀ (v : Fin (n + 3) → Real × Real), faceUnion v (c.faces c.steps.length) = ⋃ k,
            convexHull Real (Set.range (v ∘ f k))) → ((∀ h ≤ c.steps.length, faceUnion
            (P3523T1InterpolatedTarget s t) (c.faces h) = K) → (K = ⋃ k, convexHull Real
            (Set.range (P3523T1InterpolatedTarget s t ∘ f k)))) ) := by
  classical
  intro r n q p s X K t c f faceUnion enumUnion htargetCoverState
  calc
    K = faceUnion (P3523T1InterpolatedTarget s t) (c.faces c.steps.length) :=
      (htargetCoverState c.steps.length le_rfl).symm
    _ = ⋃ k,
      convexHull Real (Set.range (P3523T1InterpolatedTarget s t ∘ f k)) :=
        enumUnion (P3523T1InterpolatedTarget s t)

private theorem sourceInitialPair :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (c.faces 0 = Finset.univ.image (fun k : Fin t.count => Finset.univ.image (s.start ∘
            t.face k))) → ((∀ (k : Fin t.count), p.vertex '' ((Finset.univ.image (s.start ∘
            t.face k) : Finset (Fin (n + 3))) : Set (Fin (n + 3))) = Set.range (q.vertex ∘ t.face
            k)) → ((∀ (i : Fin t.count), ∀ (j : Fin t.count), p.vertex '' (((Finset.univ.image
            (s.start ∘ t.face i) : Finset (Fin (n + 3))) : Set _) ∩ ((Finset.univ.image (s.start
            ∘ t.face j) : Finset (Fin (n + 3))) : Set _)) = q.vertex '' (Set.range (t.face i) ∩
            Set.range (t.face j))) → (∀ F ∈ c.faces 0, ∀ G ∈ c.faces 0, convexHull Real (p.vertex
            '' (F : Set _)) ∩ convexHull Real (p.vertex '' (G : Set _)) = convexHull Real
            (p.vertex '' ((F : Set _) ∩ (G : Set _)))))) ) := by
  classical
  intro r n q p s X K t c hfaces0 sourceStartImage sourceStartCommon F hF G hG
  rw [hfaces0] at hF hG
  obtain ⟨i, -, hFi⟩ := Finset.mem_image.mp hF
  obtain ⟨j, -, hGj⟩ := Finset.mem_image.mp hG
  subst F
  subst G
  rw [sourceStartImage i, sourceStartImage j, sourceStartCommon i j]
  exact t.source_intersection i j

private theorem targetInitialPair :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (c.faces 0 = Finset.univ.image (fun k : Fin t.count => Finset.univ.image (s.start ∘
            t.face k))) → ((∀ (k : Fin t.count), (P3523T1InterpolatedTarget s t) ''
            ((Finset.univ.image (s.start ∘ t.face k) : Finset (Fin (n + 3))) : Set (Fin (n + 3)))
            = Set.range (t.target ∘ t.face k)) → ((∀ (i : Fin t.count), ∀ (j : Fin t.count),
            P3523T1InterpolatedTarget s t '' (((Finset.univ.image (s.start ∘ t.face i) : Finset
            (Fin (n + 3))) : Set _) ∩ ((Finset.univ.image (s.start ∘ t.face j) : Finset (Fin (n +
            3))) : Set _)) = t.target '' (Set.range (t.face i) ∩ Set.range (t.face j))) → (∀ F ∈
            c.faces 0, ∀ G ∈ c.faces 0, convexHull Real ((P3523T1InterpolatedTarget s t) '' (F
            : Set _)) ∩ convexHull Real ((P3523T1InterpolatedTarget s t) '' (G : Set _)) =
            convexHull Real ((P3523T1InterpolatedTarget s t) '' ((F : Set _) ∩ (G : Set _))))))
            ) := by
  classical
  intro r n q p s X K t c hfaces0 targetStartImage targetStartCommon F hF G hG
  rw [hfaces0] at hF hG
  obtain ⟨i, -, hFi⟩ := Finset.mem_image.mp hF
  obtain ⟨j, -, hGj⟩ := Finset.mem_image.mp hG
  subst F
  subst G
  rw [targetStartImage i, targetStartImage j, targetStartCommon i j]
  exact t.target_intersection i j

private theorem imageRangeAt1467 :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        ∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (k : Fin (c.faces c.steps.length).card), v ''
            Set.range (f k) = Set.range (v ∘ f k) ) := by
  classical
  intro r n q p s X K t c f v k
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, hi⟩
    exact ⟨f k i, ⟨i, rfl⟩, hi⟩

private theorem hsourcePairs :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        (∀ (k : Fin (c.faces c.steps.length).card), ∃ F ∈ c.faces c.steps.length, Set.range (f k)
            = (F : Set _)) → ((∀ h ≤ c.steps.length, ∀ F ∈ c.faces h, ∀ G ∈ c.faces h, convexHull
            Real (p.vertex '' (F : Set _)) ∩ convexHull Real (p.vertex '' (G : Set _)) =
            convexHull Real (p.vertex '' ((F : Set _) ∩ (G : Set _)))) → ((∀ (v : Fin (n + 3) →
            Real × Real), ∀ (k : Fin (c.faces c.steps.length).card), v '' Set.range (f k) =
            Set.range (v ∘ f k)) → (∀ k l : Fin (c.faces c.steps.length).card, convexHull Real
            (Set.range (p.vertex ∘ f k)) ∩ convexHull Real (Set.range (p.vertex ∘ f l)) =
            convexHull Real (p.vertex '' (Set.range (f k) ∩ Set.range (f l)))))) ) := by
  classical
  intro r n q p s X K t c f terminalFace sourcePairState imageRange k l
  obtain ⟨F, hF, hFk⟩ := terminalFace k
  obtain ⟨G, hG, hGl⟩ := terminalFace l
  have hpair := sourcePairState c.steps.length le_rfl F hF G hG
  rw [← hFk, ← hGl] at hpair
  simpa only [imageRange] using hpair

private theorem htargetPairs :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let f := P3523T1FaceEnumeration (c.faces c.steps.length)
        (∀ (k : Fin (c.faces c.steps.length).card), ∃ F ∈ c.faces c.steps.length, Set.range (f k)
            = (F : Set _)) → ((∀ h ≤ c.steps.length, ∀ F ∈ c.faces h, ∀ G ∈ c.faces h, convexHull
            Real ((P3523T1InterpolatedTarget s t) '' (F : Set _)) ∩ convexHull Real
            ((P3523T1InterpolatedTarget s t) '' (G : Set _)) = convexHull Real
            ((P3523T1InterpolatedTarget s t) '' ((F : Set _) ∩ (G : Set _)))) → ((∀ (v : Fin (n
            + 3) → Real × Real), ∀ (k : Fin (c.faces c.steps.length).card), v '' Set.range (f k)
            = Set.range (v ∘ f k)) → (∀ k l : Fin (c.faces c.steps.length).card, convexHull Real
            (Set.range (P3523T1InterpolatedTarget s t ∘ f k)) ∩ convexHull Real (Set.range
            (P3523T1InterpolatedTarget s t ∘ f l)) = convexHull Real
            ((P3523T1InterpolatedTarget s t) '' (Set.range (f k) ∩ Set.range (f l)))))) ) := by
  classical
  intro r n q p s X K t c f terminalFace targetPairState imageRange k l
  obtain ⟨F, hF, hFk⟩ := terminalFace k
  obtain ⟨G, hG, hGl⟩ := terminalFace l
  have hpair := targetPairState c.steps.length le_rfl F hF G hG
  rw [← hFk, ← hGl] at hpair
  simpa only [imageRange] using hpair

end FacialInsertionGeometry

namespace InsertionAssembly

private theorem coverState :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀
            {I : Type}, ∀ [inst : DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d :
            I), ∀ (b : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs,
            if a ∈ F ∧ b ∈ F then G = insert d (F.erase b) ∨ G = insert d (F.erase a) else G = F)
            → ((∀ h ≤ (P3523T1InsertionConstruction s t).steps.length, ∀ F ∈
            (P3523T1InsertionConstruction s t).faces h, F.card = (3 : ℕ) ∧ F ⊆
            (P3523T1InsertionConstruction s t).vertices h) → ((∀ (h : ℕ), ∀ (hh : h <
            (P3523T1InsertionConstruction s t).steps.length),
        let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2} ∈
            (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 :
            ℝ) ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
            P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s
            t e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → (
        let c := P3523T1InsertionConstruction s t
        (∀ {I : Type}, ∀ [inst : DecidableEq I], ∀ {F : Finset I}, F.card = (3 : ℕ) → ∀ {a : I},
            ∀ {b : I}, a ∈ F → b ∈ F → a ≠ b → ∃ (z : I), a ≠ z ∧ b ≠ z ∧ F = {a, b, z}) → ((∀
            {I : Type}, ∀ {a : I}, ∀ {b : I}, ∀ {z : I}, (a ≠ b) → ((a ≠ z) → ((b ≠ z) →
            (Function.Injective ![a, b, z])))) → ((∀ {I : Type}, ∀ [DecidableEq I], ∀ (a : I), ∀
            (b : I), ∀ (z : I), Set.range ![a, b, z] = (({a, b, z} : Finset I) : Set I)) → ((∀
            {I : Type}, ∀ {J : Type}, ∀ (v : I → J), ∀ (a : I), ∀ (b : I), ∀ (z : I), v ∘ ![a, b,
            z] = ![v a, v b, v z]) → (
        let faceUnion (v : Fin (n + 3) → Real × Real)
            (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
          ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
            convexHull Real (v '' (F : Set (Fin (n + 3))))
        (∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (a : Fin (n + (3 : ℕ))), ∀ (d : Fin (n + (3 : ℕ))),
            ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 : ℕ))), a ≠ b → a ≠ z → b ≠ z → ∀ (u :
            ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ) → v d = ((1 : ℝ) - u) • v a + u • v b →
            P3381T1TriangleDeterminant ![v a, v b, v z] ≠ (0 : ℝ) → (convexHull ℝ : Set (ℝ × ℝ)
            → Set (ℝ × ℝ)) (v '' (↑({a, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) =
                (convexHull ℝ : Set (ℝ
            × ℝ) → Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∪
                (convexHull ℝ :
            Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 :
                ℕ)))))) → (∀ (v :
            Fin (n + (3 : ℕ)) → ℝ × ℝ), (∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩;
          ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ) ∧ v e.2.1 = ((1 : ℝ) - u) • v e.1 + u • v e.2.2) →
        (∀ h ≤ c.steps.length,
            ∀ F ∈ c.faces h,
              ∀ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))), Function.Injective g →
                  Set.range g = (↑F : Set (Fin (n + (3 : ℕ)))) → P3381T1TriangleDeterminant (v
                      ∘ g) ≠ (0 : ℝ)) →
          ∀ (Y : Set (ℝ × ℝ)), faceUnion v (c.faces (0 : ℕ)) = Y → ∀ h ≤ c.steps.length,
              faceUnion v (c.faces h) = Y)))))))) ) := by
  classical
  intro r n q p s X K t split_mem hfaceShape hstep c existsThird tripleInj tripleRange mapTriple
      faceUnion splitHull v hinterp hnondeg Y hbase h
  induction h with
  | zero =>
      intro _
      exact hbase
  | succ h ih =>
      intro hle
      have hh : h < c.steps.length := by omega
      let e := c.steps.get ⟨h, hh⟩
      rcases hstep h hh with ⟨hab, haV, hbV, hdV, _, _⟩
      have hfacesRec : c.faces (h + 1) =
          P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2 :=
              FacialInsertionGeometry.hfacesRecAt698 r n q p s X K t h hh
      rw [hfacesRec]
      have hold : faceUnion v (c.faces h) = Y := ih (by omega)
      ext x
      simp only [faceUnion, Set.mem_iUnion, Finset.mem_coe]
      constructor
      · rintro ⟨G, hG, hxG⟩
        obtain ⟨F, hF, hbranch⟩ :=
          (split_mem (c.faces h) e.1 e.2.1 e.2.2 G).mp hG
        by_cases hhit : e.1 ∈ F ∧ e.2.2 ∈ F
        · have hchildren : G = insert e.2.1 (F.erase e.2.2) ∨
              G = insert e.2.1 (F.erase e.1) := FacialInsertionGeometry.hchildrenAt721 r n q p
                  s X K t h hh G F hbranch hhit
          have hleFace : h ≤ c.steps.length := by omega
          have hshape := hfaceShape h (by simpa [c] using hleFace) F hF
          obtain ⟨z, haz, hbz, hFeq⟩ :=
            existsThird hshape.1 hhit.1 hhit.2 hab
          have hleftFace : insert e.2.1 (F.erase e.2.2) =
              ({e.1, e.2.1, z} : Finset (Fin (n + 3))) :=
                  FacialInsertionGeometry.hleftFaceAt728 r n q p s X K t h hh hab F z hbz hFeq
          have hrightFace : insert e.2.1 (F.erase e.1) =
              ({e.2.1, e.2.2, z} : Finset (Fin (n + 3))) :=
                  FacialInsertionGeometry.hrightFaceAt744 r n q p s X K t h hh hab F z haz hFeq
          have hdet := hnondeg h hleFace F hF ![e.1, e.2.2, z]
            (tripleInj hab haz hbz) (by rw [hFeq]; exact tripleRange _ _ _)
          have hdet' := FacialInsertionGeometry.hdet'At762 r n q p s X K t mapTriple v h hh z hdet
          obtain ⟨u, hu0, hu1, hvalue⟩ := hinterp h hh
          have hgeo := splitHull v e.1 e.2.1 e.2.2 z hab haz hbz u
            ⟨hu0, hu1⟩ hvalue hdet'
          have hxold : x ∈ faceUnion v (c.faces h) := FacialInsertionGeometry.hxoldAt785 r n q
              p s X K t F v h x hF (FacialInsertionGeometry.hxParent r n q p s X K t v h hh x G
                  hxG F hchildren z hFeq hleftFace hrightFace hgeo)
          rw [hold] at hxold
          exact hxold
        · have hG' : G = F := by
            simpa only [hhit, ite_false] using hbranch
          subst G
          have hxold : x ∈ faceUnion v (c.faces h) := FacialInsertionGeometry.hxoldAt793 r n q
              p s X K t F v h x hF hxG
          rw [hold] at hxold
          exact hxold
      · intro hx
        have hxold : x ∈ faceUnion v (c.faces h) := by rw [hold]; exact hx
        have hx := hxold
        simp only [faceUnion, Set.mem_iUnion, Finset.mem_coe] at hx ⊢
        obtain ⟨F, hF, hxF⟩ := hx
        by_cases hhit : e.1 ∈ F ∧ e.2.2 ∈ F
        · have hchildren : insert e.2.1 (F.erase e.2.2) ∈
                P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2 ∧
              insert e.2.1 (F.erase e.1) ∈
                P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2 :=
                    FacialInsertionGeometry.hchildrenAt804 r n q p s X K t split_mem h hh F hF
                    hhit
          have hleFace : h ≤ c.steps.length := by omega
          have hshape := hfaceShape h (by simpa [c] using hleFace) F hF
          obtain ⟨z, haz, hbz, hFeq⟩ :=
            existsThird hshape.1 hhit.1 hhit.2 hab
          have hleftFace : insert e.2.1 (F.erase e.2.2) =
              ({e.1, e.2.1, z} : Finset (Fin (n + 3))) :=
                  FacialInsertionGeometry.hleftFaceAt728 r n q p s X K t h hh hab F z hbz hFeq
          have hrightFace : insert e.2.1 (F.erase e.1) =
              ({e.2.1, e.2.2, z} : Finset (Fin (n + 3))) :=
                  FacialInsertionGeometry.hrightFaceAt744 r n q p s X K t h hh hab F z haz hFeq
          have hdet := hnondeg h hleFace F hF ![e.1, e.2.2, z]
            (tripleInj hab haz hbz) (by rw [hFeq]; exact tripleRange _ _ _)
          have hdet' := FacialInsertionGeometry.hdet'At762 r n q p s X K t mapTriple v h hh z hdet
          obtain ⟨u, hu0, hu1, hvalue⟩ := hinterp h hh
          have hgeo := splitHull v e.1 e.2.1 e.2.2 z hab haz hbz u
            ⟨hu0, hu1⟩ hvalue hdet'
          have hxSplit : x ∈ convexHull Real (v ''
              (({e.1, e.2.1, z} : Finset (Fin (n + 3))) : Set _)) ∪
              convexHull Real (v ''
              (({e.2.1, e.2.2, z} : Finset (Fin (n + 3))) : Set _)) :=
                  FacialInsertionGeometry.hxSplit r n q p s X K t v h hh x F hxF z hFeq hgeo
          simp only [Set.mem_union] at hxSplit
          rcases hxSplit with hleft | hright
          · refine ⟨insert e.2.1 (F.erase e.2.2), hchildren.1, ?_⟩
            rw [hleftFace]
            exact hleft
          · refine ⟨insert e.2.1 (F.erase e.1), hchildren.2, ?_⟩
            rw [hrightFace]
            exact hright
        · have hunchanged : F ∈ P3523T1BoundaryFaceSplit
              (c.faces h) e.1 e.2.1 e.2.2 := FacialInsertionGeometry.hunchangedAt874 r n q p s
                  X K t split_mem h hh F hF hhit
          exact ⟨F, hunchanged, hxF⟩

private theorem pairState :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀
            {I : Type}, ∀ [inst : DecidableEq I], ∀ (fs : Finset (Finset I)), ∀ (a : I), ∀ (d :
            I), ∀ (b : I), ∀ (G : Finset I), G ∈ P3523T1BoundaryFaceSplit fs a d b ↔ ∃ F ∈ fs,
            a ∈ F ∧ b ∈ F ∧ (G = insert d (F.erase b) ∨ G = insert d (F.erase a)) ∨ ¬(a ∈ F ∧ b ∈
            F) ∧ G = F) → ((∀ {I : Type}, ∀ [DecidableEq I], ∀ {fs : Finset (Finset I)}, ∀
            {F : Finset I}, ∀ {G : Finset I}, (F = G) → ((G ∈ fs) → (F ∈ fs))) → ((∀ h ≤
            (P3523T1InsertionConstruction s t).steps.length, ∀ F ∈
            (P3523T1InsertionConstruction s t).faces h, F.card = (3 : ℕ) ∧ F ⊆
            (P3523T1InsertionConstruction s t).vertices h) → ((∀ h ≤
            (P3523T1InsertionConstruction s t).steps.length, ∀ (a : Fin (n + (3 : ℕ))), ∀ (b :
            Fin (n + (3 : ℕ))), a ≠ b → {F ∈ (P3523T1InsertionConstruction s t).faces h | a ∈ F
            ∧ b ∈ F}.card = if {a, b} ∈ (P3523T1InsertionConstruction s t).boundary h then (1 :
            ℕ) else if ∃ F ∈ (P3523T1InsertionConstruction s t).faces h, a ∈ F ∧ b ∈ F then (2
            : ℕ) else (0 : ℕ)) → ((∀ (h : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s
            t).steps.length),
        let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈
            (P3523T1InsertionConstruction s t).vertices h ∧ e.2.1 ∉
            (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2} ∈
            (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 :
            ℝ) ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
            P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s
            t e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → (
        let c := P3523T1InsertionConstruction s t
        (∀ {I : Type}, ∀ [inst : DecidableEq I], ∀ {F : Finset I}, F.card = (3 : ℕ) → ∀ {a : I},
            ∀ {b : I}, a ∈ F → b ∈ F → a ≠ b → ∃ (z : I), a ≠ z ∧ b ≠ z ∧ F = {a, b, z}) → ((∀
            {I : Type}, ∀ {a : I}, ∀ {b : I}, ∀ {z : I}, (a ≠ b) → ((a ≠ z) → ((b ≠ z) →
            (Function.Injective ![a, b, z])))) → ((∀ {I : Type}, ∀ [DecidableEq I], ∀ (a : I), ∀
            (b : I), ∀ (z : I), Set.range ![a, b, z] = (({a, b, z} : Finset I) : Set I)) → ((∀
            {I : Type}, ∀ {J : Type}, ∀ (v : I → J), ∀ (a : I), ∀ (b : I), ∀ (z : I), v ∘ ![a, b,
            z] = ![v a, v b, v z]) → ((∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ), ∀ (a : Fin (n + (3 :
            ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 : ℕ))), v '' (↑({a, b, z} :
                Finset _) : Set
            (Fin (n + (3 : ℕ)))) = {v a, v b, v z}) → ((∀ (v : Fin (n + (3 : ℕ)) → ℝ × ℝ),
            Function.Injective v → ∀ (a : Fin (n + (3 : ℕ))), ∀ (d : Fin (n + (3 : ℕ))), ∀ (b :
            Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 : ℕ))), a ≠ b → a ≠ z → b ≠ z → ∀ (F : Finset
            (Fin (n + (3 : ℕ)))), ∀ (H : Finset (Fin (n + (3 : ℕ)))), F = {a, b, z} → insert d
            (F.erase b) = {a, d, z} → insert d (F.erase a) = {d, b, z} → d ∉ H → ¬(a ∈ H ∧ b ∈ H)
            → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑F : Set (Fin (n + (3 : ℕ))))) ∩
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) =
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑F : Set (Fin (n + (3 : ℕ)))) ∩
            (↑H : Set (Fin (n + (3 : ℕ)))))) → ((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑({a, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) →
                Set (ℝ × ℝ))
            (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∪ (convexHull ℝ : Set (ℝ ×
                ℝ) → Set (ℝ
            × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∧ (convexHull ℝ :
                Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull
                ℝ : Set (ℝ ×
            ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) =
                segment ℝ (v d) (v
            z) ∧ ∀ J ⊆ {v a, v b, v z}, ¬(v a ∈ J ∧ v b ∈ J) → (convexHull ℝ : Set (ℝ × ℝ) → Set
            (ℝ × ℝ)) (v '' (↑({a, d, z} : Finset _) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ :
                Set (ℝ × ℝ)
            → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (J ∩ {v a, v z}) ∧
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑({d, b, z} : Finset _) : Set (Fin
                (n + (3 :
            ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) J = (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (J ∩ {v b, v z})) → (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v ''
            (↑(insert d (F.erase b)) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (v '' ((↑(insert d (F.erase b)) : Set (Fin (n + (3 : ℕ)))) ∩ (↑H : Set
            (Fin (n + (3 : ℕ)))))) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑(insert d
            (F.erase a)) : Set (Fin (n + (3 : ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            (v '' (↑H : Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v
            '' ((↑(insert d (F.erase a)) : Set (Fin (n + (3 : ℕ)))) ∩ (↑H : Set (Fin (n + (3 :
            ℕ)))))) ∧ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 :
            ℕ))))) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑(insert d (F.erase b)) :
            Set (Fin (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑H :
            Set (Fin (n + (3 : ℕ)))) ∩ (↑(insert d (F.erase b)) : Set (Fin (n + (3 : ℕ)))))) ∧
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑H : Set (Fin (n + (3 : ℕ))))) ∩
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑(insert d (F.erase a)) : Set (Fin
            (n + (3 : ℕ))))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' ((↑H : Set (Fin
            (n + (3 : ℕ)))) ∩ (↑(insert d (F.erase a)) : Set (Fin (n + (3 : ℕ))))))) → (∀ (v :
            Fin (n + (3 : ℕ)) → ℝ × ℝ), Function.Injective v →
        (∀ (h : ℕ), ∀ (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩;
            ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ) ∧ v e.2.1 = ((1 : ℝ) - u) • v e.1 + u • v e.2.2) →
          (∀ h ≤ c.steps.length,
              ∀ F ∈ c.faces h,
                ∀ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))), Function.Injective g →
                    Set.range g = (↑F : Set (Fin (n + (3 : ℕ)))) → P3381T1TriangleDeterminant
                        (v ∘ g) ≠ (0 : ℝ)) →
            (∀ F ∈ c.faces (0 : ℕ),
                ∀ G ∈ c.faces (0 : ℕ),
                  (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑F : Set (Fin (n + (3 : ℕ))))) ∩
                      (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑G : Set (Fin (n + (3 :
                          ℕ))))) =
                    (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
                      (v '' ((↑F : Set (Fin (n + (3 : ℕ)))) ∩ (↑G : Set (Fin (n + (3 : ℕ))))))) →
              ∀ h ≤ c.steps.length,
                ∀ F ∈ c.faces h,
                  ∀ G ∈ c.faces h,
                    (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑F : Set (Fin (n + (3 :
                        ℕ))))) ∩
                        (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (v '' (↑G : Set (Fin (n + (3 :
                            ℕ))))) =
                      (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
                        (v '' ((↑F : Set (Fin (n + (3 : ℕ)))) ∩ (↑G : Set (Fin (n + (3 :
                            ℕ))))))))))))))))) ) := by
  classical
  intro r n q p s X K t split_mem_cases faceMemTransport hfaceShape hincidence hstep c
      existsThird tripleInj tripleRange mapTriple imageTriple mixedPair v vinj hinterp hnondeg
      hinit h
  induction h with
  | zero =>
      intro _ F hF G hG
      exact hinit F hF G hG
  | succ h ih =>
      intro hle F hF G hG
      have hh : h < c.steps.length := by omega
      let e := c.steps.get ⟨h, hh⟩
      rcases hstep h hh with ⟨hab, haV, hbV, hdV, hboundary, _⟩
      have hfacesRec : c.faces (h + 1) =
          P3523T1BoundaryFaceSplit (c.faces h) e.1 e.2.1 e.2.2 :=
              FacialInsertionGeometry.hfacesRecAt698 r n q p s X K t h hh
      rw [hfacesRec] at hF hG
      obtain ⟨F₀, hF₀, hbranchF⟩ :=
        (split_mem_cases (c.faces h) e.1 e.2.1 e.2.2 F).mp hF
      obtain ⟨G₀, hG₀, hbranchG⟩ :=
        (split_mem_cases (c.faces h) e.1 e.2.1 e.2.2 G).mp hG
      have hleFace : h ≤ c.steps.length := by omega
      have hshapeF₀ := hfaceShape h (by simpa [c] using hleFace) F₀ hF₀
      have hshapeG₀ := hfaceShape h (by simpa [c] using hleFace) G₀ hG₀
      rcases hshapeF₀ with ⟨_, hF₀subset⟩
      rcases hshapeG₀ with ⟨_, hG₀subset⟩
      have splitFacts (P : Finset (Fin (n + 3))) (hP : P ∈ c.faces h)
          (hhit : e.1 ∈ P ∧ e.2.2 ∈ P) := FacialInsertionGeometry.splitFacts r n q p s X K t
              hfaceShape existsThird tripleInj tripleRange
                  (FacialInsertionGeometry.splitFinsets n) mapTriple
                  (FacialInsertionGeometry.splitGeometry n imageTriple)
              v h hh hinterp hnondeg hab hleFace P hP hhit
      rcases hbranchF with ⟨haF, hbF, hchildrenF⟩ | ⟨hnotF, hFsame⟩
      · have hhitF : e.1 ∈ F₀ ∧ e.2.2 ∈ F₀ := ⟨haF, hbF⟩
        rcases hbranchG with ⟨haG, hbG, hchildrenG⟩ | ⟨hnotG, hGsame⟩
        · have hhitG : e.1 ∈ G₀ ∧ e.2.2 ∈ G₀ := ⟨haG, hbG⟩
          obtain ⟨z, haz, hbz, hFeq, hleftFace, hrightFace,
              u, hu0, hu1, hvalue, hgeo⟩ := splitFacts F₀ hF₀ hhitF
          have hFG : F₀ = G₀ := (FacialInsertionGeometry.uniqueEdgeFace r n q p s X K t
              hincidence) h hleFace
            e.1 e.2.2 hab hboundary F₀ G₀ hF₀ hG₀
            hhitF.1 hhitF.2 hhitG.1 hhitG.2
          subst G₀
          have haV0 : e.1 ∈ c.vertices h := hF₀subset haF
          have hbV0 : e.2.2 ∈ c.vertices h := hF₀subset hbF
          have hzV0 : z ∈ c.vertices h := hF₀subset (by rw [hFeq]; simp)
          have hda := FacialInsertionGeometry.hda r n q p s X K t h hh hdV haV0
          have hdb := FacialInsertionGeometry.hdb r n q p s X K t h hh hdV hbV0
          have hdz := FacialInsertionGeometry.hdz r n q p s X K t h hh hdV z hzV0
          have siblingsPair (L R : Finset (Fin (n + 3)))
              (hL : L = {e.1, e.2.1, z})
              (hR : R = {e.2.1, e.2.2, z}) := FacialInsertionGeometry.siblingsPair r n q p s X
                  K t v h hh hab z hbz u hvalue hgeo L R hL hR
          rcases hchildrenF with hFL | hFR
          · rcases hchildrenG with hGL | hGR
            · subst F
              subst G
              simp only [Set.inter_self]
            · subst F
              subst G
              rw [hleftFace, hrightFace]
              exact siblingsPair ({e.1, e.2.1, z})
                ({e.2.1, e.2.2, z}) rfl rfl
          · rcases hchildrenG with hGL | hGR
            · subst F
              subst G
              rw [hrightFace, hleftFace]
              have hrev := siblingsPair
                ({e.1, e.2.1, z}) ({e.2.1, e.2.2, z}) rfl rfl
              simpa only [Set.inter_comm] using hrev
            · subst F
              subst G
              simp only [Set.inter_self]
        · have hGparent : G ∈ c.faces h := by
            exact faceMemTransport hGsame hG₀
          have hparentG := ih hleFace F₀ hF₀ G hGparent
          obtain ⟨z, haz, hbz, hFeq, hleftFace, hrightFace,
              u, hu0, hu1, hvalue, hgeo⟩ := splitFacts F₀ hF₀ hhitF
          have hmixed := mixedPair v vinj e.1 e.2.1 e.2.2 z
            hab haz hbz F₀ G hFeq hleftFace hrightFace (FacialInsertionGeometry.hdGactual r n q
                p s X K t h G hh G₀ hGsame (FacialInsertionGeometry.hdG r n q p s X K t h hh
                hdV G₀ hG₀subset)) (FacialInsertionGeometry.hnotGactual r n q p s X K t h G hh
                G₀ hnotG hGsame)
              hparentG hgeo
          rcases hchildrenF with hFL | hFR
          · rw [hFL]
            exact hmixed.1
          · rw [hFR]
            exact hmixed.2.1
      · rcases hbranchG with ⟨haG, hbG, hchildrenG⟩ | ⟨hnotG, hGsame⟩
        · have hhitG : e.1 ∈ G₀ ∧ e.2.2 ∈ G₀ := ⟨haG, hbG⟩
          have hFparent : F ∈ c.faces h := by
            exact faceMemTransport hFsame hF₀
          have hparentF := ih hleFace G₀ hG₀ F hFparent
          obtain ⟨z, haz, hbz, hFeq, hleftFace, hrightFace,
              u, hu0, hu1, hvalue, hgeo⟩ := splitFacts G₀ hG₀ hhitG
          have hmixed := mixedPair v vinj e.1 e.2.1 e.2.2 z
            hab haz hbz G₀ F hFeq hleftFace hrightFace (FacialInsertionGeometry.hdFactual r n q
                p s X K t h F hh F₀ hFsame (FacialInsertionGeometry.hdF r n q p s X K t h hh
                hdV F₀ hF₀subset)) (FacialInsertionGeometry.hnotFactual r n q p s X K t h F hh
                F₀ hnotF hFsame)
              hparentF hgeo
          rcases hchildrenG with hGL | hGR
          · rw [hGL]
            exact hmixed.2.2.1
          · rw [hGR]
            exact hmixed.2.2.2
        · have hFparent : F ∈ c.faces h := by
            exact faceMemTransport hFsame hF₀
          have hGparent : G ∈ c.faces h := by
            exact faceMemTransport hGsame hG₀
          exact ih hleFace F hFparent G hGparent

end InsertionAssembly

theorem P3523T1InsertionGeometry {r n : Nat}
    (q : P3381T1PolygonBoundary r) (p : P3381T1PolygonBoundary n)
    (s : P3475T1BoundarySubdivision q p)
    (X K : Set (Real × Real)) (t : P3475T1TriangleTree q X K) :
    let c := P3523T1InsertionConstruction s t
    let fs := c.faces c.steps.length
    let f := P3523T1FaceEnumeration fs
    let Q := P3523T1InterpolatedTarget s t
    (∀ k, P3381T1TriangleDeterminant (p.vertex ∘ f k) ≠ 0) ∧
    (∀ k, P3381T1TriangleDeterminant (Q ∘ f k) ≠ 0) ∧
    X = ⋃ k, convexHull Real (Set.range (p.vertex ∘ f k)) ∧
    K = ⋃ k, convexHull Real (Set.range (Q ∘ f k)) ∧
    (∀ k l,
      convexHull Real (Set.range (p.vertex ∘ f k)) ∩
        convexHull Real (Set.range (p.vertex ∘ f l)) =
        convexHull Real (p.vertex '' (Set.range (f k) ∩ Set.range (f l)))) ∧
    (∀ k l,
      convexHull Real (Set.range (Q ∘ f k)) ∩
        convexHull Real (Set.range (Q ∘ f l)) =
        convexHull Real (Q '' (Set.range (f k) ∩ Set.range (f l)))) := by
-- BODY
  classical
  dsimp only
  have split_mem {I : Type} [DecidableEq I]
      (fs : Finset (Finset I)) (a d b : I) (G : Finset I) := FacialInsertionGeometry.split_mem (I
          := I) fs a d b G
  have split_mem_cases {I : Type} [DecidableEq I]
      (fs : Finset (Finset I)) (a d b : I) (G : Finset I) :=
          FacialInsertionGeometry.split_mem_cases split_mem (I := I) fs a d b G
  have faceMemTransport {I : Type} [DecidableEq I]
      {fs : Finset (Finset I)} {F G : Finset I} (hFG : F = G)
      (hG : G ∈ fs) : F ∈ fs := hFG ▸ hG
  let triangleMatrix (v : Fin 3 → Real × Real) :
      Matrix (Fin 3) (Fin 3) Real :=
    fun i j => if j = 0 then (v i).1 else if j = 1 then (v i).2 else 1
  have det_range_transport {I : Type} (f g : Fin 3 → I)
      (hf : Function.Injective f) (hg : Function.Injective g)
      (hr : Set.range f = Set.range g) (v : I → Real × Real) :=
          FacialInsertionGeometry.det_range_transport
              (FacialInsertionGeometry.triangleMatrix_det) (I := I) f g hf hg hr v
  have hInc := P3523T1InsertionIncidence q p s X K t
  have hOrd := P3523T1OrderedInsertion q p s X K t
  have hHull := P3523T1TargetHull s t
  have hTargetBoundary := P3523T1TargetBoundary q p s X K t
  rcases hInc with ⟨hfaceShape, hincidence, hfaceInj,
    hfaceDistinct, hfaceCover, hfaceEdgeCount, hfaceRange⟩
  rcases hOrd with ⟨hstartOrdering, hstep, hvertices, hboundary⟩
  rcases hHull with ⟨hstartTarget, htargetHull⟩
  rcases hTargetBoundary with ⟨hTargetInj, _, _⟩
  let c := P3523T1InsertionConstruction s t
  have hfaces0 := FacialInsertionGeometry.hfaces0 r n q p s X K t
  have initialDet (v : Fin (n + 3) → Real × Real)
      (old : Fin (r + 3) → Real × Real)
      (hstart : ∀ i, v (s.start i) = old i)
      (hcert : ∀ k, P3381T1TriangleDeterminant (old ∘ t.face k) ≠ 0)
      (F : Finset (Fin (n + 3))) (hF : F ∈ c.faces 0)
      (g : Fin 3 → Fin (n + 3)) (hg : Function.Injective g)
      (hgrange : Set.range g = (F : Set (Fin (n + 3)))) := FacialInsertionGeometry.initialDet r n
          q p s X K t det_range_transport hfaces0 v old hstart hcert F hF g hg hgrange
  have existsThird {I : Type} [DecidableEq I] {F : Finset I}
      (hcard : F.card = 3) {a b : I} (ha : a ∈ F) (hb : b ∈ F)
      (hab : a ≠ b) := FacialInsertionGeometry.existsThird (I := I) (F := F) hcard (a := a) (b :=
          b) ha hb hab
  have hstartSource (i : Fin (r + 3)) := FacialInsertionGeometry.hstartSource r n q p s i
  have sourceInitialDet := initialDet p.vertex q.vertex hstartSource
    t.source_nondegenerate
  have targetInitialDet := initialDet (P3523T1InterpolatedTarget s t)
    t.target hstartTarget t.target_nondegenerate
  have sourceInterp := FacialInsertionGeometry.sourceInterp r n q p s X K t hstep
  have targetInterp := FacialInsertionGeometry.targetInterp r n q p s X K t hstep
  have tripleInj {I : Type} {a b z : I} (hab : a ≠ b)
      (haz : a ≠ z) (hbz : b ≠ z) := FacialInsertionGeometry.tripleInj (I := I) (a := a) (b :=
          b) (z := z) hab haz hbz
  have tripleRange {I : Type} [DecidableEq I] (a b z : I) := FacialInsertionGeometry.tripleRange
      (I := I) a b z
  have mapTriple {I J : Type} (v : I → J) (a b z : I) := FacialInsertionGeometry.mapTriple (I :=
      I) (J := J) v a b z
  have detState (v : Fin (n + 3) → Real × Real)
      (hinterp : ∀ h (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∃ u : Real, 0 < u ∧ u < 1 ∧
          v e.2.1 = (1-u) • v e.1 + u • v e.2.2)
      (hinit : ∀ F ∈ c.faces 0, ∀ g : Fin 3 → Fin (n + 3),
        Function.Injective g → Set.range g = (F : Set _) →
          P3381T1TriangleDeterminant (v ∘ g) ≠ 0) := FacialInsertionGeometry.detState r n q p s
              X K t split_mem det_range_transport hfaceShape hstep existsThird tripleInj
              tripleRange mapTriple v hinterp hinit
  have sourceState := detState p.vertex sourceInterp sourceInitialDet
  have targetState := detState (P3523T1InterpolatedTarget s t)
    targetInterp targetInitialDet
  let f := P3523T1FaceEnumeration (c.faces c.steps.length)
  have terminalFace (k : Fin (c.faces c.steps.length).card) :=
      FacialInsertionGeometry.terminalFace r n q p s X K t hfaceRange k
  let faceUnion (v : Fin (n + 3) → Real × Real)
      (faces : Finset (Finset (Fin (n + 3)))) : Set (Real × Real) :=
    ⋃ F ∈ (faces : Set (Finset (Fin (n + 3)))),
      convexHull Real (v '' (F : Set (Fin (n + 3))))
  have imageUnion {α β γ : Type} [DecidableEq β]
      (s₀ : Finset α) (g₀ : α → β) (P : β → Set γ) := FacialInsertionGeometry.imageUnion (α := α)
          (β := β) (γ := γ) s₀ g₀ P
  have imageTriple (v : Fin (n + 3) → Real × Real)
      (a b z : Fin (n + 3)) := FacialInsertionGeometry.imageTriple n v a b z
  have imagePair (v : Fin (n + 3) → Real × Real)
      (a z : Fin (n + 3)) := FacialInsertionGeometry.imagePair n v a z
  have splitHull (v : Fin (n + 3) → Real × Real)
      (a d b z : Fin (n + 3)) (hab : a ≠ b) (haz : a ≠ z)
      (hbz : b ≠ z) (u : Real) (hu : 0 < u ∧ u < 1)
      (hvalue : v d = (1-u) • v a + u • v b)
      (hdet : P3381T1TriangleDeterminant ![v a, v b, v z] ≠ 0) :=
          FacialInsertionGeometry.splitHull n imageTriple v a d b z hab haz hbz u hu hvalue hdet
  have sourceStartImage (k : Fin t.count) := FacialInsertionGeometry.sourceStartImage r n q p s X
      K t hstartSource k
  have targetStartImage (k : Fin t.count) := FacialInsertionGeometry.targetStartImage r n q p s X
      K t hstartTarget k
  have startFaceSet (k : Fin t.count) := FacialInsertionGeometry.startFaceSet r n q p s X K t k
  have coverState (v : Fin (n + 3) → Real × Real)
      (hinterp : ∀ h (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∃ u : Real, 0 < u ∧ u < 1 ∧
          v e.2.1 = (1-u) • v e.1 + u • v e.2.2)
      (hnondeg : ∀ h ≤ c.steps.length, ∀ F ∈ c.faces h,
        ∀ g : Fin 3 → Fin (n + 3), Function.Injective g →
          Set.range g = (F : Set _) →
            P3381T1TriangleDeterminant (v ∘ g) ≠ 0)
      (Y : Set (Real × Real)) (hbase : faceUnion v (c.faces 0) = Y) :=
          InsertionAssembly.coverState r n q p s X K t split_mem hfaceShape hstep existsThird
          tripleInj tripleRange mapTriple splitHull v hinterp hnondeg Y hbase
  have mixedPair (v : Fin (n + 3) → Real × Real)
      (vinj : Function.Injective v) (a d b z : Fin (n + 3))
      (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
      (F H : Finset (Fin (n + 3))) (hF : F = {a, b, z})
      (hleftFace : insert d (F.erase b) = {a, d, z})
      (hrightFace : insert d (F.erase a) = {d, b, z})
      (hdH : d ∉ H) (hnot : ¬ (a ∈ H ∧ b ∈ H))
      (hpair : convexHull Real (v '' (F : Set _)) ∩
          convexHull Real (v '' (H : Set _)) =
            convexHull Real (v '' ((F : Set _) ∩ (H : Set _))))
      (hgeo : convexHull Real (v '' (({a, b, z} : Finset (Fin (n + 3))) : Set _)) =
          convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∪
            convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3))) : Set _)) ∧
        convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∩
            convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3))) : Set _)) =
              segment Real (v d) (v z) ∧
        (∀ J : Set (Real × Real), J ⊆ {v a, v b, v z} →
          ¬ (v a ∈ J ∧ v b ∈ J) →
            convexHull Real (v '' (({a, d, z} : Finset (Fin (n + 3))) : Set _)) ∩
              convexHull Real J = convexHull Real (J ∩ {v a, v z}) ∧
            convexHull Real (v '' (({d, b, z} : Finset (Fin (n + 3))) : Set _)) ∩
              convexHull Real J = convexHull Real (J ∩ {v b, v z}))) :=
                  FacialInsertionGeometry.mixedPair n (FacialInsertionGeometry.retainedLeft n
                      imagePair) (FacialInsertionGeometry.retainedRight n imagePair) v vinj a d b z
                  hab haz hbz F H hF hleftFace hrightFace hdH hnot hpair hgeo
  have pairState (v : Fin (n + 3) → Real × Real)
      (vinj : Function.Injective v)
      (hinterp : ∀ h (hh : h < c.steps.length),
        let e := c.steps.get ⟨h, hh⟩
        ∃ u : Real, 0 < u ∧ u < 1 ∧
          v e.2.1 = (1-u) • v e.1 + u • v e.2.2)
      (hnondeg : ∀ h ≤ c.steps.length, ∀ F ∈ c.faces h,
        ∀ g : Fin 3 → Fin (n + 3), Function.Injective g →
          Set.range g = (F : Set _) →
            P3381T1TriangleDeterminant (v ∘ g) ≠ 0)
      (hinit : ∀ F ∈ c.faces 0, ∀ G ∈ c.faces 0,
        convexHull Real (v '' (F : Set _)) ∩
          convexHull Real (v '' (G : Set _)) =
            convexHull Real (v '' ((F : Set _) ∩ (G : Set _)))) := InsertionAssembly.pairState r
                n q p s X K t split_mem_cases faceMemTransport hfaceShape hincidence hstep
                existsThird tripleInj tripleRange mapTriple imageTriple mixedPair v vinj hinterp
                hnondeg hinit
  have enumUnion (v : Fin (n + 3) → Real × Real) := FacialInsertionGeometry.enumUnion r n q p s X
      K t hfaceRange v
  have hsourceCoverState :=
    coverState p.vertex sourceInterp sourceState X (FacialInsertionGeometry.sourceBase r n q p s
        X K t hfaces0 imageUnion sourceStartImage)
  have htargetCoverState := coverState (P3523T1InterpolatedTarget s t)
    targetInterp targetState K (FacialInsertionGeometry.targetBase r n q p s X K t hfaces0
        imageUnion targetStartImage)
  have sourcePairState : ∀ h ≤ c.steps.length, ∀ F ∈ c.faces h,
      ∀ G ∈ c.faces h,
        convexHull Real (p.vertex '' (F : Set _)) ∩
          convexHull Real (p.vertex '' (G : Set _)) =
            convexHull Real (p.vertex '' ((F : Set _) ∩ (G : Set _))) :=
    pairState p.vertex p.injective sourceInterp sourceState
        (FacialInsertionGeometry.sourceInitialPair r n q p s X K t hfaces0 sourceStartImage
        (FacialInsertionGeometry.sourceStartCommon r n q p s X K t hstartSource startFaceSet))
  have targetPairState : ∀ h ≤ c.steps.length, ∀ F ∈ c.faces h,
      ∀ G ∈ c.faces h,
        convexHull Real ((P3523T1InterpolatedTarget s t) '' (F : Set _)) ∩
          convexHull Real ((P3523T1InterpolatedTarget s t) '' (G : Set _)) =
            convexHull Real ((P3523T1InterpolatedTarget s t) ''
              ((F : Set _) ∩ (G : Set _))) :=
    pairState (P3523T1InterpolatedTarget s t) hTargetInj targetInterp
      targetState (FacialInsertionGeometry.targetInitialPair r n q p s X K t hfaces0
          targetStartImage (FacialInsertionGeometry.targetStartCommon r n q p s X K t
          hstartTarget startFaceSet))
  have imageRange (v : Fin (n + 3) → Real × Real)
      (k : Fin (c.faces c.steps.length).card) := FacialInsertionGeometry.imageRangeAt1467 r n q p
          s X K t v k
  exact ⟨(FacialInsertionGeometry.hsourceDet r n q p s X K t hfaceInj sourceState terminalFace),
      (FacialInsertionGeometry.htargetDet r n q p s X K t hfaceInj targetState terminalFace),
      (FacialInsertionGeometry.hsourceCoverage r n q p s X K t enumUnion hsourceCoverState),
      (FacialInsertionGeometry.htargetCoverage r n q p s X K t enumUnion htargetCoverState),
    (FacialInsertionGeometry.hsourcePairs r n q p s X K t terminalFace sourcePairState
        imageRange), (FacialInsertionGeometry.htargetPairs r n q p s X K t terminalFace
        targetPairState imageRange)⟩

end ApollonianSuperharmonic

end
