/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.AffineTriangularNoFourfoldCellOwners

-- [TABLET NODE: P4158T1EdgeSectorSelection]

/-!
# P4158T1EdgeSectorSelection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace EdgeSectorGeometry

private theorem regular_index :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (PP : PeriodicTileComplex ↥(TilingLattice
            Ci)), (∀ (a : ↥(TilingLattice Ci)), PP.tile a = TileTranslation base (↑a :
            GaussianInt)) → (∀ (U : ProtoTile), (U ∈ RegularTileFamily base (TilingLattice Ci)) →
            (∃ a : TilingLattice Ci, PP.tile a = U)) ) := by
  classical
  intro Ci base PP htiles U hU
  change ∃ v ∈ TilingLattice Ci, U = TileTranslation base v at hU
  rcases hU with ⟨v, hv, hEq⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  calc
    PP.tile ⟨v, hv⟩ = TileTranslation base v := htiles ⟨v, hv⟩
    _ = U := hEq.symm

private theorem pair_eq_iff :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (a ≠ b) →
            ((c ≠ d) → (({a, b} : Finset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c))) ) := by
  classical
  intro α typeclassInstance0 a b c d hab hcd
  constructor
  · intro h
    have ha : a = c ∨ a = d := by
      have hh := congrArg (fun s : Finset α => a ∈ s) h
      simpa using hh
    rcases ha with hac | had
    · subst c
      have hmem : b ∈ ({a, d} : Finset α) := by
        have hb : b ∈ ({a, b} : Finset α) := by simp
        rw [h] at hb
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hb
      have hmem' : b = a ∨ b = d := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
      have hbd : b = d := by
        rcases hmem' with hba | hbd
        · exact False.elim (hab hba.symm)
        · exact hbd
      exact Or.inl ⟨rfl, hbd⟩
    · subst d
      have hmem : b ∈ ({c, a} : Finset α) := by
        have hb : b ∈ ({a, b} : Finset α) := by simp
        rw [h] at hb
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hb
      have hmem' : b = c ∨ b = a := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
      have hbc : b = c := by
        rcases hmem' with hbc | hba
        · exact hbc
        · exact False.elim (hab hba.symm)
      exact Or.inr ⟨rfl, hbc⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ext w
      simp [or_comm]

private theorem vertical_edge_cells :
    (by
      classical
      exact
        (∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (a ≠ b) →
            ((c ≠ d) → (({a, b} : Finset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)))) → (∀
            (W : ProtoTile), ∀ (w : GaussianInt), ({w, w + ⟨0, 1⟩} ∈ FootprintEdges W) → (w ∈
            W.cells ∨ w - 1 ∈ W.cells)) ) := by
  classical
  intro pair_eq_iff W w he
  simp only [FootprintEdges, Set.mem_ofPred_eq] at he
  obtain ⟨y, hy, hshape⟩ := he
  let v : GaussianInt := ⟨0, 1⟩
  have hv0 : v ≠ 0 := by decide
  have hv1 : v ≠ 1 := by decide
  have hvm1 : v ≠ -1 := by decide
  have hvv : v + v ≠ 0 := by decide
  have htarget : w ≠ w + v := by
    intro hh
    have hh' : w + 0 = w + v := by simpa using hh
    have hh' : (0 : GaussianInt) = v := add_left_cancel hh'
    exact hv0 hh'.symm
  rcases hshape with h | h | h | h
  · have hsource : y ≠ y + 1 := by
      intro hh
      have hh' := congrArg Zsqrtd.re hh
      norm_num at hh'
    have hp := (pair_eq_iff w (w+v) y (y+1) htarget hsource).mp h
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv : v = 1 := by
        calc
          v = (w + v) - w := by abel
          _ = (y + 1) - y := by rw [h2, h1]
          _ = 1 := by abel
      exact (hv1 hv).elim
    · have hv : v = -1 := by
        calc
          v = (w + v) - w := by abel
          _ = y - (y + 1) := by rw [h2, h1]
          _ = -1 := by abel
      exact (hvm1 hv).elim
  · have hsource : y ≠ y + v := by
      intro hh
      have hh' := congrArg Zsqrtd.im hh
      norm_num [v] at hh'
    have hp := (pair_eq_iff w (w+v) y (y+v) htarget hsource).mp h
    rcases hp with ⟨h1, _⟩ | ⟨h1, h2⟩
    · left
      simpa [h1] using hy
    · have hsum : v + v = 0 := by
        have hh : y + v + v = y := by
          calc
            y + v + v = w + v := by rw [h1]
            _ = y := h2
        have hh' : y + (v + v) = y + 0 := by simpa [add_assoc] using hh
        exact add_left_cancel hh'
      exact (hvv hsum).elim
  · have hsource : y + 1 ≠ y + 1 + v := by
      intro hh
      have hh' := congrArg Zsqrtd.im hh
      norm_num [v] at hh'
    have hp := (pair_eq_iff w (w+v) (y+1) (y+1+v) htarget hsource).mp h
    rcases hp with ⟨h1, _⟩ | ⟨h1, h2⟩
    · right
      have hyz : y = w - 1 := by
        calc
          y = (y + 1) - 1 := by abel
          _ = w - 1 := by rw [h1]
      simpa [hyz] using hy
    · have hsum : v + v = 0 := by
        have hh : (y + 1) + v + v = y + 1 := by
          calc
            (y + 1) + v + v = w + v := by rw [h1]
            _ = y + 1 := h2
        have hh' : (y + 1) + (v + v) = (y + 1) + 0 := by
          simpa [add_assoc] using hh
        exact add_left_cancel hh'
      exact (hvv hsum).elim
  · have hsource : y + v ≠ y + 1 + v := by
      intro hh
      have hh' := congrArg Zsqrtd.re hh
      norm_num [v] at hh'
    have hp := (pair_eq_iff w (w+v) (y+v) (y+1+v) htarget hsource).mp h
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv : v = 1 := by
        calc
          v = (w + v) - w := by abel
          _ = (y + 1 + v) - (y + v) := by rw [h2, h1]
          _ = 1 := by abel
      exact (hv1 hv).elim
    · have hv : v = -1 := by
        calc
          v = (w + v) - w := by abel
          _ = (y + v) - (y + 1 + v) := by rw [h2, h1]
          _ = -1 := by abel
      exact (hvm1 hv).elim

private theorem translated_ford_bounds :
    (by
      classical
      exact
        ∀ (n : Nat),
          ∀ (w : GaussianInt),
            ∀ (c : GaussianInt),
              c ∈ (TileTranslation (FordTile n) w).cells →
                0 ≤ (c - w).re ∧ (c - w).re < n ∧ 0 ≤ (c - w).im ∧ (c - w).im < n
    ) := by
  classical
  intro n w c hc
  change c ∈ (FordCellDomain n).image (GaussianTranslation w) at hc
  obtain ⟨t, ht, htc⟩ := Finset.mem_image.mp hc
  change t ∈ FordCellDomain n at ht
  change t + w = c at htc
  simp only [FordCellDomain, Finset.mem_image] at ht
  obtain ⟨a, ha, hat⟩ := ht
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_product.mp ha
  simp only [Finset.mem_range] at ha₁ ha₂
  have ht_eq : (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt) = t := hat
  have hcw : c - w = t := by rw [← htc]; abel
  have hr : (c-w).re = (a.1 : Int) := by rw [hcw, ← ht_eq]
  have hi : (c-w).im = (a.2 : Int) := by rw [hcw, ← ht_eq]
  constructor
  · rw [hr]; omega
  constructor
  · rw [hr]; exact_mod_cast ha₁
  constructor
  · rw [hi]; omega
  · rw [hi]; exact_mod_cast ha₂

private theorem translated_ford_cell :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (a : Nat), ∀ (b : Nat), ∀ (w : GaussianInt), (a < n) → ((b < n) → (w +
            (⟨(a : Int), (b : Int)⟩ : GaussianInt) ∈ (TileTranslation (FordTile n) w).cells)) )
            := by
  classical
  intro n a b w ha hb
  change w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) ∈
    (FordCellDomain n).image (GaussianTranslation w)
  refine Finset.mem_image.mpr ⟨(⟨(a : Int), (b : Int)⟩ : GaussianInt), ?_, ?_⟩
  · unfold FordCellDomain
    refine Finset.mem_image.mpr ⟨(a,b), ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_range, ha, hb]
    · rfl
  · simp [GaussianTranslation, add_comm]

private theorem ford_disjoint_re :
    (by
      classical
      exact
        (
        (
        (
        (
        ((∀ (n : Nat), ∀ (w : GaussianInt), ∀ (c : GaussianInt), (c ∈ (TileTranslation
            (FordTile n) w).cells) → (0 ≤ (c-w).re ∧ (c-w).re < n ∧ 0 ≤ (c-w).im ∧ (c-w).im < n))
            → (∀ (n : Nat), ∀ (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt), (w.re + n ≤
            v.re) → (Disjoint (TileTranslation (FordTile n) w).cells (TileTranslation (FordTile
            m) v).cells))))))) ) := by
  classical
  intro translated_ford_bounds n m w v hgap
  apply Finset.disjoint_left.mpr
  intro c hcW hcV
  have hW := translated_ford_bounds n w c hcW
  have hV := translated_ford_bounds m v c hcV
  simp [Zsqrtd.re_sub] at hW hV
  omega

private theorem ford_disjoint_im :
    (by
      classical
      exact
        (
        (
        (
        (
        ((∀ (n : Nat), ∀ (w : GaussianInt), ∀ (c : GaussianInt), (c ∈ (TileTranslation
            (FordTile n) w).cells) → (0 ≤ (c-w).re ∧ (c-w).re < n ∧ 0 ≤ (c-w).im ∧ (c-w).im < n))
            → (∀ (n : Nat), ∀ (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt), (w.im + n ≤
            v.im) → (Disjoint (TileTranslation (FordTile n) w).cells (TileTranslation (FordTile
            m) v).cells))))))) ) := by
  classical
  intro translated_ford_bounds n m w v hgap
  apply Finset.disjoint_left.mpr
  intro c hcW hcV
  have hW := translated_ford_bounds n w c hcW
  have hV := translated_ford_bounds m v c hcV
  simp [Zsqrtd.im_sub] at hW hV
  omega

private theorem lower_lt_q :
    (by
      classical
        exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin (3 : ℕ)),
            (i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
              ((if i = 0 then (P.q₁ : Int) else P.q₂) < P.q)) := by
  classical
  intro P i hsmall
  rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
  · subst i
    have hq : (P.q₁ : Int) + P.q₂ = P.q := by exact_mod_cast P.sum_q.symm
    omega
  · subst i
    have hq : (P.q₁ : Int) + P.q₂ = P.q := by exact_mod_cast P.sum_q.symm
    omega

private theorem z_low :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ((x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x) ) := by
  classical
  intro P i u x z hlow
  change (if (x-u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
    then x else x - ⟨0, 1⟩) = x
  rw [ite_eq_left hlow]

private theorem z_other :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (¬(x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x - ⟨0, 1⟩) ) := by
  classical
  intro P i u x z hlow
  change (if (x-u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
    then x else x - ⟨0, 1⟩) = x - ⟨0, 1⟩
  rw [ite_eq_right hlow]

private theorem z_incident :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x)) → (((¬(x - u).im = (if
            i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x - ⟨0, 1⟩)) → (z = x ∨ z = x - ⟨0, 1⟩)) )
            := by
  classical
  intro P i u x z z_low z_other
  by_cases hlow : (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
  · exact Or.inl (z_low hlow)
  · exact Or.inr (z_other hlow)

private theorem hz_re :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt), ((x - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) → (
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x)) → (((¬(x - u).im = (if
            i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x - ⟨0, 1⟩)) → ((z - u).re = (if i = 0
            then (P.q : Int) else 0)))) ) := by
  classical
  intro P i u x hxr z z_low z_other
  by_cases hlow : (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
  · rw [z_low hlow]
    exact hxr
  · have hstep : (x - ⟨0, 1⟩ - u).re = (x - u).re := by
      simp [Zsqrtd.re_sub]
    rw [z_other hlow, hstep]
    exact hxr

private theorem hz_low :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin (3 : ℕ)),
            ∀ (u : GaussianInt),
              ∀ (x : GaussianInt),
                (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤
                    (x - u).im →
                  let z : GaussianInt :=
                    if (x - u).im = if i = 0 then (P.q₁ : Int) else P.q₂ then x
                    else x - ⟨0, 1⟩
                  (((x - u).im = if i = 0 then (P.q₁ : Int) else P.q₂) → z = x) →
                    ((¬(x - u).im = if i = 0 then (P.q₁ : Int) else P.q₂) →
                        z = x - ⟨0, 1⟩) →
                      (if i = 0 then (P.q₁ : Int) else P.q₂) ≤ (z - u).im
    ) := by
  classical
  intro P i u x hxl z z_low z_other
  by_cases hlow : (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
  · rw [z_low hlow]
    exact hxl
  · have hstrict : (if i = 0 then (P.q₁ : Int) else P.q₂) < (x-u).im := by
      omega
    have hstep : (x - ⟨0, 1⟩ - u).im = (x-u).im - 1 := by
      simp [Zsqrtd.im_sub]
      omega
    rw [z_other hlow, hstep]
    omega

private theorem hz_high :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin (3 : ℕ)),
            ∀ (u : GaussianInt),
              ∀ (x : GaussianInt),
                (x - u).im ≤ (↑P.q : ℤ) →
                  (if i = 0 then (P.q₁ : Int) else P.q₂) < P.q →
                    let z : GaussianInt :=
                      if (x - u).im = if i = 0 then (P.q₁ : Int) else P.q₂ then x
                      else x - ⟨0, 1⟩
                    (((x - u).im = if i = 0 then (P.q₁ : Int) else P.q₂) → z = x) →
                      ((¬(x - u).im = if i = 0 then (P.q₁ : Int) else P.q₂) →
                          z = x - ⟨0, 1⟩) →
                        (z - u).im < P.q
    ) := by
  classical
  intro P i u x hxu lower_lt_q z z_low z_other
  by_cases hlow : (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
  · rw [z_low hlow]
    simpa [hlow] using lower_lt_q
  · have hstep : (x - ⟨0, 1⟩ - u).im = (x-u).im - 1 := by
      simp [Zsqrtd.im_sub]
      omega
    rw [z_other hlow, hstep]
    omega

private theorem U_edge :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (i : Fin (3 : ℕ)), ∀ (u :
            GaussianInt), ∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt),
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ∀ (U : ProtoTile), ({z, z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges U) → (∀
            (a : ↥(TilingLattice Ci)), (PP.tile a = U) → ({z, z + ⟨0, 1⟩} ∈ FootprintEdges
            (PP.tile a))) ) := by
  classical
  intro P Ci i u PP x z U hEdgeU a hUa
  rw [hUa]
  exact hEdgeU

private theorem V_edge :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (i : Fin (3 : ℕ)), ∀ (u :
            GaussianInt), ∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt),
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ∀ (V : ProtoTile), ({z, z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges V) → (∀
            (b : ↥(TilingLattice Ci)), (PP.tile b = V) → ({z, z + ⟨0, 1⟩} ∈ FootprintEdges
            (PP.tile b))) ) := by
  classical
  intro P Ci i u PP x z V hEdgeV b hVb
  rw [hVb]
  exact hEdgeV

private theorem T_bounds :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → ((∀ (n : Nat), ∀ (w : GaussianInt), ∀ (c
            : GaussianInt), (c ∈ (TileTranslation (FordTile n) w).cells) → (0 ≤ (c-w).re ∧
            (c-w).re < n ∧ 0 ≤ (c-w).im ∧ (c-w).im < n)) → (∀ (c : GaussianInt), (c ∈ T.cells) →
            (0 ≤ (c-u).re ∧ (c-u).re < P.q ∧ 0 ≤ (c-u).im ∧ (c-u).im < P.q))) ) := by
  classical
  intro P T u hc translated_ford_bounds c hcT
  have hcT' : c ∈ (TileTranslation (FordTile P.q) u).cells := by
    simpa only [hc] using hcT
  exact translated_ford_bounds P.q u c hcT'

private theorem T'_bounds :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (T' : ProtoTile), ∀ (u : GaussianInt),
            (T'.cells = (TileTranslation (FordTile P.q) (u + if i = (0 : Fin (3 : ℕ)) then
            (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ :
            GaussianInt))).cells) → ((∀ (n : Nat), ∀ (w : GaussianInt), ∀ (c : GaussianInt), (c ∈
            (TileTranslation (FordTile n) w).cells) → (0 ≤ (c-w).re ∧ (c-w).re < n ∧ 0 ≤ (c-w).im
            ∧ (c-w).im < n)) → (∀ (c : GaussianInt), (c ∈ T'.cells) → (0 ≤ (c-(u + if i = 0 then
            ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int), (P.q₂ : Int)⟩)).re ∧ (c-(u + if i = 0
            then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int), (P.q₂ : Int)⟩)).re < P.q ∧ 0 ≤
            (c-(u + if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int), (P.q₂ :
            Int)⟩)).im ∧ (c-(u + if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int),
            (P.q₂ : Int)⟩)).im < P.q))) ) := by
  classical
  intro P i T' u hc' translated_ford_bounds c hcT
  have hcT' : c ∈ (TileTranslation (FordTile P.q)
      (u + if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
        else ⟨-(P.q : Int), (P.q₂ : Int)⟩)).cells := by
    simpa only [hc'] using hcT
  exact translated_ford_bounds P.q _ c hcT'

private theorem indexed_edge :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (i : Fin (3 :
            ℕ)), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), ∀ (u : GaussianInt), (Disjoint T.cells T'.cells) → (∀ (orientation
            : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (tiles : List ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀ (hs : List
            PartialOdometer), ∀ (reverseHs : List PartialOdometer), (TileString Ci orientation
            base Rminus Rplus tiles) → ((TileString Ci orientation base Rplus Rminus
            reverseTiles) → ((∀ (U : ProtoTile), ∀ (g : PartialOdometer), (U, g) ∈ tiles.zip hs →
            AncestorOdometer Ci.1.1 C0.1.1 U T g h → U.cells ⊆ T.cells) → ((∀ (V : ProtoTile), ∀
            (k : PartialOdometer), (V, k) ∈ reverseTiles.zip reverseHs → AncestorOdometer Ci.1.1
            C0.1.1 V T' k h' → V.cells ⊆ T'.cells) → ((∀ (z : GaussianInt), ((z - u).re = if i =
            (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) → (if i = (0 : Fin (3 : ℕ)) then
            (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤ (z - u).im → (z - u).im < (↑P.q : ℤ) → ∃ (U :
            ProtoTile) (V : ProtoTile) (g : PartialOdometer) (k : PartialOdometer), U ∈
            (List.drop (1 : ℕ) tiles).dropLast ∧ V ∈ (List.drop (1 : ℕ) reverseTiles).dropLast ∧
            (U, g) ∈ tiles.zip hs ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1
            C0.1.1 U T g h ∧ AncestorOdometer Ci.1.1 C0.1.1 V T' k h' ∧ {z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges U ∧ {z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges V) → (∀ (PP : PeriodicTileComplex
            ↥(TilingLattice Ci)), (∀ (U : ProtoTile), (U ∈ RegularTileFamily base (TilingLattice
            Ci)) → (∃ a : TilingLattice Ci, PP.tile a = U)) → ((∀ (W : ProtoTile), ∀ (w :
            GaussianInt), ({w, w + ⟨0, 1⟩} ∈ FootprintEdges W) → (w ∈ W.cells ∨ w - 1 ∈ W.cells))
            → (∀ (w : GaussianInt), ((w-u).re = (if i = 0 then (P.q : Int) else 0)) → (((if i = 0
            then (P.q₁ : Int) else P.q₂) ≤ (w-u).im) → (((w-u).im < P.q) → (∃ (aa bb :
            TilingLattice Ci) (gg kk : PartialOdometer), aa ≠ bb ∧ (PP.tile aa, gg) ∈ tiles.zip
            hs ∧ (PP.tile bb, kk) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1 C0.1.1
            (PP.tile aa) T gg h ∧ AncestorOdometer Ci.1.1 C0.1.1 (PP.tile bb) T' kk h' ∧ {w,
            w + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile aa) ∧ {w, w + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile
            bb)))))))))))) ) := by
  classical
  intro P C0 Ci i T T' h h' u hdis orientation base Rminus Rplus tiles reverseTiles hs reverseHs
      hf hr hcontain hcontain' hedges PP regular_index vertical_edge_cells w hwre hwl hwu
  obtain ⟨UU, VV, gg, kk, _, _, hUzip, hVzip, hUanc, hVanc, hEU, hEV⟩ :=
    hedges w hwre hwl hwu
  have hUlist : UU ∈ tiles := (List.of_mem_zip hUzip).1
  have hVlist : VV ∈ reverseTiles := (List.of_mem_zip hVzip).1
  obtain ⟨aa, haa⟩ := regular_index UU (hf.2.2.2.2.1 UU hUlist)
  obtain ⟨bb, hbb⟩ := regular_index VV (hr.2.2.2.2.1 VV hVlist)
  have hEU' : {w, w + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile aa) := by
    simpa [haa] using hEU
  have hEV' : {w, w + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile bb) := by
    simpa [hbb] using hEV
  have hcell : ∃ c, c ∈ UU.cells := by
    rcases vertical_edge_cells UU w hEU with hc | hc
    · exact ⟨w, hc⟩
    · exact ⟨w-1, hc⟩
  have hne : aa ≠ bb := by
    intro heq
    obtain ⟨c, hc⟩ := hcell
    have hcaa : c ∈ (PP.tile aa).cells := by simpa [haa] using hc
    have hcbb : c ∈ (PP.tile bb).cells := by simpa [heq] using hcaa
    have hcv : c ∈ VV.cells := by simpa [hbb] using hcbb
    have hcT : c ∈ T.cells := hcontain UU gg hUzip hUanc hc
    have hcT' : c ∈ T'.cells := hcontain' VV kk hVzip hVanc hcv
    exact (Finset.disjoint_left.mp hdis)
      hcT hcT'
  exact ⟨aa, bb, gg, kk, hne, by simpa [haa] using hUzip,
    by simpa [hbb] using hVzip, by simpa [haa] using hUanc,
    by simpa [hbb] using hVanc, hEU', hEV'⟩

private theorem cross_ne :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (h' : PartialOdometer), (Disjoint T.cells T'.cells) → (∀ (tiles :
            List ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀
            (reverseHs : List PartialOdometer), (∀ (U : ProtoTile), ∀ (g : PartialOdometer), (U,
            g) ∈ tiles.zip hs → AncestorOdometer Ci.1.1 C0.1.1 U T g h → U.cells ⊆ T.cells) → ((∀
            (V : ProtoTile), ∀ (k : PartialOdometer), (V, k) ∈ reverseTiles.zip reverseHs →
            AncestorOdometer Ci.1.1 C0.1.1 V T' k h' → V.cells ⊆ T'.cells) → (∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (ff : TilingLattice Ci), ∀ (bb :
            TilingLattice Ci), ∀ (gg : PartialOdometer), ∀ (kk : PartialOdometer), ((PP.tile ff,
            gg) ∈ tiles.zip hs) → (((PP.tile bb, kk) ∈ reverseTiles.zip reverseHs) →
            ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile ff) T gg h) → ((AncestorOdometer Ci.1.1
            C0.1.1 (PP.tile bb) T' kk h') → (((PP.tile ff).cells.Nonempty) → (ff ≠ bb)))))))) )
            := by
  classical
  intro C0 Ci T T' h h' hdis tiles reverseTiles hs reverseHs hcontain hcontain' PP ff bb gg kk
      hfz hbz hfa hba hfn heq
  obtain ⟨c, hc⟩ := hfn
  have hcT : c ∈ T.cells := hcontain (PP.tile ff) gg hfz hfa hc
  have hcB : c ∈ (PP.tile bb).cells := by simpa [heq] using hc
  have hcT' : c ∈ T'.cells := hcontain' (PP.tile bb) kk hbz hba hcB
  exact (Finset.disjoint_left.mp hdis) hcT hcT'

private theorem forward_support :
    (by
      classical
        exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin (3 : ℕ)),
              (i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                  i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
                (∀ (T : ProtoTile),
                  ∀ (u : GaussianInt),
                    (∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)),
                      ∀ (x : GaussianInt),
                        ((∀ (W : ProtoTile),
                            ∀ (w : GaussianInt),
                              ({w, w + ⟨0, 1⟩} ∈ FootprintEdges W) →
                                (w ∈ W.cells ∨ w - 1 ∈ W.cells)) →
                          (let z : GaussianInt :=
                            if
                                (x - u).im =
                                  (if i = 0 then (P.q₁ : Int) else P.q₂) then
                              x
                            else x - ⟨0, 1⟩;
                          (((z - u).re = (if i = 0 then (P.q : Int) else 0)) →
                            (∀ (U : ProtoTile),
                              (∀ (a : ↥(TilingLattice Ci)),
                                (PP.tile a = U) →
                                  ((U.cells ⊆ T.cells) →
                                    (({z, z + ⟨0, 1⟩} ∈
                                        FootprintEdges (PP.tile a)) →
                                      ((∀ (c : GaussianInt),
                                          (c ∈ T.cells) →
                                            (0 ≤ (c - u).re ∧
                                              (c - u).re < P.q ∧
                                                0 ≤ (c - u).im ∧
                                                  (c - u).im < P.q)) →
                                        (∃ c,
                                          c ∈ U.cells ∧
                                            (if i = 0 then c = z - 1
                                            else c = z))))))))))))) := by
  classical
  intro P Ci i hsmall T u PP x vertical_edge_cells z hz_re U a hUa U_in_T U_edge T_bounds
  have hsup := vertical_edge_cells U z (by simpa [hUa] using U_edge)
  rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
  · subst i
    rcases hsup with hleft | hright
    · have hb := T_bounds z (U_in_T hleft)
      have hzr : (z-u).re = P.q := by simpa using hz_re
      have hcontra : P.q < P.q := by simpa [hzr] using hb.2.1
      exact (lt_irrefl P.q hcontra).elim
    · exact ⟨z-1, hright, by simp⟩
  · subst i
    rcases hsup with hleft | hright
    · exact ⟨z, hleft, by simp⟩
    · have hb := T_bounds (z-1) (U_in_T hright)
      have hzr : (z-u).re = 0 := by simpa using hz_re
      have hzstep : ((z-1)-u).re = (z-u).re - 1 := by
        simp [Zsqrtd.re_sub]
        omega
      have hneg : 0 ≤ -1 := by simpa [hzstep, hzr] using hb.1
      omega

private theorem reverse_support :
    (by
      classical
        exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin (3 : ℕ)),
              (i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                  i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
                (∀ (T' : ProtoTile),
                  ∀ (u : GaussianInt),
                    (∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)),
                      ∀ (x : GaussianInt),
                        ((∀ (W : ProtoTile),
                            ∀ (w : GaussianInt),
                              ({w, w + ⟨0, 1⟩} ∈ FootprintEdges W) →
                                (w ∈ W.cells ∨ w - 1 ∈ W.cells)) →
                          (let z : GaussianInt :=
                            if
                                (x - u).im =
                                  (if i = 0 then (P.q₁ : Int) else P.q₂) then
                              x
                            else x - ⟨0, 1⟩;
                          (((z - u).re = (if i = 0 then (P.q : Int) else 0)) →
                            (∀ (V : ProtoTile),
                              (∀ (b : ↥(TilingLattice Ci)),
                                (PP.tile b = V) →
                                  ((V.cells ⊆ T'.cells) →
                                    (({z, z + ⟨0, 1⟩} ∈
                                        FootprintEdges (PP.tile b)) →
                                      ((∀ (c : GaussianInt),
                                          (c ∈ T'.cells) →
                                            (0 ≤
                                                (c -
                                                    (u +
                                                      if i = 0 then
                                                        ⟨(P.q : Int), (P.q₁ : Int)⟩
                                                      else
                                                        ⟨-(P.q : Int),
                                                          (P.q₂ : Int)⟩)).re ∧
                                              (c -
                                                      (u +
                                                        if i = 0 then
                                                          ⟨(P.q : Int),
                                                            (P.q₁ : Int)⟩
                                                        else
                                                          ⟨-(P.q : Int),
                                                            (P.q₂ : Int)⟩)).re <
                                                  P.q ∧
                                                0 ≤
                                                    (c -
                                                        (u +
                                                          if i = 0 then
                                                            ⟨(P.q : Int),
                                                              (P.q₁ : Int)⟩
                                                          else
                                                            ⟨-(P.q : Int),
                                                              (P.q₂ : Int)⟩)).im ∧
                                                  (c -
                                                        (u +
                                                          if i = 0 then
                                                            ⟨(P.q : Int),
                                                              (P.q₁ : Int)⟩
                                                          else
                                                            ⟨-(P.q : Int),
                                                              (P.q₂ : Int)⟩)).im <
                                                    P.q)) →
                                        (∃ c,
                                          c ∈ V.cells ∧
                                            (if i = 0 then c = z
                                            else c = z - 1))))))))))))) := by
  classical
  intro P Ci i hsmall T' u PP x vertical_edge_cells z hz_re V b hVb V_in_T' V_edge T'_bounds
  have hsup := vertical_edge_cells V z (by simpa [hVb] using V_edge)
  rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
  · subst i
    rcases hsup with hleft | hright
    · exact ⟨z, hleft, by simp⟩
    · have hb := T'_bounds (z-1) (V_in_T' hright)
      have hzr : (z-u).re = P.q := by simpa using hz_re
      have hzr' : z.re - u.re = P.q := by simpa [Zsqrtd.re_sub] using hzr
      have hzstep : ((z-1)-(u+⟨(P.q:Int),(P.q₁:Int)⟩)).re = -1 := by
        simp [Zsqrtd.re_sub, Zsqrtd.re_add]
        omega
      have hneg : 0 ≤ -1 := by simpa [hzstep] using hb.1
      omega
  · subst i
    rcases hsup with hleft | hright
    · have hb := T'_bounds z (V_in_T' hleft)
      have hzr : (z-u).re = 0 := by simpa using hz_re
      have hzr' : z.re - u.re = 0 := by simpa [Zsqrtd.re_sub] using hzr
      have hzstep : (z-(u+⟨-(P.q:Int),(P.q₂:Int)⟩)).re = P.q := by
        simp [Zsqrtd.re_sub, Zsqrtd.re_add]
        omega
      have hlt : P.q < P.q := by simpa [hzstep] using hb.2.1
      omega
    · exact ⟨z-1, hright, by simp⟩

private theorem hab :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), (Disjoint T.cells T'.cells) →
            (∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (a : ↥(TilingLattice Ci)), ∀ (b : ↥(TilingLattice Ci)), (PP.tile a = U)
            → ((PP.tile b = V) → ((U.cells ⊆ T.cells) → ((V.cells ⊆ T'.cells) → (∀ (cf :
            LatticeCell), (cf ∈ U.cells) → (a ≠ b)))))) ) := by
  classical
  intro Ci T T' hdis PP U V a b hUa hVb U_in_T V_in_T' cf hcf hab
  have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  have hcfB : cf ∈ (PP.tile b).cells := by simpa [hab] using hcfA
  have hcfV : cf ∈ V.cells := by simpa [hVb] using hcfB
  exact (Finset.disjoint_left.mp hdis) (U_in_T hcf) (V_in_T' hcfV)

private theorem internal_solution :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (i : Fin (3 :
            ℕ)), (i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨ i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) → (∀
            (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), ∀ (u : GaussianInt), (T'.cells = (TileTranslation (FordTile P.q) (u
            + if i = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else
            (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells) → (∀ (Rminus : ProtoTile), ∀
            (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀
            (hs : List PartialOdometer), ∀ (reverseHs : List PartialOdometer), (Rminus.cells =
            (TileTranslation (FordTile (if i = (0 : Fin (3 : ℕ)) then P.q₁ else P.q₂)) (u + if i
            = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (0 : ℤ)⟩ : GaussianInt) else (⟨(0 : ℤ), (↑P.q
            : ℤ)⟩ : GaussianInt))).cells) → ((Rplus.cells = (TileTranslation (FordTile (if i = (0
            : Fin (3 : ℕ)) then P.q₁ else P.q₂)) (u + if i = (0 : Fin (3 : ℕ)) then (⟨(↑P.q₂ :
            ℤ), (↑P.q : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩ : GaussianInt))).cells)
            → ((∀ (U : ProtoTile), ∀ (g : PartialOdometer), (U, g) ∈ tiles.zip hs →
            AncestorOdometer Ci.1.1 C0.1.1 U T g h → U.cells ⊆ T.cells) → ((∀ (V : ProtoTile), ∀
            (k : PartialOdometer), (V, k) ∈ reverseTiles.zip reverseHs → AncestorOdometer Ci.1.1
            C0.1.1 V T' k h' → V.cells ⊆ T'.cells) → ((∀ (z : GaussianInt), ((z - u).re = if i =
            (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) → (if i = (0 : Fin (3 : ℕ)) then
            (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤ (z - u).im → (z - u).im < (↑P.q : ℤ) → ∃ (U :
            ProtoTile) (V : ProtoTile) (g : PartialOdometer) (k : PartialOdometer), U ∈
            (List.drop (1 : ℕ) tiles).dropLast ∧ V ∈ (List.drop (1 : ℕ) reverseTiles).dropLast ∧
            (U, g) ∈ tiles.zip hs ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1
            C0.1.1 U T g h ∧ AncestorOdometer Ci.1.1 C0.1.1 V T' k h' ∧ {z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges U ∧ {z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges V) → (∀ (PP : PeriodicTileComplex
            ↥(TilingLattice Ci)), ∀ (tileAt : ℤ × ℤ → ProtoTile), (AffineTriangularComplexChart
            PP tileAt) → (∀ (x : GaussianInt), ((x - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q
            : ℤ) else (0 : ℤ)) → (((if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤
            (x - u).im) → ((∀ (W : ProtoTile), ∀ (w : GaussianInt), ({w, w + ⟨0, 1⟩} ∈
            FootprintEdges W) → (w ∈ W.cells ∨ w - 1 ∈ W.cells)) → (((if i = 0 then (P.q₁ : Int)
            else P.q₂) < P.q) → (
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x)) → (((¬(x - u).im = (if
            i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x - ⟨0, 1⟩)) → ((z = x ∨ z = x - ⟨0, 1⟩) →
            (((z - u).re = (if i = 0 then (P.q : Int) else 0)) → (((if i = 0 then (P.q₁ : Int)
            else P.q₂) ≤ (z-u).im) → (((z-u).im < P.q) → (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀
            (g : PartialOdometer), ∀ (k : PartialOdometer), ({z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges U) → (({z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges V) → (∀ (a : ↥(TilingLattice Ci)), ∀ (b :
            ↥(TilingLattice Ci)), (PP.tile a = U) → ((PP.tile b = V) → (({z, z + ⟨0, 1⟩} ∈
            FootprintEdges (PP.tile a)) → (({z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile b)) → ((∀
            (c : GaussianInt), (c ∈ T.cells) → (0 ≤ (c-u).re ∧ (c-u).re < P.q ∧ 0 ≤ (c-u).im ∧
            (c-u).im < P.q)) → ((∀ (c : GaussianInt), (c ∈ T'.cells) → (0 ≤ (c-(u + if i = 0 then
            ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int), (P.q₂ : Int)⟩)).re ∧ (c-(u + if i = 0
            then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int), (P.q₂ : Int)⟩)).re < P.q ∧ 0 ≤
            (c-(u + if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int), (P.q₂ :
            Int)⟩)).im ∧ (c-(u + if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int),
            (P.q₂ : Int)⟩)).im < P.q)) → ((∀ (w : GaussianInt), ((w-u).re = (if i = 0 then (P.q :
            Int) else 0)) → (((if i = 0 then (P.q₁ : Int) else P.q₂) ≤ (w-u).im) → (((w-u).im <
            P.q) → (∃ (aa bb : TilingLattice Ci) (gg kk : PartialOdometer), aa ≠ bb ∧ (PP.tile
            aa, gg) ∈ tiles.zip hs ∧ (PP.tile bb, kk) ∈ reverseTiles.zip reverseHs ∧
            AncestorOdometer Ci.1.1 C0.1.1 (PP.tile aa) T gg h ∧ AncestorOdometer Ci.1.1 C0.1.1
            (PP.tile bb) T' kk h' ∧ {w, w + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile aa) ∧ {w, w + ⟨0,
            1⟩} ∈ FootprintEdges (PP.tile bb))))) → ((∀ (ff : TilingLattice Ci), ∀ (bb :
            TilingLattice Ci), ∀ (gg : PartialOdometer), ∀ (kk : PartialOdometer), ((PP.tile ff,
            gg) ∈ tiles.zip hs) → (((PP.tile bb, kk) ∈ reverseTiles.zip reverseHs) →
            ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile ff) T gg h) → ((AncestorOdometer Ci.1.1
            C0.1.1 (PP.tile bb) T' kk h') → (((PP.tile ff).cells.Nonempty) → (ff ≠ bb)))))) → (∀
            (cf : LatticeCell), (cf ∈ U.cells) → ((if i = (0 : Fin (3 : ℕ)) then cf = z - (1 :
            LatticeCell) else cf = z) → (∀ (cb : LatticeCell), (cb ∈ V.cells) → ((if i = (0 : Fin
            (3 : ℕ)) then cb = z else cb = z - (1 : LatticeCell)) → ((a ≠ b) → (((PP.tile a, g) ∈
            tiles.zip hs) → (((PP.tile b, k) ∈ reverseTiles.zip reverseHs) → ((AncestorOdometer
            Ci.1.1 C0.1.1 (PP.tile a) T g h) → ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile b) T' k
            h') → (((if i = 0 then (P.q₁ : Int) else P.q₂) < (x-u).im) → (((x-u).im < P.q) → (∃
            (aa bb : TilingLattice Ci) (gg kk : PartialOdometer), aa ≠ bb ∧ (PP.tile aa, gg) ∈
            tiles.zip hs ∧ (PP.tile bb, kk) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer
            Ci.1.1 C0.1.1 (PP.tile aa) T gg h ∧ AncestorOdometer Ci.1.1 C0.1.1 (PP.tile bb) T' kk
            h' ∧ (∃ w, (w = x ∨ w = x - ⟨0, 1⟩) ∧ {w, w + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile aa) ∧
            {w, w + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile bb)) ∧ ((x ∈ (PP.tile aa).cells ∧ x - 1 -
            ⟨0, 1⟩ ∈ (PP.tile bb).cells) ∨ (x - 1 ∈ (PP.tile aa).cells ∧ x - ⟨0, 1⟩ ∈ (PP.tile
            bb).cells) ∨ (x - 1 - ⟨0, 1⟩ ∈ (PP.tile aa).cells ∧ x ∈ (PP.tile bb).cells) ∨ (x -
            ⟨0, 1⟩ ∈ (PP.tile aa).cells ∧ x - 1 ∈ (PP.tile
            bb).cells))))))))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro P C0 Ci i hsmall T T' h h' u hc' Rminus Rplus tiles reverseTiles hs reverseHs hRm hRp
      hcontain hcontain' hedges PP tileAt chart x hxr hxl vertical_edge_cells lower_lt_q z z_low
      z_other z_incident hz_re hz_low hz_high U V g k hEdgeU hEdgeV a b hUa hVb U_edge V_edge
      T_bounds T'_bounds indexed_edge cross_ne cf hcf hcfSide cb hcb hcbSide hab hAzip hBzip
      hAanc hBanc hlower hupper
  obtain ⟨ap, bp, gp, kp, habp, hapz, hbpz, hapA, hbpA, hapE, hbpE⟩ :=
    indexed_edge x hxr (le_of_lt hlower) hupper
  have hAroot : (PP.tile ap).cells ⊆ T.cells := hcontain (PP.tile ap) gp hapz hapA
  have hBroot : (PP.tile bp).cells ⊆ T'.cells := hcontain' (PP.tile bp) kp hbpz hbpA
  have hAat : if i = 0 then x - 1 ∈ (PP.tile ap).cells else
      x ∈ (PP.tile ap).cells := by
    have hs := vertical_edge_cells (PP.tile ap) x hapE
    rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
    · subst i
      rcases hs with hx | hxleft
      · have hbnd := T_bounds x (hAroot hx)
        have hxq : (x-u).re = P.q := by simpa using hxr
        have hbad : P.q < P.q := by simpa [hxq] using hbnd.2.1
        exact (lt_irrefl _ hbad).elim
      · exact hxleft
    · subst i
      rcases hs with hx | hxleft
      · exact hx
      · have hbnd := T_bounds (x-1) (hAroot hxleft)
        have hx0 : (x-u).re = 0 := by simpa using hxr
        have hxstep : ((x-1)-u).re = (x-u).re - 1 := by
          simp [Zsqrtd.re_sub]
          omega
        have hbad : 0 ≤ -1 := by simpa [hxstep, hx0] using hbnd.1
        omega
  have hBat : if i = 0 then x ∈ (PP.tile bp).cells else
      x - 1 ∈ (PP.tile bp).cells := by
    have hs := vertical_edge_cells (PP.tile bp) x hbpE
    rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
    · subst i
      rcases hs with hx | hxleft
      · exact hx
      · have hbnd := T'_bounds (x-1) (hBroot hxleft)
        have hxq : (x-u).re = P.q := by simpa using hxr
        have hxstep : ((x-1)-(u+⟨(P.q:Int),(P.q₁:Int)⟩)).re = -1 := by
          simp [Zsqrtd.re_sub, Zsqrtd.re_add]
          have hxq' : x.re-u.re=P.q := by simpa [Zsqrtd.re_sub] using hxq
          omega
        have hbad : 0 ≤ -1 := by simpa [hxstep] using hbnd.1
        omega
    · subst i
      rcases hs with hx | hxleft
      · have hbnd := T'_bounds x (hBroot hx)
        have hx0 : (x-u).re = 0 := by simpa using hxr
        have hxstep : (x-(u+⟨-(P.q:Int),(P.q₂:Int)⟩)).re = P.q := by
          simp [Zsqrtd.re_sub, Zsqrtd.re_add]
          have hx0' : x.re-u.re=0 := by simpa [Zsqrtd.re_sub] using hx0
          omega
        have hbad : P.q < P.q := by simpa [hxstep] using hbnd.2.1
        exact (lt_irrefl _ hbad).elim
      · exact hxleft
  have hcfBelow :
      (if i = 0 then x - 1 - ⟨0,1⟩ ∈ (PP.tile a).cells
        else x - ⟨0,1⟩ ∈ (PP.tile a).cells) := by
    rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
    · subst i
      have hside : cf = z - 1 := by simpa using hcfSide
      have hbelow : z = x - ⟨0,1⟩ := z_other (by omega)
      have hcf' : cf = x - 1 - ⟨0,1⟩ := by rw [hside,hbelow]; abel
      have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
      simpa [hcf'] using hcfA
    · subst i
      have hside : cf = z := by simpa using hcfSide
      have hbelow : z = x - ⟨0,1⟩ := z_other (by omega)
      have hcf' : cf = x - ⟨0,1⟩ := by rw [hside,hbelow]
      have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
      simpa [hcf'] using hcfA
  have hcbBelow :
      (if i = 0 then x - ⟨0,1⟩ ∈ (PP.tile b).cells
        else x - 1 - ⟨0,1⟩ ∈ (PP.tile b).cells) := by
    rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
    · subst i
      have hside : cb = z := by simpa using hcbSide
      have hbelow : z = x - ⟨0,1⟩ := z_other (by omega)
      have hcb' : cb = x - ⟨0,1⟩ := by rw [hside,hbelow]
      have hcbB : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
      simpa [hcb'] using hcbB
    · subst i
      have hside : cb = z - 1 := by simpa using hcbSide
      have hbelow : z = x - ⟨0,1⟩ := z_other (by omega)
      have hcb' : cb = x - 1 - ⟨0,1⟩ := by rw [hside,hbelow]; abel
      have hcbB : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
      simpa [hcb'] using hcbB
  rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
  · subst i
    have hfour := AffineTriangularNoFourfoldCellOwners PP tileAt chart x
      bp ap a b (by simpa using hBat) (by simpa using hAat)
      (by simpa using hcfBelow) (by simpa using hcbBelow)
    have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
    have hbpNon : (PP.tile bp).cells.Nonempty := ⟨x, by simpa using hBat⟩
    have hapNon : (PP.tile ap).cells.Nonempty := ⟨x-1, by simpa using hAat⟩
    have hrepetition : ap = a ∨ bp = b := by
      rcases hfour with h01 | h02 | h03 | h12 | h13 | h23
      · exact False.elim (habp h01.symm)
      · have hne := cross_ne a bp g kp hAzip hbpz hAanc hbpA ⟨cf, hcfA⟩
        exact False.elim (hne h02.symm)
      · exact Or.inr h03
      · exact Or.inl h12
      · have hne := cross_ne ap b gp k hapz hBzip hapA hBanc hapNon
        exact False.elim (hne h13)
      · exact False.elim (hab h23)
    refine ⟨ap, bp, gp, kp, habp, hapz, hbpz, hapA, hbpA,
      ⟨x, Or.inl rfl, hapE, hbpE⟩, ?_⟩
    rcases hrepetition with hfa | hbb
    · have hxOpp : x - 1 - ⟨0,1⟩ ∈ (PP.tile ap).cells := by
        simpa [hfa] using hcfBelow
      exact Or.inr (Or.inr (Or.inl ⟨hxOpp, by simpa using hBat⟩))
    · have hxOpp : x - ⟨0,1⟩ ∈ (PP.tile bp).cells := by
        simpa [hbb] using hcbBelow
      exact Or.inr (Or.inl ⟨by simpa using hAat, hxOpp⟩)
  · subst i
    have hfour := AffineTriangularNoFourfoldCellOwners PP tileAt chart x
      ap bp b a (by simpa using hAat) (by simpa using hBat)
      (by simpa using hcbBelow) (by simpa using hcfBelow)
    have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
    have hbpNon : (PP.tile bp).cells.Nonempty := ⟨x-1, by simpa using hBat⟩
    have hapNon : (PP.tile ap).cells.Nonempty := ⟨x, by simpa using hAat⟩
    have hrepetition : ap = a ∨ bp = b := by
      rcases hfour with h01 | h02 | h03 | h12 | h13 | h23
      · exact False.elim (habp h01)
      · have hne := cross_ne ap b gp k hapz hBzip hapA hBanc hapNon
        exact False.elim (hne h02)
      · exact Or.inl h03
      · exact Or.inr h12
      · have hne := cross_ne a bp g kp hAzip hbpz hAanc hbpA ⟨cf, hcfA⟩
        exact False.elim (hne h13.symm)
      · exact False.elim (hab h23.symm)
    refine ⟨ap, bp, gp, kp, habp, hapz, hbpz, hapA, hbpA,
      ⟨x, Or.inl rfl, hapE, hbpE⟩, ?_⟩
    rcases hrepetition with hfa | hbb
    · have hxOpp : x - ⟨0,1⟩ ∈ (PP.tile ap).cells := by
        simpa [hfa] using hcfBelow
      exact Or.inr (Or.inr (Or.inr ⟨hxOpp, by simpa using hBat⟩))
    · have hxOpp : x - 1 - ⟨0,1⟩ ∈ (PP.tile bp).cells := by
        simpa [hbb] using hcbBelow
      exact Or.inl ⟨by simpa using hAat, hxOpp⟩

private theorem hxAt721 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              (x - u).re = P.q → (x - u).im = P.q₁ → x = u + ⟨(P.q : Int), (P.q₁ : Int)⟩
    ) := by
  classical
  intro P u x hxre hxim
  ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add,
    Zsqrtd.im_add] at * <;> omega

private theorem hce :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              x = u + ⟨(P.q : Int), (P.q₁ : Int)⟩ →
                ((P.q₁ - 1 : Nat) : Int) = (P.q₁ : Int) - 1 →
                  x - ⟨0, 1⟩ = u + ⟨(P.q : Int), 0⟩ + ⟨0, ((P.q₁ - 1 : Nat) : Int)⟩
    ) := by
  classical
  intro P u x hx hnatcast
  rw [hx]
  ext <;> simp [hnatcast, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_sub, Zsqrtd.im_sub]; omega

private theorem hEcellAt735 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (Rminus : ProtoTile), ∀ (x :
            GaussianInt), (Rminus.cells = (TileTranslation (FordTile (if (0 : Fin (3 : ℕ)) = (0 :
            Fin (3 : ℕ)) then P.q₁ else P.q₂)) (u + if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then
            (⟨(↑P.q : ℤ), (0 : ℤ)⟩ : GaussianInt) else (⟨(0 : ℤ), (↑P.q : ℤ)⟩ :
            GaussianInt))).cells) → ((x - ⟨0,1⟩ = (u + ⟨(P.q : Int),0⟩) + ⟨0, ((P.q₁ - 1 : Nat) :
            Int)⟩) → ((u + (⟨(↑P.q : ℤ), (0 : ℤ)⟩ : GaussianInt) + (⟨(↑(0 : ℕ) : ℤ), (↑(P.q₁ - (1
            : ℕ)) : ℤ)⟩ : GaussianInt) ∈ (TileTranslation (FordTile P.q₁) (u + (⟨(↑P.q : ℤ), (0 :
            ℤ)⟩ : GaussianInt))).cells) → (x - ⟨0,1⟩ ∈ Rminus.cells))) ) := by
  classical
  intro P u Rminus x hRm hce hEtrans
  rw [hRm, hce]
  exact hEtrans

private theorem hdisETAt740 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → (∀ (Rminus : ProtoTile), (∀ (n : Nat), ∀
            (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt), (w.re + n ≤ v.re) → (Disjoint
            (TileTranslation (FordTile n) w).cells (TileTranslation (FordTile m) v).cells)) →
            ((Rminus.cells = (TileTranslation (FordTile (if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ))
            then P.q₁ else P.q₂)) (u + if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q :
            ℤ), (0 : ℤ)⟩ : GaussianInt) else (⟨(0 : ℤ), (↑P.q : ℤ)⟩ : GaussianInt))).cells) →
            (Disjoint T.cells Rminus.cells))) ) := by
  classical
  intro P T u hc Rminus ford_disjoint_re hRm
  rw [hc, hRm]
  apply ford_disjoint_re
  simp [Zsqrtd.re_add]

private theorem hdisET'At744 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), ∀ (Rminus :
            ProtoTile), (∀ (n : Nat), ∀ (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt),
            (w.im + n ≤ v.im) → (Disjoint (TileTranslation (FordTile n) w).cells (TileTranslation
            (FordTile m) v).cells)) → ((T'.cells = (TileTranslation (FordTile P.q) (u + if (0 :
            Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else
            (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells) → ((Rminus.cells =
            (TileTranslation (FordTile (if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then P.q₁ else
            P.q₂)) (u + if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (0 : ℤ)⟩ :
            GaussianInt) else (⟨(0 : ℤ), (↑P.q : ℤ)⟩ : GaussianInt))).cells) → (Disjoint
            Rminus.cells T'.cells))) ) := by
  classical
  intro P T' u Rminus ford_disjoint_im hc' hRm
  rw [hRm, hc']
  apply ford_disjoint_im
  simp [Zsqrtd.im_add]

private theorem he_ne_aAt748 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (U : ProtoTile), ∀ (a : ↥(TilingLattice
            Ci)), (PP.tile a = U) → ((U.cells ⊆ T.cells) → (∀ (cf : LatticeCell), (cf ∈ U.cells)
            → (∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rminus) → ((Disjoint T.cells
            Rminus.cells) → (e ≠ a))))) ) := by
  classical
  intro Ci T Rminus PP U a hUa U_in_T cf hcf e he hdisET heq
  have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  have hcfE : cf ∈ Rminus.cells := by
    rw [← he]
    simpa [heq] using hcfA
  exact (Finset.disjoint_left.mp hdisET) (U_in_T hcf) hcfE

private theorem he_ne_bAt755 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (V : ProtoTile), ∀ (b : ↥(TilingLattice
            Ci)), (PP.tile b = V) → ((V.cells ⊆ T'.cells) → (∀ (cb : LatticeCell), (cb ∈ V.cells)
            → (∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rminus) → ((Disjoint Rminus.cells
            T'.cells) → (e ≠ b))))) ) := by
  classical
  intro Ci T' Rminus PP V b hVb V_in_T' cb hcb e he hdisET' heq
  have hcbB : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
  have hcbE : cb ∈ Rminus.cells := by
    rw [← he]
    simpa [heq] using hcbB
  exact (Finset.disjoint_left.mp hdisET') hcbE (V_in_T' hcb)

private theorem hmcAt766 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              x = u + ⟨(P.q : Int), (P.q₁ : Int)⟩ →
                ((P.q₁ - 1 : Nat) : Int) = (P.q₁ : Int) - 1 →
                  let m : GaussianInt := x - 1 - ⟨0, 1⟩
                  ((P.q - 1 : Nat) : Int) = (P.q : Int) - 1 →
                    m = u + ⟨((P.q - 1 : Nat) : Int), ((P.q₁ - 1 : Nat) : Int)⟩
    ) := by
  classical
  intro P u x hx hnatcast m hqcast
  ext <;> simp [m, hx, hqcast, hnatcast, Zsqrtd.re_sub,
    Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add] <;> omega

private theorem hmTAt772 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → (∀ (x : GaussianInt),
        let m : GaussianInt := x - 1 - ⟨0,1⟩
        (m = u + ⟨((P.q - 1 : Nat) : Int), ((P.q₁ - 1 : Nat) : Int)⟩) → ((u + (⟨(↑(P.q - (1 : ℕ))
            : ℤ), (↑(P.q₁ - (1 : ℕ)) : ℤ)⟩ : GaussianInt) ∈ (TileTranslation (FordTile P.q)
            u).cells) → (m ∈ T.cells))) ) := by
  classical
  intro P T u hc x m hmc hmTtrans
  rw [hc, hmc]
  exact hmTtrans

private theorem hm_notE :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (x : GaussianInt), (Disjoint T.cells
            Rminus.cells) → (
        let m : GaussianInt := x - 1 - ⟨0,1⟩
        (m ∈ T.cells) → (m ∉ Rminus.cells)) ) := by
  classical
  intro T Rminus x hdisET m hmT hmE
  exact (Finset.disjoint_left.mp hdisET) hmT hmE

private theorem ht_ne_eAt779 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (Rminus : ProtoTile), ∀ (PP : PeriodicTileComplex ↥(TilingLattice
            Ci)), ∀ (x : GaussianInt), ∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rminus) → (
        let m : GaussianInt := x - 1 - ⟨0,1⟩
        ∀ (t : ↥(TilingLattice Ci)), (m ∈ (PP.tile t).cells) → ((m ∉ Rminus.cells) → (t ≠ e))) )
            := by
  classical
  intro Ci Rminus PP x e he m t ht hm_notE hte
  have hmt : m ∈ (PP.tile e).cells := by simpa [hte] using ht
  have hmE : m ∈ Rminus.cells := by simpa [he] using hmt
  exact hm_notE hmE

private theorem ht_ne_bAt784 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), (Disjoint T.cells T'.cells) →
            (∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V :
            ProtoTile), ∀ (b : ↥(TilingLattice Ci)), (PP.tile b = V) → ((V.cells ⊆ T'.cells) → (
        let m : GaussianInt := x - 1 - ⟨0,1⟩
        (m ∈ T.cells) → (∀ (t : ↥(TilingLattice Ci)), (m ∈ (PP.tile t).cells) → (t ≠ b))))) ) := by
  classical
  intro Ci T T' hdis PP x V b hVb V_in_T' m hmT t ht htb
  have hmb : m ∈ (PP.tile b).cells := by simpa [htb] using ht
  have hmV : m ∈ V.cells := by simpa [hVb] using hmb
  exact (Finset.disjoint_left.mp hdis) hmT (V_in_T' hmV)

private theorem hxbAt789 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V : ProtoTile), ∀
            (b : ↥(TilingLattice Ci)), (PP.tile b = V) → (∀ (cb : LatticeCell), (cb ∈ V.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (0 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x) → ((if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then cb = z else cb = z -
            (1 : LatticeCell)) → (((x - u).im = if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then
            (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x ∈ (PP.tile b).cells))))) ) := by
  classical
  intro P Ci u PP x V b hVb cb hcb z z_low hcbSide hlow
  have hside : cb = x := by simpa [z_low hlow] using hcbSide
  have hcb' : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
  simpa [hside] using hcb'

private theorem hxaAt793 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀
            (a : ↥(TilingLattice Ci)), (PP.tile a = U) → (∀ (cf : LatticeCell), (cf ∈ U.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (0 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x) → ((if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then cf = z - (1 :
            LatticeCell) else cf = z) → (((x - u).im = if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ))
            then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x - 1 ∈ (PP.tile a).cells))))) ) := by
  classical
  intro P Ci u PP x U a hUa cf hcf z z_low hcfSide hlow
  have hside : cf = x - 1 := by simpa [z_low hlow] using hcfSide
  have hcf' : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  simpa [hside] using hcf'

private theorem hrepeatAt799 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (a : ↥(TilingLattice Ci)), ∀ (b : ↥(TilingLattice Ci)), (a ≠ b) →
            (∀ (e : ↥(TilingLattice Ci)), (e ≠ a) → ((e ≠ b) → (∀ (t : ↥(TilingLattice Ci)), (t ≠
            e) → ((t ≠ b) → ((b = a ∨ b = t ∨ b = e ∨ a = t ∨ a = e ∨ t = e) → (a = t)))))) ) := by
  classical
  intro Ci a b hab e he_ne_a he_ne_b t ht_ne_e ht_ne_b hfour
  rcases hfour with h01 | h02 | h03 | h12 | h13 | h23
  · exact False.elim (hab h01.symm)
  · exact False.elim (ht_ne_b h02.symm)
  · exact False.elim (he_ne_b h03.symm)
  · exact h12
  · exact False.elim (he_ne_a h13.symm)
  · exact False.elim (ht_ne_e h23)

private theorem hxAt816 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              (x - u).re = 0 → (x - u).im = P.q₂ → x = u + ⟨0, (P.q₂ : Int)⟩
    ) := by
  classical
  intro P u x hxre hxim
  ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add,
    Zsqrtd.im_add] at * <;> omega

private theorem hmcAt823 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              x = u + ⟨0, (P.q₂ : Int)⟩ →
                ((P.q₂ - 1 : Nat) : Int) = (P.q₂ : Int) - 1 →
                  let m : GaussianInt := x - ⟨0, 1⟩
                  m = u + ⟨0, ((P.q₂ - 1 : Nat) : Int)⟩
    ) := by
  classical
  intro P u x hx hncast m
  ext <;> simp [m, hx, hncast, Zsqrtd.re_sub, Zsqrtd.im_sub,
    Zsqrtd.re_add, Zsqrtd.im_add]; omega

private theorem hncAt832 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              x = u + ⟨0, (P.q₂ : Int)⟩ →
                ((P.q₂ - 1 : Nat) : Int) = (P.q₂ : Int) - 1 →
                  let n : GaussianInt := x - 1 - ⟨0, 1⟩
                  n =
                    u + ⟨-(P.q₂ : Int), 0⟩ +
                      ⟨((P.q₂ - 1 : Nat) : Int), ((P.q₂ - 1 : Nat) : Int)⟩
    )
            := by
  classical
  intro P u x hx hncast' n
  ext <;> simp [n, hx, hncast', Zsqrtd.re_sub, Zsqrtd.im_sub,
    Zsqrtd.re_add, Zsqrtd.im_add] <;> omega

private theorem hdisETAt843 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → (∀ (Rplus : ProtoTile), (∀ (n : Nat), ∀
            (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt), (w.re + n ≤ v.re) → (Disjoint
            (TileTranslation (FordTile n) w).cells (TileTranslation (FordTile m) v).cells)) →
            ((Rplus.cells = (TileTranslation (FordTile (if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ))
            then P.q₁ else P.q₂)) (u + if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q₂ :
            ℤ), (↑P.q : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩ : GaussianInt))).cells)
            → (Disjoint Rplus.cells T.cells))) ) := by
  classical
  intro P T u hc Rplus ford_disjoint_re hRp
  rw [hRp, hc]
  apply ford_disjoint_re
  simp [Zsqrtd.re_add]

private theorem hdisET'At847 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), ∀ (Rplus :
            ProtoTile), (∀ (n : Nat), ∀ (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt),
            (w.im + n ≤ v.im) → (Disjoint (TileTranslation (FordTile n) w).cells (TileTranslation
            (FordTile m) v).cells)) → ((T'.cells = (TileTranslation (FordTile P.q) (u + if (1 :
            Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else
            (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells) → ((Rplus.cells =
            (TileTranslation (FordTile (if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then P.q₁ else
            P.q₂)) (u + if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q₂ : ℤ), (↑P.q : ℤ)⟩
            : GaussianInt) else (⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩ : GaussianInt))).cells) → (Disjoint
            Rplus.cells T'.cells))) ) := by
  classical
  intro P T' u Rplus ford_disjoint_im hc' hRp
  rw [hRp, hc']
  apply ford_disjoint_im
  simp [Zsqrtd.im_add]

private theorem he_ne_aAt851 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (U : ProtoTile), ∀ (a : ↥(TilingLattice
            Ci)), (PP.tile a = U) → ((U.cells ⊆ T.cells) → (∀ (cf : LatticeCell), (cf ∈ U.cells)
            → (∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rplus) → ((Disjoint Rplus.cells T.cells)
            → (e ≠ a))))) ) := by
  classical
  intro Ci T Rplus PP U a hUa U_in_T cf hcf e he hdisET heq
  have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  have hcfE : cf ∈ Rplus.cells := by
    rw [← he]
    simpa [heq] using hcfA
  exact (Finset.disjoint_left.mp hdisET) hcfE (U_in_T hcf)

private abbrev he_ne_bAt858 :=
  ApollonianSuperharmonic.EdgeSectorGeometry.he_ne_bAt755

private theorem ht_ne_eAt866 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt),
        let m : GaussianInt := x - ⟨0,1⟩
        (m ∈ T.cells) → (∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rplus) → ((Disjoint
            Rplus.cells T.cells) → (∀ (t : ↥(TilingLattice Ci)), (m ∈ (PP.tile t).cells) → (t ≠
            e)))) ) := by
  classical
  intro Ci T Rplus PP x m hmT e he hdisET t ht hte
  have hmt : m ∈ (PP.tile e).cells := by simpa [hte] using ht
  have hmE : m ∈ Rplus.cells := by simpa [he] using hmt
  exact (Finset.disjoint_left.mp hdisET) hmE hmT

private theorem ht_ne_bAt871 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), (Disjoint T.cells T'.cells) →
            (∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V :
            ProtoTile), ∀ (b : ↥(TilingLattice Ci)), (PP.tile b = V) → ((V.cells ⊆ T'.cells) → (
        let m : GaussianInt := x - ⟨0,1⟩
        (m ∈ T.cells) → (∀ (t : ↥(TilingLattice Ci)), (m ∈ (PP.tile t).cells) → (t ≠ b))))) ) := by
  classical
  intro Ci T T' hdis PP x V b hVb V_in_T' m hmT t ht htb
  have hmb : m ∈ (PP.tile b).cells := by simpa [htb] using ht
  have hmV : m ∈ V.cells := by simpa [hVb] using hmb
  exact (Finset.disjoint_left.mp hdis) hmT (V_in_T' hmV)

private theorem hxaAt876 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀
            (a : ↥(TilingLattice Ci)), (PP.tile a = U) → (∀ (cf : LatticeCell), (cf ∈ U.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (1 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x) → ((if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then cf = z - (1 :
            LatticeCell) else cf = z) → (((x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ))
            then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x ∈ (PP.tile a).cells))))) ) := by
  classical
  intro P Ci u PP x U a hUa cf hcf z z_low hcfSide hlow
  have hside : cf = x := by simpa [z_low hlow] using hcfSide
  have hcf' : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  simpa [hside] using hcf'

private theorem hxbAt880 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V : ProtoTile), ∀
            (b : ↥(TilingLattice Ci)), (PP.tile b = V) → (∀ (cb : LatticeCell), (cb ∈ V.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (1 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x) → ((if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then cb = z else cb = z -
            (1 : LatticeCell)) → (((x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then
            (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x - 1 ∈ (PP.tile b).cells))))) ) := by
  classical
  intro P Ci u PP x V b hVb cb hcb z z_low hcbSide hlow
  have hside : cb = x - 1 := by simpa [z_low hlow] using hcbSide
  have hcb' : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
  simpa [hside] using hcb'

private theorem hrepeatAt886 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (a : ↥(TilingLattice Ci)), ∀ (b : ↥(TilingLattice Ci)), (a ≠ b) →
            (∀ (e : ↥(TilingLattice Ci)), (e ≠ a) → ((e ≠ b) → (∀ (t : ↥(TilingLattice Ci)), (t ≠
            e) → ((t ≠ b) → ((a = b ∨ a = e ∨ a = t ∨ b = e ∨ b = t ∨ e = t) → (a = t)))))) ) := by
  classical
  intro Ci a b hab e he_ne_a he_ne_b t ht_ne_e ht_ne_b hfour
  rcases hfour with h01 | h02 | h03 | h12 | h13 | h23
  · exact False.elim (hab h01)
  · exact False.elim (he_ne_a h02.symm)
  · exact h03
  · exact False.elim (he_ne_b h12.symm)
  · exact False.elim (ht_ne_b h13.symm)
  · exact False.elim (ht_ne_e h23.symm)

private theorem hxAt909 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt), (x.re = u.re + P.q)
            → ((x.im = u.im + P.q) → (x = u + ⟨(P.q : Int), (P.q : Int)⟩)) ) := by
  classical
  intro P u x hxre'' hxim''
  ext
  · simp only [Zsqrtd.re_add]
    omega
  · simp only [Zsqrtd.im_add]
    omega

private theorem hncAt920 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt), (x.re = u.re + P.q)
            → ((x.im = u.im + P.q) → ((((P.q₁ - 1 : Nat) : Int) = (P.q₁ : Int) - 1) → (((P.q₁ :
            Int) + P.q₂ = P.q) → (
        let n : GaussianInt := x - 1
        n = (u + ⟨(P.q₂ : Int), (P.q : Int)⟩) + ⟨((P.q₁ - 1 : Nat) : Int), 0⟩)))) ) := by
  classical
  intro P u x hxre'' hxim'' hq1cast hqsum n
  dsimp only [n]
  apply Zsqrtd.ext_iff.mpr
  constructor
  · simp only [Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_one]
    rw [hxre'', hq1cast]
    rw [← hqsum]
    ring
  · simp only [Zsqrtd.im_sub, Zsqrtd.im_add, Zsqrtd.im_one,
      ]
    rw [hxim'']
    ring

private theorem hdisETAt940 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → (∀ (Rplus : ProtoTile), (∀ (n : Nat), ∀
            (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt), (w.im + n ≤ v.im) → (Disjoint
            (TileTranslation (FordTile n) w).cells (TileTranslation (FordTile m) v).cells)) →
            ((Rplus.cells = (TileTranslation (FordTile (if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ))
            then P.q₁ else P.q₂)) (u + if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q₂ :
            ℤ), (↑P.q : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩ : GaussianInt))).cells)
            → (Disjoint T.cells Rplus.cells))) ) := by
  classical
  intro P T u hc Rplus ford_disjoint_im hRp
  rw [hc, hRp]
  apply ford_disjoint_im
  simp [Zsqrtd.im_add]

private theorem hdisET'At944 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (T' : ProtoTile),
            ∀ (u : GaussianInt),
              ∀ (Rplus : ProtoTile),
                (∀ (n : Nat),
                    ∀ (m : Nat),
                      ∀ (w : GaussianInt),
                        ∀ (v : GaussianInt),
                          w.re + n ≤ v.re →
                            Disjoint (TileTranslation (FordTile n) w).cells
                              (TileTranslation (FordTile m) v).cells) →
                  T'.cells =
                      (TileTranslation (FordTile P.q)
                          (u +
                            if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then
                              (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt)
                            else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells →
                    Rplus.cells =
                        (TileTranslation
                            (FordTile
                              (if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then P.q₁
                              else P.q₂))
                            (u +
                              if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then
                                (⟨(↑P.q₂ : ℤ), (↑P.q : ℤ)⟩ : GaussianInt)
                              else (⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩ : GaussianInt))).cells →
                      (P.q₁ : Int) + P.q₂ = P.q → Disjoint Rplus.cells T'.cells
    ) := by
  classical
  intro P T' u Rplus ford_disjoint_re hc' hRp hqsum
  have hgap :
      (u + ⟨(P.q₂ : Int), (P.q : Int)⟩).re + P.q₁ ≤
        (u + ⟨(P.q : Int), (P.q₁ : Int)⟩).re := by
    simp only [Zsqrtd.re_add]
    rw [← hqsum]
    omega
  have hford := ford_disjoint_re P.q₁ P.q
    (u + ⟨(P.q₂ : Int), (P.q : Int)⟩)
    (u + ⟨(P.q : Int), (P.q₁ : Int)⟩) hgap
  simpa [hRp, hc'] using hford

private theorem hq2lt :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (0 : ℕ) < P.q₁ → ((P.q₁ - 1 : Nat) : Int) = (P.q₁ : Int) - 1 → P.q₂ < P.q
    )
            := by
  classical
  intro P hrpos hq1cast
  rw [P.sum_q]
  omega

private theorem hxroot :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt), (x = u + ⟨(P.q :
            Int), (P.q : Int)⟩) → (((P.q₁ : Int) + P.q₂ = P.q) → (x = (u + ⟨(P.q : Int), (P.q₁ :
            Int)⟩) + ⟨0, (P.q₂ : Int)⟩)) ) := by
  classical
  intro P u x hx hqsum
  rw [hx]
  apply Zsqrtd.ext_iff.mpr
  constructor
  · simp [Zsqrtd.re_add]
  · simp only [Int.reduceNeg, Zsqrtd.im_add]
    rw [← hqsum]
    ring

private theorem hxT' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
            (T'.cells = (TileTranslation (FordTile P.q) (u + if (0 : Fin (3 : ℕ)) = (0 : Fin (3 :
            ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ :
            GaussianInt))).cells) → ((x = (u + ⟨(P.q : Int), (P.q₁ : Int)⟩) + ⟨0, (P.q₂ : Int)⟩)
            → ((u + (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) + (⟨(↑(0 : ℕ) : ℤ), (↑P.q₂ : ℤ)⟩ :
            GaussianInt) ∈ (TileTranslation (FordTile P.q) (u + (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ :
            GaussianInt))).cells) → (x ∈ T'.cells))) ) := by
  classical
  intro P T' u x hc' hxroot hrootCell
  rw [hc']
  simp only []
  simpa [GaussianTranslation, add_comm, hxroot] using hrootCell

private theorem ht_ne_eAt974 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T' : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (e : ↥(TilingLattice
            Ci)), (PP.tile e = Rplus) → ((Disjoint Rplus.cells T'.cells) → ((x ∈ T'.cells) → (∀
            (t : ↥(TilingLattice Ci)), (x ∈ (PP.tile t).cells) → (t ≠ e)))) ) := by
  classical
  intro Ci T' Rplus PP x e he hdisET' hxT' t ht hte
  have hmt : x ∈ (PP.tile e).cells := by simpa [hte] using ht
  have hxE : x ∈ Rplus.cells := by simpa [he] using hmt
  exact (Finset.disjoint_left.mp hdisET') hxE hxT'

private theorem ht_ne_aAt979 :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h :
            PartialOdometer), (Disjoint T.cells T'.cells) → (∀ (tiles : List ProtoTile), ∀ (hs :
            List PartialOdometer), (∀ (U : ProtoTile), ∀ (g : PartialOdometer), (U, g) ∈
            tiles.zip hs → AncestorOdometer Ci.1.1 C0.1.1 U T g h → U.cells ⊆ T.cells) → (∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (g :
            PartialOdometer), ∀ (a : ↥(TilingLattice Ci)), ((PP.tile a, g) ∈ tiles.zip hs) →
            ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile a) T g h) → ((x ∈ T'.cells) → (∀ (t :
            ↥(TilingLattice Ci)), (x ∈ (PP.tile t).cells) → (t ≠ a)))))) ) := by
  classical
  intro C0 Ci T T' h hdis tiles hs hcontain PP x g a hAzip hAanc hxT' t ht hta
  have hma : x ∈ (PP.tile a).cells := by simpa [hta] using ht
  exact (Finset.disjoint_left.mp hdis)
    (hcontain (PP.tile a) g hAzip hAanc hma) hxT'

private theorem he_ne_aAt984 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀
            (a : ↥(TilingLattice Ci)), (PP.tile a = U) → ((U.cells ⊆ T.cells) → (∀ (cf :
            LatticeCell), (cf ∈ U.cells) → (
        let n : GaussianInt := x - 1
        ∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rplus) → ((n ∈ Rplus.cells) → ((n ∈ (PP.tile
            e).cells) → ((Disjoint T.cells Rplus.cells) → (e ≠ a))))))) ) := by
  classical
  intro Ci T Rplus PP x U a hUa U_in_T cf hcf n e he hEcell hEidx hdisET heq
  have hcfA : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  have hcfE : cf ∈ Rplus.cells := by
    rw [← he]
    simpa [heq] using hcfA
  have hnA : n ∈ (PP.tile a).cells := by simpa [heq] using hEidx
  have hnU : n ∈ U.cells := by simpa [hUa] using hnA
  exact (Finset.disjoint_left.mp hdisET) (U_in_T hnU) hEcell

private theorem he_ne_bAt993 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T' : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V : ProtoTile), ∀
            (b : ↥(TilingLattice Ci)), (PP.tile b = V) → ((V.cells ⊆ T'.cells) → (∀ (cb :
            LatticeCell), (cb ∈ V.cells) → (
        let n : GaussianInt := x - 1
        ∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rplus) → ((n ∈ Rplus.cells) → ((n ∈ (PP.tile
            e).cells) → ((Disjoint Rplus.cells T'.cells) → (e ≠ b))))))) ) := by
  classical
  intro Ci T' Rplus PP x V b hVb V_in_T' cb hcb n e he hEcell hEidx hdisET' heq
  have hcbB : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
  have hcbE : cb ∈ Rplus.cells := by
    rw [← he]
    simpa [heq] using hcbB
  have hnB : n ∈ (PP.tile b).cells := by simpa [heq] using hEidx
  have hnV : n ∈ V.cells := by simpa [hVb] using hnB
  exact (Finset.disjoint_left.mp hdisET') hEcell (V_in_T' hnV)

private theorem hxaAt1002 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀
            (a : ↥(TilingLattice Ci)), (PP.tile a = U) → (∀ (cf : LatticeCell), (cf ∈ U.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (0 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ((¬(x - u).im = if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((if (0 : Fin (3 : ℕ)) = (0 : Fin
            (3 : ℕ)) then cf = z - (1 : LatticeCell) else cf = z) → ((¬(x - u).im = if (0 : Fin
            (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x - 1 - ⟨0,1⟩ ∈
            (PP.tile a).cells))))) ) := by
  classical
  intro P Ci u PP x U a hUa cf hcf z z_other hcfSide hlow
  have hside : cf = z - 1 := by simpa using hcfSide
  have hside' : cf = x - 1 - ⟨0,1⟩ := by
    rw [hside, z_other (by omega)]
    abel
  have hcf' : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  simpa [hside'] using hcf'

private theorem hxbAt1009 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V : ProtoTile), ∀
            (b : ↥(TilingLattice Ci)), (PP.tile b = V) → (∀ (cb : LatticeCell), (cb ∈ V.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (0 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ((¬(x - u).im = if (0 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((if (0 : Fin (3 : ℕ)) = (0 : Fin
            (3 : ℕ)) then cb = z else cb = z - (1 : LatticeCell)) → ((¬(x - u).im = if (0 : Fin
            (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x - ⟨0,1⟩ ∈
            (PP.tile b).cells))))) ) := by
  classical
  intro P Ci u PP x V b hVb cb hcb z z_other hcbSide hlow
  have hside : cb = z := by simpa using hcbSide
  have hside' : cb = x - ⟨0,1⟩ := by rw [hside, z_other (by omega)]
  have hcb' : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
  simpa [hside'] using hcb'

private theorem hrepeatAt1016 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (a : ↥(TilingLattice Ci)), ∀ (b : ↥(TilingLattice Ci)), (a ≠ b) →
            (∀ (e : ↥(TilingLattice Ci)), ∀ (t : ↥(TilingLattice Ci)), (t ≠ e) → ((t ≠ a) → ((e ≠
            a) → ((e ≠ b) → ((t = e ∨ t = a ∨ t = b ∨ e = a ∨ e = b ∨ a = b) → (b = t)))))) ) := by
  classical
  intro Ci a b hab e t ht_ne_e ht_ne_a he_ne_a he_ne_b hfour
  rcases hfour with h01 | h02 | h03 | h12 | h13 | h23
  · exact False.elim (ht_ne_e h01)
  · exact False.elim (ht_ne_a h02)
  · exact h03.symm
  · exact False.elim (he_ne_a h12)
  · exact False.elim (he_ne_b h13)
  · exact False.elim (hab h23)

private theorem hxAt1035 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              x.re - u.re = 0 → x.im = u.im + P.q → x = u + ⟨0, (P.q : Int)⟩
    ) := by
  classical
  intro P u x hxre' hxim''
  ext
  · simp only [Zsqrtd.re_add]
    omega
  · simp only [Zsqrtd.im_add]
    omega

private theorem hq1castAt1045 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (0 : ℕ) < P.q₁ →
            GaussianInt →
              GaussianInt →
                (P.q₁ : Int) + P.q₂ = P.q →
                  ((P.q - 1 : Nat) : Int) = (P.q : Int) - 1 →
                    ((P.q₁ - 1 : Nat) : Int) = (P.q₁ : Int) - 1
    ) := by
  classical
  intro P hrpos u x hqsum hqcast
  exact_mod_cast Nat.cast_sub (by omega : 1 ≤ P.q₁)

private theorem hmcAt1049 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (u : GaussianInt),
            ∀ (x : GaussianInt),
              x.re = u.re →
                x.im = u.im + P.q →
                  (P.q₁ : Int) + P.q₂ = P.q →
                    ((P.q - 1 : Nat) : Int) = (P.q : Int) - 1 →
                      let m : GaussianInt := x - 1
                      m =
                        u + ⟨-(P.q : Int), (P.q₂ : Int)⟩ +
                          ⟨((P.q - 1 : Nat) : Int), (P.q₁ : Int)⟩
    )
            := by
  classical
  intro P u x hxre'' hxim'' hqsum hqcast m
  ext
  · simp only [m, Zsqrtd.re_sub, Zsqrtd.re_one,
      Zsqrtd.re_add]
    rw [hxre'']
    rw [hqcast]
    omega
  · simp only [m, Zsqrtd.im_sub, Zsqrtd.im_one,
      Zsqrtd.im_add]
    rw [hxim'']
    rw [← hqsum]
    ring

private theorem hRm1 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (Rminus : ProtoTile), (Rminus.cells =
            (TileTranslation (FordTile (if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then P.q₁ else
            P.q₂)) (u + if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (0 : ℤ)⟩ :
            GaussianInt) else (⟨(0 : ℤ), (↑P.q : ℤ)⟩ : GaussianInt))).cells) → (Rminus.cells =
            (TileTranslation (FordTile P.q₂) (u + ⟨0, (P.q : Int)⟩)).cells) ) := by
  classical
  intro P u Rminus hRm
  simpa using hRm

private theorem hc'1 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), (T'.cells =
            (TileTranslation (FordTile P.q) (u + if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then
            (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ :
            GaussianInt))).cells) → (T'.cells = (TileTranslation (FordTile P.q) (u + ⟨-(P.q :
            Int), (P.q₂ : Int)⟩)).cells) ) := by
  classical
  intro P T' u hc'
  simpa using hc'

private theorem hEcellAt1075 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (Rminus : ProtoTile), ∀ (x :
            GaussianInt), (x = u + ⟨0, (P.q : Int)⟩) → ((Rminus.cells = (TileTranslation
            (FordTile P.q₂) (u + ⟨0, (P.q : Int)⟩)).cells) → ((u + (⟨(0 : ℤ), (↑P.q : ℤ)⟩ :
            GaussianInt) + (⟨(↑(0 : ℕ) : ℤ), (↑(0 : ℕ) : ℤ)⟩ : GaussianInt) ∈ (TileTranslation
            (FordTile P.q₂) (u + (⟨(0 : ℤ), (↑P.q : ℤ)⟩ : GaussianInt))).cells) → (x ∈
            Rminus.cells))) ) := by
  classical
  intro P u Rminus x hx hRm1 hEtrans
  rw [hRm1, hx]
  convert hEtrans using 1; abel

private theorem hdisETAt1079 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → (∀ (Rminus : ProtoTile), (∀ (n : Nat), ∀
            (m : Nat), ∀ (w : GaussianInt), ∀ (v : GaussianInt), (w.im + n ≤ v.im) → (Disjoint
            (TileTranslation (FordTile n) w).cells (TileTranslation (FordTile m) v).cells)) →
            ((Rminus.cells = (TileTranslation (FordTile P.q₂) (u + ⟨0, (P.q : Int)⟩)).cells) →
            (Disjoint Rminus.cells T.cells))) ) := by
  classical
  intro P T u hc Rminus ford_disjoint_im hRm1
  have htmp : Disjoint T.cells Rminus.cells := by
    rw [hc, hRm1]
    apply ford_disjoint_im
    simp [Zsqrtd.im_add]
  simpa [hRm1, hc] using htmp.symm

private theorem hdisET'At1085 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (T' : ProtoTile),
            ∀ (u : GaussianInt),
              ∀ (Rminus : ProtoTile),
                (∀ (n : Nat),
                    ∀ (m : Nat),
                      ∀ (w : GaussianInt),
                        ∀ (v : GaussianInt),
                          w.re + n ≤ v.re →
                            Disjoint (TileTranslation (FordTile n) w).cells
                              (TileTranslation (FordTile m) v).cells) →
                  Rminus.cells =
                      (TileTranslation (FordTile P.q₂) (u + ⟨0, (P.q : Int)⟩)).cells →
                    T'.cells =
                        (TileTranslation (FordTile P.q)
                            (u + ⟨-(P.q : Int), (P.q₂ : Int)⟩)).cells →
                      Disjoint Rminus.cells T'.cells
    ) := by
  classical
  intro P T' u Rminus ford_disjoint_re hRm1 hc'1
  have hgap :
      (u + ⟨-(P.q : Int), (P.q₂ : Int)⟩).re + P.q ≤
        (u + ⟨0, (P.q : Int)⟩).re := by
    simp only [Zsqrtd.re_add]
    omega
  have htmp := ford_disjoint_re P.q P.q₂
    (u + ⟨-(P.q : Int), (P.q₂ : Int)⟩)
    (u + ⟨0, (P.q : Int)⟩) hgap
  simpa [hRm1, hc'1] using htmp.symm

private theorem hmT' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let m : GaussianInt := x - 1
        (m = (u + ⟨-(P.q : Int), (P.q₂ : Int)⟩) + ⟨((P.q - 1 : Nat) : Int), (P.q₁ : Int)⟩) →
            ((T'.cells = (TileTranslation (FordTile P.q) (u + ⟨-(P.q : Int), (P.q₂ :
            Int)⟩)).cells) → ((u + (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt) + (⟨(↑(P.q - (1 :
            ℕ)) : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) ∈ (TileTranslation (FordTile P.q) (u + (⟨-(↑P.q
            : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells) → (m ∈ T'.cells))) ) := by
  classical
  intro P T' u x m hmc hc'1 httrans
  rw [hc'1]
  rw [hmc]
  exact httrans

private theorem ht_ne_eAt1103 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt),
        let m : GaussianInt := x - 1
        ∀ (e : ↥(TilingLattice Ci)), (PP.tile e = Rminus) → ((Disjoint Rminus.cells T'.cells) →
            ((m ∈ T'.cells) → (∀ (t : ↥(TilingLattice Ci)), (m ∈ (PP.tile t).cells) → (t ≠ e))))
            ) := by
  classical
  intro Ci T' Rminus PP x m e he hdisET' hmT' t ht hte
  have hmt : m ∈ (PP.tile e).cells := by simpa [hte] using ht
  have hmE : m ∈ Rminus.cells := by simpa [he] using hmt
  exact (Finset.disjoint_left.mp hdisET') hmE hmT'

private theorem ht_ne_aAt1108 :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h :
            PartialOdometer), (Disjoint T.cells T'.cells) → (∀ (tiles : List ProtoTile), ∀ (hs :
            List PartialOdometer), (∀ (U : ProtoTile), ∀ (g : PartialOdometer), (U, g) ∈
            tiles.zip hs → AncestorOdometer Ci.1.1 C0.1.1 U T g h → U.cells ⊆ T.cells) → (∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (g :
            PartialOdometer), ∀ (a : ↥(TilingLattice Ci)), ((PP.tile a, g) ∈ tiles.zip hs) →
            ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile a) T g h) → (
        let m : GaussianInt := x - 1
        (m ∈ T'.cells) → (∀ (t : ↥(TilingLattice Ci)), (m ∈ (PP.tile t).cells) → (t ≠ a)))))) )
            := by
  classical
  intro C0 Ci T T' h hdis tiles hs hcontain PP x g a hAzip hAanc m hmT' t ht hta
  have hma : m ∈ (PP.tile a).cells := by simpa [hta] using ht
  exact (Finset.disjoint_left.mp hdis)
    (hcontain (PP.tile a) g hAzip hAanc hma) hmT'

private theorem he_ne_aAt1113 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T : ProtoTile),
            ∀ (h : PartialOdometer), ∀ (u : GaussianInt), ∀ (Rminus : ProtoTile), ∀ (tiles : List
            ProtoTile), ∀ (hs : List PartialOdometer), (∀ (U : ProtoTile), ∀ (g :
            PartialOdometer), (U, g) ∈ tiles.zip hs → AncestorOdometer Ci.1.1 C0.1.1 U T g h →
            U.cells ⊆ T.cells) → (∀ (PP : PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x :
            GaussianInt), ∀ (U : ProtoTile), ∀ (g : PartialOdometer), ∀ (a : ↥(TilingLattice
            Ci)), (PP.tile a = U) → (∀ (cf : LatticeCell), (cf ∈ U.cells) → (((PP.tile a, g) ∈
            tiles.zip hs) → ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile a) T g h) → (
        let z : GaussianInt :=
          if (x - u).im = (if (1 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ((¬(x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((if (1 : Fin (3 : ℕ)) = (0 : Fin
            (3 : ℕ)) then cf = z - (1 : LatticeCell) else cf = z) → ((¬(x - u).im = if (1 : Fin
            (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (∀ (e :
            ↥(TilingLattice Ci)), (PP.tile e = Rminus) → ((Disjoint Rminus.cells T.cells) → (e ≠
            a)))))))))) ) := by
  classical
  intro P C0 Ci T h u Rminus tiles hs hcontain PP x U g a hUa cf hcf hAzip hAanc z z_other
      hcfSide hlow e he hdisET heq
  have hxa' : x - ⟨0,1⟩ ∈ (PP.tile a).cells := by
    have hside : cf = z := by simpa using hcfSide
    have hcf' : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
    simpa [hside, z_other (by omega)] using hcf'
  have hxaT : x - ⟨0,1⟩ ∈ T.cells :=
    hcontain (PP.tile a) g hAzip hAanc hxa'
  have hxaE : x - ⟨0,1⟩ ∈ Rminus.cells := by
    rw [← he]
    simpa [heq] using hxa'
  exact (Finset.disjoint_left.mp hdisET) hxaE hxaT

private theorem he_ne_bAt1125 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T' : ProtoTile),
            ∀ (h' : PartialOdometer), ∀ (u : GaussianInt), ∀ (Rminus : ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (reverseHs : List PartialOdometer), (∀ (V :
            ProtoTile), ∀ (k : PartialOdometer), (V, k) ∈ reverseTiles.zip reverseHs →
            AncestorOdometer Ci.1.1 C0.1.1 V T' k h' → V.cells ⊆ T'.cells) → (∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V : ProtoTile), ∀
            (k : PartialOdometer), ∀ (b : ↥(TilingLattice Ci)), (PP.tile b = V) → (∀ (cb :
            LatticeCell), (cb ∈ V.cells) → (((PP.tile b, k) ∈ reverseTiles.zip reverseHs) →
            ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile b) T' k h') → (
        let z : GaussianInt :=
          if (x - u).im = (if (1 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ((¬(x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((if (1 : Fin (3 : ℕ)) = (0 : Fin
            (3 : ℕ)) then cb = z else cb = z - (1 : LatticeCell)) → ((¬(x - u).im = if (1 : Fin
            (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (∀ (e :
            ↥(TilingLattice Ci)), (PP.tile e = Rminus) → ((Disjoint Rminus.cells T'.cells) → (e ≠
            b)))))))))) ) := by
  classical
  intro P C0 Ci T' h' u Rminus reverseTiles reverseHs hcontain' PP x V k b hVb cb hcb hBzip hBanc
      z z_other hcbSide hlow e he hdisET' heq
  have hxb' : x - 1 - ⟨0,1⟩ ∈ (PP.tile b).cells := by
    have hside : cb = z - 1 := by simpa using hcbSide
    have hcb' : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
    have hsub : x - ⟨0,1⟩ - 1 = x - 1 - ⟨0,1⟩ := by abel
    simpa [hside, z_other (by omega), hsub] using hcb'
  have hxbT' : x - 1 - ⟨0,1⟩ ∈ T'.cells :=
    hcontain' (PP.tile b) k hBzip hBanc hxb'
  have hxbE : x - 1 - ⟨0,1⟩ ∈ Rminus.cells := by
    rw [← he]
    simpa [heq] using hxb'
  exact (Finset.disjoint_left.mp hdisET') hxbE hxbT'

private theorem hxaAt1138 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀
            (a : ↥(TilingLattice Ci)), (PP.tile a = U) → (∀ (cf : LatticeCell), (cf ∈ U.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (1 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ((¬(x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((if (1 : Fin (3 : ℕ)) = (0 : Fin
            (3 : ℕ)) then cf = z - (1 : LatticeCell) else cf = z) → ((¬(x - u).im = if (1 : Fin
            (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x - ⟨0,1⟩ ∈
            (PP.tile a).cells))))) ) := by
  classical
  intro P Ci u PP x U a hUa cf hcf z z_other hcfSide hlow
  have hside : cf = z := by simpa using hcfSide
  have hcf' : cf ∈ (PP.tile a).cells := by simpa [hUa] using hcf
  simpa [hside, z_other (by omega)] using hcf'

private theorem hxbAt1142 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt), ∀ (PP :
            PeriodicTileComplex ↥(TilingLattice Ci)), ∀ (x : GaussianInt), ∀ (V : ProtoTile), ∀
            (b : ↥(TilingLattice Ci)), (PP.tile b = V) → (∀ (cb : LatticeCell), (cb ∈ V.cells) → (
        let z : GaussianInt :=
          if (x - u).im = (if (1 : Fin 3) = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        ((¬(x - u).im = if (1 : Fin (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) → z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((if (1 : Fin (3 : ℕ)) = (0 : Fin
            (3 : ℕ)) then cb = z else cb = z - (1 : LatticeCell)) → ((¬(x - u).im = if (1 : Fin
            (3 : ℕ)) = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → (x - 1 - ⟨0,1⟩ ∈
            (PP.tile b).cells))))) ) := by
  classical
  intro P Ci u PP x V b hVb cb hcb z z_other hcbSide hlow
  have hside : cb = z - 1 := by simpa using hcbSide
  have hcb' : cb ∈ (PP.tile b).cells := by simpa [hVb] using hcb
  have hsub : x - ⟨0,1⟩ - 1 = x - 1 - ⟨0,1⟩ := by abel
  simpa [hside, z_other (by omega), hsub] using hcb'

private theorem hrepeatAt1149 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (a : ↥(TilingLattice Ci)), ∀ (b : ↥(TilingLattice Ci)), (a ≠ b) →
            (∀ (e : ↥(TilingLattice Ci)), ∀ (t : ↥(TilingLattice Ci)), (t ≠ e) → ((t ≠ a) → ((e ≠
            a) → ((e ≠ b) → ((e = t ∨ e = b ∨ e = a ∨ t = b ∨ t = a ∨ b = a) → (b = t)))))) ) := by
  classical
  intro Ci a b hab e t ht_ne_e ht_ne_a he_ne_a he_ne_b hfour
  rcases hfour with h01 | h02 | h03 | h12 | h13 | h23
  · exact False.elim (ht_ne_e h01.symm)
  · exact False.elim (he_ne_b h02)
  · exact False.elim (he_ne_a h03)
  · exact h12.symm
  · exact False.elim (ht_ne_a h13)
  · exact False.elim (hab h23.symm)

end EdgeSectorGeometry

namespace EdgeSectorBoundary

private theorem lowerBoundary :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (i : Fin (3 :
            ℕ)), (i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨ i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
            (((0 : ℕ) < P.q₁) → (∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer),
            ∀ (h' : PartialOdometer), ∀ (u : GaussianInt), (T.cells = (TileTranslation (FordTile
            P.q) u).cells) → ((T'.cells = (TileTranslation (FordTile P.q) (u + if i = (0 : Fin (3
            : ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩
            : GaussianInt))).cells) → ((Disjoint T.cells T'.cells) → (∀ (orientation : Bool), ∀
            (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List
            ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀
            (reverseHs : List PartialOdometer), (TileString Ci orientation base Rminus Rplus
            tiles) → ((TileString Ci orientation base Rplus Rminus reverseTiles) → ((Rminus.cells
            = (TileTranslation (FordTile (if i = (0 : Fin (3 : ℕ)) then P.q₁ else P.q₂)) (u + if
            i = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (0 : ℤ)⟩ : GaussianInt) else (⟨(0 : ℤ),
            (↑P.q : ℤ)⟩ : GaussianInt))).cells) → ((Rplus.cells = (TileTranslation (FordTile (if
            i = (0 : Fin (3 : ℕ)) then P.q₁ else P.q₂)) (u + if i = (0 : Fin (3 : ℕ)) then
            (⟨(↑P.q₂ : ℤ), (↑P.q : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩ :
            GaussianInt))).cells) → ((∀ (z : GaussianInt), ((z - u).re = if i = (0 : Fin (3 : ℕ))
            then (↑P.q : ℤ) else (0 : ℤ)) → (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else
            (↑P.q₂ : ℤ)) ≤ (z - u).im → (z - u).im < (↑P.q : ℤ) → ∃ (U : ProtoTile) (V :
            ProtoTile) (g : PartialOdometer) (k : PartialOdometer), U ∈ (List.drop (1 : ℕ)
            tiles).dropLast ∧ V ∈ (List.drop (1 : ℕ) reverseTiles).dropLast ∧ (U, g) ∈ tiles.zip
            hs ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1 C0.1.1 U T g h ∧
            AncestorOdometer Ci.1.1 C0.1.1 V T' k h' ∧ {z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges U ∧ {z, z + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges V) → (∀ (PP : PeriodicTileComplex
            ↥(TilingLattice Ci)), ∀ (tileAt : ℤ × ℤ → ProtoTile), (AffineTriangularComplexChart
            PP tileAt) → (∀ (x : GaussianInt), ((x - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q
            : ℤ) else (0 : ℤ)) → (((if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤
            (x - u).im) → ((∀ U ∈ RegularTileFamily base (TilingLattice Ci), ∃ (a :
            ↥(TilingLattice Ci)), PP.tile a = U) → ((∀ (n : ℕ), ∀ (a : ℕ), ∀ (b : ℕ), ∀ (w :
            GaussianInt), a < n → b < n → w + (⟨(↑a : ℤ), (↑b : ℤ)⟩ : GaussianInt) ∈
            (TileTranslation (FordTile n) w).cells) → ((∀ (n : ℕ), ∀ (m : ℕ), ∀ (w :
            GaussianInt), ∀ (v : GaussianInt), w.re + (↑n : ℤ) ≤ v.re → Disjoint (TileTranslation
            (FordTile n) w).cells (TileTranslation (FordTile m) v).cells) → ((∀ (n : ℕ), ∀ (m :
            ℕ), ∀ (w : GaussianInt), ∀ (v : GaussianInt), w.im + (↑n : ℤ) ≤ v.im → Disjoint
            (TileTranslation (FordTile n) w).cells (TileTranslation (FordTile m) v).cells) → (((0
            : ℕ) < P.q₁) → (((if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) < (↑P.q
            : ℤ)) → (
        let z : GaussianInt :=
          if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
          then x else x - ⟨0, 1⟩
        (((x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) → (z = x)) → ((
        let z := if (x - u).im = if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then
            x else x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt); (¬(x - u).im = if i = (0 : Fin (3 :
            ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) → z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            → (((if (x - u).im = if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then
            x else x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) = x ∨ (if (x - u).im = if i = (0 : Fin
            (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then x else x - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((((if (x - u).im = if i =
            (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then x else x - (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt)) - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ))
            → (((if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤ ((if (x - u).im =
            if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then x else x - (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)) - u).im) → ((((if (x - u).im = if i = (0 : Fin (3 : ℕ)) then
            (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then x else x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) -
            u).im < (↑P.q : ℤ)) → (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (g : PartialOdometer),
            ∀ (k : PartialOdometer), ({z, z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)} ∈
            FootprintEdges U) → (({z, z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges V)
            → (∀ (a : ↥(TilingLattice Ci)), ∀ (b : ↥(TilingLattice Ci)), (PP.tile a = U) →
            ((PP.tile b = V) → ((U.cells ⊆ T.cells) → ((V.cells ⊆ T'.cells) → (({z, z + ⟨0, 1⟩} ∈
            FootprintEdges (PP.tile a)) → (({z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile b)) → ((∀ c
            ∈ T'.cells, (0 : ℤ) ≤ (c - (u + if i = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ :
            ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).re ∧ (c - (u +
            if i = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q
            : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).re < (↑P.q : ℤ) ∧ (0 : ℤ) ≤ (c - (u + if i = (0 :
            Fin (3 : ℕ)) then (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ),
            (↑P.q₂ : ℤ)⟩ : GaussianInt))).im ∧ (c - (u + if i = (0 : Fin (3 : ℕ)) then (⟨(↑P.q :
            ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).im
            < (↑P.q : ℤ)) → ((∀ (w : GaussianInt), ((w - u).re = if i = (0 : Fin (3 : ℕ)) then
            (↑P.q : ℤ) else (0 : ℤ)) → (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ :
            ℤ)) ≤ (w - u).im → (w - u).im < (↑P.q : ℤ) → ∃ (aa : ↥(TilingLattice Ci)) (bb :
            ↥(TilingLattice Ci)) (gg : PartialOdometer) (kk : PartialOdometer), aa ≠ bb ∧
            (PP.tile aa, gg) ∈ tiles.zip hs ∧ (PP.tile bb, kk) ∈ reverseTiles.zip reverseHs ∧
            AncestorOdometer Ci.1.1 C0.1.1 (PP.tile aa) T gg h ∧ AncestorOdometer Ci.1.1 C0.1.1
            (PP.tile bb) T' kk h' ∧ {w, w + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges
            (PP.tile aa) ∧ {w, w + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)} ∈ FootprintEdges (PP.tile
            bb)) → (∀ (cf : LatticeCell), (cf ∈ U.cells) → ((if i = (0 : Fin (3 : ℕ)) then cf =
            (if (x - u).im = if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then x
            else x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) - (1 : LatticeCell) else cf = if (x -
            u).im = if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then x else x -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → (∀ (cb : LatticeCell), (cb ∈ V.cells) → ((if i
            = (0 : Fin (3 : ℕ)) then cb = if (x - u).im = if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ :
            ℤ) else (↑P.q₂ : ℤ) then x else x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) else cb = (if
            (x - u).im = if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ) then x else x
            - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) - (1 : LatticeCell)) → ((a ≠ b) → (((PP.tile a,
            g) ∈ tiles.zip hs) → (((PP.tile b, k) ∈ reverseTiles.zip reverseHs) →
            ((AncestorOdometer Ci.1.1 C0.1.1 (PP.tile a) T g h) → ((AncestorOdometer Ci.1.1
            C0.1.1 (PP.tile b) T' k h') → (((x-u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) →
            (∃ (a b : TilingLattice Ci) (g k : PartialOdometer), a ≠ b ∧ (PP.tile a, g) ∈
            tiles.zip hs ∧ (PP.tile b, k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1
            C0.1.1 (PP.tile a) T g h ∧ AncestorOdometer Ci.1.1 C0.1.1 (PP.tile b) T' k h' ∧ (∃ z,
            (z = x ∨ z = x - ⟨0, 1⟩) ∧ {z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile a) ∧ {z, z + ⟨0,
            1⟩} ∈ FootprintEdges (PP.tile b)) ∧ ((x ∈ (PP.tile a).cells ∧ x - 1 - ⟨0, 1⟩ ∈
            (PP.tile b).cells) ∨ (x - 1 ∈ (PP.tile a).cells ∧ x - ⟨0, 1⟩ ∈ (PP.tile b).cells) ∨
            (x - 1 - ⟨0, 1⟩ ∈ (PP.tile a).cells ∧ x ∈ (PP.tile b).cells) ∨ (x - ⟨0, 1⟩ ∈ (PP.tile
            a).cells ∧ x - 1 ∈ (PP.tile b).cells))))))))))))))))))))))))))))))))))))))))))))))) )
            := by
  classical
  intro P C0 Ci i hsmall hrpos T T' h h' u hc hc' hdis orientation base Rminus Rplus tiles
      reverseTiles hs reverseHs hf hr hRm hRp hedges PP tileAt chart x hxr hxl regular_index
      translated_ford_cell ford_disjoint_re ford_disjoint_im q₁pos lower_lt_q z z_low z_other
      z_incident hz_re hz_low hz_high U V g k hEdgeU hEdgeV a b hUa hVb U_in_T V_in_T' U_edge
      V_edge T'_bounds indexed_edge cf hcf hcfSide cb hcb hcbSide hab hAzip hBzip hAanc hBanc hlow
  rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
  · subst i
    have hxre : (x-u).re = P.q := by simpa using hxr
    have hxim : (x-u).im = P.q₁ := hlow
    have hx := EdgeSectorGeometry.hxAt721 P u x hxre hxim
    have hnatcast : ((P.q₁ - 1 : Nat) : Int) = (P.q₁ : Int) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : 1 ≤ P.q₁)
    have hRmem : Rminus ∈ tiles := List.mem_of_head? hf.2.1
    obtain ⟨e, he⟩ := regular_index Rminus (hf.2.2.2.2.1 Rminus hRmem)
    have hEtrans := translated_ford_cell P.q₁ 0 (P.q₁-1)
      (u + ⟨(P.q : Int),0⟩) (by omega) (by omega)
    have hEcell : x - ⟨0,1⟩ ∈ Rminus.cells := EdgeSectorGeometry.hEcellAt735 P u Rminus x hRm
        (EdgeSectorGeometry.hce P u x hx hnatcast) hEtrans
    have hEidx : x - ⟨0,1⟩ ∈ (PP.tile e).cells := by
      simpa [he] using hEcell
    have hdisET := EdgeSectorGeometry.hdisETAt740 P T u hc Rminus ford_disjoint_re hRm
    have hdisET' := EdgeSectorGeometry.hdisET'At744 P T' u Rminus ford_disjoint_im hc' hRm
    have he_ne_a := EdgeSectorGeometry.he_ne_aAt748 Ci T Rminus PP U a hUa U_in_T cf hcf e he
        hdisET
    have he_ne_b := EdgeSectorGeometry.he_ne_bAt755 Ci T' Rminus PP V b hVb V_in_T' cb hcb e
        he hdisET'
    let m : GaussianInt := x - 1 - ⟨0,1⟩
    have hqcast : ((P.q - 1 : Nat) : Int) = (P.q : Int) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : 1 ≤ P.q)
    have hq1leq : P.q₁ ≤ P.q := by omega
    have hmc := EdgeSectorGeometry.hmcAt766 P u x hx hnatcast hqcast
    have hmTtrans := translated_ford_cell P.q (P.q - 1) (P.q₁ - 1) u
      (by omega) (by omega)
    have hmT : m ∈ T.cells := EdgeSectorGeometry.hmTAt772 P T u hc x hmc hmTtrans
    obtain ⟨t, ht, htuniq⟩ := PeriodicTileIndexedMultiplicityOne PP m
    have ht_ne_e := EdgeSectorGeometry.ht_ne_eAt779 Ci Rminus PP x e he t ht
        (EdgeSectorGeometry.hm_notE T Rminus x hdisET hmT)
    have ht_ne_b := EdgeSectorGeometry.ht_ne_bAt784 Ci T T' hdis PP x V b hVb V_in_T' hmT t ht
    have hxb : x ∈ (PP.tile b).cells := EdgeSectorGeometry.hxbAt789 P Ci u PP x V b hVb cb
        hcb z_low hcbSide hlow
    have hxa := EdgeSectorGeometry.hxaAt793 P Ci u PP x U a hUa cf hcf z_low hcfSide hlow
    have hfour := AffineTriangularNoFourfoldCellOwners PP tileAt chart x
      b a t e hxb hxa ht hEidx
    have hrepeat : a = t := EdgeSectorGeometry.hrepeatAt799 Ci a b hab e he_ne_a he_ne_b t
        ht_ne_e ht_ne_b hfour
    refine ⟨a, b, g, k, hab, hAzip, hBzip, hAanc, hBanc,
      ⟨x, Or.inl rfl, ?_, ?_⟩, ?_⟩
    · simpa [z_low hlow] using U_edge
    · simpa [z_low hlow] using V_edge
    · have hma : m ∈ (PP.tile a).cells := by simpa [hrepeat] using ht
      exact Or.inr (Or.inr (Or.inl ⟨hma, hxb⟩))
  · subst i
    have hxre : (x-u).re = 0 := by simpa using hxr
    have hxim : (x-u).im = P.q₂ := hlow
    have hx := EdgeSectorGeometry.hxAt816 P u x hxre hxim
    have hq2pos : 0 < P.q₂ := P.q₂_pos
    have hncast : ((P.q₂ - 1 : Nat) : Int) = (P.q₂ : Int) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : 1 ≤ P.q₂)
    let m : GaussianInt := x - ⟨0,1⟩
    have hmc := EdgeSectorGeometry.hmcAt823 P u x hx hncast
    have htc : m = u + ⟨0, ((P.q₂ - 1 : Nat) : Int)⟩ := hmc
    have hmTtrans := translated_ford_cell P.q 0 (P.q₂ - 1) u
      (by omega) (by omega)
    have hmT : m ∈ T.cells := by rw [hc, htc]; exact hmTtrans
    have hncast' : ((P.q₂ - 1 : Nat) : Int) = (P.q₂ : Int) - 1 := hncast
    let n : GaussianInt := x - 1 - ⟨0,1⟩
    have hnc : n = (u + ⟨-(P.q₂ : Int),0⟩) +
        ⟨((P.q₂ - 1 : Nat) : Int), ((P.q₂ - 1 : Nat) : Int)⟩ := EdgeSectorGeometry.hncAt832 P u
            x hx hncast'
    have hRmem : Rplus ∈ reverseTiles := List.mem_of_head? hr.2.1
    obtain ⟨e, he⟩ := regular_index Rplus
      (hr.2.2.2.2.1 Rplus hRmem)
    have hEtrans := translated_ford_cell P.q₂ (P.q₂ - 1) (P.q₂ - 1)
      (u + ⟨-(P.q₂ : Int),0⟩) (by omega) (by omega)
    have hEcell : n ∈ Rplus.cells := by rw [hRp, hnc]; exact hEtrans
    have hEidx : n ∈ (PP.tile e).cells := by simpa [he] using hEcell
    have hdisET := EdgeSectorGeometry.hdisETAt843 P T u hc Rplus ford_disjoint_re hRp
    have hdisET' := EdgeSectorGeometry.hdisET'At847 P T' u Rplus ford_disjoint_im hc' hRp
    have he_ne_a := EdgeSectorGeometry.he_ne_aAt851 Ci T Rplus PP U a hUa U_in_T cf hcf e he
        hdisET
    have he_ne_b := EdgeSectorGeometry.he_ne_bAt858 Ci T' Rplus PP V b hVb V_in_T' cb hcb e
        he hdisET'
    obtain ⟨t, ht, htuniq⟩ := PeriodicTileIndexedMultiplicityOne PP m
    have ht_ne_e := EdgeSectorGeometry.ht_ne_eAt866 Ci T Rplus PP x hmT e he hdisET t ht
    have ht_ne_b := EdgeSectorGeometry.ht_ne_bAt871 Ci T T' hdis PP x V b hVb V_in_T' hmT t ht
    have hxa := EdgeSectorGeometry.hxaAt876 P Ci u PP x U a hUa cf hcf z_low hcfSide hlow
    have hxb : x - 1 ∈ (PP.tile b).cells := EdgeSectorGeometry.hxbAt880 P Ci u PP x V b hVb
        cb hcb z_low hcbSide hlow
    have hfour := AffineTriangularNoFourfoldCellOwners PP tileAt chart x
      a b e t hxa hxb hEidx ht
    have hrepeat : a = t := EdgeSectorGeometry.hrepeatAt886 Ci a b hab e he_ne_a he_ne_b t
        ht_ne_e ht_ne_b hfour
    refine ⟨a, b, g, k, hab, hAzip, hBzip, hAanc, hBanc,
      ⟨x, Or.inl rfl, ?_, ?_⟩, ?_⟩
    · simpa [z_low hlow] using U_edge
    · simpa [z_low hlow] using V_edge
    · have hma : m ∈ (PP.tile a).cells := by simpa [hrepeat] using ht
      exact Or.inr (Or.inr (Or.inr ⟨hma, hxb⟩))

end EdgeSectorBoundary

theorem P4158T1EdgeSectorSelection :
    ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (i : Fin 3), ((i = 0
        ∧ P.q₁ < P.q₂) ∨ (i = 1 ∧ P.q₂ < P.q₁)) → ((0 < P.q₁) → ((1 < Ci.1.1.1) → (∀ (T :
        ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' : PartialOdometer), ∀ (u :
        GaussianInt), (T.cells = (TileTranslation (FordTile P.q) u).cells) → ((T'.cells =
        (TileTranslation (FordTile P.q)
      (u + if i = 0 then ⟨P.q, P.q₁⟩ else ⟨-(P.q : Int), P.q₂⟩)).cells) → ((Disjoint T.cells
          T'.cells) → (∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
          (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀
          (hs : List PartialOdometer), ∀ (reverseHs : List PartialOdometer), (TileString Ci
          orientation base Rminus Rplus tiles) → ((TileString Ci orientation base Rplus Rminus
          reverseTiles) → ((Rminus.cells = (TileTranslation (FordTile (if i = 0 then P.q₁ else
          P.q₂))
      (u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩)).cells) → ((Rplus.cells = (TileTranslation
          (FordTile (if i = 0 then P.q₁ else P.q₂))
      (u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩)).cells) → ((∀ U, ∀ g, (U, g) ∈
          tiles.zip hs →
      AncestorOdometer Ci.1.1 C0.1.1 U T g h → U.cells ⊆ T.cells) → ((∀ V, ∀ k, (V, k) ∈
          reverseTiles.zip reverseHs →
      AncestorOdometer Ci.1.1 C0.1.1 V T' k h' → V.cells ⊆ T'.cells) → ((∀ z : GaussianInt,
      (z - u).re = (if i = 0 then (P.q : Int) else 0) →
      (if i = 0 then (P.q₁ : Int) else P.q₂) ≤ (z - u).im →
      (z - u).im < (P.q : Int) →
      ∃ (U V : ProtoTile) (g k : PartialOdometer),
        U ∈ (tiles.drop 1).dropLast ∧ V ∈ (reverseTiles.drop 1).dropLast ∧
        (U, g) ∈ tiles.zip hs ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧
        AncestorOdometer Ci.1.1 C0.1.1 U T g h ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T' k h' ∧
        {z, z + ⟨0, 1⟩} ∈ FootprintEdges U ∧
        {z, z + ⟨0, 1⟩} ∈ FootprintEdges V) → (∀ (PP : PeriodicTileComplex (TilingLattice Ci)),
            (∀ a, PP.tile a = TileTranslation base (a : GaussianInt)) → (∀ (tileAt : (Int × Int)
            → ProtoTile), (AffineTriangularComplexChart PP tileAt) → (∀ (x : GaussianInt), ((x -
            u).re = (if i = 0 then (P.q : Int) else 0)) → (((if i = 0 then (P.q₁ : Int) else
            P.q₂) ≤ (x - u).im) → (((x - u).im ≤ (P.q : Int)) → (∃ (a b : TilingLattice Ci) (g k
            : PartialOdometer),
      a ≠ b ∧ (PP.tile a, g) ∈ tiles.zip hs ∧
      (PP.tile b, k) ∈ reverseTiles.zip reverseHs ∧
      AncestorOdometer Ci.1.1 C0.1.1 (PP.tile a) T g h ∧
      AncestorOdometer Ci.1.1 C0.1.1 (PP.tile b) T' k h' ∧
      (∃ z, (z = x ∨ z = x - ⟨0, 1⟩) ∧
        {z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile a) ∧
        {z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile b)) ∧
      ((x ∈ (PP.tile a).cells ∧ x - 1 - ⟨0, 1⟩ ∈ (PP.tile b).cells) ∨
       (x - 1 ∈ (PP.tile a).cells ∧ x - ⟨0, 1⟩ ∈ (PP.tile b).cells) ∨
       (x - 1 - ⟨0, 1⟩ ∈ (PP.tile a).cells ∧ x ∈ (PP.tile b).cells) ∨
       (x - ⟨0, 1⟩ ∈ (PP.tile a).cells ∧ x - 1 ∈ (PP.tile b).cells)))))))))))))))))))) := by
  intro P C0 Ci i hsmall hrpos hlarge T T' h h' u hc hc' hdis orientation base Rminus Rplus tiles
      reverseTiles hs reverseHs hf hr hRm hRp hcontain hcontain' hedges PP htiles tileAt chart x
      hxr hxl hxu
-- BODY
  all_goals
    classical
    have regular_index := EdgeSectorGeometry.regular_index Ci base PP htiles
    have same_index_of_cell (c : GaussianInt) (a b : TilingLattice Ci)
        (ha : c ∈ (PP.tile a).cells) (hb : c ∈ (PP.tile b).cells) : a = b :=
      (PeriodicTileIndexedMultiplicityOne PP c).unique ha hb
    have vertical_edge_cells := EdgeSectorGeometry.vertical_edge_cells
        (EdgeSectorGeometry.pair_eq_iff)
    have translated_ford_bounds := EdgeSectorGeometry.translated_ford_bounds
    have translated_ford_cell := EdgeSectorGeometry.translated_ford_cell
    have ford_disjoint_re := EdgeSectorGeometry.ford_disjoint_re translated_ford_bounds
    have ford_disjoint_im := EdgeSectorGeometry.ford_disjoint_im translated_ford_bounds
    have q₁pos := hrpos
    have lower_lt_q := EdgeSectorGeometry.lower_lt_q P i hsmall
    let z : GaussianInt :=
      if (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
      then x else x - ⟨0, 1⟩
    have z_low (hlow : (x - u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) :
        z = x := EdgeSectorGeometry.z_low P i u x hlow
    have z_other := EdgeSectorGeometry.z_other P i u x
    have z_incident := EdgeSectorGeometry.z_incident P i u x z_low z_other
    have hz_re := EdgeSectorGeometry.hz_re P i u x hxr z_low z_other
    have hz_low := EdgeSectorGeometry.hz_low P i u x hxl z_low z_other
    have hz_high := EdgeSectorGeometry.hz_high P i u x hxu lower_lt_q z_low z_other
    obtain ⟨U, V, g, k, hUint, hVint, hUz, hVk, hAg, hAk, hEdgeU, hEdgeV⟩ :=
      hedges z hz_re hz_low hz_high
    have hUmem : U ∈ tiles := (List.of_mem_zip hUz).1
    have hVmem : V ∈ reverseTiles := (List.of_mem_zip hVk).1
    obtain ⟨a, ha⟩ := regular_index U (hf.2.2.2.2.1 U hUmem)
    obtain ⟨b, hb⟩ := regular_index V (hr.2.2.2.2.1 V hVmem)
    have hUa : PP.tile a = U := ha
    have hVb : PP.tile b = V := hb
    have U_in_T : U.cells ⊆ T.cells := hcontain U g hUz hAg
    have V_in_T' : V.cells ⊆ T'.cells := hcontain' V k hVk hAk
    have U_edge : {z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile a) := EdgeSectorGeometry.U_edge P Ci
        i u PP x U hEdgeU a hUa
    have V_edge : {z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile b) := EdgeSectorGeometry.V_edge P Ci
        i u PP x V hEdgeV b hVb
    have T_bounds := EdgeSectorGeometry.T_bounds P T u hc translated_ford_bounds
    have T'_bounds := EdgeSectorGeometry.T'_bounds P i T' u hc' translated_ford_bounds
    have indexed_edge := EdgeSectorGeometry.indexed_edge P C0 Ci i T T' h h' u hdis orientation
        base Rminus Rplus tiles reverseTiles hs reverseHs hf hr hcontain hcontain' hedges PP
        regular_index vertical_edge_cells
    have forward_support := EdgeSectorGeometry.forward_support P Ci i hsmall T u PP x
        vertical_edge_cells hz_re U a hUa U_in_T U_edge T_bounds
    have reverse_support := EdgeSectorGeometry.reverse_support P Ci i hsmall T' u PP x
        vertical_edge_cells hz_re V b hVb V_in_T' V_edge T'_bounds
    obtain ⟨cf, hcf, hcfSide⟩ := forward_support
    obtain ⟨cb, hcb, hcbSide⟩ := reverse_support
    have hab := EdgeSectorGeometry.hab Ci T T' hdis PP U V a b hUa hVb U_in_T V_in_T' cf hcf
    have hAzip : (PP.tile a, g) ∈ tiles.zip hs := by simpa [hUa] using hUz
    have hBzip : (PP.tile b, k) ∈ reverseTiles.zip reverseHs := by
      simpa [hVb] using hVk
    have hAanc : AncestorOdometer Ci.1.1 C0.1.1 (PP.tile a) T g h := by
      simpa [hUa] using hAg
    have hBanc : AncestorOdometer Ci.1.1 C0.1.1 (PP.tile b) T' k h' := by
      simpa [hVb] using hAk
    have lowerBoundary (hlow : (x-u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)) :
      ∃ (a b : TilingLattice Ci) (g k
      : PartialOdometer),
      a ≠ b ∧ (PP.tile a, g) ∈ tiles.zip hs ∧
      (PP.tile b, k) ∈ reverseTiles.zip reverseHs ∧
      AncestorOdometer Ci.1.1 C0.1.1 (PP.tile a) T g h ∧
      AncestorOdometer Ci.1.1 C0.1.1 (PP.tile b) T' k h' ∧
      (∃ z, (z = x ∨ z = x - ⟨0, 1⟩) ∧
      {z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile a) ∧
      {z, z + ⟨0, 1⟩} ∈ FootprintEdges (PP.tile b)) ∧
      ((x ∈ (PP.tile a).cells ∧ x - 1 - ⟨0, 1⟩ ∈ (PP.tile b).cells) ∨
      (x - 1 ∈ (PP.tile a).cells ∧ x - ⟨0, 1⟩ ∈ (PP.tile b).cells) ∨
      (x - 1 - ⟨0, 1⟩ ∈ (PP.tile a).cells ∧ x ∈ (PP.tile b).cells) ∨
      (x - ⟨0, 1⟩ ∈ (PP.tile a).cells ∧ x - 1 ∈ (PP.tile b).cells)) :=
          EdgeSectorBoundary.lowerBoundary P C0 Ci i hsmall hrpos T T' h h' u hc hc' hdis
          orientation base Rminus Rplus tiles reverseTiles hs reverseHs hf hr hRm hRp hedges PP
          tileAt chart x hxr hxl regular_index translated_ford_cell ford_disjoint_re
          ford_disjoint_im q₁pos lower_lt_q z_low z_other z_incident hz_re hz_low hz_high U V g k
          hEdgeU hEdgeV a b hUa hVb U_in_T V_in_T' U_edge V_edge T'_bounds indexed_edge cf hcf
          hcfSide cb hcb hcbSide hab hAzip hBzip hAanc hBanc hlow
    by_cases hlow : (x-u).im = (if i = 0 then (P.q₁ : Int) else P.q₂)
    · exact lowerBoundary hlow
    · by_cases htop : (x-u).im = P.q
      · rcases hsmall with ⟨hi, hlt⟩ | ⟨hi, hlt⟩
        · subst i
          have hxre' : x.re - u.re = P.q := by
            simpa [Zsqrtd.re_sub] using hxr
          have hxim' : x.im - u.im = P.q := by
            simpa [Zsqrtd.im_sub] using htop
          have hxre'' : x.re = u.re + P.q := by omega
          have hxim'' : x.im = u.im + P.q := by omega
          have hx := EdgeSectorGeometry.hxAt909 P u x hxre'' hxim''
          have hq1cast : ((P.q₁ - 1 : Nat) : Int) = (P.q₁ : Int) - 1 := by
            exact_mod_cast Nat.cast_sub (by omega : 1 ≤ P.q₁)
          have hqsum : (P.q₁ : Int) + P.q₂ = P.q := by
            exact_mod_cast P.sum_q.symm
          let n : GaussianInt := x - 1
          have hnc : n = (u + ⟨(P.q₂ : Int), (P.q : Int)⟩) +
              ⟨((P.q₁ - 1 : Nat) : Int), 0⟩ := EdgeSectorGeometry.hncAt920 P u x hxre'' hxim''
                  hq1cast hqsum
          have hRmem : Rplus ∈ tiles := List.mem_of_getLast? hf.2.2.1
          obtain ⟨e, he⟩ := regular_index Rplus
            (hf.2.2.2.2.1 Rplus hRmem)
          have hEtrans := translated_ford_cell P.q₁ (P.q₁ - 1) 0
            (u + ⟨(P.q₂ : Int), (P.q : Int)⟩) (by omega) (by omega)
          have hEcell : n ∈ Rplus.cells := by rw [hRp, hnc]; exact hEtrans
          have hEidx : n ∈ (PP.tile e).cells := by simpa [he] using hEcell
          have hdisET := EdgeSectorGeometry.hdisETAt940 P T u hc Rplus ford_disjoint_im hRp
          have hdisET' := EdgeSectorGeometry.hdisET'At944 P T' u Rplus ford_disjoint_re hc'
              hRp hqsum
          have hrootCell := translated_ford_cell P.q 0 P.q₂
            (u + ⟨(P.q : Int), (P.q₁ : Int)⟩) (by omega) (EdgeSectorGeometry.hq2lt P hrpos
                hq1cast)
          have hxT' := EdgeSectorGeometry.hxT' P T' u x hc' (EdgeSectorGeometry.hxroot P u x hx
              hqsum) hrootCell
          obtain ⟨t, ht, htuniq⟩ := PeriodicTileIndexedMultiplicityOne PP x
          have ht_ne_e := EdgeSectorGeometry.ht_ne_eAt974 Ci T' Rplus PP x e he hdisET' hxT' t ht
          have ht_ne_a := EdgeSectorGeometry.ht_ne_aAt979 C0 Ci T T' h hdis tiles hs hcontain PP
              x g a hAzip hAanc hxT' t ht
          have he_ne_a := EdgeSectorGeometry.he_ne_aAt984 Ci T Rplus PP x U a hUa U_in_T cf hcf e
              he hEcell hEidx hdisET
          have he_ne_b := EdgeSectorGeometry.he_ne_bAt993 Ci T' Rplus PP x V b hVb V_in_T' cb hcb
              e he hEcell hEidx hdisET'
          have hxa := EdgeSectorGeometry.hxaAt1002 P Ci u PP x U a hUa cf hcf z_other hcfSide hlow
          have hxb : x - ⟨0,1⟩ ∈ (PP.tile b).cells := EdgeSectorGeometry.hxbAt1009 P Ci u PP x V
              b hVb cb hcb z_other hcbSide hlow
          have hfour := AffineTriangularNoFourfoldCellOwners PP tileAt chart x
            t e a b ht hEidx hxa hxb
          have hrepeat : b = t := EdgeSectorGeometry.hrepeatAt1016 Ci a b hab e t ht_ne_e ht_ne_a
              he_ne_a he_ne_b hfour
          refine ⟨a, b, g, k, hab, hAzip, hBzip, hAanc, hBanc,
            ⟨z, z_incident, U_edge, V_edge⟩, ?_⟩
          have hbx : x ∈ (PP.tile b).cells := by simpa [hrepeat] using ht
          exact Or.inr (Or.inr (Or.inl ⟨hxa, hbx⟩))
        · subst i
          have hxre' : x.re - u.re = 0 := by
            simpa [Zsqrtd.re_sub] using hxr
          have hxim' : x.im - u.im = P.q := by
            simpa [Zsqrtd.im_sub] using htop
          have hxre'' : x.re = u.re := by omega
          have hxim'' : x.im = u.im + P.q := by omega
          have hx := EdgeSectorGeometry.hxAt1035 P u x hxre' hxim''
          have hqsum : (P.q₁ : Int) + P.q₂ = P.q := by
            exact_mod_cast P.sum_q.symm
          have hqcast : ((P.q - 1 : Nat) : Int) = (P.q : Int) - 1 := by
            exact_mod_cast Nat.cast_sub (by omega : 1 ≤ P.q)
          have hq1cast := EdgeSectorGeometry.hq1castAt1045 P hrpos u x hqsum hqcast
          let m : GaussianInt := x - 1
          have hmc := EdgeSectorGeometry.hmcAt1049 P u x hxre'' hxim'' hqsum hqcast
          have hRmem : Rminus ∈ tiles := List.mem_of_head? hf.2.1
          obtain ⟨e, he⟩ := regular_index Rminus
            (hf.2.2.2.2.1 Rminus hRmem)
          have hRm1 := EdgeSectorGeometry.hRm1 P u Rminus hRm
          have hc'1 := EdgeSectorGeometry.hc'1 P T' u hc'
          have hEtrans := translated_ford_cell P.q₂ 0 0
            (u + ⟨0, (P.q : Int)⟩) P.q₂_pos P.q₂_pos
          have hEcell : x ∈ Rminus.cells := EdgeSectorGeometry.hEcellAt1075 P u Rminus x hx hRm1
              hEtrans
          have hEidx : x ∈ (PP.tile e).cells := by simpa [he] using hEcell
          have hdisET := EdgeSectorGeometry.hdisETAt1079 P T u hc Rminus ford_disjoint_im hRm1
          have hdisET' := EdgeSectorGeometry.hdisET'At1085 P T' u Rminus ford_disjoint_re
              hRm1 hc'1
          have httrans := translated_ford_cell P.q (P.q - 1) P.q₁
            (u + ⟨-(P.q : Int), (P.q₂ : Int)⟩) (by omega) (P.q₁_lt)
          have hmT' := EdgeSectorGeometry.hmT' P T' u x hmc hc'1 httrans
          obtain ⟨t, ht, htuniq⟩ := PeriodicTileIndexedMultiplicityOne PP m
          have ht_ne_e := EdgeSectorGeometry.ht_ne_eAt1103 Ci T' Rminus PP x e he hdisET' hmT' t ht
          have ht_ne_a := EdgeSectorGeometry.ht_ne_aAt1108 C0 Ci T T' h hdis tiles hs hcontain PP
              x g a hAzip hAanc hmT' t ht
          have he_ne_a := EdgeSectorGeometry.he_ne_aAt1113 P C0 Ci T h u Rminus tiles hs hcontain
              PP x U g a hUa cf hcf hAzip hAanc z_other hcfSide hlow e he hdisET
          have he_ne_b := EdgeSectorGeometry.he_ne_bAt1125 P C0 Ci T' h' u Rminus reverseTiles
              reverseHs hcontain' PP x V k b hVb cb hcb hBzip hBanc z_other hcbSide hlow e he
              hdisET'
          have hxa := EdgeSectorGeometry.hxaAt1138 P Ci u PP x U a hUa cf hcf z_other hcfSide hlow
          have hxb : x - 1 - ⟨0,1⟩ ∈ (PP.tile b).cells := EdgeSectorGeometry.hxbAt1142 P Ci u PP
              x V b hVb cb hcb z_other hcbSide hlow
          have hfour := AffineTriangularNoFourfoldCellOwners PP tileAt chart x
            e t b a hEidx ht hxb hxa
          have hrepeat : b = t := EdgeSectorGeometry.hrepeatAt1149 Ci a b hab e t ht_ne_e ht_ne_a
              he_ne_a he_ne_b hfour
          refine ⟨a, b, g, k, hab, hAzip, hBzip, hAanc, hBanc,
            ⟨z, z_incident, U_edge, V_edge⟩, ?_⟩
          have hbx : x - 1 ∈ (PP.tile b).cells := by simpa [hrepeat] using ht
          exact Or.inr (Or.inr (Or.inr ⟨hxa, hbx⟩))
      · apply (EdgeSectorGeometry.internal_solution P C0 Ci i hsmall T T' h h' u hc' Rminus Rplus
          tiles reverseTiles hs reverseHs hRm hRp hcontain hcontain' hedges PP tileAt chart x hxr
          hxl vertical_edge_cells lower_lt_q z_low z_other z_incident hz_re hz_low hz_high U V g
          k hEdgeU hEdgeV a b hUa hVb U_edge V_edge T_bounds T'_bounds indexed_edge
          (EdgeSectorGeometry.cross_ne C0 Ci T T' h h' hdis tiles reverseTiles hs reverseHs
          hcontain hcontain' PP) cf hcf hcfSide cb hcb hcbSide hab hAzip hBzip hAanc hBanc)
        · omega
        · omega

end ApollonianSuperharmonic

end
