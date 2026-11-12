/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.InteriorFootprintIncidence

public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.FordBoundaryMultiplicity
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrenceTranslation
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P4120T1FordGeometry]

/-!
# P4120T1FordGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordTileGeometry



private theorem cellCanonical :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → (∀ (z : GaussianInt), z ∈ T.cells ↔ z - u
            ∈ (FordTile P.q).cells) ) := by
  classical
  intro P T u hcells z
  rw [hcells, (TileTranslationFormulas (FordTile P.q) u).1]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' : a = z - u := by
      rw [← he]
      dsimp [GaussianTranslation]
      abel
    simpa [he'] using ha
  · intro hz
    exact ⟨z - u, hz, by dsimp [GaussianTranslation]; abel⟩

private theorem squareCell :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (z : GaussianInt), z ∈ (FordTile P.q).cells ↔ (0 : ℤ) ≤
            z.re ∧ z.re < (↑P.q : ℤ) ∧ (0 : ℤ) ≤ z.im ∧ z.im < (↑P.q : ℤ) ) := by
  classical
  intro P z
  change z ∈ FordCellDomain P.q ↔ _
  change z ∈ ((Finset.range P.q).product (Finset.range P.q)).image
    (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, hz⟩
    have hab := Finset.mem_product.mp hab
    have ha := Finset.mem_range.mp hab.1
    have hb := Finset.mem_range.mp hab.2
    have hre : z.re = (a : Int) := by
      have hh := congrArg (fun w : GaussianInt => w.re) hz
      simpa using hh.symm
    have him : z.im = (b : Int) := by
      have hh := congrArg (fun w : GaussianInt => w.im) hz
      simpa using hh.symm
    rw [hre, him]
    exact ⟨by exact_mod_cast (Nat.zero_le a),
      by exact_mod_cast ha,
      by exact_mod_cast (Nat.zero_le b),
      by exact_mod_cast hb⟩
  · rintro ⟨hr, hrq, hi, hiq⟩
    let a := z.re.toNat
    let b := z.im.toNat
    have ha : (a : Int) = z.re := Int.toNat_of_nonneg hr
    have hb : (b : Int) = z.im := Int.toNat_of_nonneg hi
    have haq : a < P.q := by exact_mod_cast (show (a : Int) < P.q by omega)
    have hbq : b < P.q := by exact_mod_cast (show (b : Int) < P.q by omega)
    refine ⟨(a, b), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr haq, Finset.mem_range.mpr hbq⟩, ?_⟩
    apply Zsqrtd.ext <;> simp [ha, hb]

private theorem hbounds :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
            (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) → (
        let y : GaussianInt := x - u
        (∀ (z : GaussianInt), z ∈ T.cells ↔ z - u ∈ (FordTile P.q).cells) → ((∀ (z :
            GaussianInt), z ∈ (FordTile P.q).cells ↔ 0 ≤ z.re ∧ z.re < (P.q : Int) ∧ 0 ≤ z.im ∧
            z.im < (P.q : Int)) → (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤ (P.q :
            Int) - 1)))) := by
  classical
  intro P T u x cells y cellCanonical squareCell
  have c0 := (cellCanonical x).mp (by simpa [LatticeVertexIncidentCell] using cells 0)
  have c1 := (cellCanonical (x - 1)).mp (by simpa [LatticeVertexIncidentCell] using cells 1)
  have c2 := (cellCanonical (x - 1 - ⟨0, 1⟩)).mp
    (by simpa [LatticeVertexIncidentCell] using cells 2)
  have c3 := (cellCanonical (x - ⟨0, 1⟩)).mp
    (by simpa [LatticeVertexIncidentCell] using cells 3)
  rw [squareCell] at c0 c1 c2 c3
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one,
    Zsqrtd.im_one] at c0 c1 c2 c3
  dsimp [y]
  omega

private theorem fordCentroid :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → ((GaussianInt) → ((GaussianInt) →
            (TileCentroid (FordTile P.q) = ((P.q : Real) / 2, (P.q : Real) / 2)))) ) := by
  classical
  intro P hP u x
  let domain : Finset GaussianInt :=
    (Finset.range P.q).product (Finset.range P.q) |>.image
      (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
  have hneDomain : domain.Nonempty := by
    refine ⟨⟨0, 0⟩, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), by simp [P.q_pos], rfl⟩
  have hinj : Set.InjOn
      (fun a : ℕ × ℕ => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
      ↑((Finset.range P.q).product (Finset.range P.q)) := by
    intro a ha b hb hab
    apply Prod.ext
    · have h := congrArg Zsqrtd.re hab
      change (a.1 : Int) = (b.1 : Int) at h
      exact_mod_cast h
    · have h := congrArg Zsqrtd.im hab
      change (a.2 : Int) = (b.2 : Int) at h
      exact_mod_cast h
  have hcard : domain.card = P.q * P.q := by
    calc
      domain.card = ((Finset.range P.q).product (Finset.range P.q)).card := by
        dsimp [domain]
        exact Finset.card_image_iff.mpr hinj
      _ = P.q * P.q := by simp
  have hsumRe : domain.sum (fun z : GaussianInt => z.re) =
      (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 * (P.q : Int) := by
    have hrange : (Finset.range P.q).sum (fun n => (n : Int)) =
        (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, domain]
    conv_lhs => rw [← Finset.mul_sum (Finset.range P.q)
      (fun n => (n : Int)) (P.q : Int)]
    rw [hrange]
    ring
  have hsumIm : domain.sum (fun z : GaussianInt => z.im) =
      (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 * (P.q : Int) := by
    have hrange : (Finset.range P.q).sum (fun n => (n : Int)) =
        (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, domain]
    rw [hrange]
    ring
  change (if domain.Nonempty then
    ((↑(domain.sum (fun z : GaussianInt => z.re) : Int) /
        ↑domain.card + (1 / 2 : Real)),
     (↑(domain.sum (fun z : GaussianInt => z.im) : Int) /
        ↑domain.card + (1 / 2 : Real))) else _) = _
  rw [ite_eq_left hneDomain, hcard, hsumRe, hsumIm]
  have hqcast : ((P.q - 1 : Nat) : Int) = (P.q : Int) - 1 := by omega
  rw [hqcast]
  norm_num
  field_simp
  have arithmetic := Finset.sum_range_id_mul_two P.q
  have rangeSum : (Finset.range P.q).sum (fun n => (n : Int)) =
      (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 := by
    rw [← Nat.cast_sum]
    simp [Finset.sum_range_id]
  have arithmeticCast :
      ((Finset.range P.q).sum (fun n => (n : Int))) * 2 =
        (P.q : Int) * ((P.q - 1 : Nat) : Int) := by
    rw [← Nat.cast_sum]
    exact_mod_cast arithmetic
  rw [rangeSum] at arithmeticCast
  rw [hqcast] at arithmeticCast
  have natIdentity : P.q * (P.q - 1) / 2 * 2 + P.q = P.q * P.q := by
    rw [← Finset.sum_range_id P.q]
    rw [Finset.sum_range_id_mul_two]
    have hprod : P.q ≤ P.q * P.q := by nlinarith
    rw [Nat.mul_sub_left_distrib]
    simp only [Nat.mul_one]
    rw [Nat.sub_add_cancel hprod]
  norm_num [Int.subNatNat, pow_two]
  have hreal :
      (((P.q : Int) * ((P.q : Int) - 1) / 2 : Int) : Real) * 2 =
        (((P.q : Int) * ((P.q : Int) - 1) : Int) : Real) := by
    exact_mod_cast arithmeticCast
  rw [hreal]
  push_cast
  ring

private theorem hparentCentroid :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u :
            GaussianInt), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            (FordRecursiveQuadruple P) T i s (S i s)) → (∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile),
            (FootprintVertices T = FootprintVertices (TileTranslation (FordTile P.q) u) ∧
            BoundaryFootprintVertices T = BoundaryFootprintVertices (TileTranslation (FordTile
            P.q) u) ∧ BoundaryFootprintEdges T = BoundaryFootprintEdges (TileTranslation
            (FordTile P.q) u) ∧ TileRealization T = TileRealization (TileTranslation (FordTile
            P.q) u) ∧ TileCentroid T = TileCentroid (TileTranslation (FordTile P.q) u)) → ((∀ (i
            : Fin 3), ∀ (s : Bool), BandSubtileOccurrence (FordRecursiveQuadruple P)
            (TileTranslation (FordTile P.q) u) i s (TileTranslation (Sc i s) u)) → (∀ (i : Fin (3
            : ℕ)), ∀ (s : Bool), TileCentroid (S i s) = TileCentroid (TileTranslation (Sc i s)
            u)))) ) := by
  classical
  intro P T S u hS Sc hrootObs hScTranslated i s
  have hs := (hS i s).2.2
  have hc := (hScTranslated i s).2.2
  have hoff : TileCentroid (S i s) - TileCentroid T =
      TileCentroid (TileTranslation (Sc i s) u) -
        TileCentroid (TileTranslation (FordTile P.q) u) := hs.trans hc.symm
  calc
    TileCentroid (S i s) =
        (TileCentroid (S i s) - TileCentroid T) + TileCentroid T := by
          ext <;> simp [sub_eq_add_neg, add_comm]
    _ = (TileCentroid (TileTranslation (Sc i s) u) -
          TileCentroid (TileTranslation (FordTile P.q) u)) + TileCentroid T := by
            rw [hoff]
    _ = TileCentroid (TileTranslation (Sc i s) u) := by
          rw [hrootObs.2.2.2.2]
          ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm]

private theorem hparentObs :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u :
            GaussianInt), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            (FordRecursiveQuadruple P) T i s (S i s)) → (∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin 3), ∀ (s : Bool), BandSubtileOccurrence (FordRecursiveQuadruple P)
            (TileTranslation (FordTile P.q) u) i s (TileTranslation (Sc i s) u)) → ((∀ (i : Fin
            3), ∀ (s : Bool), TileCentroid (S i s) = TileCentroid (TileTranslation (Sc i s) u)) →
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), FootprintVertices (S i s) = FootprintVertices
            (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices (S i s) =
            BoundaryFootprintVertices (TileTranslation (Sc i s) u)))) ) := by
  classical
  intro P T S u hS Sc hScTranslated hparentCentroid i s
  have heq := BandPrototileCentroidUnique _ _ _ (hS i s).1
    (hScTranslated i s).1 (hparentCentroid i s)
  have obs := ProtoTileObservableExtensionality (S i s)
    (TileTranslation (Sc i s) u) heq.1 heq.2
  exact ⟨obs.1, obs.2.1⟩

private theorem hparentCells :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u :
            GaussianInt), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            (FordRecursiveQuadruple P) T i s (S i s)) → (∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin 3), ∀ (s : Bool), BandSubtileOccurrence (FordRecursiveQuadruple P)
            (TileTranslation (FordTile P.q) u) i s (TileTranslation (Sc i s) u)) → ((∀ (i : Fin
            3), ∀ (s : Bool), TileCentroid (S i s) = TileCentroid (TileTranslation (Sc i s) u)) →
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (S i s).cells = (TileTranslation (Sc i s)
            u).cells))) ) := by
  classical
  intro P T S u hS Sc hScTranslated hparentCentroid i s
  exact (BandPrototileCentroidUnique _ _ _ (hS i s).1
    (hScTranslated i s).1 (hparentCentroid i s)).1

private theorem hrpos :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → ((GaussianInt) → ((GaussianInt) → (0 <
            P.q₁))) ) := by
  classical
  intro P hP u x
  by_contra hn
  have hz : P.q₁ = 0 := by omega
  have hqint : 1 < (P.q : Int) := by exact_mod_cast hP
  have hdet := P.det₁
  rw [hz] at hdet
  have hdiv : (P.q : Int) ∣ 1 := by
    refine ⟨P.p₁, ?_⟩
    simpa [mul_comm] using hdet.symm
  have hu := Int.eq_one_of_dvd_one (by omega : (0 : Int) ≤ P.q) hdiv
  have : P.q = 1 := by exact_mod_cast hu
  omega

private theorem rectBoundary :
    (by
      classical
      exact
        (FordFareyParameter) → ((GaussianInt) → ((GaussianInt) → (∀ (l : ℤ), ∀ (r : ℤ), ∀ (b :
            ℤ), ∀ (t : ℤ), ∀ (z : GaussianInt), z ∈ LatticeVertexBoundary {w : GaussianInt | l ≤
            w.re ∧ w.re ≤ r ∧ b ≤ w.im ∧ w.im ≤ t} ↔ (l ≤ z.re ∧ z.re ≤ r ∧ b ≤ z.im ∧ z.im ≤ t)
            ∧ (z.re = l ∨ z.re = r ∨ z.im = b ∨ z.im = t)))) ) := by
  classical
  intro P u x l r b t z
  constructor
  · rintro ⟨hz, w, hw, hre, him⟩
    refine ⟨hz, ?_⟩
    change l ≤ z.re ∧ z.re ≤ r ∧ b ≤ z.im ∧ z.im ≤ t at hz
    change ¬(l ≤ w.re ∧ w.re ≤ r ∧ b ≤ w.im ∧ w.im ≤ t) at hw
    omega
  · rintro ⟨hz, he⟩
    refine ⟨hz, ?_⟩
    rcases he with he | he | he | he
    · refine ⟨⟨z.re - 1, z.im⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re + 1, z.im⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re, z.im - 1⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re, z.im + 1⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega

private theorem boundaryTranslation :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), z ∈
            BoundaryFootprintVertices (TileTranslation A v) ↔ z - v ∈ BoundaryFootprintVertices A
            ) := by
  classical
  intro A v z
  rw [(TileTranslationFormulas A v).2.2.2.2.2.2.2.1]
  constructor
  · rintro ⟨w, hw, he⟩
    have he' : w = z - v := by
      rw [← he]
      dsimp [GaussianTranslation]
      abel
    simpa [he'] using hw
  · intro hz
    exact ⟨z - v, hz, by dsimp [GaussianTranslation]; abel⟩

private theorem footprintTranslation :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), z ∈ FootprintVertices
            (TileTranslation A v) ↔ z - v ∈ FootprintVertices A ) := by
  classical
  intro A v z
  rw [(TileTranslationFormulas A v).2.2.2.2.2.1]
  constructor
  · rintro ⟨w, hw, he⟩
    have he' : w = z - v := by
      rw [← he]
      dsimp [GaussianTranslation]
      abel
    simpa [he'] using hw
  · intro hz
    exact ⟨z - v, hz, by dsimp [GaussianTranslation]; abel⟩

private theorem hSc00 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (0 : Fin (3 :
            ℕ)) true).cells = (FordTile P.q₁).cells) → ((0 < P.q₁) → (BoundaryFootprintVertices
            (Sc 0 true) = BoundaryFootprintVertices (FordTile P.q₁))) ) := by
  classical
  intro P Sc h00 hrpos
  have hne : (FordTile P.q₁).cells.Nonempty := by
    refine ⟨⟨0, 0⟩, ?_⟩
    simp only [FordTile, FordCellDomain, Int.reduceNeg, Finset.product_eq_sprod,
        Finset.mem_image, Finset.mem_product, Finset.mem_range, Zsqrtd.mk.injEq,
        Int.natCast_eq_zero, Prod.exists, exists_eq_right_right, exists_eq_right, and_self]
    exact hrpos
  have ha : (Sc 0 true).cells = ∅ →
      (Sc 0 true).anchor = (FordTile P.q₁).anchor := by
    intro he
    have hempty : (FordTile P.q₁).cells = ∅ := h00.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h00 ha).2.1

private theorem hSc01 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (0 : Fin (3 :
            ℕ)) false).cells = (TileTranslation (FordTile P.q₁) ⟨(↑P.q₂ : ℤ), (↑P.q₂ :
            ℤ)⟩).cells) → ((0 < P.q₁) → (BoundaryFootprintVertices (Sc 0 false) =
            BoundaryFootprintVertices (TileTranslation (FordTile P.q₁) ⟨(P.q₂ : Int), (P.q₂ :
            Int)⟩))) ) := by
  classical
  intro P Sc h01 hrpos
  have hbase : (FordTile P.q₁).cells.Nonempty := by
    exact ⟨⟨0, 0⟩, by simp [FordTile, FordCellDomain, hrpos]⟩
  have hne : (TileTranslation (FordTile P.q₁)
      ⟨(P.q₂ : Int), (P.q₂ : Int)⟩).cells.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [(TileTranslationFormulas _ _).2.2.1] at he
    exact (Finset.nonempty_iff_ne_empty.mp hbase) he
  have ha : (Sc 0 false).cells = ∅ →
      (Sc 0 false).anchor =
        (TileTranslation (FordTile P.q₁)
          ⟨(P.q₂ : Int), (P.q₂ : Int)⟩).anchor := by
    intro he
    have hempty := h01.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h01 ha).2.1

private theorem hSc10 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (1 : Fin (3 :
            ℕ)) true).cells = (TileTranslation (FordTile P.q₂) ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩).cells) →
            (BoundaryFootprintVertices (Sc 1 true) = BoundaryFootprintVertices (TileTranslation
            (FordTile P.q₂) ⟨(P.q₁ : Int), 0⟩)) ) := by
  classical
  intro P Sc h10
  have hbase : (FordTile P.q₂).cells.Nonempty := by
    exact ⟨⟨0, 0⟩, by simp [FordTile, FordCellDomain, P.q₂_pos]⟩
  have hne : (TileTranslation (FordTile P.q₂)
      ⟨(P.q₁ : Int), 0⟩).cells.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [(TileTranslationFormulas _ _).2.2.1] at he
    exact (Finset.nonempty_iff_ne_empty.mp hbase) he
  have ha : (Sc 1 true).cells = ∅ →
      (Sc 1 true).anchor =
        (TileTranslation (FordTile P.q₂) ⟨(P.q₁ : Int), 0⟩).anchor := by
    intro he
    have hempty := h10.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h10 ha).2.1

private theorem hSc11 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (1 : Fin (3 :
            ℕ)) false).cells = (TileTranslation (FordTile P.q₂) ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩).cells) →
            (BoundaryFootprintVertices (Sc 1 false) = BoundaryFootprintVertices (TileTranslation
            (FordTile P.q₂) ⟨0, (P.q₁ : Int)⟩)) ) := by
  classical
  intro P Sc h11
  have hbase : (FordTile P.q₂).cells.Nonempty := by
    exact ⟨⟨0, 0⟩, by simp [FordTile, FordCellDomain, P.q₂_pos]⟩
  have hne : (TileTranslation (FordTile P.q₂)
      ⟨0, (P.q₁ : Int)⟩).cells.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [(TileTranslationFormulas _ _).2.2.1] at he
    exact (Finset.nonempty_iff_ne_empty.mp hbase) he
  have ha : (Sc 1 false).cells = ∅ →
      (Sc 1 false).anchor =
        (TileTranslation (FordTile P.q₂) ⟨0, (P.q₁ : Int)⟩).anchor := by
    intro he
    have hempty := h11.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h11 ha).2.1

private theorem hSc00Foot :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (0 : Fin (3 :
            ℕ)) true).cells = (FordTile P.q₁).cells) → ((0 < P.q₁) → (FootprintVertices (Sc 0
            true) = FootprintVertices (FordTile P.q₁))) ) := by
  classical
  intro P Sc h00 hrpos
  have hne : (FordTile P.q₁).cells.Nonempty :=
    ⟨⟨0, 0⟩, by simp [FordTile, FordCellDomain, hrpos]⟩
  have ha : (Sc 0 true).cells = ∅ →
      (Sc 0 true).anchor = (FordTile P.q₁).anchor := by
    intro he
    have hempty := h00.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h00 ha).1

private theorem hSc01Foot :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (0 : Fin (3 :
            ℕ)) false).cells = (TileTranslation (FordTile P.q₁) ⟨(↑P.q₂ : ℤ), (↑P.q₂ :
            ℤ)⟩).cells) → ((0 < P.q₁) → (FootprintVertices (Sc 0 false) = FootprintVertices
            (TileTranslation (FordTile P.q₁) ⟨(P.q₂ : Int), (P.q₂ : Int)⟩))) ) := by
  classical
  intro P Sc h01 hrpos
  have hbase : (FordTile P.q₁).cells.Nonempty :=
    ⟨⟨0, 0⟩, by simp [FordTile, FordCellDomain, hrpos]⟩
  have hne : (TileTranslation (FordTile P.q₁)
      ⟨(P.q₂ : Int), (P.q₂ : Int)⟩).cells.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [(TileTranslationFormulas _ _).2.2.1] at he
    exact (Finset.nonempty_iff_ne_empty.mp hbase) he
  have ha : (Sc 0 false).cells = ∅ →
      (Sc 0 false).anchor =
        (TileTranslation (FordTile P.q₁)
          ⟨(P.q₂ : Int), (P.q₂ : Int)⟩).anchor := by
    intro he
    have hempty := h01.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h01 ha).1

private theorem hSc10Foot :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (1 : Fin (3 :
            ℕ)) true).cells = (TileTranslation (FordTile P.q₂) ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩).cells) →
            (FootprintVertices (Sc 1 true) = FootprintVertices (TileTranslation (FordTile P.q₂)
            ⟨(P.q₁ : Int), 0⟩)) ) := by
  classical
  intro P Sc h10
  have hbase : (FordTile P.q₂).cells.Nonempty :=
    ⟨⟨0, 0⟩, by simp [FordTile, FordCellDomain, P.q₂_pos]⟩
  have hne : (TileTranslation (FordTile P.q₂)
      ⟨(P.q₁ : Int), 0⟩).cells.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [(TileTranslationFormulas _ _).2.2.1] at he
    exact (Finset.nonempty_iff_ne_empty.mp hbase) he
  have ha : (Sc 1 true).cells = ∅ →
      (Sc 1 true).anchor =
        (TileTranslation (FordTile P.q₂) ⟨(P.q₁ : Int), 0⟩).anchor := by
    intro he
    have hempty := h10.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h10 ha).1

private theorem hSc11Foot :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (1 : Fin (3 :
            ℕ)) false).cells = (TileTranslation (FordTile P.q₂) ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩).cells) →
            (FootprintVertices (Sc 1 false) = FootprintVertices (TileTranslation (FordTile P.q₂)
            ⟨0, (P.q₁ : Int)⟩)) ) := by
  classical
  intro P Sc h11
  have hbase : (FordTile P.q₂).cells.Nonempty :=
    ⟨⟨0, 0⟩, by simp [FordTile, FordCellDomain, P.q₂_pos]⟩
  have hne : (TileTranslation (FordTile P.q₂)
      ⟨0, (P.q₁ : Int)⟩).cells.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [(TileTranslationFormulas _ _).2.2.1] at he
    exact (Finset.nonempty_iff_ne_empty.mp hbase) he
  have ha : (Sc 1 false).cells = ∅ →
      (Sc 1 false).anchor =
        (TileTranslation (FordTile P.q₂) ⟨0, (P.q₁ : Int)⟩).anchor := by
    intro he
    have hempty := h11.symm.trans he
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp hne) hempty)
  exact (ProtoTileObservableExtensionality _ _ h11 ha).1

private theorem foot0 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → ((0 < P.q₁) → ((∀
            (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), z ∈ FootprintVertices
            (TileTranslation A v) ↔ z - v ∈ FootprintVertices A) → ((FootprintVertices (Sc 0
            true) = FootprintVertices (FordTile P.q₁)) → (x ∈ FootprintVertices (S 0 true) ↔ 0 ≤
            y.re ∧ y.re ≤ P.q₁ ∧ 0 ≤ y.im ∧ y.im ≤ P.q₁)))) ) := by
  classical
  intro P S u x y Sc hparentObs hrpos footprintTranslation hSc00Foot
  rw [(hparentObs 0 true).1, footprintTranslation, hSc00Foot,
    (P4062T1CanonicalSupport P.q₁ hrpos).1]
  dsimp [FordVertexDomain, y]
  rfl

private theorem foot1 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → ((0 < P.q₁) →
            (((P.q : Int) = P.q₁ + P.q₂) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z :
            GaussianInt), z ∈ FootprintVertices (TileTranslation A v) ↔ z - v ∈ FootprintVertices
            A) → ((FootprintVertices (Sc 0 false) = FootprintVertices (TileTranslation (FordTile
            P.q₁) ⟨(P.q₂ : Int), (P.q₂ : Int)⟩)) → (x ∈ FootprintVertices (S 0 false) ↔ P.q₂ ≤
            y.re ∧ y.re ≤ P.q ∧ P.q₂ ≤ y.im ∧ y.im ≤ P.q))))) ) := by
  classical
  intro P S u x y Sc hparentObs hrpos hqsum footprintTranslation hSc01Foot
  rw [(hparentObs 0 false).1, footprintTranslation, hSc01Foot,
    footprintTranslation, (P4062T1CanonicalSupport P.q₁ hrpos).1]
  dsimp [FordVertexDomain, y]
  omega

private theorem foot2 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → (((P.q : Int) =
            P.q₁ + P.q₂) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), z ∈
            FootprintVertices (TileTranslation A v) ↔ z - v ∈ FootprintVertices A) →
            ((FootprintVertices (Sc 1 true) = FootprintVertices (TileTranslation (FordTile P.q₂)
            ⟨(P.q₁ : Int), 0⟩)) → (x ∈ FootprintVertices (S 1 true) ↔ P.q₁ ≤ y.re ∧ y.re ≤ P.q ∧
            0 ≤ y.im ∧ y.im ≤ P.q₂)))) ) := by
  classical
  intro P S u x y Sc hparentObs hqsum footprintTranslation hSc10Foot
  rw [(hparentObs 1 true).1, footprintTranslation, hSc10Foot,
    footprintTranslation, (P4062T1CanonicalSupport P.q₂ P.q₂_pos).1]
  dsimp [FordVertexDomain, y]
  omega

private theorem foot3 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → (((P.q : Int) =
            P.q₁ + P.q₂) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), z ∈
            FootprintVertices (TileTranslation A v) ↔ z - v ∈ FootprintVertices A) →
            ((FootprintVertices (Sc 1 false) = FootprintVertices (TileTranslation (FordTile P.q₂)
            ⟨0, (P.q₁ : Int)⟩)) → (x ∈ FootprintVertices (S 1 false) ↔ 0 ≤ y.re ∧ y.re ≤ P.q₂ ∧
            P.q₁ ≤ y.im ∧ y.im ≤ P.q)))) ) := by
  classical
  intro P S u x y Sc hparentObs hqsum footprintTranslation hSc11Foot
  rw [(hparentObs 1 false).1, footprintTranslation, hSc11Foot,
    footprintTranslation, (P4062T1CanonicalSupport P.q₂ P.q₂_pos).1]
  dsimp [FordVertexDomain, y]
  omega

private theorem squareBoundary :
    (by
      classical
      exact
        ∀ (n : ℕ), (0 : ℕ) < n → ∀ (z : GaussianInt), z ∈ BoundaryFootprintVertices (FordTile n)
            ↔ (0 : ℤ) ≤ z.re ∧ z.re ≤ (↑n : ℤ) ∧ (0 : ℤ) ≤ z.im ∧ z.im ≤ (↑n : ℤ) ∧ (z.re = (0 :
            ℤ) ∨ z.re = (↑n : ℤ) ∨ z.im = (0 : ℤ) ∨ z.im = (↑n : ℤ)) ) := by
  classical
  intro n hn z
  have hb := (P4062T1CanonicalSupport n hn).2
  rw [hb]
  simp only [Set.mem_ofPred_eq]

private theorem domain0 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        (∀ (l : Int), ∀ (r : Int), ∀ (b : Int), ∀ (t : Int), ∀ (z : GaussianInt), z ∈
            LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤ r ∧ b ≤ w.im ∧ w.im ≤ t} ↔
            (l ≤ z.re ∧ z.re ≤ r ∧ b ≤ z.im ∧ z.im ≤ t) ∧ (z.re = l ∨ z.re = r ∨ z.im = b ∨ z.im
            = t)) → (y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) ↔ (0 : Int) ≤
            y.re ∧ y.re ≤ P.q₁ ∧ 0 ≤ y.im ∧ y.im ≤ P.q₁ ∧ (y.re = 0 ∨ y.re = P.q₁ ∨ y.im = 0 ∨
            y.im = P.q₁)) ) := by
  classical
  intro P u x y rectBoundary
  change y ∈ LatticeVertexBoundary {z : GaussianInt |
    0 ≤ z.re ∧ z.re ≤ P.q₁ ∧ 0 ≤ z.im ∧ z.im ≤ P.q₁} ↔ _
  rw [rectBoundary]
  simp only [and_assoc]

private theorem domain1 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        (∀ (l : Int), ∀ (r : Int), ∀ (b : Int), ∀ (t : Int), ∀ (z : GaussianInt), z ∈
            LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤ r ∧ b ≤ w.im ∧ w.im ≤ t} ↔
            (l ≤ z.re ∧ z.re ≤ r ∧ b ≤ z.im ∧ z.im ≤ t) ∧ (z.re = l ∨ z.re = r ∨ z.im = b ∨ z.im
            = t)) → (y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) ↔ (P.q₂ : Int) ≤
            y.re ∧ y.re ≤ P.q ∧ P.q₂ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = P.q₂ ∨ y.re = P.q ∨ y.im =
            P.q₂ ∨ y.im = P.q)) ) := by
  classical
  intro P u x y rectBoundary
  change y ∈ LatticeVertexBoundary {z : GaussianInt |
    P.q₂ ≤ z.re ∧ z.re ≤ P.q ∧ P.q₂ ≤ z.im ∧ z.im ≤ P.q} ↔ _
  rw [rectBoundary]
  simp only [and_assoc]

private theorem domain2 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        (∀ (l : Int), ∀ (r : Int), ∀ (b : Int), ∀ (t : Int), ∀ (z : GaussianInt), z ∈
            LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤ r ∧ b ≤ w.im ∧ w.im ≤ t} ↔
            (l ≤ z.re ∧ z.re ≤ r ∧ b ≤ z.im ∧ z.im ≤ t) ∧ (z.re = l ∨ z.re = r ∨ z.im = b ∨ z.im
            = t)) → (y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) ↔ P.q₁ ≤ y.re ∧
            y.re ≤ P.q ∧ (0 : Int) ≤ y.im ∧ y.im ≤ P.q₂ ∧ (y.re = P.q₁ ∨ y.re = P.q ∨ y.im = 0 ∨
            y.im = P.q₂)) ) := by
  classical
  intro P u x y rectBoundary
  change y ∈ LatticeVertexBoundary {z : GaussianInt |
    P.q₁ ≤ z.re ∧ z.re ≤ P.q ∧ 0 ≤ z.im ∧ z.im ≤ P.q₂} ↔ _
  rw [rectBoundary]
  simp only [and_assoc]

private theorem domain3 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        (∀ (l : Int), ∀ (r : Int), ∀ (b : Int), ∀ (t : Int), ∀ (z : GaussianInt), z ∈
            LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤ r ∧ b ≤ w.im ∧ w.im ≤ t} ↔
            (l ≤ z.re ∧ z.re ≤ r ∧ b ≤ z.im ∧ z.im ≤ t) ∧ (z.re = l ∨ z.re = r ∨ z.im = b ∨ z.im
            = t)) → (y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) ↔ (0 : Int) ≤
            y.re ∧ y.re ≤ P.q₂ ∧ P.q₁ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = 0 ∨ y.re = P.q₂ ∨ y.im = P.q₁
            ∨ y.im = P.q)) ) := by
  classical
  intro P u x y rectBoundary
  change y ∈ LatticeVertexBoundary {z : GaussianInt |
    0 ≤ z.re ∧ z.re ≤ P.q₂ ∧ P.q₁ ≤ z.im ∧ z.im ≤ P.q} ↔ _
  rw [rectBoundary]
  simp only [and_assoc]

private theorem label0 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → ((0 < P.q₁) → ((∀
            (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), z ∈
            BoundaryFootprintVertices (TileTranslation A v) ↔ z - v ∈ BoundaryFootprintVertices
            A) → ((BoundaryFootprintVertices (Sc 0 true) = BoundaryFootprintVertices (FordTile
            P.q₁)) → ((∀ (n : Nat), (0 < n) → (∀ (z : GaussianInt), z ∈ BoundaryFootprintVertices
            (FordTile n) ↔ 0 ≤ z.re ∧ z.re ≤ (n : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (n : Int) ∧ (z.re = 0
            ∨ z.re = n ∨ z.im = 0 ∨ z.im = n))) → ((y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0) ↔ (0 : Int) ≤ y.re ∧ y.re ≤ P.q₁ ∧ 0 ≤ y.im ∧ y.im ≤
            P.q₁ ∧ (y.re = 0 ∨ y.re = P.q₁ ∨ y.im = 0 ∨ y.im = P.q₁)) → (x ∈
            BoundaryFootprintVertices (S 0 true) ↔ y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0))))))) ) := by
  classical
  intro P S u x y Sc hparentObs hrpos boundaryTranslation hSc00 squareBoundary domain0
  rw [(hparentObs 0 true).2, boundaryTranslation, hSc00]
  rw [squareBoundary P.q₁ hrpos]
  dsimp [y]
  rw [domain0]
  exact Iff.rfl

private theorem label1 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → ((0 < P.q₁) →
            (((P.q : Int) = P.q₁ + P.q₂) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z :
            GaussianInt), z ∈ BoundaryFootprintVertices (TileTranslation A v) ↔ z - v ∈
            BoundaryFootprintVertices A) → ((BoundaryFootprintVertices (Sc 0 false) =
            BoundaryFootprintVertices (TileTranslation (FordTile P.q₁) ⟨(P.q₂ : Int), (P.q₂ :
            Int)⟩)) → ((∀ (n : Nat), (0 < n) → (∀ (z : GaussianInt), z ∈
            BoundaryFootprintVertices (FordTile n) ↔ 0 ≤ z.re ∧ z.re ≤ (n : Int) ∧ 0 ≤ z.im ∧
            z.im ≤ (n : Int) ∧ (z.re = 0 ∨ z.re = n ∨ z.im = 0 ∨ z.im = n))) → ((y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 1) ↔ (P.q₂ : Int) ≤ y.re ∧ y.re ≤
            P.q ∧ P.q₂ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = P.q₂ ∨ y.re = P.q ∨ y.im = P.q₂ ∨ y.im =
            P.q)) → (x ∈ BoundaryFootprintVertices (S 0 false) ↔ y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 1)))))))) ) := by
  classical
  intro P S u x y Sc hparentObs hrpos hqsum boundaryTranslation hSc01 squareBoundary domain1
  rw [(hparentObs 0 false).2, boundaryTranslation, hSc01]
  rw [boundaryTranslation, squareBoundary P.q₁ hrpos]
  rw [domain1]
  dsimp [y]
  omega

private theorem label2 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → (((P.q₂ : Int) >
            0) → (((P.q : Int) = P.q₁ + P.q₂) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z :
            GaussianInt), z ∈ BoundaryFootprintVertices (TileTranslation A v) ↔ z - v ∈
            BoundaryFootprintVertices A) → ((BoundaryFootprintVertices (Sc 1 true) =
            BoundaryFootprintVertices (TileTranslation (FordTile P.q₂) ⟨(P.q₁ : Int), 0⟩)) → ((∀
            (n : Nat), (0 < n) → (∀ (z : GaussianInt), z ∈ BoundaryFootprintVertices (FordTile n)
            ↔ 0 ≤ z.re ∧ z.re ≤ (n : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (n : Int) ∧ (z.re = 0 ∨ z.re = n ∨
            z.im = 0 ∨ z.im = n))) → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2)
            ↔ P.q₁ ≤ y.re ∧ y.re ≤ P.q ∧ (0 : Int) ≤ y.im ∧ y.im ≤ P.q₂ ∧ (y.re = P.q₁ ∨ y.re =
            P.q ∨ y.im = 0 ∨ y.im = P.q₂)) → (x ∈ BoundaryFootprintVertices (S 1 true) ↔ y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 2)))))))) ) := by
  classical
  intro P S u x y Sc hparentObs ht hqsum boundaryTranslation hSc10 squareBoundary domain2
  rw [(hparentObs 1 true).2, boundaryTranslation, hSc10]
  rw [boundaryTranslation, squareBoundary P.q₂ P.q₂_pos]
  rw [domain2]
  dsimp [y]
  omega

private theorem label3 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices
            (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧ BoundaryFootprintVertices
            (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i s) u)) → (((P.q₂ : Int) >
            0) → (((P.q : Int) = P.q₁ + P.q₂) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z :
            GaussianInt), z ∈ BoundaryFootprintVertices (TileTranslation A v) ↔ z - v ∈
            BoundaryFootprintVertices A) → ((BoundaryFootprintVertices (Sc 1 false) =
            BoundaryFootprintVertices (TileTranslation (FordTile P.q₂) ⟨0, (P.q₁ : Int)⟩)) → ((∀
            (n : Nat), (0 < n) → (∀ (z : GaussianInt), z ∈ BoundaryFootprintVertices (FordTile n)
            ↔ 0 ≤ z.re ∧ z.re ≤ (n : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (n : Int) ∧ (z.re = 0 ∨ z.re = n ∨
            z.im = 0 ∨ z.im = n))) → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3)
            ↔ (0 : Int) ≤ y.re ∧ y.re ≤ P.q₂ ∧ P.q₁ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = 0 ∨ y.re = P.q₂
            ∨ y.im = P.q₁ ∨ y.im = P.q)) → (x ∈ BoundaryFootprintVertices (S 1 false) ↔ y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 3)))))))) ) := by
  classical
  intro P S u x y Sc hparentObs ht hqsum boundaryTranslation hSc11 squareBoundary domain3
  rw [(hparentObs 1 false).2, boundaryTranslation, hSc11]
  rw [boundaryTranslation, squareBoundary P.q₂ P.q₂_pos]
  rw [domain3]
  dsimp [y]
  omega

private theorem lineTrue :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1) → (∀ (Sc : Fin (3
            : ℕ) → Bool → ProtoTile), ((Sc (2 : Fin (3 : ℕ)) true).cells = ∅) → (((Sc (2 : Fin (3
            : ℕ)) true).anchor = ⟨(↑P.q₂ : ℤ), (↑P.q : ℤ)⟩) → ((∀ (i : Fin 3), ∀ (s : Bool),
            FootprintVertices (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧
            BoundaryFootprintVertices (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i
            s) u)) → (((P.q : Int) = P.q₁ + P.q₂) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀
            (z : GaussianInt), z ∈ BoundaryFootprintVertices (TileTranslation A v) ↔ z - v ∈
            BoundaryFootprintVertices A) → (x ∉ BoundaryFootprintVertices (S 2 true))))))) ) := by
  classical
  intro P S u x y hbounds Sc h20 h20a hparentObs hqsum boundaryTranslation
  rw [(hparentObs 2 true).2, boundaryTranslation]
  simp only [BoundaryFootprintVertices, h20, Finset.not_nonempty_iff_eq_empty,
    ite_eq_right, Set.mem_singleton_iff, h20a]
  intro he
  have him : (x - u).im = (P.q : Int) := by
    simpa using congrArg (fun z : GaussianInt => z.im) he
  have hi : (x - u).im ≤ (P.q : Int) - 1 := by
    simpa [y] using hbounds.2.2.2
  omega

private theorem lineFalse :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1) → (∀ (Sc : Fin (3
            : ℕ) → Bool → ProtoTile), ((Sc (2 : Fin (3 : ℕ)) false).cells = ∅) → (((Sc (2 : Fin
            (3 : ℕ)) false).anchor = ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) → ((∀ (i : Fin 3), ∀ (s : Bool),
            FootprintVertices (S i s) = FootprintVertices (TileTranslation (Sc i s) u) ∧
            BoundaryFootprintVertices (S i s) = BoundaryFootprintVertices (TileTranslation (Sc i
            s) u)) → ((∀ (A : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), z ∈
            BoundaryFootprintVertices (TileTranslation A v) ↔ z - v ∈ BoundaryFootprintVertices
            A) → (x ∉ BoundaryFootprintVertices (S 2 false)))))) ) := by
  classical
  intro P S u x y hbounds Sc h21 h21a hparentObs boundaryTranslation
  rw [(hparentObs 2 false).2, boundaryTranslation]
  simp only [BoundaryFootprintVertices, h21, Finset.not_nonempty_iff_eq_empty,
    ite_eq_right, Set.mem_singleton_iff, h21a]
  intro he
  have him : (x - u).im = 0 := by
    simpa using congrArg (fun z : GaussianInt => z.im) he
  have hi : 1 ≤ (x - u).im := by simpa [y] using hbounds.2.2.1
  omega

private theorem hcardSix :
    (by
      classical
      exact
        ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} = (if x ∈
            BoundaryFootprintVertices (S 0 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 0 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 false) then 1 else 0) ) := by
  classical
  intro S x
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter fun a : Fin 3 × Bool =>
      x ∈ BoundaryFootprintVertices (S a.1 a.2)).card = _
  simp only [Finset.card_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Fintype.sum_bool, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

private theorem hcardFour :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        FordBoundaryMultiplicity P y = Nat.card
            {i : Fin 4 // y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)} ) := by
  classical
  intro P u x y
  classical
  unfold FordBoundaryMultiplicity
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem hcardFourFormula :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (Fin 3 → Bool → ProtoTile) → (∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        FordBoundaryMultiplicity P y = (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains
            P 0) then 1 else 0) + (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1)
            then 1 else 0) + (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) then
            1 else 0) + (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) then 1
            else 0)) ) := by
  classical
  intro P S u x y
  classical
  unfold FordBoundaryMultiplicity
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) then 1 else 0) +
    ((if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) then 1 else 0) +
    ((if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) then 1 else 0) +
    (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) then 1 else 0))) = _
  omega

private theorem hcount :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        (x ∈ BoundaryFootprintVertices (S 0 true) ↔ y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0)) → ((x ∈ BoundaryFootprintVertices (S 0 false) ↔ y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 1)) → ((x ∈
            BoundaryFootprintVertices (S 1 true) ↔ y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 2)) → ((x ∈ BoundaryFootprintVertices (S 1 false) ↔ y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 3)) → ((x ∉
            BoundaryFootprintVertices (S 2 true)) → ((x ∉ BoundaryFootprintVertices (S 2 false))
            → ((Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} = (if x
            ∈ BoundaryFootprintVertices (S 0 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 0 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 false) then 1 else 0)) → ((FordBoundaryMultiplicity P
            y = (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) then 1 else 0) +
            (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) then 1 else 0) + (if y
            ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) then 1 else 0) + (if y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 3) then 1 else 0)) → (Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} =
            FordBoundaryMultiplicity P y)))))))) ) := by
  classical
  intro P S u x y label0 label1 label2 label3 lineTrue lineFalse hcardSix hcardFourFormula
  rw [hcardSix, hcardFourFormula]
  rw [label0, label1, label2, label3]
  simp only [ite_eq_right lineTrue, ite_eq_right lineFalse]
  omega

private theorem rootCentroid :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (TileCentroid
            (FordTile P.q) = ((P.q : Real) / 2, (P.q : Real) / 2)) → ((FootprintVertices T =
            FootprintVertices (TileTranslation (FordTile P.q) u) ∧ BoundaryFootprintVertices T =
            BoundaryFootprintVertices (TileTranslation (FordTile P.q) u) ∧ BoundaryFootprintEdges
            T = BoundaryFootprintEdges (TileTranslation (FordTile P.q) u) ∧ TileRealization T =
            TileRealization (TileTranslation (FordTile P.q) u) ∧ TileCentroid T = TileCentroid
            (TileTranslation (FordTile P.q) u)) → (TileCentroid T = ((P.q : Real) / 2 + (u.re :
            Real), (P.q : Real) / 2 + (u.im : Real)))) ) := by
  classical
  intro P T u fordCentroid hrootObs
  rw [hrootObs.2.2.2.2,
    (TileTranslationFormulas (FordTile P.q) u).2.2.2.2.1,
    fordCentroid]

private theorem centerCoords :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        (TileCentroid T = ((P.q : Real) / 2 + (u.re : Real), (P.q : Real) / 2 + (u.im : Real))) →
            (GaussianRealPoint x = TileCentroid T → (↑y.re : ℝ) = (↑P.q : ℝ) / (2 : ℝ) ∧ (↑y.im :
            ℝ) = (↑P.q : ℝ) / (2 : ℝ)) ) := by
  classical
  intro P T u x y rootCentroid hc
  rw [rootCentroid] at hc
  dsimp [GaussianRealPoint] at hc
  have hr := congrArg Prod.fst hc
  have hi := congrArg Prod.snd hc
  constructor
  · dsimp [y]
    push_cast at hr ⊢
    linarith
  · dsimp [y]
    push_cast at hi ⊢
    linarith

private theorem centerTwice :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        ((GaussianRealPoint x = TileCentroid T) → (((y.re : Int) : Real) = (P.q : Real) / 2 ∧
            ((y.im : Int) : Real) = (P.q : Real) / 2)) → (GaussianRealPoint x = TileCentroid T →
            (2 : ℤ) * y.re = (↑P.q : ℤ) ∧ (2 : ℤ) * y.im = (↑P.q : ℤ)) ) := by
  classical
  intro P T u x y centerCoords hc
  obtain ⟨hrc, hic⟩ := centerCoords hc
  constructor
  · have he : ((2 * y.re : Int) : Real) = (P.q : Real) := by
      push_cast
      linarith
    exact_mod_cast he
  · have he : ((2 * y.im : Int) : Real) = (P.q : Real) := by
      push_cast
      linarith
    exact_mod_cast he

private theorem noCenteredCountTwo :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (T : ProtoTile), (Fin 3 → Bool →
            ProtoTile) → (∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1) → ((0 < P.q₁) →
            (((P.q : Int) = P.q₁ + P.q₂) → ((y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0) ↔ (0 : Int) ≤ y.re ∧ y.re ≤ P.q₁ ∧ 0 ≤ y.im ∧ y.im ≤
            P.q₁ ∧ (y.re = 0 ∨ y.re = P.q₁ ∨ y.im = 0 ∨ y.im = P.q₁)) → ((y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 1) ↔ (P.q₂ : Int) ≤ y.re ∧ y.re ≤
            P.q ∧ P.q₂ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = P.q₂ ∨ y.re = P.q ∨ y.im = P.q₂ ∨ y.im =
            P.q)) → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) ↔ P.q₁ ≤ y.re ∧
            y.re ≤ P.q ∧ (0 : Int) ≤ y.im ∧ y.im ≤ P.q₂ ∧ (y.re = P.q₁ ∨ y.re = P.q ∨ y.im = 0 ∨
            y.im = P.q₂)) → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) ↔ (0 :
            Int) ≤ y.re ∧ y.re ≤ P.q₂ ∧ P.q₁ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = 0 ∨ y.re = P.q₂ ∨ y.im
            = P.q₁ ∨ y.im = P.q)) → ((FordBoundaryMultiplicity P y = (if y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 0) then 1 else 0) + (if y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 1) then 1 else 0) + (if y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 2) then 1 else 0) + (if y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 3) then 1 else 0)) →
            (((GaussianRealPoint x = TileCentroid T) → (2 * y.re = (P.q : Int) ∧ 2 * y.im = (P.q
            : Int))) → (GaussianRealPoint x = TileCentroid T → FordBoundaryMultiplicity P y ≠ (2
            : ℕ)))))))))))) ) := by
  classical
  intro P hP T S u x y hbounds hrpos hqsum domain0 domain1 domain2 domain3 hcardFourFormula
      centerTwice hc
  obtain ⟨h2re, h2im⟩ := centerTwice hc
  by_cases heq : P.q₁ = P.q₂
  · have d0 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) := by
      apply domain0.mpr
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      exact Or.inr (Or.inl (by omega))
    have d1 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) := by
      apply domain1.mpr
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      exact Or.inl (by omega)
    have d2 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) := by
      apply domain2.mpr
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      exact Or.inl (by omega)
    have d3 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) := by
      apply domain3.mpr
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      exact Or.inr (Or.inr (Or.inl (by omega)))
    intro hm
    rw [hcardFourFormula] at hm
    simp [d0, d1, d2, d3] at hm
  · have nd0 : y ∉ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) := by
      intro hd
      rcases domain0.mp hd with ⟨_, _, _, _, hside⟩
      rcases hside with h | h | h | h <;> omega
    have nd1 : y ∉ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) := by
      intro hd
      rcases domain1.mp hd with ⟨_, _, _, _, hside⟩
      rcases hside with h | h | h | h <;> omega
    have nd2 : y ∉ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) := by
      intro hd
      rcases domain2.mp hd with ⟨_, _, _, _, hside⟩
      rcases hside with h | h | h | h <;> omega
    have nd3 : y ∉ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) := by
      intro hd
      rcases domain3.mp hd with ⟨_, _, _, _, hside⟩
      rcases hside with h | h | h | h <;> omega
    intro hm
    rw [hcardFourFormula] at hm
    simp only [ite_eq_right nd0, ite_eq_right nd1, ite_eq_right nd2, ite_eq_right nd3] at hm
    norm_num at hm

private theorem countFourConclusion :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (T : ProtoTile), ∀ (S : Fin 3 → Bool →
            ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt),
        let y : GaussianInt := x - u
        ((P.q : Int) = P.q₁ + P.q₂) → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P
            0) ↔ (0 : Int) ≤ y.re ∧ y.re ≤ P.q₁ ∧ 0 ≤ y.im ∧ y.im ≤ P.q₁ ∧ (y.re = 0 ∨ y.re =
            P.q₁ ∨ y.im = 0 ∨ y.im = P.q₁)) → ((y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 1) ↔ (P.q₂ : Int) ≤ y.re ∧ y.re ≤ P.q ∧ P.q₂ ≤ y.im ∧
            y.im ≤ P.q ∧ (y.re = P.q₂ ∨ y.re = P.q ∨ y.im = P.q₂ ∨ y.im = P.q)) → ((y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 2) ↔ P.q₁ ≤ y.re ∧ y.re ≤ P.q ∧
            (0 : Int) ≤ y.im ∧ y.im ≤ P.q₂ ∧ (y.re = P.q₁ ∨ y.re = P.q ∨ y.im = 0 ∨ y.im = P.q₂))
            → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) ↔ (0 : Int) ≤ y.re ∧
            y.re ≤ P.q₂ ∧ P.q₁ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = 0 ∨ y.re = P.q₂ ∨ y.im = P.q₁ ∨ y.im
            = P.q)) → ((FordBoundaryMultiplicity P y = (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 1) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 2) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 3) then 1 else 0)) → ((Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} =
            FordBoundaryMultiplicity P y) → ((TileCentroid T = ((P.q : Real) / 2 + (u.re : Real),
            (P.q : Real) / 2 + (u.im : Real))) → (Nat.card
            { a : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2) } = (4 : ℕ) →
            P.q = (2 : ℕ) ∧ GaussianRealPoint x = TileCentroid T))))))))) ) := by
  classical
  intro P hP T S u x y hqsum domain0 domain1 domain2 domain3 hcardFourFormula hcount rootCentroid hk
  have hm : FordBoundaryMultiplicity P y = 4 := hcount.symm.trans hk
  have d0 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) := by
    by_contra hn
    rw [hcardFourFormula] at hm
    simp only [ite_eq_right hn] at hm
    split_ifs at hm <;> omega
  have d1 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) := by
    by_contra hn
    rw [hcardFourFormula] at hm
    simp only [ite_eq_right hn] at hm
    split_ifs at hm <;> omega
  have d2 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) := by
    by_contra hn
    rw [hcardFourFormula] at hm
    simp only [ite_eq_right hn] at hm
    split_ifs at hm <;> omega
  have d3 : y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) := by
    by_contra hn
    rw [hcardFourFormula] at hm
    simp only [ite_eq_right hn] at hm
    split_ifs at hm; omega
  rcases domain0.mp d0 with ⟨_, h0r, _, h0i, _⟩
  rcases domain1.mp d1 with ⟨h1r, _, h1i, _, _⟩
  rcases domain2.mp d2 with ⟨h2r, _, _, h2i, _⟩
  rcases domain3.mp d3 with ⟨_, h3r, h3i, _, _⟩
  have heq : P.q₁ = P.q₂ := by
    apply Nat.le_antisymm
    · exact_mod_cast (le_trans (show (P.q₁ : Int) ≤ y.im by omega) h2i)
    · exact_mod_cast (le_trans (show (P.q₂ : Int) ≤ y.re by omega) h0r)
  have hqeq : (P.q : Int) = 2 * (P.q₁ : Int) := by
    have hs : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by
      exact_mod_cast P.sum_q
    have heq' : (P.q₁ : Int) = (P.q₂ : Int) := by exact_mod_cast heq
    rw [heq'] at hs
    nlinarith [hs]
  have hdet := P.det₁
  have hp := P.sum_p
  have hprod : (P.q₁ : Int) * (P.p₁ - P.p₂) = 1 := by
    rw [hp, hqeq] at hdet
    calc
      (P.q₁ : Int) * (P.p₁ - P.p₂) =
          P.p₁ * (2 * P.q₁) - P.q₁ * (P.p₁ + P.p₂) := by ring
      _ = 1 := by simpa [mul_comm, mul_left_comm, mul_assoc] using hdet
  have hdiv : (P.q₁ : Int) ∣ 1 := ⟨P.p₁ - P.p₂, hprod.symm⟩
  have hroneInt := Int.eq_one_of_dvd_one (by omega : (0 : Int) ≤ P.q₁) hdiv
  have hrone : P.q₁ = 1 := by exact_mod_cast hroneInt
  have hqone : P.q = 2 := by omega
  have hyre : y.re = 1 := by omega
  have hyim : y.im = 1 := by omega
  have hxre : x.re = u.re + 1 := by
    have h := congrArg (fun z : GaussianInt => z.re) (show x - u = y by rfl)
    simp only [Zsqrtd.re_sub] at h
    rw [hyre] at h
    omega
  have hxim : x.im = u.im + 1 := by
    have h := congrArg (fun z : GaussianInt => z.im) (show x - u = y by rfl)
    simp only [Zsqrtd.im_sub] at h
    rw [hyim] at h
    omega
  refine ⟨hqone, ?_⟩
  rw [rootCentroid, hqone]
  norm_num
  apply Prod.ext
  · dsimp [GaussianRealPoint]
    have hr : (x.re : Real) = (u.re : Real) + 1 := by exact_mod_cast hxre
    simpa only [GaussianInt.intCast_re, add_comm] using hr
  · dsimp [GaussianRealPoint]
    have hi : (x.im : Real) = (u.im : Real) + 1 := by exact_mod_cast hxim
    simpa only [GaussianInt.intCast_im, add_comm] using hi

private theorem incidentFootprint :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (R : ProtoTile), ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x
            j ∈ R.cells → x ∈ FootprintVertices R ) := by
  classical
  intro x R j hc
  have hneR : R.cells.Nonempty := ⟨_, hc⟩
  simp only [FootprintVertices, ite_eq_left hneR]
  refine ⟨LatticeVertexIncidentCell x j, hc, ?_⟩
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by simp [LatticeVertexIncidentCell]))
  · exact Or.inr (Or.inr (Or.inr (by
      simp [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm])))
  · exact Or.inr (Or.inr (Or.inl (by simp [LatticeVertexIncidentCell])))

private theorem noBoundaryFour :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u :
            GaussianInt), ∀ (x : GaussianInt), (x ∈ FootprintVertices T) → ((x ∉
            BoundaryFootprintVertices T) → ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells) → ((∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) → (
        let y : GaussianInt := x - u
        (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧ 1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1) → ((x ∈
            FootprintVertices (S 0 true) ↔ 0 ≤ y.re ∧ y.re ≤ P.q₁ ∧ 0 ≤ y.im ∧ y.im ≤ P.q₁) → ((x
            ∈ FootprintVertices (S 0 false) ↔ P.q₂ ≤ y.re ∧ y.re ≤ P.q ∧ P.q₂ ≤ y.im ∧ y.im ≤
            P.q) → ((x ∈ FootprintVertices (S 1 true) ↔ P.q₁ ≤ y.re ∧ y.re ≤ P.q ∧ 0 ≤ y.im ∧
            y.im ≤ P.q₂) → ((x ∈ FootprintVertices (S 1 false) ↔ 0 ≤ y.re ∧ y.re ≤ P.q₂ ∧ P.q₁ ≤
            y.im ∧ y.im ≤ P.q) → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) ↔
            (0 : Int) ≤ y.re ∧ y.re ≤ P.q₁ ∧ 0 ≤ y.im ∧ y.im ≤ P.q₁ ∧ (y.re = 0 ∨ y.re = P.q₁ ∨
            y.im = 0 ∨ y.im = P.q₁)) → ((y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P
            1) ↔ (P.q₂ : Int) ≤ y.re ∧ y.re ≤ P.q ∧ P.q₂ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = P.q₂ ∨
            y.re = P.q ∨ y.im = P.q₂ ∨ y.im = P.q)) → ((y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 2) ↔ P.q₁ ≤ y.re ∧ y.re ≤ P.q ∧ (0 : Int) ≤ y.im ∧ y.im
            ≤ P.q₂ ∧ (y.re = P.q₁ ∨ y.re = P.q ∨ y.im = 0 ∨ y.im = P.q₂)) → ((y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 3) ↔ (0 : Int) ≤ y.re ∧ y.re ≤
            P.q₂ ∧ P.q₁ ≤ y.im ∧ y.im ≤ P.q ∧ (y.re = 0 ∨ y.re = P.q₂ ∨ y.im = P.q₁ ∨ y.im =
            P.q)) → ((x ∈ BoundaryFootprintVertices (S 0 true) ↔ y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0)) → ((x ∈ BoundaryFootprintVertices (S 0 false) ↔ y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 1)) → ((x ∈
            BoundaryFootprintVertices (S 1 true) ↔ y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 2)) → ((x ∈ BoundaryFootprintVertices (S 1 false) ↔ y ∈
            LatticeVertexBoundary (FordRecursiveVertexDomains P 3)) → ((x ∉
            BoundaryFootprintVertices (S 2 true)) → ((x ∉ BoundaryFootprintVertices (S 2 false))
            → ((Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} = (if x
            ∈ BoundaryFootprintVertices (S 0 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 0 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 false) then 1 else 0)) → ((FordBoundaryMultiplicity P
            y = Nat.card
            {i : Fin 4 // y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)}) →
            ((FordBoundaryMultiplicity P y = (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 1) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 2) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 3) then 1 else 0)) → ((Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} =
            FordBoundaryMultiplicity P y) → (((GaussianRealPoint x = TileCentroid T) → (((y.re :
            Int) : Real) = (P.q : Real) / 2 ∧ ((y.im : Int) : Real) = (P.q : Real) / 2)) →
            (((GaussianRealPoint x = TileCentroid T) → (2 * y.re = (P.q : Int) ∧ 2 * y.im = (P.q
            : Int))) → (((GaussianRealPoint x = TileCentroid T) → (FordBoundaryMultiplicity P y ≠
            2)) → (((Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} =
            4) → (P.q = 2 ∧ GaussianRealPoint x = TileCentroid T)) → ((∀ (R : ProtoTile), ∀ (j :
                Fin 4), (LatticeVertexIncidentCell x j ∈ R.cells) → (x ∈ FootprintVertices R)) →
                (∀ (R : ProtoTile), (∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
                R.cells) → x ∉
            BoundaryFootprintVertices R))))))))))))))))))))))))))))) := by
  classical
  intro P T S u x hx hxb hsome cells y hbounds foot0 foot1 foot2 foot3 domain0 domain1 domain2
      domain3 label0 label1 label2 label3 lineTrue lineFalse hcardSix hcardFour hcardFourFormula
      hcount centerCoords centerTwice noCenteredCountTwo countFourConclusion incidentFootprint R
      hall
  have hneR : R.cells.Nonempty := ⟨_, hall 0⟩
  intro hx
  simp only [BoundaryFootprintVertices, ite_eq_left hneR,
    Set.mem_ofPred_eq] at hx
  rcases hx with ⟨e, he, hxe⟩
  change ∃ z : GaussianInt,
    (e = {z, z + 1} ∧
      ((z ∈ R.cells ∧ z - ⟨0, 1⟩ ∉ R.cells) ∨
        (z ∉ R.cells ∧ z - ⟨0, 1⟩ ∈ R.cells))) ∨
    (e = {z, z + ⟨0, 1⟩} ∧
      ((z ∈ R.cells ∧ z - 1 ∉ R.cells) ∨
        (z ∉ R.cells ∧ z - 1 ∈ R.cells))) at he
  rcases he with ⟨z, hz⟩
  rcases hz with ⟨rfl, htog⟩ | ⟨rfl, htog⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with hxe | hxe
    · subst x
      have h0 : z ∈ R.cells := by
        simpa [LatticeVertexIncidentCell] using hall 0
      have h3 : z - ⟨0, 1⟩ ∈ R.cells := by
        simpa [LatticeVertexIncidentCell] using hall 3
      rcases htog with ⟨hz, hn⟩ | ⟨hn, hz⟩
      · exact hn h3
      · exact hn h0
    · have heq : x = z + 1 := hxe
      subst x
      have h1 : z ∈ R.cells := by
        simpa [LatticeVertexIncidentCell] using hall 1
      have h2 : z - ⟨0, 1⟩ ∈ R.cells := by
        simpa [LatticeVertexIncidentCell] using hall 2
      rcases htog with ⟨hz, hn⟩ | ⟨hn, hz⟩
      · exact hn h2
      · exact hn h1
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with hxe | hxe
    · subst x
      have h0 : z ∈ R.cells := by
        simpa [LatticeVertexIncidentCell] using hall 0
      have h1 : z - 1 ∈ R.cells := by
        simpa [LatticeVertexIncidentCell] using hall 1
      rcases htog with ⟨hz, hn⟩ | ⟨hn, hz⟩
      · exact hn h1
      · exact hn h0
    · have heq : x = z + ⟨0, 1⟩ := hxe
      subst x
      have h3 : z ∈ R.cells := by
        simpa [LatticeVertexIncidentCell] using hall 3
      have h2 : z - 1 ∈ R.cells := by
        simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using hall 2
      rcases htog with ⟨hz, hn⟩ | ⟨hn, hz⟩
      · exact hn h2
      · exact hn h3

private theorem incidentOwner :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u :
            GaussianInt), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell
            x j ∈ T.cells) → ((∀ (z : GaussianInt), z ∈ T.cells ↔ z - u ∈ (FordTile P.q).cells) →
            (∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (x : LatticeCell), x ∈ (FordTile
            P.q).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (Sc i s).cells) → ((∀ (i : Fin 3), ∀
                (s : Bool), (S i s).cells = (TileTranslation (Sc i s) u).cells) → (∀ (j : Fin (4 :
            ℕ)), ∃ (a : Fin (3 : ℕ) × Bool), LatticeVertexIncidentCell x j ∈ (S a.1
                a.2).cells))))) := by
  classical
  intro P T S u x cells cellCanonical Sc hcover hparentCells j
  have hc := (cellCanonical (LatticeVertexIncidentCell x j)).mp (cells j)
  obtain ⟨i, s, hs⟩ := (hcover (LatticeVertexIncidentCell x j - u)).mp hc
  refine ⟨(i, s), ?_⟩
  rw [hparentCells i s, (TileTranslationFormulas (Sc i s) u).1]
  apply Finset.mem_image.mpr
  refine ⟨LatticeVertexIncidentCell x j - u, hs, ?_⟩
  dsimp [GaussianTranslation]
  abel

private theorem twoBoundaryCount :
    (by
      classical
      exact
        ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (a : Fin (3 : ℕ) × Bool), ∀ (b :
            Fin (3 : ℕ) × Bool), a ≠ b → x ∈ BoundaryFootprintVertices (S a.1 a.2) → x ∈
            BoundaryFootprintVertices (S b.1 b.2) → (2 : ℕ) ≤ Nat.card
            { c : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (S c.1 c.2) } ) := by
  classical
  intro S x a b hab ha hb
  classical
  let A := {c : Fin 3 × Bool //
    x ∈ BoundaryFootprintVertices (S c.1 c.2)}
  let f : Fin 2 → A := fun j =>
    if j = 0 then ⟨a, ha⟩ else ⟨b, hb⟩
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i
    · fin_cases j
      · rfl
      · have hv := congrArg Subtype.val he
        have hv' : a = b := by simpa [f] using hv
        exact False.elim (hab hv')
    · fin_cases j
      · have hv := congrArg Subtype.val he
        have hv' : b = a := by simpa [f] using hv
        exact False.elim (hab hv'.symm)
      · rfl
  rw [Nat.card_eq_fintype_card]
  simpa [A] using Fintype.card_le_of_injective f hf

private theorem multiplicityBound :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (Fin 3 → Bool → ProtoTile) → (∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        (FordBoundaryMultiplicity P y = (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains
            P 0) then 1 else 0) + (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1)
            then 1 else 0) + (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) then
            1 else 0) + (if y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) then 1
            else 0)) → (FordBoundaryMultiplicity P y ≤ 4)) ) := by
  classical
  intro P S u x y hcardFourFormula
  rw [hcardFourFormula]
  split_ifs <;> omega

private theorem descent :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (S : Fin 3 → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (x :
            GaussianInt),
        let y : GaussianInt := x - u
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), ((Sc (2 : Fin (3 : ℕ)) true).cells = ∅) → (((Sc
            (2 : Fin (3 : ℕ)) false).cells = ∅) → ((∀ (i : Fin 3), ∀ (s : Bool), (S i s).cells =
            (TileTranslation (Sc i s) u).cells) → ((0 < P.q₁) → ((Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} = (if x ∈
            BoundaryFootprintVertices (S 0 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 0 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 1 false) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 true) then 1 else 0) + (if x ∈
            BoundaryFootprintVertices (S 2 false) then 1 else 0)) → ((FordBoundaryMultiplicity P
            y = Nat.card
            {i : Fin 4 // y ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)}) →
            ((FordBoundaryMultiplicity P y = (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 0) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 1) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 2) then 1 else 0) + (if y ∈ LatticeVertexBoundary
            (FordRecursiveVertexDomains P 3) then 1 else 0)) → ((Nat.card
            {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)} =
            FordBoundaryMultiplicity P y) → ((∀ (R : ProtoTile), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ R.cells) → (x ∈ FootprintVertices R)) → ((∀ (R :
            ProtoTile), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ R.cells) → (x ∉
            BoundaryFootprintVertices R)) → ((∀ (j : Fin 4), ∃ a : Fin 3 × Bool,
            LatticeVertexIncidentCell x j ∈ (S a.1 a.2).cells) → ((∀ (a : Fin 3 × Bool), ∀ (b :
            Fin 3 × Bool), (a ≠ b) → ((x ∈ BoundaryFootprintVertices (S a.1 a.2)) → ((x ∈
            BoundaryFootprintVertices (S b.1 b.2)) → (2 ≤ Nat.card
            {c : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S c.1 c.2)})))) →
            ((FordBoundaryMultiplicity P y ≤ 4) → (¬(Nat.card
            { a : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2) } = (2 : ℕ) ∨
            Nat.card { a : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2) } = (3
            : ℕ) ∨ Nat.card
            { a : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2) } = (4 : ℕ)) →
            ∃ (i : Fin (3 : ℕ)) (s : Bool), (0 : ℤ) < (FordRecursiveQuadruple P i.succ).1 ∧ x ∈
            FootprintVertices (S i s) ∧ x ∉ BoundaryFootprintVertices (S i s)))))))))))))) ) := by
  classical
  intro P S u x y Sc h20 h21 hparentCells hrpos hcardSix hcardFour hcardFourFormula hcount
      incidentFootprint noBoundaryFour incidentOwner twoBoundaryCount multiplicityBound hno
  have hkle : Nat.card {a : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (S a.1 a.2)} ≤ 1 := by
    have hmax : Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (S a.1 a.2)} ≤ 4 := by
      calc
        Nat.card {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (S a.1 a.2)} = FordBoundaryMultiplicity P y := hcount
        _ ≤ 4 := multiplicityBound
    omega
  obtain ⟨a, haCell⟩ := incidentOwner 0
  have findInteriorOwner : ∃ b : Fin 3 × Bool, ∃ j : Fin 4,
      LatticeVertexIncidentCell x j ∈ (S b.1 b.2).cells ∧
      x ∉ BoundaryFootprintVertices (S b.1 b.2) := by
    by_cases hbd : x ∈ BoundaryFootprintVertices (S a.1 a.2)
    · by_cases hall : ∀ j : Fin 4, ∀ b : Fin 3 × Bool,
          LatticeVertexIncidentCell x j ∈ (S b.1 b.2).cells → b = a
      · have hAll : ∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (S a.1 a.2).cells := by
          intro j
          obtain ⟨b, hb⟩ := incidentOwner j
          have heq := hall j b hb
          simpa [heq] using hb
        exact False.elim ((noBoundaryFour (S a.1 a.2) hAll) hbd)
      · push Not at hall
        obtain ⟨j, b, hbcell, hba⟩ := hall
        have hab : a ≠ b := hba.symm
        have hnotb : x ∉ BoundaryFootprintVertices (S b.1 b.2) := by
          intro hb
          have htwo := twoBoundaryCount a b hab hbd hb
          omega
        exact ⟨b, j, hbcell, hnotb⟩
    · exact ⟨a, 0, haCell, hbd⟩
  obtain ⟨b, j, hbcell, hnotb⟩ := findInteriorOwner
  have hfoot := incidentFootprint (S b.1 b.2) j hbcell
  rcases b with ⟨i, s⟩
  fin_cases i
  · refine ⟨0, s, ?_, hfoot, hnotb⟩
    by_cases hz : P.q₁ = 0
    · omega
    · simp [FordRecursiveQuadruple, FordCircleCoordinate, hz]
  · refine ⟨1, s, ?_, hfoot, hnotb⟩
    simp [FordRecursiveQuadruple, FordCircleCoordinate, P.q₂_pos]
  · have hscEmpty : (Sc 2 s).cells = ∅ := by
      cases s <;> assumption
    have hparentEmpty : (S 2 s).cells = ∅ := by
      rw [hparentCells 2 s, (TileTranslationFormulas (Sc 2 s) u).1, hscEmpty]
      simp
    simp [hparentEmpty] at hbcell

end FordTileGeometry

theorem P4120T1FordGeometry
    (P : FordFareyParameter) (hP : 1 < P.q)
    (T : ProtoTile) (S : Fin 3 → Bool → ProtoTile) (u : GaussianInt)
    (hcells : T.cells = (TileTranslation (FordTile P.q) u).cells)
    (hanchor : T.cells = ∅ → T.anchor = (TileTranslation (FordTile P.q) u).anchor)
    (hS : ∀ i s, BandSubtileOccurrence (FordRecursiveQuadruple P) T i s (S i s))
    (x : GaussianInt) (hx : x ∈ FootprintVertices T)
    (hxb : x ∉ BoundaryFootprintVertices T) :
    let y := x - u
    let k := Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)}
    (1 ≤ y.re ∧ y.re ≤ (P.q : Int) - 1 ∧
      1 ≤ y.im ∧ y.im ≤ (P.q : Int) - 1) ∧
    k = FordBoundaryMultiplicity P y ∧
    (k = 2 → GaussianRealPoint x ≠ TileCentroid T) ∧
    (k = 4 → P.q = 2 ∧ GaussianRealPoint x = TileCentroid T) ∧
    ((k = 2 ∨ k = 3 ∨ k = 4) ∨
      ∃ i : Fin 3, ∃ s : Bool,
        0 < ((FordRecursiveQuadruple P) i.succ).1 ∧
        x ∈ FootprintVertices (S i s) ∧ x ∉ BoundaryFootprintVertices (S i s)) := by
-- BODY
  classical
  have hne := InteriorFootprintIncidence.nonempty T x hx hxb
  have hsome := InteriorFootprintIncidence.someIncidentCell T x hx hxb hne
  have cells := InteriorFootprintIncidence.allIncidentCells T x hxb hsome
  let y : GaussianInt := x - u
  have cellCanonical (z : GaussianInt) := FordTileGeometry.cellCanonical P T u hcells z
  have squareCell (z : GaussianInt) := FordTileGeometry.squareCell P z
  have hbounds := FordTileGeometry.hbounds P T u x cells cellCanonical squareCell
  have fordCentroid := FordTileGeometry.fordCentroid P hP u x
  obtain ⟨_, _, hrec⟩ := FordTileRecursiveIdentification P
  obtain ⟨_, ⟨Sc, hSc, hcover, h00, h01, h10, h11, h20, h20a, h21, h21a⟩⟩ :=
    hrec hP
  have hrootObs := ProtoTileObservableExtensionality T
    (TileTranslation (FordTile P.q) u) hcells hanchor
  have hScTranslated (i : Fin 3) (s : Bool) :
      BandSubtileOccurrence (FordRecursiveQuadruple P)
        (TileTranslation (FordTile P.q) u) i s
        (TileTranslation (Sc i s) u) :=
    (BandSubtileOccurrenceTranslation (FordRecursiveQuadruple P)
      (FordTile P.q) (Sc i s) i s u).mp (hSc i s)
  have hparentCentroid (i : Fin 3) (s : Bool) := FordTileGeometry.hparentCentroid P T S u hS Sc
      hrootObs hScTranslated i s
  have hparentObs (i : Fin 3) (s : Bool) := FordTileGeometry.hparentObs P T S u hS Sc
      hScTranslated hparentCentroid i s
  have hparentCells (i : Fin 3) (s : Bool) := FordTileGeometry.hparentCells P T S u hS Sc
      hScTranslated hparentCentroid i s
  have hrpos := FordTileGeometry.hrpos P hP u x
  have hr : (P.q₁ : Int) > 0 := by exact_mod_cast hrpos
  have ht : (P.q₂ : Int) > 0 := by exact_mod_cast P.q₂_pos
  have hqsum : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  have rectBoundary (l r b t : Int) (z : GaussianInt) := FordTileGeometry.rectBoundary P u x l r
      b t z
  have boundaryTranslation (A : ProtoTile) (v z : GaussianInt) :=
      FordTileGeometry.boundaryTranslation A v z
  have footprintTranslation (A : ProtoTile) (v z : GaussianInt) :=
      FordTileGeometry.footprintTranslation A v z
  have hSc00 := FordTileGeometry.hSc00 P Sc h00 hrpos
  have hSc01 := FordTileGeometry.hSc01 P Sc h01 hrpos
  have hSc10 := FordTileGeometry.hSc10 P Sc h10
  have hSc11 := FordTileGeometry.hSc11 P Sc h11
  have hSc00Foot := FordTileGeometry.hSc00Foot P Sc h00 hrpos
  have hSc01Foot := FordTileGeometry.hSc01Foot P Sc h01 hrpos
  have hSc10Foot := FordTileGeometry.hSc10Foot P Sc h10
  have hSc11Foot := FordTileGeometry.hSc11Foot P Sc h11
  have foot0 := FordTileGeometry.foot0 P S u x Sc hparentObs hrpos footprintTranslation hSc00Foot
  have foot1 := FordTileGeometry.foot1 P S u x Sc hparentObs hrpos hqsum footprintTranslation
      hSc01Foot
  have foot2 := FordTileGeometry.foot2 P S u x Sc hparentObs hqsum footprintTranslation hSc10Foot
  have foot3 := FordTileGeometry.foot3 P S u x Sc hparentObs hqsum footprintTranslation hSc11Foot
  have squareBoundary (n : Nat) (hn : 0 < n) (z : GaussianInt) := FordTileGeometry.squareBoundary
      n hn z
  have domain0 := FordTileGeometry.domain0 P u x rectBoundary
  have domain1 := FordTileGeometry.domain1 P u x rectBoundary
  have domain2 := FordTileGeometry.domain2 P u x rectBoundary
  have domain3 := FordTileGeometry.domain3 P u x rectBoundary
  have label0 := FordTileGeometry.label0 P S u x Sc hparentObs hrpos boundaryTranslation hSc00
      squareBoundary domain0
  have label1 := FordTileGeometry.label1 P S u x Sc hparentObs hrpos hqsum boundaryTranslation
      hSc01 squareBoundary domain1
  have label2 := FordTileGeometry.label2 P S u x Sc hparentObs ht hqsum boundaryTranslation hSc10
      squareBoundary domain2
  have label3 := FordTileGeometry.label3 P S u x Sc hparentObs ht hqsum boundaryTranslation hSc11
      squareBoundary domain3
  have lineTrue := FordTileGeometry.lineTrue P S u x hbounds Sc h20 h20a hparentObs hqsum
      boundaryTranslation
  have lineFalse := FordTileGeometry.lineFalse P S u x hbounds Sc h21 h21a hparentObs
      boundaryTranslation
  have hcardSix := FordTileGeometry.hcardSix S x
  have hcardFour := FordTileGeometry.hcardFour P u x
  have hcardFourFormula := FordTileGeometry.hcardFourFormula P S u x
  have hcount := FordTileGeometry.hcount P S u x label0 label1 label2 label3 lineTrue lineFalse
      hcardSix hcardFourFormula
  have rootCentroid := FordTileGeometry.rootCentroid P T u fordCentroid hrootObs
  have centerCoords (hc : GaussianRealPoint x = TileCentroid T) := FordTileGeometry.centerCoords
      P T u x rootCentroid hc
  have centerTwice (hc : GaussianRealPoint x = TileCentroid T) := FordTileGeometry.centerTwice P
      T u x centerCoords hc
  have noCenteredCountTwo (hc : GaussianRealPoint x = TileCentroid T) :=
      FordTileGeometry.noCenteredCountTwo P hP T S u x hbounds hrpos hqsum domain0 domain1
      domain2 domain3 hcardFourFormula centerTwice hc
  have countFourConclusion (hk : Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (S a.1 a.2)} = 4) := FordTileGeometry.countFourConclusion P
            hP T S u x hqsum domain0 domain1 domain2 domain3 hcardFourFormula hcount rootCentroid hk
  have incidentFootprint (R : ProtoTile) (j : Fin 4)
      (hc : LatticeVertexIncidentCell x j ∈ R.cells) := FordTileGeometry.incidentFootprint x R j hc
  have noBoundaryFour (R : ProtoTile)
      (hall : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ R.cells) :=
          FordTileGeometry.noBoundaryFour P T S u x hx hxb hsome cells hbounds foot0 foot1 foot2
          foot3 domain0 domain1 domain2 domain3 label0 label1 label2 label3 lineTrue lineFalse
          hcardSix hcardFour hcardFourFormula hcount centerCoords centerTwice noCenteredCountTwo
          countFourConclusion incidentFootprint R hall
  have incidentOwner (j : Fin 4) := FordTileGeometry.incidentOwner P T S u x cells cellCanonical
      Sc hcover hparentCells j
  have twoBoundaryCount (a b : Fin 3 × Bool) (hab : a ≠ b)
      (ha : x ∈ BoundaryFootprintVertices (S a.1 a.2))
      (hb : x ∈ BoundaryFootprintVertices (S b.1 b.2)) := FordTileGeometry.twoBoundaryCount S x a
          b hab ha hb
  have multiplicityBound := FordTileGeometry.multiplicityBound P S u x hcardFourFormula
  have descent (hno : ¬ (Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (S a.1 a.2)} = 2 ∨
        Nat.card {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (S a.1 a.2)} = 3 ∨
        Nat.card {a : Fin 3 × Bool //
          x ∈ BoundaryFootprintVertices (S a.1 a.2)} = 4)) := FordTileGeometry.descent P S u x Sc
              h20 h21 hparentCells hrpos hcardSix hcardFour hcardFourFormula hcount
              incidentFootprint noBoundaryFour incidentOwner twoBoundaryCount multiplicityBound hno
  refine ⟨hbounds, hcount, ?_, ?_, ?_⟩
  · intro hk hc
    exact noCenteredCountTwo hc (hcount.symm.trans hk)
  · exact countFourConclusion
  · by_cases hk : Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (S a.1 a.2)} = 2 ∨
      Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (S a.1 a.2)} = 3 ∨
      Nat.card {a : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (S a.1 a.2)} = 4
    · exact Or.inl hk
    · exact Or.inr (descent hk)

end ApollonianSuperharmonic

end
