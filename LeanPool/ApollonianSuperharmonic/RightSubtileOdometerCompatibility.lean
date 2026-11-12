/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.OdometerAdjacencyInduction
public import LeanPool.ApollonianSuperharmonic.LeftAdjacentOdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.LatticeAdjacentInterfacePath

-- [TABLET NODE: RightSubtileOdometerCompatibility]

/-!
# RightSubtileOdometerCompatibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightCompatibilityGeometry

private theorem singleton_case :
    (by
      classical
      exact
        ∀ (a : PartialOdometer), ∀ (b : PartialOdometer), ((a.domain : Set GaussianInt) ∩
            (b.domain : Set GaussianInt)).Subsingleton → OdometerCompatibility a b ) := by
  classical
  intro a b hs
  by_cases hn : ((a.domain : Set GaussianInt) ∩
      (b.domain : Set GaussianInt)).Nonempty
  · rcases hn with ⟨x, hx, hx'⟩
    right
    refine ⟨b.value x - a.value x, ?_⟩
    intro y hy hy'
    have hxy : y = x := hs ⟨hy, hy'⟩ ⟨hx, hx'⟩
    subst y
    rfl
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hn
    exact Set.disjoint_iff_inter_eq_empty.mpr hn

private theorem list_glue :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (a : PartialOdometer), ∀ (b : PartialOdometer), 2 ≤ p.length
            → (∀ u, ∀ v, ∀ l, ∀ r, p = l ++ u :: v :: r → ∃ c : ℤ, ∀ z, (z = u ∨ z = v) → z ∈
            a.domain → z ∈ b.domain → b.value z - a.value z = c) → (∀ z, z ∈ (p.toFinset : Set
            GaussianInt) → z ∈ a.domain ∧ z ∈ b.domain) → ∃ c : ℤ, ∀ z, z ∈ (p.toFinset : Set
            GaussianInt) → z ∈ a.domain → z ∈ b.domain → b.value z - a.value z = c ) := by
  classical
  intro p
  induction p with
  | nil => simp_all
  | cons u p ih =>
    intro a b hlen hedge hmem
    cases p with
    | nil => simp at hlen
    | cons v r =>
      cases r with
      | nil =>
        obtain ⟨c, hc⟩ := hedge u v [] [] (by simp)
        refine ⟨c, ?_⟩
        intro z hz ha hb
        have hz' : z = u ∨ z = v := by simpa using hz
        rcases hz' with rfl | rfl
        · exact hc _ (Or.inl rfl) ha hb
        · exact hc _ (Or.inr rfl) ha hb
      | cons w r =>
        have htail : 2 ≤ (v :: w :: r).length := by simp
        have hedgeTail : ∀ u' v' l' r', v :: w :: r = l' ++ u' :: v' :: r' →
            ∃ c : ℤ, ∀ z, (z = u' ∨ z = v') →
              z ∈ a.domain → z ∈ b.domain → b.value z - a.value z = c := by
          intro u' v' l' r' he
          apply hedge u' v' (u :: l') r'
          simpa [List.cons_append, List.append_assoc] using congrArg (fun t => u :: t) he
        obtain ⟨d, hd⟩ := ih a b htail hedgeTail (by
          intro z hz
          apply hmem z
          exact by
            simpa [List.toFinset_cons] using
              (Or.inr hz : z = u ∨ z ∈ ((v :: w :: r).toFinset : Set GaussianInt)))
        obtain ⟨c, hc⟩ := hedge u v [] (w :: r) (by simp)
        have same : c = d := by
          have hv := hc v (Or.inr rfl)
          have hv' := hd v (by simp)
          have hm := hmem v (by simp)
          have e1 := hv hm.1 hm.2
          have e2 := hv' hm.1 hm.2
          omega
        refine ⟨c, ?_⟩
        intro z hz ha hb
        have hz' : z = u ∨ z ∈ ((v :: w :: r).toFinset : Set GaussianInt) := by
          simpa using hz
        rcases hz' with rfl | hz
        · exact hc _ (Or.inl rfl) ha hb
        · have := hd z hz ha hb
          simpa [same] using this

private theorem edge_endpoints :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), {a, b} ∈ FootprintEdges U →
            a ∈ FootprintVertices U ∧ b ∈ FootprintVertices U ) := by
  classical
  intro U a b he
  rcases he with ⟨x, hx, he⟩
  have hn : U.cells.Nonempty := ⟨x, hx⟩
  rcases he with he | he | he | he
  · have ha : a ∈ ({x, x + 1} : Finset GaussianInt) := by
      rw [← he]
      simp
    have hb : b ∈ ({x, x + 1} : Finset GaussianInt) := by
      rw [← he]
      simp
    have lift : ∀ w, w = x ∨ w = x + 1 →
        w = x ∨ w = x + 1 ∨ w = x + ⟨0, 1⟩ ∨ w = x + 1 + ⟨0, 1⟩ := by
      intro w hw
      rcases hw with hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
    constructor <;> simp only [FootprintVertices, ite_eq_left hn, Set.mem_ofPred_eq]
    · exact ⟨x, hx, lift a (by simpa using ha)⟩
    · exact ⟨x, hx, lift b (by simpa using hb)⟩
  · have ha : a ∈ ({x, x + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← he]
      simp
    have hb : b ∈ ({x, x + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← he]
      simp
    have lift : ∀ w, w = x ∨ w = x + ⟨0, 1⟩ →
        w = x ∨ w = x + 1 ∨ w = x + ⟨0, 1⟩ ∨ w = x + 1 + ⟨0, 1⟩ := by
      intro w hw
      rcases hw with hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inr (Or.inl hw))
    constructor <;> simp only [FootprintVertices, ite_eq_left hn, Set.mem_ofPred_eq]
    · exact ⟨x, hx, lift a (by simpa using ha)⟩
    · exact ⟨x, hx, lift b (by simpa using hb)⟩
  · have ha : a ∈ ({x + 1, x + 1 + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← he]
      simp
    have hb : b ∈ ({x + 1, x + 1 + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← he]
      simp
    have lift : ∀ w, w = x + 1 ∨ w = x + 1 + ⟨0, 1⟩ →
        w = x ∨ w = x + 1 ∨ w = x + ⟨0, 1⟩ ∨ w = x + 1 + ⟨0, 1⟩ := by
      intro w hw
      rcases hw with hw | hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inr hw))
    constructor <;> simp only [FootprintVertices, ite_eq_left hn, Set.mem_ofPred_eq]
    · exact ⟨x, hx, lift a (by simpa using ha)⟩
    · exact ⟨x, hx, lift b (by simpa using hb)⟩
  · have ha : a ∈ ({x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← he]
      simp
    have hb : b ∈ ({x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← he]
      simp
    have lift : ∀ w, w = x + ⟨0, 1⟩ ∨ w = x + 1 + ⟨0, 1⟩ →
        w = x ∨ w = x + 1 ∨ w = x + ⟨0, 1⟩ ∨ w = x + 1 + ⟨0, 1⟩ := by
      intro w hw
      rcases hw with hw | hw
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inr hw))
    constructor <;> simp only [FootprintVertices, ite_eq_left hn, Set.mem_ofPred_eq]
    · exact ⟨x, hx, lift a (by simpa using ha)⟩
    · exact ⟨x, hx, lift b (by simpa using hb)⟩

private theorem qdata :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h'
            : PartialOdometer), (∃ (p : ℝ × ℝ) (p' : ℝ × ℝ), PartialOdometerSlope h = some p ∧
            PartialOdometerSlope h' = some p' ∧ ∃ (q : Fin (4 : ℕ) → CircleCoordinates) (i : Fin
            (3 : ℕ)) (e : Bool), ProperBandQuadruple q ∧ q (0 : Fin (4 : ℕ)) = C.1.1 ∧
            TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1 : ℝ)) •
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)) ∧ p'.1 - p.1 = (if
            e = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            i.succ)).re : ℝ) ∧ p'.2 - p.2 = (if e = true then (1 : ℝ) else (-1 : ℝ)) *
            (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)).im : ℝ)) → (∃ q : Fin 4 →
            CircleCoordinates, ∃ _ : Fin 3, ∃ _ : Bool, ProperBandQuadruple q ∧ q 0 = C.1.1) ) := by
  classical
  intro C T T' h h' hdata
  rcases hdata with ⟨p₀, p₁, hp₀, hp₁, q, i, e, hq, hqC, rest⟩
  exact ⟨q, i, e, hq, hqC⟩

private theorem hrootAt310 :
    (by
      classical
      exact
        (ℕ) → (∀ (C : BandCircle), (List GaussianInt) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple q) → ((q (0 : Fin (4 : ℕ)) = C.1.1) → (1 < (q 0).1)))) ) := by
  classical
  intro n C p q hq hqC
  have hpq := hq.2 (0 : Fin 3)
  have hpos : 0 < (q 0).1 := by simpa only [hqC] using C.property
  have hnon := (ProperBandCurvatureStructure q hq).2.1
  have hunique := (ProperBandCurvatureStructure q hq).2.2
  have hnon0 := hnon 0
  have hnon1 := hnon 1
  have hpq1 := hq.2 (1 : Fin 3)
  have huniq01 := hunique 0 1
  by_contra hn
  have hle : (q 0).1 ≤ 1 := by omega
  have hz0 : (q (0 : Fin 3).succ).1 = 0 := by omega
  have hz1 : (q (1 : Fin 3).succ).1 = 0 := by omega
  have bad := huniq01 hz0 hz1
  omega

private theorem edgeStepAt328 :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), {a, b} ∈ FootprintEdges U →
            a ∈ FootprintVertices U ∧ b ∈ FootprintVertices U) → (∀ (n : ℕ), (∀ m < n, (∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), C.1.1.1.toNat + C.1.1.1.toNat = m → RightLatticeAdjacent C T T' h
            h' → OdometerCompatibility h h') ∧ ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ :
            ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ : PartialOdometer),
            C₀.1.1.1.toNat + Cᵢ.1.1.1.toNat = m → SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ →
            OdometerCompatibility h₀ hᵢ) → (∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T' :
            ProtoTile), ∀ (h : PartialOdometer), ∀ (h' : PartialOdometer), (C.1.1.1.toNat +
            C.1.1.1.toNat = n) → ((TileOdometer C.1.1 T h) → ((TileOdometer C.1.1 T' h') → ((∃ (p
            : ℝ × ℝ) (p' : ℝ × ℝ), PartialOdometerSlope h = some p ∧ PartialOdometerSlope h' =
            some p' ∧ ∃ (q : Fin (4 : ℕ) → CircleCoordinates) (i : Fin (3 : ℕ)) (e : Bool),
            ProperBandQuadruple q ∧ q (0 : Fin (4 : ℕ)) = C.1.1 ∧ TileCentroid T' - TileCentroid
            T = (if e = true then (1 : ℝ) else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0
            : Fin (4 : ℕ))) (q i.succ)) ∧ p'.1 - p.1 = (if e = true then (1 : ℝ) else (-1 : ℝ)) *
            (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)).re : ℝ) ∧ p'.2 - p.2 = (if e =
            true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            i.succ)).im : ℝ)) → (((h'.domain : Set GaussianInt) = FootprintVertices T') → ((¬((∃
            (g : BandPackingSymmetry) (P : FordFareyParameter), BandPackingSymmetryCircleAction g
            (FordCircleCoordinate P.p P.q) = C.1.1) ∨ ∃ (g : BandPackingSymmetry) (K :
            DiamondParameter), BandPackingSymmetryCircleAction g (DiamondRecursiveQuadruple K (0
            : Fin (4 : ℕ))) = C.1.1)) → (∀ (p : List GaussianInt), (∀ (e : Finset GaussianInt), e
            ∈ FootprintEdges T ∩ FootprintEdges T' ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ :
            List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀
            (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → ((q (0 : Fin (4 :
            ℕ)) = C.1.1) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hsx : Fin (3 : ℕ) → Bool →
            PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (S i s)
            (hsx i s)) → ((∀ (x : LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈
            (S i s).cells) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), FootprintVertices (S i s) ⊆
            FootprintVertices T) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) -
            TileCentroid T = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → ((∀ (x :
            GaussianInt), x ∈ h.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (hsx i s).domain) →
            ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (hsx i s).domain, h.value x = (hsx i
            s).value x) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (q i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ
            × ℝ) (p_i : ℝ × ℝ), PartialOdometerSlope h = some p ∧ PartialOdometerSlope (hsx i s)
            = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
            ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q
            (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (∀ u, ∀ v, ∀ l, ∀ r, p = l ++ u :: v :: r
            → ∃ c : ℤ, ∀ z, (z = u ∨ z = v) → z ∈ h'.domain → z ∈ h.domain → h.value z - h'.value
            z = c)))))))))))))))))) ) := by
  classical
  intro edge_endpoints n ih C T T' h h' hn hOT hOT' hdata hdom' hex p hpedges q hq hqC S hsx
      hchildren hcells hfoot hcent hdoms hvalues hslopes u v l r hpr
  have he : {u, v} ∈ FootprintEdges T ∩ FootprintEdges T' := by
    apply (hpedges {u, v}).mpr
    exact ⟨u, v, l, r, hpr, rfl⟩
  have heT : {u, v} ∈ FootprintEdges T := he.1
  rcases heT with ⟨a, ha, heq⟩
  rcases heq with heq | heq | heq | heq
  all_goals
    have hac : ∃ j s, a ∈ (S j s).cells := (hcells a).mp ha
    rcases hac with ⟨j, s, has⟩
    have heS : {u, v} ∈ FootprintEdges (S j s) := by
      rw [heq]
      exact ⟨a, has, by simp⟩
    have hposchild : 0 < (q j.succ).1 := by
      have hnonchild := (ProperBandCurvatureStructure q hq).2.1 j
      have hchild := hchildren j s
      generalize hqj : q j.succ = cj at hchild
      have hposcj : 0 < cj.1 := by
        by_contra hz
        have hnoncj : 0 ≤ cj.1 := by simpa [hqj] using hnonchild
        have hz0 : cj.1 = 0 := by omega
        generalize hS : S j s = U at hchild heS
        revert heS
        cases hchild with
        | line w z hw k hd =>
            intro heS
            simp [FootprintEdges] at heS
        | unit z x U k hU hd ht => intro; omega
        | decompose hq' hT' hs' hU hcells' hfoot' hcent' hdom'
            hvalue' hcompat' =>
          have hp' := (ProperBandCurvatureStructure _ hq').1
          intro
          omega
      simpa [hqj] using hposcj
    have hsub : TileSubodometer C.1.1 (q j.succ)
        T (S j s) h (hsx j s) := by
      refine ⟨hOT, hchildren j s, hfoot j s, ?_, ?_, ?_⟩
      · intro z hz
        exact (hdoms z).mpr ⟨j, s, hz⟩
      · exact fun z hz => hvalues j s z hz
      · refine ⟨q, j, hq, hqC, rfl, s, hcent j s, ?_⟩
        exact hslopes j s
    let Cj : BandCircle :=
      ⟨⟨q j.succ,
        ⟨Or.inl hposchild, ⟨q, hq.1, ⟨j.succ, rfl⟩⟩⟩⟩,
        hposchild⟩
    have had0 := ((OdometerAdjacencyInduction.1 C hex).1) T T' h h'
      ⟨hOT, hOT', hdata⟩
    have had := had0 (C' := Cj) (T' := S j s) (h' := hsx j s)
      (by simpa [Cj] using hsub) ⟨{u, v}, ⟨heS, he.2⟩⟩
    have hlt := hq.2 j
    have hltNat : (Int.toNat (q j.succ).1 : Nat) <
        Int.toNat (q 0).1 :=
      (Int.toNat_lt_toNat (by simpa [hqC] using C.property)).2 hlt
    have hCeq : Int.toNat C.1.1.1 = Int.toNat (q 0).1 := by
      simp [hqC]
    have hsum : Int.toNat C.1.1.1 + Int.toNat (q j.succ).1 <
        Int.toNat C.1.1.1 + Int.toNat (q 0).1 :=
      Nat.add_lt_add_left hltNat _
    have hltSum : Int.toNat C.1.1.1 + Int.toNat (q j.succ).1 < n := by
      omega
    have hltSum' : Int.toNat C.1.1.1 + Int.toNat Cj.1.1.1 < n := by
      simpa [Cj] using hltSum
    have hcpt := (ih (Int.toNat C.1.1.1 + Int.toNat Cj.1.1.1)
        hltSum').2
        C Cj T' (S j s) h' (hsx j s)
        (by omega) had
    rcases hcpt with hdis | ⟨c, hc⟩
    · exfalso
      have hu := edge_endpoints (S j s) u v heS
      have hu' := edge_endpoints T' u v he.2
      have huS := (PositiveCurvatureTileOdometerDomain
        (q j.succ) (S j s) (hsx j s) hposchild (hchildren j s)).symm ▸ hu.1
      have huT' : u ∈ (h'.domain : Set GaussianInt) := by
        rw [hdom']
        exact hu'.1
      exact (Set.disjoint_left.1 hdis) huT' huS
    · refine ⟨c, ?_⟩
      intro z hz hz' hz0
      have hzV : z ∈ FootprintVertices (S j s) := by
        have hev := edge_endpoints (S j s) u v heS
        rcases hz with rfl | rfl
        · exact hev.1
        · exact hev.2
      have hzS : z ∈ (hsx j s).domain := by
        exact (Set.ext_iff.mp (PositiveCurvatureTileOdometerDomain
          (q j.succ) (S j s) (hsx j s) hposchild (hchildren j s)) z).mpr hzV
      have hh := hc z hz' hzS
      rw [hvalues j s z hzS]
      omega

private theorem hz'At423 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (p : List GaussianInt), (FootprintVertices T ∩
            FootprintVertices T' = (↑p.toFinset : Set GaussianInt)) → (∀ (z : GaussianInt), (z ∈
            (↑p.toFinset : Set GaussianInt)) → (z ∈ FootprintVertices T ∩ FootprintVertices T'))
            ) := by
  classical
  intro T T' p hpverts z hz
  rw [hpverts]
  exact hz

private theorem hzPAt435 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (p : List GaussianInt), (FootprintVertices T ∩
            FootprintVertices T' = (↑p.toFinset : Set GaussianInt)) → (∀ (z : GaussianInt), (z ∈
            FootprintVertices T ∩ FootprintVertices T') → (z ∈ (p.toFinset : Set GaussianInt))) )
            := by
  classical
  intro T T' p hpverts z hzV
  rw [← hpverts]
  exact hzV

private theorem hrootAt463 :
    (by
      classical
      exact
        (ℕ) → (∀ (C₀ : BandCircle), (BandCircle) → ((List GaussianInt) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), (ProperBandQuadruple q) → ((q (0 : Fin (4 : ℕ)) = C₀.1.1) → (1 <
            (q 0).1))))) ) := by
  classical
  intro n C₀ Cᵢ p q hq hqC
  have hnon := (ProperBandCurvatureStructure q hq).2.1
  have hunique := (ProperBandCurvatureStructure q hq).2.2
  have hnon0 := hnon 0
  have hnon1 := hnon 1
  have hpq0 := hq.2 (0 : Fin 3)
  have hpq1 := hq.2 (1 : Fin 3)
  have huniq01 := hunique 0 1
  have hpos : 0 < (q 0).1 := by simpa [hqC] using C₀.property
  by_contra hn0
  have hle : (q 0).1 ≤ 1 := by omega
  have hz0 : (q (0 : Fin 3).succ).1 = 0 := by omega
  have hz1 : (q (1 : Fin 3).succ).1 = 0 := by omega
  have bad := huniq01 hz0 hz1
  omega

private theorem edgeStepAt482 :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), {a, b} ∈ FootprintEdges U →
            a ∈ FootprintVertices U ∧ b ∈ FootprintVertices U) → (∀ (n : ℕ), (∀ m < n, (∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), C.1.1.1.toNat + C.1.1.1.toNat = m → RightLatticeAdjacent C T T' h
            h' → OdometerCompatibility h h') ∧ ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ :
            ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ : PartialOdometer),
            C₀.1.1.1.toNat + Cᵢ.1.1.1.toNat = m → SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ →
            OdometerCompatibility h₀ hᵢ) → (∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ :
            ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ : PartialOdometer),
            (C₀.1.1.1.toNat + Cᵢ.1.1.1.toNat = n) → ((TileOdometer C₀.1.1 T₀ h₀) → ((TileOdometer
            Cᵢ.1.1 Tᵢ hᵢ) → (((hᵢ.domain : Set GaussianInt) = FootprintVertices Tᵢ) → ((¬((∃ (g :
            BandPackingSymmetry) (P : FordFareyParameter), BandPackingSymmetryCircleAction g
            (FordCircleCoordinate P.p P.q) = C₀.1.1) ∨ ∃ (g : BandPackingSymmetry) (K :
            DiamondParameter), BandPackingSymmetryCircleAction g (DiamondRecursiveQuadruple K (0
            : Fin (4 : ℕ))) = C₀.1.1)) → (∀ (p : List GaussianInt), (∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b
            :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1 : GaussianInt) ∨ b = a + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∨ b = a - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → ((∀ (e : Finset
            GaussianInt), e ∈ FootprintEdges T₀ ∩ FootprintEdges Tᵢ ↔ ∃ (a : GaussianInt) (b :
            GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂
            ∧ e = {a, b}) → (∀ (p₀ : ℝ × ℝ), ∀ (pᵢ : ℝ × ℝ), (PartialOdometerSlope h₀ = some p₀)
            → ((PartialOdometerSlope hᵢ = some pᵢ) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀
            (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), (ProperBandQuadruple q) → ((q (0 : Fin (4 :
            ℕ)) = C₀.1.1) → ((q i.succ = Cᵢ.1.1) → ((TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 :
            ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) *
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ)))
            (q i.succ))) ∧ pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)))).1 ∧ pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) •
            GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2
            (q i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            i.succ)))).2) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hsx : Fin (3 : ℕ) → Bool
            → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (S i
            s) (hsx i s)) → ((∀ (x : LatticeCell), x ∈ T₀.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool),
            x ∈ (S i s).cells) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), FootprintVertices (S i s) ⊆
            FootprintVertices T₀) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) -
            TileCentroid T₀ = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → ((∀ (x :
            GaussianInt), x ∈ h₀.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (hsx i s).domain) →
            ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (hsx i s).domain, h₀.value x = (hsx i
            s).value x) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (q i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ
            × ℝ) (p_i : ℝ × ℝ), PartialOdometerSlope h₀ = some p ∧ PartialOdometerSlope (hsx i s)
            = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
            ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q
            (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (∀ u, ∀ v, ∀ l, ∀ r, p = l ++ u :: v :: r
            → ∃ c : ℤ, ∀ z, (z = u ∨ z = v) → z ∈ hᵢ.domain → z ∈ h₀.domain → hᵢ.value z -
            h₀.value z = c)))))))))))))))))))))) ) := by
  classical
  intro edge_endpoints n ih C₀ Cᵢ T₀ Tᵢ h₀ hᵢ hn hOT0 hOTi hdomi hex p hstep hpedges p₀ pᵢ hp₀
      hpᵢ q i s hq hqC hqI rest S hsx hchildren hcells hfoot hcent hdoms hvalues hslopes u v l r hpr
  have he : {u, v} ∈ FootprintEdges T₀ ∩ FootprintEdges Tᵢ := by
    apply (hpedges {u, v}).mpr
    exact ⟨u, v, l, r, hpr, rfl⟩
  rcases he.1 with ⟨a, ha, heq⟩
  rcases heq with heq | heq | heq | heq
  all_goals
    have hac : ∃ j t, a ∈ (S j t).cells := (hcells a).mp ha
    rcases hac with ⟨j, t, has⟩
    have heS : {u, v} ∈ FootprintEdges (S j t) := by
      rw [heq]
      exact ⟨a, has, by simp⟩
    have hposchild : 0 < (q j.succ).1 := by
      have hnchild := (ProperBandCurvatureStructure q hq).2.1 j
      have hchild := hchildren j t
      generalize hqj : q j.succ = cj at hchild heS
      have hposcj : 0 < cj.1 := by
        by_contra hz
        have hnoncj : 0 ≤ cj.1 := by simpa [hqj] using hnchild
        have hz0 : cj.1 = 0 := by omega
        generalize hS : S j t = U at hchild heS
        revert heS
        cases hchild with
        | line w z hw k hd => intro heS; simp [FootprintEdges] at heS
        | unit z x U k hU hd ht => intro; omega
        | decompose hq' hT' hs' hU hcells' hfoot' hcent' hdom'
            hvalue' hcompat' =>
          have hp' := (ProperBandCurvatureStructure _ hq').1
          intro
          omega
      simpa [hqj] using hposcj
    have hsub : TileSubodometer C₀.1.1 (q j.succ)
        T₀ (S j t) h₀ (hsx j t) := by
      refine ⟨hOT0, hchildren j t, hfoot j t, ?_, ?_, ?_⟩
      · intro z hz; exact (hdoms z).mpr ⟨j, t, hz⟩
      · exact fun z hz => hvalues j t z hz
      · refine ⟨q, j, hq, hqC, rfl, t, hcent j t, ?_⟩
        exact hslopes j t
    let Cj : BandCircle :=
      ⟨⟨q j.succ, ⟨Or.inl hposchild,
        ⟨q, hq.1, ⟨j.succ, rfl⟩⟩⟩⟩, hposchild⟩
    have had0 := ((OdometerAdjacencyInduction.1 C₀ hex).2
      Cᵢ Tᵢ T₀ hᵢ h₀ ⟨hOT0, hOTi, ⟨p₀, pᵢ, hp₀, hpᵢ,
        q, i, s, hq, hqC, hqI, rest⟩⟩)
    have had := had0 (C' := Cj) (T' := S j t) (h' := hsx j t)
      (by simpa [Cj] using hsub) (by
        refine ⟨u, ?_, ?_⟩
        · exact (Set.ext_iff.mp (PositiveCurvatureTileOdometerDomain
            (q j.succ) (S j t) (hsx j t) hposchild (hchildren j t)) u).mpr
            (edge_endpoints (S j t) u v heS).1
        · exact (Set.ext_iff.mp hdomi u).mpr
            (edge_endpoints Tᵢ u v he.2).1)
    have hlt := hq.2 j
    have hltNat : (Int.toNat (q j.succ).1 : Nat) < Int.toNat (q 0).1 :=
      (Int.toNat_lt_toNat (by simpa [hqC] using C₀.property)).2 hlt
    have hci : Int.toNat Cᵢ.1.1.1 = Int.toNat (q i.succ).1 := by
      simp [hqI]
    have hc0 : Int.toNat C₀.1.1.1 = Int.toNat (q 0).1 := by
      simp [hqC]
    have hcj : Int.toNat Cj.1.1.1 = Int.toNat (q j.succ).1 := by
      simp [Cj]
    have hltSum : Int.toNat Cᵢ.1.1.1 + Int.toNat (q j.succ).1 < n := by
      omega
    have hcpt := (ih (Int.toNat Cᵢ.1.1.1 + Int.toNat Cj.1.1.1)
        (by simpa [Cj] using hltSum)).2
    have common : ∃ c : ℤ, ∀ z, (z = u ∨ z = v) →
        z ∈ hᵢ.domain → z ∈ h₀.domain → hᵢ.value z - h₀.value z = c := by
      have child_mem : ∀ z, z = u ∨ z = v → z ∈ (hsx j t).domain := by
        intro z hz
        have ev := edge_endpoints (S j t) u v heS
        rcases hz with hz | hz
        · subst z
          exact (Set.ext_iff.mp (PositiveCurvatureTileOdometerDomain
            (q j.succ) (S j t) (hsx j t) hposchild (hchildren j t)) u).mpr ev.1
        · subst z
          exact (Set.ext_iff.mp (PositiveCurvatureTileOdometerDomain
            (q j.succ) (S j t) (hsx j t) hposchild (hchildren j t)) v).mpr ev.2
      have outer_mem : ∀ z, z = u ∨ z = v → z ∈ hᵢ.domain := by
        intro z hz
        have ev := edge_endpoints Tᵢ u v he.2
        rcases hz with hz | hz
        · subst z; exact (Set.ext_iff.mp hdomi u).mpr ev.1
        · subst z; exact (Set.ext_iff.mp hdomi v).mpr ev.2
      rcases had with hsingle | had
      · exfalso
        have eu := edge_endpoints (S j t) u v heS
        have ei := edge_endpoints Tᵢ u v he.2
        have eus : u ∈ (hsx j t).domain := child_mem u (Or.inl rfl)
        have evs : v ∈ (hsx j t).domain := child_mem v (Or.inr rfl)
        have eui : u ∈ hᵢ.domain := (Set.ext_iff.mp hdomi u).mpr ei.1
        have evi : v ∈ hᵢ.domain := (Set.ext_iff.mp hdomi v).mpr ei.2
        have huv := hsingle ⟨eus, eui⟩ ⟨evs, evi⟩
        have hne : u ≠ v := by
          intro huv'
          subst v
          have hh := hstep u u l r hpr
          rcases hh with hh | hh | hh | hh
          · have hbad := congrArg (fun z : GaussianInt => z.re) hh
            norm_num at hbad
          · have hbad := congrArg (fun z : GaussianInt => z.re) hh
            norm_num at hbad; omega
          · have hbad := congrArg (fun z : GaussianInt => z.im) hh
            norm_num at hbad
          · have hbad := congrArg (fun z : GaussianInt => z.im) hh
            norm_num at hbad; omega
        exact False.elim (hne huv)
      · rcases had with hleft | had
        have compat := (LeftAdjacentOdometerCompatibility
          Cᵢ Tᵢ (S j t) hᵢ (hsx j t) hleft.2).1
        rcases compat with hd | ⟨c, hc⟩
        · exact False.elim (Set.disjoint_left.1 hd
            (outer_mem u (Or.inl rfl)) (child_mem u (Or.inl rfl)))
        · refine ⟨-c, ?_⟩
          intro z hz hz0 hz00
          have hzS := child_mem z hz
          have hv := hc z (outer_mem z hz) hzS
          rw [hvalues j t z hzS]
          omega
        · rcases had with hsubadj | hrev
          · have hh := (ih (Int.toNat Cᵢ.1.1.1 + Int.toNat Cj.1.1.1)
              (by omega)).2 Cᵢ Cj Tᵢ (S j t) hᵢ (hsx j t) (by omega) hsubadj
            rcases hh with hd | ⟨c, hc⟩
            · exfalso
              exact (Set.disjoint_left.1 hd)
                (outer_mem u (Or.inl rfl)) (child_mem u (Or.inl rfl))
            · refine ⟨-c, ?_⟩
              intro z hz hz0 hz00
              have hzS := child_mem z hz
              have hv := hc z (outer_mem z hz) hzS
              rw [hvalues j t z hzS]
              omega
          · have hh := (ih (Int.toNat Cj.1.1.1 + Int.toNat Cᵢ.1.1.1)
              (by omega)).2 Cj Cᵢ (S j t) Tᵢ (hsx j t) hᵢ (by omega) hrev
            rcases hh with hd | ⟨c, hc⟩
            · exfalso
              exact (Set.disjoint_left.1 hd)
                (child_mem u (Or.inl rfl)) (outer_mem u (Or.inl rfl))
            · refine ⟨c, ?_⟩
              intro z hz hz0 hz00
              have hzS := child_mem z hz
              have hv := hc z hzS (outer_mem z hz)
              rw [hvalues j t z hzS]
              exact hv
    exact common

end RightCompatibilityGeometry

theorem RightSubtileOdometerCompatibility :
    (∀ (C : BandCircle) (T T' : ProtoTile) (h h' : PartialOdometer),
      RightLatticeAdjacent C T T' h h' → OdometerCompatibility h h') ∧
    ∀ (C₀ Cᵢ : BandCircle) (T₀ Tᵢ : ProtoTile)
        (h₀ hᵢ : PartialOdometer),
      SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ →
      OdometerCompatibility h₀ hᵢ := by
-- BODY
  have singleton_case := RightCompatibilityGeometry.singleton_case
  have list_glue := RightCompatibilityGeometry.list_glue
  have child_circle : ∀ (q : Fin 4 → CircleCoordinates),
      ProperBandQuadruple q → ∀ j : Fin 3, 0 < (q j.succ).1 → BandCircle := by
    intro q hq j hj
    refine ⟨⟨q j.succ, ?_⟩, hj⟩
    exact ⟨Or.inl hj, ⟨q, hq.1, ⟨j.succ, rfl⟩⟩⟩
  have edge_endpoints := RightCompatibilityGeometry.edge_endpoints
  have main : ∀ n : Nat,
      (∀ (C : BandCircle) (T T' : ProtoTile) (h h' : PartialOdometer),
        Int.toNat C.1.1.1 + Int.toNat C.1.1.1 = n →
        RightLatticeAdjacent C T T' h h' → OdometerCompatibility h h') ∧
      (∀ (C₀ Cᵢ : BandCircle) (T₀ Tᵢ : ProtoTile)
        (h₀ hᵢ : PartialOdometer),
        Int.toNat C₀.1.1.1 + Int.toNat Cᵢ.1.1.1 = n →
        SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ →
        OdometerCompatibility h₀ hᵢ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      constructor
      · intro C T T' h h' hn hadj
        by_cases hs : ((h.domain : Set GaussianInt) ∩
            (h'.domain : Set GaussianInt)).Subsingleton
        · exact singleton_case h h' hs
        · rcases hadj with ⟨hOT, hOT', hdata⟩
          have hdom : (h.domain : Set GaussianInt) = FootprintVertices T :=
            PositiveCurvatureTileOdometerDomain C.1.1 T h C.property hOT
          have hdom' : (h'.domain : Set GaussianInt) = FootprintVertices T' :=
            PositiveCurvatureTileOdometerDomain C.1.1 T' h' C.property hOT'
          by_cases hex :
              (∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
                BandPackingSymmetryCircleAction g
                  (FordCircleCoordinate P.p P.q) = C.1.1) ∨
              (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
                BandPackingSymmetryCircleAction g
                  (DiamondRecursiveQuadruple K 0) = C.1.1)
          · exact ((OdometerAdjacencyInduction).2 C hex).1 T T' h h'
              ⟨hOT, hOT', hdata⟩
          · obtain ⟨x, y, path⟩ :=
              (LatticeAdjacentInterfacePath.1 C T T' h h'
                ⟨hOT, hOT', hdata⟩)
            rcases path with ⟨p, hpnd, hplen, hhead, hlast, hpverts, hstep, hpedges⟩
            have qdata := RightCompatibilityGeometry.qdata C T T' h h' hdata
            rcases qdata with ⟨q, i, e, hq, hqC⟩
            have hroot : 1 < (q 0).1 := RightCompatibilityGeometry.hrootAt310 n C p q hq hqC
            obtain ⟨S, hsx, hband, hchildren, hcells, hfoot, hcent,
              hdoms, hvalues, hcomps, hslopes⟩ :=
              TileOdometerReindexedDecomposition q hq T h hroot (by simpa [hqC] using hOT)
            have edgeStep := RightCompatibilityGeometry.edgeStepAt328 edge_endpoints n ih C T T'
                h h' hn hOT hOT' hdata hdom' hex p hpedges q hq hqC S hsx hchildren hcells hfoot
                hcent hdoms hvalues hslopes
            obtain ⟨c, hc⟩ := list_glue p h' h hplen edgeStep (by
              intro z hz
              have hz' : z ∈ FootprintVertices T ∩ FootprintVertices T' :=
                  RightCompatibilityGeometry.hz'At423 T T' p hpverts z hz
              constructor
              · change z ∈ (h'.domain : Set GaussianInt)
                exact hdom'.symm ▸ hz'.2
              · change z ∈ (h.domain : Set GaussianInt)
                exact hdom.symm ▸ hz'.1)
            exact Or.inr ⟨-c, by
              intro z hz0 hz1
              have hzV : z ∈ FootprintVertices T ∩ FootprintVertices T' := by
                exact ⟨hdom ▸ hz0, hdom' ▸ hz1⟩
              have hzP := RightCompatibilityGeometry.hzPAt435 T T' p hpverts z hzV
              have hv := hc z hzP hz1 hz0
              omega⟩
      · intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ hn hadj
        by_cases hs : ((h₀.domain : Set GaussianInt) ∩
            (hᵢ.domain : Set GaussianInt)).Subsingleton
        · exact singleton_case h₀ hᵢ hs
        · rcases hadj with ⟨hOT0, hOTi, hdata⟩
          have hdom0 : (h₀.domain : Set GaussianInt) = FootprintVertices T₀ :=
            PositiveCurvatureTileOdometerDomain C₀.1.1 T₀ h₀ C₀.property hOT0
          have hdomi : (hᵢ.domain : Set GaussianInt) = FootprintVertices Tᵢ :=
            PositiveCurvatureTileOdometerDomain Cᵢ.1.1 Tᵢ hᵢ Cᵢ.property hOTi
          by_cases hex :
              (∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
                BandPackingSymmetryCircleAction g
                  (FordCircleCoordinate P.p P.q) = C₀.1.1) ∨
              (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
                BandPackingSymmetryCircleAction g
                  (DiamondRecursiveQuadruple K 0) = C₀.1.1)
          · exact ((OdometerAdjacencyInduction.2 C₀ hex).2 Cᵢ T₀ Tᵢ h₀ hᵢ
              ⟨hOT0, hOTi, hdata⟩)
          · obtain ⟨x, y, path⟩ :=
              (LatticeAdjacentInterfacePath.2 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ
                ⟨hOT0, hOTi, hdata⟩)
            rcases path with ⟨p, hpnd, hplen, hhead, hlast, hpverts, hstep, hpedges⟩
            rcases hdata with ⟨p₀, pᵢ, hp₀, hpᵢ, q, i, s, hq, hqC, hqI, rest⟩
            have hroot : 1 < (q 0).1 := RightCompatibilityGeometry.hrootAt463 n C₀ Cᵢ p q hq hqC
            obtain ⟨S, hsx, hband, hchildren, hcells, hfoot, hcent,
              hdoms, hvalues, hcomps, hslopes⟩ :=
              TileOdometerReindexedDecomposition q hq T₀ h₀ hroot
                (by simpa [hqC] using hOT0)
            have edgeStep := RightCompatibilityGeometry.edgeStepAt482 edge_endpoints n ih C₀ Cᵢ
                T₀ Tᵢ h₀ hᵢ hn hOT0 hOTi hdomi hex p hstep hpedges p₀ pᵢ hp₀ hpᵢ q i s hq hqC hqI
                rest S hsx hchildren hcells hfoot hcent hdoms hvalues hslopes
            obtain ⟨c, hc⟩ := list_glue p h₀ hᵢ hplen (by
              intro u v l r hpr
              obtain ⟨d, hd⟩ := edgeStep u v l r hpr
              refine ⟨d, ?_⟩
              intro z hz hz0 hzi
              have hv := hd z hz hzi hz0
              exact hv) (by
              intro z hz
              have hz' : z ∈ FootprintVertices T₀ ∩ FootprintVertices Tᵢ := by
                rw [hpverts]; exact hz
              constructor
              · change z ∈ (h₀.domain : Set GaussianInt)
                exact hdom0.symm ▸ hz'.1
              · change z ∈ (hᵢ.domain : Set GaussianInt)
                exact hdomi.symm ▸ hz'.2)
            refine Or.inr ⟨c, ?_⟩
            intro z hz0 hzi
            have hzV : z ∈ FootprintVertices T₀ ∩ FootprintVertices Tᵢ :=
              ⟨hdom0 ▸ hz0, hdomi ▸ hzi⟩
            have hzP : z ∈ (p.toFinset : Set GaussianInt) := by
              rw [← hpverts]; exact hzV
            exact hc z hzP hz0 hzi
  constructor
  · intro C T T' h h' hadj
    exact main (Int.toNat C.1.1.1 + Int.toNat C.1.1.1) |>.1 C T T' h h' rfl hadj
  · intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ hadj
    exact main (Int.toNat C₀.1.1.1 + Int.toNat Cᵢ.1.1.1) |>.2 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ rfl hadj

end ApollonianSuperharmonic

end
