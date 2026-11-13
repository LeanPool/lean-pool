/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.TileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique

-- [TABLET NODE: AncestorOdometerRestriction]

/-!
# AncestorOdometerRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace AncestorRestrictionProof

private theorem odo_eq :
    (by
      classical
      exact
        ∀ a b : PartialOdometer, (a.domain : Set GaussianInt) = b.domain → (∀ x, x ∈ a.domain →
        a.value x = b.value x) → a = b ) := by
  classical
  intro a b hab hv
  cases a with
  | mk ad av ao =>
    cases b with
    | mk bd bv bo =>
      have hd : ad = bd := by
        ext x
        exact Set.ext_iff.mp hab x
      subst bd
      have he : av = bv := by
        funext x
        by_cases hx : x ∈ ad
        · exact hv x hx
        · rw [ao x hx, bo x hx]
      subst bv
      rfl

private theorem band_one :
    (by
      classical
      exact
        ∀ c : CircleCoordinates, ∀ U : ProtoTile, BandPrototile c U → c.1 = 1 → ∃ x : GaussianInt,
        U.cells = {x} ) := by
  classical
  intro c U hu
  induction hu with
  | line w x hw =>
      intro hc
      norm_num at hc
  | unit z x anchor =>
      intro hc
      exact ⟨x, rfl⟩
  | @decompose q hq S U hS hcells hfoot hcent ih =>
      intro hc
      have facts := ProperBandCurvatureStructure q hq
      have hz : ∀ j : Fin 3, (q j.succ).1 = 0 := by
        intro j
        have hlt := hq.2 j
        have hn := facts.2.1 j
        omega
      exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 (hz 0) (hz 1))).elim

private theorem parent_gt_one :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (((0 : ℤ) < (q (0 :
            Fin (4
        : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j :
            Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) → (1 < (q
            0).1)) ) := by
  classical
  intro q hq facts
  have hp := facts.1
  by_contra hn
  have hle : (q 0).1 ≤ 1 := by omega
  have z0 : (q (0 : Fin 3).succ).1 = 0 := by
    have hb := hq.2 0
    have hn0 := facts.2.1 (0 : Fin 3)
    omega
  have z1 : (q (1 : Fin 3).succ).1 = 0 := by
    have hb := hq.2 1
    have hn1 := facts.2.1 (1 : Fin 3)
    omega
  exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim

private theorem hrestrict :
    (by
      classical
      exact
        ∀ (domain_from_odo : ∀ (c : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k :
            PartialOdometer), TileOdometer c U k → (k.domain : Set GaussianInt) =
            FootprintVertices U),
        let vertices : ProtoTile → Finset GaussianInt := fun U =>
        if U.cells.Nonempty then
        U.cells.biUnion (fun x => {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
        else {U.anchor}
        let restrict : ProtoTile → PartialOdometer → PartialOdometer :=
        fun U g =>
          { domain := vertices U
            value := fun x => if x ∈ vertices U then g.value x else 0
            value_outside := by
              intro x hx
              simp [hx] }
        (∀ U, ∀ g, ((restrict U g).domain : Set GaussianInt) = FootprintVertices U) → ((∀ a b :
        PartialOdometer, (a.domain : Set GaussianInt) = b.domain → (∀ x, x ∈ a.domain → a.value x
        = b.value x) → a = b) → ((∀ (c : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k :
            PartialOdometer), TileOdometer c U k → BandPrototile c U) → (∀ (X : CircleCoordinates ×
        ProtoTile), ∀ (Y : CircleCoordinates × ProtoTile), ∀ (g : PartialOdometer), ((↑g.domain :
        Set GaussianInt) = FootprintVertices Y.2) → ((TileOdometer Y.1 Y.2 g) → (∀ (q : Fin (4 :
        ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (ProperBandQuadruple q) → ((q
        (0 : Fin (4 : ℕ)) = Y.1) → ((q i.succ = X.1) → ((BandPrototile Y.1 Y.2) → ((BandPrototile
        X.1 X.2) → ((FootprintVertices X.2 ⊆ FootprintVertices Y.2) → ((TileCentroid X.2 -
        TileCentroid Y.2 = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
        (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
        ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i
        + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
        ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → ((1 < (q 0).1) → (TileOdometer X.1
        X.2 (restrict X.2 g)))))))))))))) ) := by
  classical
  intro domain_from_odo vertices restrict restrict_domain odo_eq band_from_odo X Y g hgd hgo q i
      s hq hq0 hqi hY hX hfoot hcent parent_gt_one
  cases Y with
  | mk yc yt =>
    cases hgo with
    | line w x hw hdom =>
        have bad : (q 0).1 = 0 := by
          have hh := congrArg (fun c : CircleCoordinates => c.1) hq0
          simpa using hh
        omega
    | unit z x U hU hdom htrans =>
        have bad : (q 0).1 = 1 := by
          have hh := congrArg (fun c : CircleCoordinates => c.1) hq0
          simpa using hh
        omega
    | @decompose q' hq' S V hs hV hsub hcells hfoot' hcentroid hdom hvalue hcompat hslope =>
        have hrot := BandPredecessorNoCollision q q' hq hq'
          (by simp [hq0])
        rcases hrot with ⟨r, hrotation, _⟩
        let a : Fin 3 := i - r
        have har : a + r = i := by
          fin_cases i <;> fin_cases r <;> simp [a]
        have hqa : q' a.succ = X.1 := by
          calc
            q' a.succ = q ((a + r).succ) := hrotation a
            _ = q i.succ := by rw [har]
            _ = X.1 := hqi
        have hv1 : q' ((a + 2).succ) = q ((i + 2).succ) := by
          have hh := hrotation (a + 2)
          convert hh using 1; fin_cases i <;> fin_cases r <;> simp [a]
        have hv2 : q' ((a + 1).succ) = q ((i + 1).succ) := by
          have hh := hrotation (a + 1)
          convert hh using 1; fin_cases i <;> fin_cases r <;> simp [a]
        have hcentS : TileCentroid (S a s) = TileCentroid X.2 := by
          have hd : TileCentroid (S a s) - TileCentroid (q' 0, yt).2 =
              TileCentroid X.2 - TileCentroid (q' 0, yt).2 := by
            rw [hdom a s, hv1, hv2]
            exact hcent.symm
          exact sub_left_inj.mp hd.symm |>.symm
        have hbandS : BandPrototile X.1 (S a s) := by
          have hh := band_from_odo _ _ _ (hcells a s)
          rw [hqa] at hh
          exact hh
        have huniq := BandPrototileCentroidUnique X.1 X.2 (S a s)
          hX hbandS hcentS.symm
        have hfp : FootprintVertices (S a s) = FootprintVertices X.2 := by
          rcases huniq with ⟨heq, hempty⟩
          by_cases hn : (S a s).cells.Nonempty
          · have hn' : X.2.cells.Nonempty := by simpa [heq] using hn
            simp [FootprintVertices, hn, heq]
          · have he : (S a s).cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
            have he' : X.2.cells = ∅ := by simpa [heq] using he
            have ha := hempty he'
            simp [FootprintVertices, hn, he', ha]
        have hkeq : restrict X.2 g = hs a s := by
          apply odo_eq
          focus rw [restrict_domain, domain_from_odo _ _ _ (hcells a s), hfp]
          intro x hx
          have hx' : x ∈ FootprintVertices (S a s) :=
            Set.ext_iff.mp hfp x |>.mpr
              (Set.ext_iff.mp (restrict_domain X.2 g) x |>.mp hx)
          have hxhs : x ∈ (hs a s).domain :=
            Set.ext_iff.mp (domain_from_odo _ _ _ (hcells a s)) x |>.mpr hx'
          have hxg : x ∈ g.domain :=
            Set.ext_iff.mp hgd x |>.mpr
              (hfoot (Set.ext_iff.mp (restrict_domain X.2 g) x |>.mp hx))
          simp [restrict, hx, hcompat a s x hxhs]
        rw [hkeq]
        have ho := hcells a s
        have htarget : TileOdometer (q' a.succ) (S a s) (hs a s) := by
          generalize hcoord : q' a.succ = coord at ho ⊢
          generalize htile : S a s = tile at ho ⊢
          cases ho with
          | line w x hw =>
              exact TileOdometer.line w x hw (hs a s) (by assumption)
          | unit z x =>
              exact TileOdometer.unit z x tile (hs a s) (by assumption)
                (by assumption) (by assumption)
          | decompose hqz hTz hsz hcz hfz hdz hvz hcoz hslz =>
              apply TileOdometer.decompose <;> assumption
        have htarget' : TileOdometer X.1 (S a s) (hs a s) := by
          simpa [hqa] using htarget
        generalize hcoord : X.1 = coord at htarget' ⊢
        generalize htileX : X.2 = target at htarget' ⊢
        generalize htileS : S a s = source at htarget' ⊢
        cases htarget' with
        | line w x hw =>
            have hc : target.cells = ∅ := by
              have hcX : X.2.cells = ∅ := by rw [huniq.1, htileS]
              exact (congrArg ProtoTile.cells htileX).symm ▸ hcX
            have ha : target.anchor = x := by
              have he := huniq.2 (by rw [huniq.1, htileS])
              have hx : X.2.anchor = x := by simpa [htileS] using he
              exact (congrArg ProtoTile.anchor htileX).symm ▸ hx
            have ht : target = ⟨∅, x⟩ := by
              cases target
              simp only [ProtoTile.mk.injEq]
              exact ⟨hc, ha⟩
            rw [ht]
            exact TileOdometer.line w x hw (hs a s) (by assumption)
        | unit z x =>
            have hd := domain_from_odo _ _ _ ho
            have hsource : source.cells = {x} := by assumption
            have htargetcells : target.cells = {x} := by
              have heX : X.2.cells = source.cells :=
                huniq.1.trans (congrArg ProtoTile.cells htileS)
              have he : target.cells = source.cells :=
                (congrArg ProtoTile.cells htileX).symm ▸ heX
              exact he.trans hsource
            have hsource_ne : source.cells.Nonempty := by
              rw [hsource]
              simp
            have htarget_ne : target.cells.Nonempty := by
              rw [htargetcells]
              simp
            have hfootst : FootprintVertices source =
                FootprintVertices target := by
              simp only [FootprintVertices, ite_eq_left hsource_ne,
                ite_eq_left htarget_ne]
              rw [htargetcells, hsource]
            exact TileOdometer.unit z x target (hs a s) htargetcells
              (by
                rw [htileS] at hd
                exact hd.trans hfootst)
              (by assumption)
        | decompose hqz hTz hsz hcz hfz hdz hvz hcoz hslz hslopez =>
            have hX' := hX
            rw [htileX, hcoord] at hX'
            have hcst : target.cells = source.cells := by
              exact (congrArg ProtoTile.cells htileX).symm ▸
                huniq.1.trans (congrArg ProtoTile.cells htileS)
            have hpst : FootprintVertices source = FootprintVertices target := by
              rw [← htileS, hfp, htileX]
            have hcentst : TileCentroid source = TileCentroid target := by
              rw [← htileS, hcentS, htileX]
            refine TileOdometer.decompose hqz hX' hsz ?_ ?_ ?_ hvz hcoz hslz hslopez
            · intro x
              rw [hcst]
              exact hcz x
            · intro j t x hx
              rw [← hpst]
              exact hfz j t hx
            · intro j t
              simpa [hcentst] using hdz j t

private theorem chain_foot :
    (by
      classical
      exact
        ∀ (p : CircleCoordinates × ProtoTile), ∀ (q : CircleCoordinates × ProtoTile), AncestorTile
        p.1 q.1 p.2 q.2 → FootprintVertices p.2 ⊆ FootprintVertices q.2 ) := by
  classical
  intro p q hc
  unfold AncestorTile at hc
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => FootprintVertices a.2 ⊆ FootprintVertices q.2) hc ?_ ?_
  · intro x hx
    exact hx
  · intro a c hedge hrest ih
    rcases hedge with ⟨q, i, s, hq, hq0, hqi, hY, hX, hfoot, hcent⟩
    exact Set.Subset.trans hfoot ih

private theorem main :
    (by
      classical
      exact
        let vertices : ProtoTile → Finset GaussianInt := fun U =>
        if U.cells.Nonempty then
        U.cells.biUnion (fun x => {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
        else {U.anchor}
        let restrict : ProtoTile → PartialOdometer → PartialOdometer :=
        fun U g =>
          { domain := vertices U
            value := fun x => if x ∈ vertices U then g.value x else 0
            value_outside := by
              intro x hx
              simp [hx] }
        (∀ U, ∀ g, ((restrict U g).domain : Set GaussianInt) = FootprintVertices U) → ((∀ (X :
            CircleCoordinates × ProtoTile), ∀ (Y : CircleCoordinates × ProtoTile), (∃ r : Fin 4 →
        CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool, ProperBandQuadruple r ∧ r 0 = Y.1 ∧ r i.succ
        = X.1 ∧ BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧ FootprintVertices X.2 ⊆
        FootprintVertices Y.2 ∧ TileCentroid X.2 - TileCentroid Y.2 = (if s = true then (1 :
        Real) else -1) • ((1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (r ((i + 2).succ))
        (r ((i + 1).succ))) - (-((GaussianRealPoint (BandVectors.1 (r ((i + 2).succ)) (r ((i +
        1).succ)))).2), (GaussianRealPoint (BandVectors.1 (r ((i + 2).succ)) (r ((i +
        1).succ)))).1)))) → ∀ g : PartialOdometer, (g.domain : Set GaussianInt) =
        FootprintVertices Y.2 → TileOdometer Y.1 Y.2 g → TileOdometer X.1 X.2 (restrict X.2 g)) →
        ((∀ (p : CircleCoordinates × ProtoTile), ∀ (q : CircleCoordinates × ProtoTile),
            AncestorTile p.1 q.1 p.2 q.2 → FootprintVertices p.2 ⊆ FootprintVertices q.2) → (∀ (p
            : CircleCoordinates × ProtoTile), ∀ (q : CircleCoordinates × ProtoTile),
            Relation.ReflTransGen (fun X Y : CircleCoordinates × ProtoTile => ∃ r : Fin 4 →
        CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool, ProperBandQuadruple r ∧ r 0 = Y.1 ∧ r i.succ
        = X.1 ∧ BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧ FootprintVertices X.2 ⊆
        FootprintVertices Y.2 ∧ TileCentroid X.2 - TileCentroid Y.2 = (if s = true then (1 :
        Real) else -1) • ((1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (r ((i + 2).succ))
        (r ((i + 1).succ))) - (-((GaussianRealPoint (BandVectors.1 (r ((i + 2).succ)) (r ((i +
        1).succ)))).2), (GaussianRealPoint (BandVectors.1 (r ((i + 2).succ)) (r ((i +
        1).succ)))).1)))) p q → ∀ (k : PartialOdometer), ∀ (g : PartialOdometer), (g.domain : Set
        GaussianInt) = FootprintVertices q.2 → (k.domain : Set GaussianInt) = FootprintVertices
        p.2 → k.domain ⊆ g.domain → (∀ x, x ∈ k.domain → k.value x = g.value x) → TileOdometer
        q.1 q.2 g → TileOdometer p.1 p.2 k))) ) := by
  classical
  intro vertices restrict restrict_domain one_step chain_foot p q hac
  induction hac with
  | refl =>
      intro k g hdom hkd hsub hval hodo
      cases p with
      | mk c u =>
        have heqdom : (g.domain : Set GaussianInt) = (k.domain : Set GaussianInt) := by
          rw [hdom, hkd]
        have heqval : ∀ x, k.value x = g.value x := by
          intro x
          by_cases hx : x ∈ k.domain
          · exact hval x hx
          · have hg : x ∉ g.domain := by
              intro hgx
              apply hx
              exact Set.ext_iff.mp heqdom x |>.mp hgx
            rw [k.value_outside x hx, g.value_outside x hg]
        have hk : k = g := by
          cases k with
          | mk kd kv ko =>
            cases g with
            | mk gd gv go =>
              simp only at heqdom heqval ⊢
              have hd : kd = gd := by
                ext x
                exact (Set.ext_iff.mp heqdom x).symm
              subst gd
              have hv : kv = gv := by
                funext x
                exact heqval x
              subst gv
              rfl
        simpa [hk] using hodo
  | @tail b c hxy hy ih =>
      intro k g hgd hkd hsub hval hodo
      rcases hy with ⟨r, j, t, hr, hr0, hrj, hY, hX, hinc, hdiff⟩
      have hpq : FootprintVertices p.2 ⊆ FootprintVertices b.2 :=
        chain_foot _ _ hxy
      let gm := restrict b.2 g
      have hgm : TileOdometer b.1 b.2 gm := by
        exact one_step (b.1, b.2) (c.1, c.2)
          ⟨r, j, t, hr, hr0, hrj, hY, hX, hinc, hdiff⟩ g hgd hodo
      apply ih k gm (restrict_domain b.2 g) hkd
      · intro x hx
        have hxb : x ∈ FootprintVertices b.2 :=
          hpq (Set.ext_iff.mp hkd x |>.mp hx)
        exact Set.ext_iff.mp (restrict_domain b.2 g) x |>.mpr hxb
      · intro x hx
        have hxb : x ∈ FootprintVertices b.2 :=
          hpq (Set.ext_iff.mp hkd x |>.mp hx)
        rw [hval x hx]
        have hxv : x ∈ vertices b.2 :=
          Set.ext_iff.mp (restrict_domain b.2 g) x |>.mpr hxb
        simp [gm, restrict, hxv]
      · exact hgm

end AncestorRestrictionProof

theorem AncestorOdometerRestriction
    (C C₀ : CircleCoordinates) (T T₀ : ProtoTile)
    (h h₀ : PartialOdometer)
    (ha : AncestorOdometer C C₀ T T₀ h h₀) :
    TileOdometer C T h := by
-- BODY
  classical
  have domain_from_odo : ∀ (c : CircleCoordinates) (U : ProtoTile)
      (k : PartialOdometer), TileOdometer c U k →
        (k.domain : Set GaussianInt) = FootprintVertices U :=
            TileOdometerDomain
  have positive_cells : ∀ (c : CircleCoordinates) (U : ProtoTile),
      0 < c.1 → BandPrototile c U → U.cells.Nonempty := BandPrototileNonempty.positive
  let vertices : ProtoTile → Finset GaussianInt := fun U =>
    if U.cells.Nonempty then
      U.cells.biUnion (fun x => {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
    else {U.anchor}
  have vertices_spec : ∀ U : ProtoTile,
      (vertices U : Set GaussianInt) = FootprintVertices U := by
    intro U
    classical
    by_cases hn : U.cells.Nonempty
    · ext x
      simp [vertices, FootprintVertices, hn]
    · ext x
      simp [vertices, FootprintVertices, hn]
  let restrict : ProtoTile → PartialOdometer → PartialOdometer :=
    fun U g =>
      { domain := vertices U
        value := fun x => if x ∈ vertices U then g.value x else 0
        value_outside := by
          intro x hx
          simp [hx] }
  have restrict_domain : ∀ U g,
      ((restrict U g).domain : Set GaussianInt) = FootprintVertices U := by
    intro U g
    exact vertices_spec U
  have restrict_subset : ∀ U g V,
      (g.domain : Set GaussianInt) = FootprintVertices V →
      FootprintVertices U ⊆ FootprintVertices V →
      (restrict U g).domain ⊆ g.domain := by
    intro U g V hgd hincl x hx
    have hx' : x ∈ FootprintVertices U :=
      Set.ext_iff.mp (restrict_domain U g) x |>.mp hx
    have hx'' := hincl hx'
    exact Set.ext_iff.mp hgd x |>.mpr hx''
  have restrict_agrees : ∀ U g,
      ∀ x, x ∈ (restrict U g).domain → (restrict U g).value x = g.value x := by
    intro U g x hx
    have hx' : x ∈ vertices U := hx
    simp [restrict, hx']
  have odo_eq : ∀ a b : PartialOdometer,
      (a.domain : Set GaussianInt) = b.domain →
      (∀ x, x ∈ a.domain → a.value x = b.value x) → a = b := AncestorRestrictionProof.odo_eq
  have band_from_odo : ∀ (c : CircleCoordinates) (U : ProtoTile)
      (k : PartialOdometer), TileOdometer c U k → BandPrototile c U :=
          TileOdometerBandPrototile
  have one_step : ∀ (X Y : CircleCoordinates × ProtoTile),
      (∃ r : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
        ProperBandQuadruple r ∧ r 0 = Y.1 ∧ r i.succ = X.1 ∧
        BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
        FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
        TileCentroid X.2 - TileCentroid Y.2 =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (r ((i + 2).succ))
                      (r ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (r ((i + 2).succ))
                      (r ((i + 1).succ)))).1)))) →
      ∀ g : PartialOdometer,
        (g.domain : Set GaussianInt) = FootprintVertices Y.2 →
        TileOdometer Y.1 Y.2 g →
        TileOdometer X.1 X.2 (restrict X.2 g) := by
    intro X Y hedge g hgd hgo
    rcases hedge with ⟨q, i, s, hq, hq0, hqi, hY, hX, hfoot, hcent⟩
    have band_one : ∀ c : CircleCoordinates, ∀ U : ProtoTile,
        BandPrototile c U → c.1 = 1 → ∃ x : GaussianInt, U.cells = {x} :=
            AncestorRestrictionProof.band_one
    have facts := ProperBandCurvatureStructure q hq
    have parent_gt_one : 1 < (q 0).1 := AncestorRestrictionProof.parent_gt_one q hq facts
    have hrestrict : TileOdometer X.1 X.2 (restrict X.2 g) := AncestorRestrictionProof.hrestrict
        domain_from_odo restrict_domain odo_eq band_from_odo X Y g hgd hgo q i s hq hq0 hqi hY hX
        hfoot hcent parent_gt_one
    exact hrestrict
  have chain_foot : ∀ (p q : CircleCoordinates × ProtoTile),
      AncestorTile p.1 q.1 p.2 q.2 → FootprintVertices p.2 ⊆ FootprintVertices q.2 :=
          AncestorRestrictionProof.chain_foot
  have main : ∀ (p q : CircleCoordinates × ProtoTile),
      Relation.ReflTransGen (fun X Y : CircleCoordinates × ProtoTile =>
        ∃ r : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
          ProperBandQuadruple r ∧ r 0 = Y.1 ∧ r i.succ = X.1 ∧
          BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
          FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
          TileCentroid X.2 - TileCentroid Y.2 =
            (if s = true then (1 : Real) else -1) •
              ((1 / 2 : Real) •
                (GaussianRealPoint
                    (BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))) -
                  (-((GaussianRealPoint
                      (BandVectors.1 (r ((i + 2).succ))
                        (r ((i + 1).succ)))).2),
                    (GaussianRealPoint
                      (BandVectors.1 (r ((i + 2).succ))
                        (r ((i + 1).succ)))).1)))) p q →
      ∀ (k g : PartialOdometer),
        (g.domain : Set GaussianInt) = FootprintVertices q.2 →
        (k.domain : Set GaussianInt) = FootprintVertices p.2 →
        k.domain ⊆ g.domain →
        (∀ x, x ∈ k.domain → k.value x = g.value x) →
        TileOdometer q.1 q.2 g → TileOdometer p.1 p.2 k := AncestorRestrictionProof.main
            restrict_domain one_step chain_foot
  exact main (C, T) (C₀, T₀) ha.2.1 h h₀
    (domain_from_odo C₀ T₀ h₀ ha.1) ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 ha.1

end ApollonianSuperharmonic

end
