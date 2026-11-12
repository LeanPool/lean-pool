/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: QuarterTurnSymmetricExactInterfaceTransport]

/-!
# QuarterTurnSymmetricExactInterfaceTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace QuarterInterfaceProof

private theorem hbaseE :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ((TileTranslation (TileQuarterTurn T) u).cells =
            T.cells) → (((TileQuarterTurn T).cells = Finset.image (fun (x : GaussianInt) =>
            GaussianQuarterTurn x - (1 : GaussianInt)) T.cells ∧ (TileQuarterTurn T).anchor =
            GaussianQuarterTurn T.anchor ∧ ((TileQuarterTurn T).cells = ∅ ↔ T.cells = ∅) ∧
            TileRealization (TileQuarterTurn T) = (fun (p : ℝ × ℝ) => (-p.2, p.1)) ''
            TileRealization T ∧ TileCentroid (TileQuarterTurn T) = (-(TileCentroid T).2,
            (TileCentroid T).1) ∧ FootprintVertices (TileQuarterTurn T) = GaussianQuarterTurn ''
            FootprintVertices T ∧ FootprintEdges (TileQuarterTurn T) = (fun (e : Finset
            GaussianInt) => Finset.image GaussianQuarterTurn e) '' FootprintEdges T ∧
            BoundaryFootprintVertices (TileQuarterTurn T) = GaussianQuarterTurn ''
            BoundaryFootprintVertices T ∧ BoundaryFootprintEdges (TileQuarterTurn T) = (fun (e :
            Finset GaussianInt) => Finset.image GaussianQuarterTurn e) '' BoundaryFootprintEdges
            T) → (((TileTranslation (TileQuarterTurn T) u).cells = Finset.image
            (GaussianTranslation u) (TileQuarterTurn T).cells ∧ (TileTranslation (TileQuarterTurn
            T) u).anchor = GaussianTranslation u (TileQuarterTurn T).anchor ∧ ((TileTranslation
            (TileQuarterTurn T) u).cells = ∅ ↔ (TileQuarterTurn T).cells = ∅) ∧ TileRealization
            (TileTranslation (TileQuarterTurn T) u) = (fun (p : ℝ × ℝ) => (p.1 + (↑u.re : ℝ), p.2
            + (↑u.im : ℝ))) '' TileRealization (TileQuarterTurn T) ∧ TileCentroid
            (TileTranslation (TileQuarterTurn T) u) = ((TileCentroid (TileQuarterTurn T)).1 +
            (↑u.re : ℝ), (TileCentroid (TileQuarterTurn T)).2 + (↑u.im : ℝ)) ∧ FootprintVertices
            (TileTranslation (TileQuarterTurn T) u) = GaussianTranslation u '' FootprintVertices
            (TileQuarterTurn T) ∧ FootprintEdges (TileTranslation (TileQuarterTurn T) u) = (fun
            (e : Finset GaussianInt) => Finset.image (GaussianTranslation u) e) '' FootprintEdges
            (TileQuarterTurn T) ∧ BoundaryFootprintVertices (TileTranslation (TileQuarterTurn T)
            u) = GaussianTranslation u '' BoundaryFootprintVertices (TileQuarterTurn T) ∧
            BoundaryFootprintEdges (TileTranslation (TileQuarterTurn T) u) = (fun (e : Finset
            GaussianInt) => Finset.image (GaussianTranslation u) e) '' BoundaryFootprintEdges
            (TileQuarterTurn T)) → ((fun e : Finset GaussianInt => e.image (GaussianTranslation
            u)) '' ((fun e : Finset GaussianInt => e.image GaussianQuarterTurn) '' FootprintEdges
            T) = FootprintEdges T)))
    ) := by
  classical
  intro T u hcell qt tu
  have hedge : FootprintEdges (TileTranslation (TileQuarterTurn T) u) =
      FootprintEdges T := by
    simp [FootprintEdges, hcell]
  have hedge' := hedge
  have hqedge : FootprintEdges (TileQuarterTurn T) =
      (fun e : Finset GaussianInt => e.image GaussianQuarterTurn) ''
        FootprintEdges T := qt.2.2.2.2.2.2.1
  rw [tu.2.2.2.2.2.2.1, hqedge] at hedge'
  exact hedge'

private theorem vertex_cov :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), (GaussianTranslation u '' (GaussianQuarterTurn ''
            FootprintVertices T) = FootprintVertices T) → (∀ (d : GaussianInt), FootprintVertices
            (TileTranslation T (GaussianQuarterTurn d)) = (fun (x : GaussianInt) =>
            GaussianQuarterTurn x + u) '' FootprintVertices (TileTranslation T d))
    ) := by
  classical
  intro T u hbaseV d
  have trq := TileTranslationFormulas T (GaussianQuarterTurn d)
  have trd := TileTranslationFormulas T d
  rw [trq.2.2.2.2.2.1, trd.2.2.2.2.2.1]
  calc
    GaussianTranslation (GaussianQuarterTurn d) '' FootprintVertices T =
        GaussianTranslation (GaussianQuarterTurn d) ''
          (GaussianTranslation u '' GaussianQuarterTurn '' FootprintVertices T) :=
      congrArg (fun s => GaussianTranslation (GaussianQuarterTurn d) '' s)
        hbaseV.symm
    _ = (fun x : GaussianInt => GaussianQuarterTurn x + u) ''
          (GaussianTranslation d '' FootprintVertices T) := by
      rw [Set.image_image, Set.image_image]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨GaussianTranslation d x, ⟨x, hx, rfl⟩, ?_⟩
        simp [GaussianTranslation, GaussianQuarterTurn, add_comm,
          add_left_comm]
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        simp [GaussianTranslation, GaussianQuarterTurn, add_comm,
          add_left_comm]

private theorem step_map :
    (by
      classical
      exact
        ∀ (u : GaussianInt), ∀ (r : GaussianInt), ∀ (s : GaussianInt), s = r + (1 : GaussianInt)
            ∨ s = r - (1 : GaussianInt) ∨ s = r + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ s = r - ⟨(0 : ℤ), (1 : ℤ)⟩
            → GaussianQuarterTurn s + u = GaussianQuarterTurn r + u + (1 : GaussianInt) ∨
            GaussianQuarterTurn s + u = GaussianQuarterTurn r + u - (1 : GaussianInt) ∨
            GaussianQuarterTurn s + u = GaussianQuarterTurn r + u + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨
            GaussianQuarterTurn s + u = GaussianQuarterTurn r + u - ⟨(0 : ℤ), (1 : ℤ)⟩
    ) := by
  classical
  intro u r s h
  rcases h with h | h | h | h
  · subst s
    right; right; left
    ext <;> simp [GaussianQuarterTurn, add_assoc, add_comm, add_left_comm]
  · subst s
    right; right; right
    ext <;> simp [GaussianQuarterTurn, add_comm]; omega
  · subst s
    right; left
    ext <;> simp [GaussianQuarterTurn, add_comm]; omega
  · subst s
    left
    ext <;> simp [GaussianQuarterTurn, add_comm, add_left_comm]; omega

private theorem path_map :
    (by
      classical
      exact
        ∀ (u : GaussianInt), (Function.Injective GaussianQuarterTurn) → ((Function.Injective (fun
            z : GaussianInt => GaussianQuarterTurn z + u)) → ((∀ (r : GaussianInt), ∀ (s :
            GaussianInt), (s = r + 1 ∨ s = r - 1 ∨ s = r + ⟨0, 1⟩ ∨ s = r - ⟨0, 1⟩) →
            (GaussianQuarterTurn s + u = GaussianQuarterTurn r + u + 1 ∨ GaussianQuarterTurn s +
            u = GaussianQuarterTurn r + u - 1 ∨ GaussianQuarterTurn s + u = GaussianQuarterTurn r
            + u + ⟨0, 1⟩ ∨ GaussianQuarterTurn s + u = GaussianQuarterTurn r + u - ⟨0, 1⟩)) → (∀
            (V : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (E' : Set (Finset
            GaussianInt)), ∀ (V' : Set GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), V'
            = (fun z : GaussianInt => GaussianQuarterTurn z + u) '' V → E' = (fun e : Finset
            GaussianInt => e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) '' E →
            SimpleGridPathBetween V E x y → SimpleGridPathBetween V' E' (GaussianQuarterTurn x +
            u) (GaussianQuarterTurn y + u))))
    ) := by
  classical
  intro u qinj finj step_map V E E' V' x y hV hE hp
  rcases hp with ⟨p, hnd, hlen, hhead, hlast, hpV, hstep, hpE⟩
  refine ⟨p.map (fun z => GaussianQuarterTurn z + u), hnd.map finj, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa using hlen
  · rw [List.head?_map, hhead]
    rfl
  · rw [List.getLast?_map, hlast]
    rfl
  · rw [hV, hpV]
    ext z
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset,
      List.mem_map]
  · intro r s l₁ l₂ hm
    have mappedStep : ∀ (p : List GaussianInt),
        (∀ r s l₁ l₂, p = l₁ ++ r :: s :: l₂ →
          s = r + 1 ∨ s = r - 1 ∨ s = r + ⟨0, 1⟩ ∨ s = r - ⟨0, 1⟩) →
        ∀ r s l₁ l₂, p.map (fun z => GaussianQuarterTurn z + u) =
          l₁ ++ r :: s :: l₂ →
          s = r + 1 ∨ s = r - 1 ∨ s = r + ⟨0, 1⟩ ∨ s = r - ⟨0, 1⟩ := by
      intro q
      induction q with
      | nil =>
        intro hh r s k m hm
        cases k with
        | nil => simp at hm
        | cons z zs => simp at hm
      | cons z q ih =>
        intro hh r s k m hm
        cases q with
        | nil => cases k <;> cases m <;> simp_all
        | cons w q =>
          cases k with
          | nil =>
            injection hm with hzr hrest
            subst r
            injection hrest with hws htail
            subst s
            exact step_map z w (hh z w [] q (by simp))
          | cons k ks =>
            simp only [List.map_cons, List.cons_append] at hm
            have hz : k = GaussianQuarterTurn z + u := by
              simpa using (congrArg List.head? hm).symm
            subst k
            apply ih
            focus intro c d k m hkm
            focus apply hh c d (z :: k) m
            focus simp [hkm]
            simpa using hm
    exact mappedStep p hstep r s l₁ l₂ hm
  · intro e
    constructor
    · rw [hE]
      rintro ⟨f, hf, rfl⟩
      rcases (hpE f).mp hf with ⟨r, s, l₁, l₂, hm, he⟩
      refine ⟨GaussianQuarterTurn r + u, GaussianQuarterTurn s + u,
        l₁.map (fun z => GaussianQuarterTurn z + u),
        l₂.map (fun z => GaussianQuarterTurn z + u), by simp [hm], ?_⟩
      simp [he, Finset.image_insert]
    · intro he
      rcases he with ⟨r, s, l₁, l₂, hm, he⟩
      have hr : r ∈ p.map (fun z => GaussianQuarterTurn z + u) := by
        rw [hm]
        simp
      have hs : s ∈ p.map (fun z => GaussianQuarterTurn z + u) := by
        rw [hm]
        simp
      rcases List.mem_map.mp hr with ⟨c, hc, hcr⟩
      rcases List.mem_map.mp hs with ⟨d, hd, hds⟩
      have unmap : ∀ (q : List GaussianInt) (k m : List GaussianInt),
          q.map (fun z => GaussianQuarterTurn z + u) =
            k ++ (GaussianQuarterTurn c + u) ::
              (GaussianQuarterTurn d + u) :: m →
          ∃ k₀ m₀, q = k₀ ++ c :: d :: m₀ := by
        intro q
        induction q with
        | nil => intro k m h; cases k with | nil => cases h | cons z zs => cases h
        | cons z q ih =>
          intro k m h
          cases k with
          | nil =>
            simp only [List.map_cons, List.nil_append, List.cons.injEq, add_left_inj] at h
            rcases h with ⟨hz, hrest⟩
            have hz' : z = c := qinj hz
            subst z
            cases q with
            | nil => simp_all
            | cons w q =>
              simp only [List.map_cons, List.cons.injEq, add_left_inj] at hrest
              have hw' : w = d := qinj hrest.1
              subst w
              exact ⟨[], q, by simp []⟩
          | cons k ks =>
            simp only [List.map_cons, List.cons_append] at h
            have hz : k = GaussianQuarterTurn z + u := by
              simpa using (congrArg List.head? h).symm
            subst k
            have htail : List.map (fun z => GaussianQuarterTurn z + u) q =
                ks ++ (GaussianQuarterTurn c + u) ::
                  (GaussianQuarterTurn d + u) :: m := by
              exact List.cons.inj h |>.2
            rcases ih ks m htail with ⟨k₀, m₀, hq⟩
            exact ⟨z :: k₀, m₀, by simp [hq]⟩
      rw [← hcr, ← hds] at hm
      have hcd := unmap p l₁ l₂ hm
      rcases hcd with ⟨k, m, hpm⟩
      subst r
      subst s
      rw [hE]
      refine ⟨({c, d} : Finset GaussianInt),
        (hpE {c, d}).mpr ⟨c, d, k, m, hpm, rfl⟩, ?_⟩
      rw [he]
      simp [Finset.image_insert]

private theorem edge_cov :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ((fun e : Finset GaussianInt => e.image
            (GaussianTranslation u)) '' ((fun e : Finset GaussianInt => e.image
            GaussianQuarterTurn) '' FootprintEdges T) = FootprintEdges T) → (∀ (d : GaussianInt),
            FootprintEdges (TileTranslation T (GaussianQuarterTurn d)) = (fun (e : Finset
            GaussianInt) => Finset.image (fun (z : GaussianInt) => GaussianQuarterTurn z + u) e)
            '' FootprintEdges (TileTranslation T d))
    ) := by
  classical
  intro T u hbaseE d
  have trq := TileTranslationFormulas T (GaussianQuarterTurn d)
  have trd := TileTranslationFormulas T d
  rw [trq.2.2.2.2.2.2.1, trd.2.2.2.2.2.2.1]
  have hfin (e : Finset GaussianInt) :
      ((e.image GaussianQuarterTurn).image (GaussianTranslation u)).image
          (GaussianTranslation (GaussianQuarterTurn d)) =
        (e.image (GaussianTranslation d)).image
          (fun z : GaussianInt => GaussianQuarterTurn z + u) := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨y, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      exact ⟨GaussianTranslation d w, ⟨w, hw, rfl⟩, by simp [GaussianTranslation,
          GaussianQuarterTurn,
        add_comm, add_left_comm]⟩
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨GaussianTranslation u (GaussianQuarterTurn y),
        ⟨GaussianQuarterTurn y, ⟨y, hy, rfl⟩, rfl⟩, by
        simp [GaussianTranslation, GaussianQuarterTurn,
          add_comm, add_left_comm]⟩
  calc
    (fun e : Finset GaussianInt => e.image (GaussianTranslation (GaussianQuarterTurn d))) ''
        FootprintEdges T =
        (fun e : Finset GaussianInt => e.image (GaussianTranslation (GaussianQuarterTurn d))) ''
          ((fun e : Finset GaussianInt => e.image (GaussianTranslation u)) ''
            ((fun e : Finset GaussianInt => e.image GaussianQuarterTurn) '' FootprintEdges T)) :=
      congrArg (fun s => (fun e : Finset GaussianInt =>
        e.image (GaussianTranslation (GaussianQuarterTurn d))) '' s) hbaseE.symm
    _ = (fun e : Finset GaussianInt => e.image (fun z => GaussianQuarterTurn z + u)) ''
        ((fun e : Finset GaussianInt => e.image (GaussianTranslation d)) '' FootprintEdges T) := by
      rw [Set.image_image, Set.image_image]
      have hf : (fun e : Finset GaussianInt =>
          ((e.image GaussianQuarterTurn).image (GaussianTranslation u)).image
            (GaussianTranslation (GaussianQuarterTurn d))) =
          (fun e : Finset GaussianInt =>
            e.image (fun z => GaussianQuarterTurn z + u)) ∘
            (fun e : Finset GaussianInt => e.image (GaussianTranslation d)) := by
        funext e
        exact hfin e
      rw [hf]
      simp only [Function.comp_apply, Set.image_image]

private theorem edge_zero :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ((fun (x : Finset GaussianInt) => Finset.image
            (GaussianTranslation u) (Finset.image GaussianQuarterTurn x)) '' FootprintEdges T =
            FootprintEdges T) → (FootprintEdges T = (fun e : Finset GaussianInt => e.image (fun z
            : GaussianInt => GaussianQuarterTurn z + u)) '' FootprintEdges T)
    ) := by
  classical
  intro T u hbaseE'
  have hf : (fun e : Finset GaussianInt =>
      (e.image GaussianQuarterTurn).image (GaussianTranslation u)) =
      (fun e : Finset GaussianInt =>
        e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) := by
    funext e
    apply Finset.ext
    intro z
    simp only [Finset.mem_image]
    simp [GaussianQuarterTurn, GaussianTranslation,
      add_comm]
  calc
    FootprintEdges T =
        (fun e : Finset GaussianInt =>
          (e.image GaussianQuarterTurn).image (GaussianTranslation u)) ''
          FootprintEdges T := hbaseE'.symm
    _ = _ := by rw [hf]

private theorem ebc :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (u : GaussianInt),
            (Function.Injective (fun z : GaussianInt => GaussianQuarterTurn z + u)) → ((∀
            {α : Type}, ∀ {β : Type}, ∀ (f : α → β), Function.Injective f → ∀ (A : Set α), ∀ (B :
            Set α), ∀ (A' : Set β), ∀ (B' : Set β), A' = f '' A → B' = f '' B → A' ∩ B' = f '' (A
            ∩ B)) → ((FootprintEdges (TileTranslation T (GaussianQuarterTurn a)) = (fun (e :
            Finset GaussianInt) => Finset.image (fun (z : GaussianInt) => GaussianQuarterTurn z +
            u) e) '' FootprintEdges (TileTranslation T a)) → ((FootprintEdges (TileTranslation T
            (GaussianQuarterTurn b)) = (fun (e : Finset GaussianInt) => Finset.image (fun (z :
            GaussianInt) => GaussianQuarterTurn z + u) e) '' FootprintEdges (TileTranslation T
            b)) → (FootprintEdges (TileTranslation T (GaussianQuarterTurn a)) ∩ FootprintEdges
            (TileTranslation T (GaussianQuarterTurn b)) = (fun e : Finset GaussianInt => e.image
            (fun z : GaussianInt => GaussianQuarterTurn z + u)) '' (FootprintEdges
            (TileTranslation T a) ∩ FootprintEdges (TileTranslation T b))))))
    ) := by
  classical
  intro T a b u finj intersection_map ea eb
  have ffinj : Function.Injective (fun e : Finset GaussianInt =>
      e.image (fun z => GaussianQuarterTurn z + u)) := Finset.image_injective finj
  exact intersection_map (fun e : Finset GaussianInt =>
    e.image (fun z => GaussianQuarterTurn z + u)) ffinj _ _ _ _ ea eb

private theorem unique_target :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (data :
            ExactTileInterfaceTriple T (TileTranslation T a) (TileTranslation T b)), ∀ (u :
            GaussianInt), (FootprintVertices T ∩ FootprintVertices (TileTranslation T
            (GaussianQuarterTurn a)) ∩ FootprintVertices (TileTranslation T (GaussianQuarterTurn
            b)) = (fun z : GaussianInt => GaussianQuarterTurn z + u) '' (FootprintVertices T ∩
            FootprintVertices (TileTranslation T a) ∩ FootprintVertices (TileTranslation T b))) →
            (∀ y, y ∈ FootprintVertices T ∩ FootprintVertices (TileTranslation T
            (GaussianQuarterTurn a)) ∩ FootprintVertices (TileTranslation T (GaussianQuarterTurn
            b)) ↔ y = GaussianQuarterTurn data.point + u)
    ) := by
  classical
  intro T a b data u vtriple y
  rw [vtriple]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hp := (data.unique_common z).mp hz
    simp [hp]
  · intro hy
    subst y
    exact ⟨data.point, (data.unique_common data.point).mpr rfl, rfl⟩

end QuarterInterfaceProof

theorem QuarterTurnSymmetricExactInterfaceTransport
    (T : ProtoTile) (a b : GaussianInt)
    (data : ExactTileInterfaceTriple T (TileTranslation T a)
      (TileTranslation T b))
    (hsym : QuarterTurnSymmetric T) :
    ∃ u : GaussianInt,
      GaussianRealPoint u =
        ((TileCentroid T).1 + (TileCentroid T).2,
          (TileCentroid T).2 - (TileCentroid T).1) ∧
      ∃ transported : ExactTileInterfaceTriple T
          (TileTranslation T (GaussianQuarterTurn a))
          (TileTranslation T (GaussianQuarterTurn b)),
        transported.point = GaussianQuarterTurn data.point + u ∧
        transported.otherAB = GaussianQuarterTurn data.otherAB + u ∧
        transported.otherBC = GaussianQuarterTurn data.otherBC + u ∧
        transported.otherCA = GaussianQuarterTurn data.otherCA + u := by
-- BODY
  obtain ⟨u, hu, hcell, hanchor, hvert, hcent⟩ :=
    QuarterTurnSymmetricCenteredTransport T hsym
  have qt := TileQuarterTurnFormulas T
  have tu := TileTranslationFormulas (TileQuarterTurn T) u
  have qinj : Function.Injective GaussianQuarterTurn := by
    intro x y h
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) h
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) h
  have tinj : Function.Injective (GaussianTranslation u) := by
    intro x y h
    dsimp [GaussianTranslation] at h
    exact add_right_cancel h
  have finj : Function.Injective (fun z : GaussianInt => GaussianQuarterTurn z + u) := by
    intro x y h
    apply qinj
    dsimp [GaussianTranslation] at h
    exact add_right_cancel h
  have hbaseV : GaussianTranslation u '' (GaussianQuarterTurn ''
      FootprintVertices T) = FootprintVertices T := by
    calc
      GaussianTranslation u '' (GaussianQuarterTurn '' FootprintVertices T) =
          FootprintVertices (TileTranslation (TileQuarterTurn T) u) :=
        by rw [← qt.2.2.2.2.2.1]; exact (tu.2.2.2.2.2.1).symm
      _ = _ := hvert
  have hbaseE : (fun e : Finset GaussianInt =>
      e.image (GaussianTranslation u)) ''
      ((fun e : Finset GaussianInt => e.image GaussianQuarterTurn) ''
        FootprintEdges T) = FootprintEdges T := QuarterInterfaceProof.hbaseE T u hcell qt tu
  have hbaseV' := hbaseV
  rw [Set.image_image] at hbaseV'
  have hbaseE' := hbaseE
  rw [Set.image_image] at hbaseE'
  have point_map (d x : GaussianInt) :
      GaussianQuarterTurn (GaussianTranslation d x) + u =
        GaussianTranslation (GaussianQuarterTurn d)
          (GaussianQuarterTurn x + u) := by
    simp [GaussianTranslation, GaussianQuarterTurn, add_comm,
      add_left_comm]
  have vertex_cov (d : GaussianInt) :
      FootprintVertices (TileTranslation T (GaussianQuarterTurn d)) =
        (fun x : GaussianInt => GaussianQuarterTurn x + u) ''
          FootprintVertices (TileTranslation T d) := QuarterInterfaceProof.vertex_cov T u hbaseV d
  have step_map (r s : GaussianInt)
      (h : s = r + 1 ∨ s = r - 1 ∨ s = r + ⟨0, 1⟩ ∨
        s = r - ⟨0, 1⟩) :
      GaussianQuarterTurn s + u = GaussianQuarterTurn r + u + 1 ∨
      GaussianQuarterTurn s + u = GaussianQuarterTurn r + u - 1 ∨
      GaussianQuarterTurn s + u = GaussianQuarterTurn r + u + ⟨0, 1⟩ ∨
      GaussianQuarterTurn s + u = GaussianQuarterTurn r + u - ⟨0, 1⟩ :=
          QuarterInterfaceProof.step_map u r s h
  have path_map : ∀ (V : Set GaussianInt) (E E' : Set (Finset GaussianInt))
      (V' : Set GaussianInt) (x y : GaussianInt),
      V' = (fun z : GaussianInt => GaussianQuarterTurn z + u) '' V →
      E' = (fun e : Finset GaussianInt =>
        e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) '' E →
      SimpleGridPathBetween V E x y →
      SimpleGridPathBetween V' E' (GaussianQuarterTurn x + u)
        (GaussianQuarterTurn y + u) := QuarterInterfaceProof.path_map u qinj finj step_map
  have edge_cov (d : GaussianInt) :
      FootprintEdges (TileTranslation T (GaussianQuarterTurn d)) =
        (fun e : Finset GaussianInt =>
          e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) ''
          FootprintEdges (TileTranslation T d) := QuarterInterfaceProof.edge_cov T u hbaseE d
  have vertex_zero : FootprintVertices T =
      (fun x : GaussianInt => GaussianQuarterTurn x + u) ''
        FootprintVertices T := by
    simpa [GaussianQuarterTurn, GaussianTranslation] using hbaseV'.symm
  have edge_zero : FootprintEdges T =
      (fun e : Finset GaussianInt =>
        e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) ''
        FootprintEdges T := QuarterInterfaceProof.edge_zero T u hbaseE'
  have intersection_map : ∀ {α β : Type} (f : α → β), Function.Injective f →
      ∀ (A B : Set α) (A' B' : Set β),
      A' = f '' A → B' = f '' B →
      A' ∩ B' = f '' (A ∩ B) := by
    intro α β f hf A B A' B' hA hB
    rw [hA, hB]
    exact (Set.image_inter hf).symm
  have v0 := vertex_zero
  have va := vertex_cov a
  have vb := vertex_cov b
  have e0 := edge_zero
  have ea := edge_cov a
  have eb := edge_cov b
  have vab :
      FootprintVertices T ∩ FootprintVertices (TileTranslation T (GaussianQuarterTurn a)) =
        (fun z : GaussianInt => GaussianQuarterTurn z + u) ''
          (FootprintVertices T ∩ FootprintVertices (TileTranslation T a)) := by
    exact intersection_map (fun z : GaussianInt => GaussianQuarterTurn z + u) finj _ _ _ _ v0 va
  have vbc :
      FootprintVertices (TileTranslation T (GaussianQuarterTurn a)) ∩
          FootprintVertices (TileTranslation T (GaussianQuarterTurn b)) =
        (fun z : GaussianInt => GaussianQuarterTurn z + u) ''
          (FootprintVertices (TileTranslation T a) ∩
            FootprintVertices (TileTranslation T b)) := by
    exact intersection_map (fun z : GaussianInt => GaussianQuarterTurn z + u) finj _ _ _ _ va vb
  have vca :
      FootprintVertices (TileTranslation T (GaussianQuarterTurn b)) ∩ FootprintVertices T =
        (fun z : GaussianInt => GaussianQuarterTurn z + u) ''
          (FootprintVertices (TileTranslation T b) ∩ FootprintVertices T) := by
    exact intersection_map (fun z : GaussianInt => GaussianQuarterTurn z + u) finj _ _ _ _ vb v0
  have eab :
      FootprintEdges T ∩ FootprintEdges (TileTranslation T (GaussianQuarterTurn a)) =
      (fun e : Finset GaussianInt =>
          e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) ''
          (FootprintEdges T ∩ FootprintEdges (TileTranslation T a)) := by
    have ffinj : Function.Injective (fun e : Finset GaussianInt =>
        e.image (fun z => GaussianQuarterTurn z + u)) := Finset.image_injective finj
    exact intersection_map (fun e : Finset GaussianInt =>
      e.image (fun z => GaussianQuarterTurn z + u)) ffinj _ _ _ _ e0 ea
  have ebc :
      FootprintEdges (TileTranslation T (GaussianQuarterTurn a)) ∩
          FootprintEdges (TileTranslation T (GaussianQuarterTurn b)) =
        (fun e : Finset GaussianInt =>
          e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) ''
          (FootprintEdges (TileTranslation T a) ∩ FootprintEdges (TileTranslation T b)) :=
              QuarterInterfaceProof.ebc T a b u finj intersection_map ea eb
  have eca :
      FootprintEdges (TileTranslation T (GaussianQuarterTurn b)) ∩ FootprintEdges T =
        (fun e : Finset GaussianInt =>
          e.image (fun z : GaussianInt => GaussianQuarterTurn z + u)) ''
          (FootprintEdges (TileTranslation T b) ∩ FootprintEdges T) := by
    have ffinj : Function.Injective (fun e : Finset GaussianInt =>
        e.image (fun z => GaussianQuarterTurn z + u)) := Finset.image_injective finj
    exact intersection_map (fun e : Finset GaussianInt =>
      e.image (fun z => GaussianQuarterTurn z + u)) ffinj _ _ _ _ eb e0
  have pAB := path_map _ _ _ _ _ _ vab eab data.pathAB
  have pBC := path_map _ _ _ _ _ _ vbc ebc data.pathBC
  have pCA := path_map _ _ _ _ _ _ vca eca data.pathCA
  have vtriple :
      FootprintVertices T ∩ FootprintVertices (TileTranslation T (GaussianQuarterTurn a)) ∩
          FootprintVertices (TileTranslation T (GaussianQuarterTurn b)) =
        (fun z : GaussianInt => GaussianQuarterTurn z + u) ''
          (FootprintVertices T ∩ FootprintVertices (TileTranslation T a) ∩
            FootprintVertices (TileTranslation T b)) := by
    exact intersection_map (fun z : GaussianInt => GaussianQuarterTurn z + u) finj _ _ _ _ vab vb
  have unique_target : ∀ y,
      y ∈ FootprintVertices T ∩
          FootprintVertices (TileTranslation T (GaussianQuarterTurn a)) ∩
            FootprintVertices (TileTranslation T (GaussianQuarterTurn b)) ↔
        y = GaussianQuarterTurn data.point + u := QuarterInterfaceProof.unique_target T a b data
            u vtriple
  refine ⟨u, hu, ⟨GaussianQuarterTurn data.point + u,
    GaussianQuarterTurn data.otherAB + u,
    GaussianQuarterTurn data.otherBC + u,
    GaussianQuarterTurn data.otherCA + u, pAB, pBC, pCA, ?_⟩, rfl, rfl, rfl, rfl⟩
  exact unique_target

end ApollonianSuperharmonic

end
