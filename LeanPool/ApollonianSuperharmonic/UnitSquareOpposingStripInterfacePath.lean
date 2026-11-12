/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineOpposingStripCorridor
public import LeanPool.ApollonianSuperharmonic.AffineTriangularCorridorStep
public import LeanPool.ApollonianSuperharmonic.AffineTriangularFaceVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TriangularStripSegment
public import Mathlib.Data.List.Chain

-- [TABLET NODE: UnitSquareOpposingStripInterfacePath]

/-!
# UnitSquareOpposingStripInterfacePath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem UnitSquareOpposingStripInterfacePath
    (anchor : GaussianInt) (r s : Int × Int) (hrs : r ≠ s)
    (hnadj : ¬ TriangularLatticeAdjacent r s)
    (forward reverse : List (Int × Int))
    (hforward : TriangularStripSegment r s forward)
    (hreverse : TriangularStripSegment s r reverse) :
    let base : ProtoTile := ⟨{anchor}, anchor⟩
    let tileAt := fun z : Int × Int =>
      TileTranslation base (⟨z.1, z.2⟩ : GaussianInt)
    ∃ p : List GaussianInt,
      (∃ x, p.head? = some x ∧ x ∈ FootprintVertices (tileAt r)) ∧
      (∃ y, p.getLast? = some y ∧ y ∈ FootprintVertices (tileAt s)) ∧
      p.IsChain (fun x y =>
        y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) ∧
      (∀ x, x ∈ p →
        (∃ a ∈ (forward.drop 1).dropLast,
          x ∈ FootprintVertices (tileAt a)) ∧
        (∃ b ∈ (reverse.drop 1).dropLast,
          x ∈ FootprintVertices (tileAt b))) ∧
      ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ x :: y :: l₂ →
          (∃ a ∈ (forward.drop 1).dropLast,
            {x, y} ∈ FootprintEdges (tileAt a)) ∧
          (∃ b ∈ (reverse.drop 1).dropLast,
            {x, y} ∈ FootprintEdges (tileAt b)) := by
-- BODY
  dsimp only
  let tileAt := fun z : Int × Int =>
    TileTranslation (⟨{anchor}, anchor⟩ : ProtoTile)
      (⟨z.1, z.2⟩ : GaussianInt)
  let rho : AffineTriangularFace → GaussianInt := fun f => match f with
    | .up z => anchor + (⟨z.1, z.2⟩ : GaussianInt) + 1
    | .down z => anchor + (⟨z.1, z.2⟩ : GaussianInt) + ⟨0, 1⟩
  let step := fun x y : GaussianInt =>
    y = x + 1 ∨ y = x - 1 ∨
      y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  have corner (f : AffineTriangularFace) (z : Int × Int)
      (hz : z ∈ AffineTriangularFaceVertices f) :
      rho f ∈ FootprintVertices (tileAt z) := by
    cases f with
    | up w =>
      simp only [AffineTriangularFaceVertices, Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;>
        simp only [tileAt, rho, TileTranslation, Finset.image_singleton,
          GaussianTranslation]
      all_goals
        simp only [FootprintVertices, Finset.singleton_nonempty, ite_eq_left,
          Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left]
        simp [Zsqrtd.ext_iff, add_assoc]
    | down w =>
      simp only [AffineTriangularFaceVertices, Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;>
        simp only [tileAt, rho, TileTranslation, Finset.image_singleton,
          GaussianTranslation]
      all_goals
        simp only [FootprintVertices, Finset.singleton_nonempty, ite_eq_left,
          Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left]
        simp [Zsqrtd.ext_iff, add_assoc]
  have bounds (z : Int × Int) (w : GaussianInt)
      (hw : w ∈ FootprintVertices (tileAt z)) :
      anchor.re + z.1 ≤ w.re ∧ w.re ≤ anchor.re + z.1 + 1 ∧
      anchor.im + z.2 ≤ w.im ∧ w.im ≤ anchor.im + z.2 + 1 := by
    simp only [tileAt, TileTranslation, Finset.image_singleton, GaussianTranslation,
      FootprintVertices, Finset.singleton_nonempty, ite_eq_left,
      Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left] at hw
    simp [Zsqrtd.ext_iff] at hw
    omega
  have common_corners (u v : Int × Int) (huv : u ≠ v) (x y : GaussianInt)
      (hxu : x ∈ FootprintVertices (tileAt u))
      (hyu : y ∈ FootprintVertices (tileAt u))
      (hxv : x ∈ FootprintVertices (tileAt v))
      (hyv : y ∈ FootprintVertices (tileAt v)) : x = y ∨ step x y := by
    have h1 := bounds u x hxu
    have h2 := bounds u y hyu
    have h3 := bounds v x hxv
    have h4 := bounds v y hyv
    have hne : ¬ (u.1 = v.1 ∧ u.2 = v.2) := fun h => huv (Prod.ext h.1 h.2)
    clear hxu hyu hxv hyv
    simp [step, Zsqrtd.ext_iff]
    omega
  have square_edge (k x y : GaussianInt)
      (hx : x ∈ FootprintVertices (⟨{k}, k⟩ : ProtoTile))
      (hy : y ∈ FootprintVertices (⟨{k}, k⟩ : ProtoTile))
      (hstep : step x y) :
      {x, y} ∈ FootprintEdges (⟨{k}, k⟩ : ProtoTile) := by
    simp only [FootprintVertices, Finset.singleton_nonempty, ite_eq_left,
      Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl
    all_goals simp only [step, Zsqrtd.ext_iff, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one] at hstep
    all_goals first | omega | simp [FootprintEdges, Finset.pair_comm, add_assoc]
  have edge (z : Int × Int) (x y : GaussianInt)
      (hx : x ∈ FootprintVertices (tileAt z))
      (hy : y ∈ FootprintVertices (tileAt z)) (hstep : step x y) :
      {x, y} ∈ FootprintEdges (tileAt z) := by
    simp only [tileAt, TileTranslation, Finset.image_singleton,
      GaussianTranslation] at hx hy ⊢
    exact square_edge _ x y hx hy hstep
  let witnessed := fun x y : GaussianInt => step x y ∧
    (∃ a ∈ (forward.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt a)) ∧
    (∃ b ∈ (reverse.drop 1).dropLast, {x, y} ∈ FootprintEdges (tileAt b))
  have corridor_step (f g : AffineTriangularFace)
      (hfg : AffineTriangularCorridorStep forward reverse f g) :
      rho f = rho g ∨ witnessed (rho f) (rho g) := by
    obtain ⟨_, u, v, huv, _, huf, hvf, hug, hvg, howners⟩ := hfg
    have hxu := corner f u huf
    have hyu := corner g u hug
    have hxv := corner f v hvf
    have hyv := corner g v hvg
    rcases common_corners u v huv (rho f) (rho g) hxu hyu hxv hyv with heq | hstep
    · exact Or.inl heq
    · right
      refine ⟨hstep, ?_⟩
      rcases howners with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨⟨u, ha, edge u _ _ hxu hyu hstep⟩,
          ⟨v, hb, edge v _ _ hxv hyv hstep⟩⟩
      · exact ⟨⟨u, ha, edge u _ _ hxu hyu hstep⟩,
          ⟨u, hb, edge u _ _ hxu hyu hstep⟩⟩
  -- Compress equal corners without forgetting the final changing step's witnesses.
  have compress (l : List GaussianInt)
      (hl : l.IsChain (fun x y => x = y ∨ witnessed x y)) :
      ∃ p : List GaussianInt, p.head? = l.head? ∧ p.getLast? = l.getLast? ∧
        (∀ x ∈ p, x ∈ l) ∧ p.IsChain witnessed := by
    induction l with
    | nil => exact ⟨[], rfl, rfl, by simp, .nil⟩
    | cons x l ih =>
      cases l with
      | nil => exact ⟨[x], rfl, rfl, by simp, .singleton _⟩
      | cons y l =>
        have h := List.isChain_cons_cons.mp hl
        obtain ⟨p, hphead, hplast, hpmem, hpchain⟩ := ih h.2
        cases p with
        | nil => simp at hphead
        | cons z p =>
          have hzy : z = y := by simpa using hphead
          subst z
          rcases h.1 with hxy | hxy
          · subst x
            refine ⟨y :: p, rfl, ?_, ?_, hpchain⟩
            · simpa using hplast
            · intro a ha
              exact List.mem_cons_of_mem _ (hpmem a ha)
          · refine ⟨x :: y :: p, rfl, ?_, ?_, ?_⟩
            · simpa using hplast
            · intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (hpmem a ha)
            · exact List.isChain_cons_cons.mpr ⟨hxy, hpchain⟩
  obtain ⟨faces, _, hfirst, hlast, hvertices, hchain⟩ :=
    AffineOpposingStripCorridor r s hrs hnadj forward reverse hforward hreverse
  have hraw : (faces.map rho).IsChain (fun x y => x = y ∨ witnessed x y) :=
    (List.isChain_map rho).mpr (hchain.imp fun _ _ h => corridor_step _ _ h)
  obtain ⟨p, hphead, hplast, hpmem, hpchain⟩ := compress (faces.map rho) hraw
  refine ⟨p, ?_, ?_, hpchain.imp (fun _ _ h => h.1), ?_, ?_⟩
  · obtain ⟨f, hf, hfr⟩ := hfirst
    refine ⟨rho f, ?_, corner f r hfr⟩
    rw [hphead, List.head?_map, hf]
    rfl
  · obtain ⟨f, hf, hfs⟩ := hlast
    refine ⟨rho f, ?_, corner f s hfs⟩
    rw [hplast, List.getLast?_map, hf]
    rfl
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (hpmem x hx)
    obtain ⟨⟨a, ha, haf⟩, ⟨b, hb, hbf⟩⟩ := hvertices f hf
    exact ⟨⟨a, ha, corner f a haf⟩, ⟨b, hb, corner f b hbf⟩⟩
  · intro x y l₁ l₂ hp
    exact (List.isChain_iff_forall_rel_of_append_cons_cons.mp hpchain hp).2

end ApollonianSuperharmonic

end
