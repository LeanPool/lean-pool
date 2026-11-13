/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordTileCellMembership
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.FordParentVectors

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleSwapLast
public import LeanPool.ApollonianSuperharmonic.P5269T1FordSquareNormalForm
public import LeanPool.ApollonianSuperharmonic.P5269T1CenteredSquareTripleTransport

-- [TABLET NODE: FordOrientedChildParentEndpoints]

/-!
# FordOrientedChildParentEndpoints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordEndpointProof

private theorem obs :
    (by
      classical
      exact
        let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
          {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = { x, y }}
        ∀ (T : ProtoTile),
          ∀ (a : Int),
            ∀ (b : Int),
              ∀ (n : Int),
                0 < n →
                  (∀ z : GaussianInt,
                      z ∈ T.cells ↔ a ≤ z.re ∧ z.re < a + n ∧ b ≤ z.im ∧ z.im < b + n) →
                    FootprintVertices T = rect a b n ∧
                      FootprintEdges T = edges (rect a b n)
    ) := by
  classical
  intro rect adj edges T a b n hn hc
  have hne : T.cells.Nonempty := ⟨⟨a,b⟩, (hc _).mpr (by dsimp; omega)⟩
  have hv (z : GaussianInt) : z ∈ FootprintVertices T ↔ z ∈ rect a b n := by
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, hz⟩
      have hx := (hc x).mp hx
      rcases hz with rfl | rfl | rfl | rfl <;>
        dsimp [rect] <;> omega
    · intro hz
      change a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n at hz
      let x : GaussianInt := ⟨min z.re (a+n-1), min z.im (b+n-1)⟩
      refine ⟨x, (hc x).mpr ?_, ?_⟩
      · dsimp [x]; omega
      · simp only [Zsqrtd.ext_iff, Zsqrtd.re_add, Zsqrtd.im_add,
          Zsqrtd.re_one, Zsqrtd.im_one]
        dsimp [x]
        omega
  refine ⟨Set.ext hv, ?_⟩
  have he (z : GaussianInt) (hz : z ∈ rect a b n)
      (hw : z + 1 ∈ rect a b n) : {z, z+1} ∈ FootprintEdges T := by
    change a ≤ z.re ∧ z.re ≤ a+n ∧ b ≤ z.im ∧ z.im ≤ b+n at hz
    change a ≤ (z+1).re ∧ (z+1).re ≤ a+n ∧
      b ≤ (z+1).im ∧ (z+1).im ≤ b+n at hw
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one] at hw
    by_cases ht : z.im < b+n
    · exact ⟨z, (hc z).mpr (by omega), Or.inl rfl⟩
    · refine ⟨z-⟨0,1⟩, (hc _).mpr ?_, Or.inr (Or.inr (Or.inr ?_))⟩
      · simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]; omega
      · congr 1 <;> abel
  have ve (z : GaussianInt) (hz : z ∈ rect a b n)
      (hw : z + ⟨0,1⟩ ∈ rect a b n) :
      {z, z+⟨0,1⟩} ∈ FootprintEdges T := by
    change a ≤ z.re ∧ z.re ≤ a+n ∧ b ≤ z.im ∧ z.im ≤ b+n at hz
    change a ≤ (z+⟨0,1⟩).re ∧ (z+⟨0,1⟩).re ≤ a+n ∧
      b ≤ (z+⟨0,1⟩).im ∧ (z+⟨0,1⟩).im ≤ b+n at hw
    simp only [Zsqrtd.re_add, Zsqrtd.im_add] at hw
    by_cases ht : z.re < a+n
    · exact ⟨z, (hc z).mpr (by omega), Or.inr (Or.inl rfl)⟩
    · refine ⟨z-1, (hc _).mpr ?_, Or.inr (Or.inr (Or.inl ?_))⟩
      · simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]; omega
      · congr 1 <;> abel
  ext e
  constructor
  · rintro ⟨z, hz, heq⟩
    have hz' := (hc z).mp hz
    rcases heq with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨_, ?_, _, ?_, ?_, rfl⟩
      · dsimp [rect]; omega
      · dsimp [rect]; omega
      · simp [adj, add_assoc, add_comm, add_left_comm]
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    rcases hxy with rfl | rfl | rfl | rfl
    · exact he x hx hy
    · have h := he (x-1) hy (by simpa using hx)
      simpa [Finset.pair_comm] using h
    · exact ve x hx hy
    · have h := ve (x-⟨0,1⟩) hy (by simpa using hx)
      simpa [Finset.pair_comm] using h

private theorem edge_inter :
    (by
      classical
      exact
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = {x, y}}
        ∀ (V : Set GaussianInt), ∀ (W : Set GaussianInt), edges V ∩ edges W = edges (V ∩ W) ) := by
  classical
  intro adj edges V W
  ext e
  constructor
  · rintro ⟨⟨x,hx,y,hy,hxy,rfl⟩, ⟨u,hu,v,hv,huv,he⟩⟩
    have hall : ∀ z ∈ ({x,y} : Finset GaussianInt), z ∈ W := by
      intro z hz
      rw [he] at hz
      have hz' : z = u ∨ z = v := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
      rcases hz' with rfl | rfl
      · exact hu
      · exact hv
    exact ⟨x,⟨hx,hall x (by simp)⟩,y,⟨hy,hall y (by simp)⟩,hxy,rfl⟩
  · rintro ⟨x,hx,y,hy,hxy,rfl⟩
    exact ⟨⟨x,hx.1,y,hy.1,hxy,rfl⟩, ⟨x,hx.2,y,hy.2,hxy,rfl⟩⟩

private theorem linepath :
    (by
      classical
      exact
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = { x, y }}
        ∀ (f : Nat → GaussianInt),
          ∀ (n : Nat),
            0 < n →
              Function.Injective f →
                (∀ k, adj (f k) (f (k + 1))) →
                  (∀ j, ∀ k, adj (f j) (f k) → k = j + 1 ∨ j = k + 1) →
                    SimpleGridPathBetween (f '' Set.Icc 0 n) (edges (f '' Set.Icc 0 n))
                      (f 0) (f n)
    ) := by
  classical
  intro adj edges f n hn hf hs ha
  let p := (List.range (n+1)).map f
  have hm (z : GaussianInt) : z ∈ p ↔ z ∈ f '' Set.Icc 0 n := by
    simp [p]
  have chain : p.IsChain adj := by
    apply (List.isChain_map f).mpr
    exact (List.isChain_range_succ _ n).mpr (fun k hk => hs k)
  have step : ∀ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ → adj a b := by
    exact List.isChain_iff_forall_rel_of_append_cons_cons.mp chain
  have occurs (k : Nat) (hk : k < n) :
      ∃ l₁ l₂, p = l₁ ++ f k :: f (k+1) :: l₂ := by
    have hk' : k < p.length := by simp [p]; omega
    have hk'' : k+1 < p.length := by simp [p]; omega
    refine ⟨p.take k, p.drop (k+2), ?_⟩
    conv_lhs => rw [← List.take_append_drop k p]
    rw [List.drop_eq_getElem_cons hk', List.drop_eq_getElem_cons hk'']
    simp [p]
  refine ⟨p, List.nodup_range.map hf, by simp [p]; omega,
    ?_, ?_, ?_, step, ?_⟩
  · simp [p, List.range_succ_eq_map]
  · simp [p, List.range_succ]
  · ext z; simpa using (hm z).symm
  · intro e
    constructor
    · rintro ⟨x,hx,y,hy,hxy,rfl⟩
      rcases hx with ⟨j,hj,rfl⟩
      rcases hy with ⟨k,hk,rfl⟩
      rcases ha j k hxy with rfl | rfl
      · rcases occurs j (by have := hk.2; omega) with ⟨l₁,l₂,hp⟩
        exact ⟨f j,f (j+1),l₁,l₂,hp,rfl⟩
      · rcases occurs k (by have := hj.2; omega) with ⟨l₁,l₂,hp⟩
        exact ⟨f k,f (k+1),l₁,l₂,hp,Finset.pair_comm _ _⟩
    · rintro ⟨x,y,l₁,l₂,hp,rfl⟩
      exact ⟨x, (hm x).mp (by rw [hp]; simp),
        y, (hm y).mp (by rw [hp]; simp), step x y l₁ l₂ hp, rfl⟩

private theorem horizontal :
    (by
      classical
      exact
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = { x, y }}
        (∀ (f : Nat → GaussianInt),
            ∀ (n : Nat),
              0 < n →
                Function.Injective f →
                  (∀ k, adj (f k) (f (k + 1))) →
                    (∀ j, ∀ k, adj (f j) (f k) → k = j + 1 ∨ j = k + 1) →
                      SimpleGridPathBetween (f '' Set.Icc 0 n) (edges (f '' Set.Icc 0 n))
                        (f 0) (f n)) →
          ∀ (l : Int),
            ∀ (h : Int),
              ∀ (b : Int),
                l < h →
                  SimpleGridPathBetween {z : GaussianInt | l ≤ z.re ∧ z.re ≤ h ∧ z.im = b}
                    (edges {z : GaussianInt | l ≤ z.re ∧ z.re ≤ h ∧ z.im = b}) ⟨l, b⟩
                    ⟨h, b⟩
    ) := by
  classical
  intro adj edges linepath l h b hlh
  let f := fun k : Nat => (⟨l+k,b⟩ : GaussianInt)
  let n := (h-l).toNat
  have hn : (n : Int) = h-l := by dsimp [n]; omega
  have hV : f '' Set.Icc 0 n =
      {z : GaussianInt | l ≤ z.re ∧ z.re ≤ h ∧ z.im = b} := by
    ext z
    constructor
    · rintro ⟨k,⟨_,hk⟩,rfl⟩; dsimp [f]; omega
    · rintro ⟨hzl,hzh,hzb⟩
      refine ⟨(z.re-l).toNat, ?_, ?_⟩
      · constructor <;> omega
      · apply Zsqrtd.ext <;> dsimp [f] <;> omega
  have hp := linepath f n (by omega)
    (by intro j k he; have := congrArg Zsqrtd.re he; dsimp [f] at this; omega)
    (by intro k; left; ext <;> simp [f, add_assoc])
    (by intro j k ha; simp [adj, f, Zsqrtd.ext_iff] at ha; omega)
  simpa [hV, f, hn] using hp

private theorem vertical :
    (by
      classical
      exact
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = { x, y }}
        (∀ (f : Nat → GaussianInt),
            ∀ (n : Nat),
              0 < n →
                Function.Injective f →
                  (∀ k, adj (f k) (f (k + 1))) →
                    (∀ j, ∀ k, adj (f j) (f k) → k = j + 1 ∨ j = k + 1) →
                      SimpleGridPathBetween (f '' Set.Icc 0 n) (edges (f '' Set.Icc 0 n))
                        (f 0) (f n)) →
          ∀ (l : Int),
            ∀ (h : Int),
              ∀ (a : Int),
                l < h →
                  SimpleGridPathBetween {z : GaussianInt | l ≤ z.im ∧ z.im ≤ h ∧ z.re = a}
                    (edges {z : GaussianInt | l ≤ z.im ∧ z.im ≤ h ∧ z.re = a}) ⟨a, l⟩
                    ⟨a, h⟩
    ) := by
  classical
  intro adj edges linepath l h a hlh
  let f := fun k : Nat => (⟨a,l+k⟩ : GaussianInt)
  let n := (h-l).toNat
  have hn : (n : Int) = h-l := by dsimp [n]; omega
  have hV : f '' Set.Icc 0 n =
      {z : GaussianInt | l ≤ z.im ∧ z.im ≤ h ∧ z.re = a} := by
    ext z
    constructor
    · rintro ⟨k,⟨_,hk⟩,rfl⟩; dsimp [f]; omega
    · rintro ⟨hzl,hzh,hza⟩
      refine ⟨(z.im-l).toNat, ?_, ?_⟩
      · constructor <;> omega
      · apply Zsqrtd.ext <;> dsimp [f] <;> omega
  have hp := linepath f n (by omega)
    (by intro j k he; have := congrArg Zsqrtd.im he; dsimp [f] at this; omega)
    (by intro k; right; right; left; ext <;> simp [f, add_assoc])
    (by intro j k ha; simp [adj, f, Zsqrtd.ext_iff] at ha; omega)
  simpa [hV, f, hn] using hp

private abbrev reverse_path := @SimpleGridPathBetween.reverse

private theorem sqcell :
    (by
      classical
      exact
        (∀ (n : Nat),
            ∀ (z : GaussianInt),
              z ∈ (FordTile n).cells ↔ 0 ≤ z.re ∧ z.re < n ∧ 0 ≤ z.im ∧ z.im < n) →
          let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
          ∀ (n : Nat),
            ∀ (a : Int),
              ∀ (b : Int),
                ∀ (z : GaussianInt),
                  z ∈ (sq n a b).cells ↔ a ≤ z.re ∧ z.re < a + n ∧ b ≤ z.im ∧ z.im < b + n
    ) := by
  classical
  intro fordcell sq n a b z
  change z ∈ (FordTile n).cells.image (GaussianTranslation ⟨a,b⟩) ↔ _
  constructor
  · rintro hz
    rcases Finset.mem_image.mp hz with ⟨x,hx,rfl⟩
    have hx := (fordcell n x).mp hx
    dsimp [GaussianTranslation]; omega
  · intro hz
    exact Finset.mem_image.mpr ⟨z-⟨a,b⟩, (fordcell n _).mpr (by dsimp; omega), by simp
        [GaussianTranslation]⟩

private theorem fordcent :
    (by
      classical
      exact
        (∀ (n : Nat),
            ∀ (z : GaussianInt),
              z ∈ (FordTile n).cells ↔ 0 ≤ z.re ∧ z.re < n ∧ 0 ≤ z.im ∧ z.im < n) →
          ∀ (n : Nat),
            0 < n → TileCentroid (FordTile n) = ((n : Real) / 2, (n : Real) / 2)
    ) := by
  classical
  intro fordcell n hn
  let R := TileTranslation (TileQuarterTurn (FordTile n)) ⟨n,0⟩
  have hc : R.cells = (FordTile n).cells := by
    ext z
    change z ∈ ((FordTile n).cells.image (fun x => GaussianQuarterTurn x - 1)).image
      (GaussianTranslation ⟨n,0⟩) ↔ _
    rw [Finset.image_image, fordcell]
    constructor
    · rintro hz
      rcases Finset.mem_image.mp hz with ⟨x,hx,hz⟩
      have hx := (fordcell n x).mp hx
      have hr := congrArg Zsqrtd.re hz
      have hi := congrArg Zsqrtd.im hz
      dsimp [GaussianTranslation, GaussianQuarterTurn, Function.comp_def] at hr hi
      omega
    · intro hz
      refine Finset.mem_image.mpr ⟨⟨z.im,(n:Int)-1-z.re⟩, (fordcell n _).mpr ?_, ?_⟩
      · dsimp; omega
      · ext <;> simp [GaussianTranslation,GaussianQuarterTurn]; omega
  have hne : (FordTile n).cells.Nonempty :=
    ⟨0,(fordcell n 0).mpr (by simp; omega)⟩
  have he : TileCentroid R = TileCentroid (FordTile n) :=
    (ProtoTileObservableExtensionality R (FordTile n) hc
      (by intro h; rw [hc] at h; exact (hne.ne_empty h).elim)).2.2.2.2
  rw [(TileTranslationFormulas _ _).2.2.2.2.1,
    (TileQuarterTurnFormulas _).2.2.2.2.1] at he
  apply Prod.ext
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    norm_num at h1 h2 ⊢; linarith
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    norm_num at h1 h2 ⊢; linarith

private theorem sqcent :
    (by
      classical
      exact
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩
        (∀ (n : Nat), (0 < n) → (TileCentroid (FordTile n) = ((n:Real)/2,(n:Real)/2))) → (∀ (n :
            Nat), ∀ (a : Int), ∀ (b : Int), (0 < n) → (TileCentroid (sq n a b) =
            ((a:Real)+(n:Real)/2,(b:Real)+(n:Real)/2))) ) := by
  classical
  intro sq fordcent n a b hn
  rw [(TileTranslationFormulas _ _).2.2.2.2.1,fordcent n hn]
  dsimp
  congr 1 <;> ring

private theorem hpH :
    (by
      classical
      exact
        let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
          {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = {x, y}}
        (∀ (V : Set GaussianInt), ∀ (W : Set GaussianInt), edges V ∩ edges W = edges (V ∩ W)) →
            ((∀ (l : Int), ∀ (h : Int), ∀ (b : Int), (l < h) → (SimpleGridPathBetween {z :
            GaussianInt | l ≤ z.re ∧ z.re ≤ h ∧ z.im = b} (edges {z : GaussianInt | l ≤ z.re ∧
            z.re ≤ h ∧ z.im = b}) ⟨l,b⟩ ⟨h,b⟩)) → (
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩
        (∀ (n : Nat), ∀ (a : Int), ∀ (b : Int), (0 < n) → (FootprintVertices (sq n a b) = rect a
            b n ∧ FootprintEdges (sq n a b) = edges (rect a b n))) → (∀ (n : Nat), ∀ (m : Nat), ∀
            (a : Int), ∀ (b : Int), ∀ (c : Int), ∀ (d : Int), ∀ (l : Int), ∀ (h : Int), ∀ (y :
            Int), (0 < n) → ((0 < m) → ((l < h) → ((rect a b n ∩ rect c d m = {z : GaussianInt |
            l ≤ z.re ∧ z.re ≤ h ∧ z.im = y}) → (SimpleGridPathBetween (FootprintVertices (sq n a
            b) ∩ FootprintVertices (sq m c d)) (FootprintEdges (sq n a b) ∩ FootprintEdges (sq m
            c d)) ⟨l,y⟩ ⟨h,y⟩))))))) ) := by
  classical
  intro rect adj edges edge_inter horizontal sq sqobs n m a b c d l h y hn hm hlh hv
  rw [(sqobs n a b hn).1,(sqobs m c d hm).1,
    (sqobs n a b hn).2,(sqobs m c d hm).2,edge_inter,hv]
  exact horizontal l h y hlh

private theorem hpV :
    (by
      classical
      exact
        let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
          {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = {x, y}}
        (∀ (V : Set GaussianInt), ∀ (W : Set GaussianInt), edges V ∩ edges W = edges (V ∩ W)) →
            ((∀ (l : Int), ∀ (h : Int), ∀ (a : Int), (l < h) → (SimpleGridPathBetween {z :
            GaussianInt | l ≤ z.im ∧ z.im ≤ h ∧ z.re = a} (edges {z : GaussianInt | l ≤ z.im ∧
            z.im ≤ h ∧ z.re = a}) ⟨a,l⟩ ⟨a,h⟩)) → (
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩
        (∀ (n : Nat), ∀ (a : Int), ∀ (b : Int), (0 < n) → (FootprintVertices (sq n a b) = rect a
            b n ∧ FootprintEdges (sq n a b) = edges (rect a b n))) → (∀ (n : Nat), ∀ (m : Nat), ∀
            (a : Int), ∀ (b : Int), ∀ (c : Int), ∀ (d : Int), ∀ (l : Int), ∀ (h : Int), ∀ (x :
            Int), (0 < n) → ((0 < m) → ((l < h) → ((rect a b n ∩ rect c d m = {z : GaussianInt |
            l ≤ z.im ∧ z.im ≤ h ∧ z.re = x}) → (SimpleGridPathBetween (FootprintVertices (sq n a
            b) ∩ FootprintVertices (sq m c d)) (FootprintEdges (sq n a b) ∩ FootprintEdges (sq m
            c d)) ⟨x,l⟩ ⟨x,h⟩))))))) ) := by
  classical
  intro rect adj edges edge_inter vertical sq sqobs n m a b c d l h x hn hm hlh hv
  rw [(sqobs n a b hn).1,(sqobs m c d hm).1,
    (sqobs n a b hn).2,(sqobs m c d hm).2,edge_inter,hv]
  exact vertical l h x hlh

private theorem ledger0 :
    (by
      classical
      exact
        let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
          {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = { x, y }}
        (∀ {V : Set GaussianInt},
            ∀ {E : Set (Finset GaussianInt)},
              ∀ {x : GaussianInt},
                ∀ {y : GaussianInt},
                  SimpleGridPathBetween V E x y → SimpleGridPathBetween V E y x) →
          let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
          (∀ (n : Nat),
              ∀ (a : Int),
                ∀ (b : Int),
                  0 < n →
                    FootprintVertices (sq n a b) = rect a b n ∧
                      FootprintEdges (sq n a b) = edges (rect a b n)) →
            (∀ (n : Nat),
                ∀ (m : Nat),
                  ∀ (a : Int),
                    ∀ (b : Int),
                      ∀ (c : Int),
                        ∀ (d : Int),
                          ∀ (l : Int),
                            ∀ (h : Int),
                              ∀ (y : Int),
                                0 < n →
                                0 < m →
                                l < h →
                                rect a b n ∩ rect c d m =
                                {z : GaussianInt | l ≤ z.re ∧ z.re ≤ h ∧ z.im = y} →
                                SimpleGridPathBetween
                                (FootprintVertices (sq n a b) ∩
                                FootprintVertices (sq m c d))
                                (FootprintEdges (sq n a b) ∩ FootprintEdges (sq m c d))
                                ⟨l, y⟩ ⟨h, y⟩) →
              (∀ (n : Nat),
                  ∀ (m : Nat),
                    ∀ (a : Int),
                      ∀ (b : Int),
                        ∀ (c : Int),
                          ∀ (d : Int),
                            ∀ (l : Int),
                              ∀ (h : Int),
                                ∀ (x : Int),
                                0 < n →
                                0 < m →
                                l < h →
                                rect a b n ∩ rect c d m =
                                {z : GaussianInt | l ≤ z.im ∧ z.im ≤ h ∧ z.re = x} →
                                SimpleGridPathBetween
                                (FootprintVertices (sq n a b) ∩
                                FootprintVertices (sq m c d))
                                (FootprintEdges (sq n a b) ∩ FootprintEdges (sq m c d))
                                ⟨x, l⟩ ⟨x, h⟩) →
                ∀ (r : Nat),
                  ∀ (s : Nat),
                    0 < r →
                      0 < s →
                        ∃ R :
                          ExactTileInterfaceTriple (sq (r + s) 0 0)
                            (sq (r + s) (-(s : Int)) (-(r + s : Int)))
                            (sq s (-(s : Int)) 0),
                          ∃ I :
                            ExactTileInterfaceTriple (sq (r + s) 0 0)
                              (sq (r + s) (-(r + s : Int)) s) (sq s (-(s : Int)) 0),
                            ∃ A :
                              ExactTileInterfaceTriple (sq (r + s) 0 0)
                                (sq s (-(s : Int)) 0) (sq r (-(r : Int)) s),
                              R.point = ⟨0, 0⟩ ∧
                                I.point = ⟨0, s⟩ ∧
                                A.point = ⟨0, s⟩ ∧
                                R.otherCA = ⟨0, s⟩ ∧
                                I.otherCA = ⟨0, 0⟩ ∧
                                A.otherAB = ⟨0, 0⟩ ∧ A.otherCA = ⟨0, r + s⟩
    ) := by
  classical
  intro rect adj edges reverse_path sq sqobs hpH hpV r s hr hs
  have hq : 0 < r+s := by omega
  have ca := hpV s (r+s) (-(s:Int)) 0 0 0 0 s 0 hs hq (by omega)
    (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega)
  have az := hpV r (r+s) (-(r:Int)) s 0 0 s (r+s) 0 hr hq (by omega)
    (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega)
  let R : ExactTileInterfaceTriple (sq (r+s) 0 0)
      (sq (r+s) (-(s:Int)) (-(r+s:Int))) (sq s (-(s:Int)) 0) :=
    { point := ⟨0,0⟩
      otherAB := ⟨r,0⟩
      otherBC := ⟨-(s:Int),0⟩
      otherCA := ⟨0,s⟩
      pathAB := hpH _ _ _ _ _ _ 0 r 0 hq hq (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega)
      pathBC := reverse_path (hpH _ _ _ _ _ _ (-(s:Int)) 0 0 hq hs (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega))
      pathCA := ca
      unique_common := by
        intro z
        rw [(sqobs _ _ _ hq).1,(sqobs _ _ _ hq).1,(sqobs _ _ _ hs).1]
        simp only [Set.mem_inter_iff, Zsqrtd.ext_iff]
        dsimp [rect]
        omega }
  let I : ExactTileInterfaceTriple (sq (r+s) 0 0)
      (sq (r+s) (-(r+s:Int)) s) (sq s (-(s:Int)) 0) :=
    { point := ⟨0,s⟩
      otherAB := ⟨0,r+s⟩
      otherBC := ⟨-(s:Int),s⟩
      otherCA := ⟨0,0⟩
      pathAB := hpV _ _ _ _ _ _ s (r+s) 0 hq hq (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega)
      pathBC := reverse_path (hpH _ _ _ _ _ _ (-(s:Int)) 0 s hq hs (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega))
      pathCA := reverse_path ca
      unique_common := by
        intro z
        rw [(sqobs _ _ _ hq).1,(sqobs _ _ _ hq).1,(sqobs _ _ _ hs).1]
        simp only [Set.mem_inter_iff, Zsqrtd.ext_iff]
        dsimp [rect]
        omega }
  let A : ExactTileInterfaceTriple (sq (r+s) 0 0)
      (sq s (-(s:Int)) 0) (sq r (-(r:Int)) s) :=
    { point := ⟨0,s⟩
      otherAB := ⟨0,0⟩
      otherBC := ⟨-min (r:Int) s,s⟩
      otherCA := ⟨0,r+s⟩
      pathAB := by simpa only [Set.inter_comm] using reverse_path ca
      pathBC := reverse_path (hpH _ _ _ _ _ _ (-min (r:Int) s) 0 s hs hr (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq]; omega))
      pathCA := az
      unique_common := by
        intro z
        rw [(sqobs _ _ _ hq).1,(sqobs _ _ _ hs).1,(sqobs _ _ _ hr).1]
        simp only [Set.mem_inter_iff, Zsqrtd.ext_iff]
        dsimp [rect]
        omega }
  exact ⟨R,I,A,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem ledger1 :
    (by
      classical
      exact
        let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
          {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = { x, y }}
        (∀ {V : Set GaussianInt},
            ∀ {E : Set (Finset GaussianInt)},
              ∀ {x : GaussianInt},
                ∀ {y : GaussianInt},
                  SimpleGridPathBetween V E x y → SimpleGridPathBetween V E y x) →
          let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
          (∀ (n : Nat),
              ∀ (a : Int),
                ∀ (b : Int),
                  0 < n →
                    FootprintVertices (sq n a b) = rect a b n ∧
                      FootprintEdges (sq n a b) = edges (rect a b n)) →
            (∀ (n : Nat),
                ∀ (m : Nat),
                  ∀ (a : Int),
                    ∀ (b : Int),
                      ∀ (c : Int),
                        ∀ (d : Int),
                          ∀ (l : Int),
                            ∀ (h : Int),
                              ∀ (y : Int),
                                0 < n →
                                0 < m →
                                l < h →
                                rect a b n ∩ rect c d m =
                                {z : GaussianInt | l ≤ z.re ∧ z.re ≤ h ∧ z.im = y} →
                                SimpleGridPathBetween
                                (FootprintVertices (sq n a b) ∩
                                FootprintVertices (sq m c d))
                                (FootprintEdges (sq n a b) ∩ FootprintEdges (sq m c d))
                                ⟨l, y⟩ ⟨h, y⟩) →
              (∀ (n : Nat),
                  ∀ (m : Nat),
                    ∀ (a : Int),
                      ∀ (b : Int),
                        ∀ (c : Int),
                          ∀ (d : Int),
                            ∀ (l : Int),
                              ∀ (h : Int),
                                ∀ (x : Int),
                                0 < n →
                                0 < m →
                                l < h →
                                rect a b n ∩ rect c d m =
                                {z : GaussianInt | l ≤ z.im ∧ z.im ≤ h ∧ z.re = x} →
                                SimpleGridPathBetween
                                (FootprintVertices (sq n a b) ∩
                                FootprintVertices (sq m c d))
                                (FootprintEdges (sq n a b) ∩ FootprintEdges (sq m c d))
                                ⟨x, l⟩ ⟨x, h⟩) →
                (∀ (r : Nat),
                    ∀ (s : Nat),
                      0 < r →
                        0 < s →
                          ∃ R :
                            ExactTileInterfaceTriple (sq (r + s) 0 0)
                              (sq (r + s) (-(s : Int)) (-(r + s : Int)))
                              (sq s (-(s : Int)) 0),
                            ∃ I :
                              ExactTileInterfaceTriple (sq (r + s) 0 0)
                                (sq (r + s) (-(r + s : Int)) s) (sq s (-(s : Int)) 0),
                              ∃ A :
                                ExactTileInterfaceTriple (sq (r + s) 0 0)
                                (sq s (-(s : Int)) 0) (sq r (-(r : Int)) s),
                                R.point = ⟨0, 0⟩ ∧
                                I.point = ⟨0, s⟩ ∧
                                A.point = ⟨0, s⟩ ∧
                                R.otherCA = ⟨0, s⟩ ∧
                                I.otherCA = ⟨0, 0⟩ ∧
                                A.otherAB = ⟨0, 0⟩ ∧ A.otherCA = ⟨0, r + s⟩) →
                  ∀ (r : Nat),
                    ∀ (s : Nat),
                      0 < r →
                        0 < s →
                          ∃ R :
                            ExactTileInterfaceTriple (sq (r + s) 0 0)
                              (sq (r + s) (-(r : Int)) (r + s)) (sq r (-(r : Int)) s),
                            ∃ I :
                              ExactTileInterfaceTriple (sq (r + s) 0 0)
                                (sq (r + s) (-(r + s : Int)) (-(r : Int)))
                                (sq r (-(r : Int)) s),
                              ∃ A :
                                ExactTileInterfaceTriple (sq (r + s) 0 0)
                                (sq r (-(r : Int)) s) (sq s (-(s : Int)) 0),
                                R.point = ⟨0, r + s⟩ ∧
                                I.point = ⟨0, s⟩ ∧
                                A.point = ⟨0, s⟩ ∧
                                R.otherCA = ⟨0, s⟩ ∧
                                I.otherCA = ⟨0, r + s⟩ ∧ A.otherAB = ⟨0, r + s⟩
    ) := by
  classical
  intro rect adj edges reverse_path sq sqobs hpH hpV ledger0 r s hr hs
  have hq : 0 < r+s := by omega
  have ca := hpV r (r+s) (-(r:Int)) s 0 0 s (r+s) 0 hr hq (by omega)
    (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega)
  let R : ExactTileInterfaceTriple (sq (r+s) 0 0)
      (sq (r+s) (-(r:Int)) (r+s)) (sq r (-(r:Int)) s) :=
    { point := ⟨0,r+s⟩
      otherAB := ⟨s,r+s⟩
      otherBC := ⟨-(r:Int),r+s⟩
      otherCA := ⟨0,s⟩
      pathAB := hpH _ _ _ _ _ _ 0 s (r+s) hq hq (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega)
      pathBC := reverse_path (hpH _ _ _ _ _ _ (-(r:Int)) 0 (r+s) hq hr (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega))
      pathCA := reverse_path ca
      unique_common := by
        intro z
        rw [(sqobs _ _ _ hq).1,(sqobs _ _ _ hq).1,(sqobs _ _ _ hr).1]
        simp only [Set.mem_inter_iff, Zsqrtd.ext_iff]
        dsimp [rect]
        omega }
  let I : ExactTileInterfaceTriple (sq (r+s) 0 0)
      (sq (r+s) (-(r+s:Int)) (-(r:Int))) (sq r (-(r:Int)) s) :=
    { point := ⟨0,s⟩
      otherAB := ⟨0,0⟩
      otherBC := ⟨-(r:Int),s⟩
      otherCA := ⟨0,r+s⟩
      pathAB := reverse_path (hpV _ _ _ _ _ _ 0 s 0 hq hq (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega))
      pathBC := reverse_path (hpH _ _ _ _ _ _ (-(r:Int)) 0 s hq hr (by omega)
        (by ext z; simp only [rect, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.cast_add]; omega))
      pathCA := ca
      unique_common := by
        intro z
        rw [(sqobs _ _ _ hq).1,(sqobs _ _ _ hq).1,(sqobs _ _ _ hr).1]
        simp only [Set.mem_inter_iff, Zsqrtd.ext_iff]
        dsimp [rect]
        omega }
  obtain ⟨_,_,A,_,_,ha,_,_,hab,hac⟩ := ledger0 r s hr hs
  obtain ⟨A',hap,hab',hbc',hca'⟩ := ExactTileInterfaceTripleSwapLast _ _ _ A
  refine ⟨R,I,A',rfl,rfl,hap.trans ha,rfl,rfl,?_⟩
  exact hab'.trans hac

private theorem base0 :
    (by
      classical
      exact
        let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
        (∀ (r : Nat),
            ∀ (s : Nat),
              0 < r →
                0 < s →
                  ∃ R :
                    ExactTileInterfaceTriple (sq (r + s) 0 0)
                      (sq (r + s) (-(s : Int)) (-(r + s : Int))) (sq s (-(s : Int)) 0),
                    ∃ I :
                      ExactTileInterfaceTriple (sq (r + s) 0 0)
                        (sq (r + s) (-(r + s : Int)) s) (sq s (-(s : Int)) 0),
                      ∃ A :
                        ExactTileInterfaceTriple (sq (r + s) 0 0) (sq s (-(s : Int)) 0)
                          (sq r (-(r : Int)) s),
                        R.point = ⟨0, 0⟩ ∧
                          I.point = ⟨0, s⟩ ∧
                            A.point = ⟨0, s⟩ ∧
                              R.otherCA = ⟨0, s⟩ ∧
                                I.otherCA = ⟨0, 0⟩ ∧
                                A.otherAB = ⟨0, 0⟩ ∧ A.otherCA = ⟨0, r + s⟩) →
          let package := fun U UR UL W Z : ProtoTile =>
            ∃ R : ExactTileInterfaceTriple U UR W,
              ∃ I : ExactTileInterfaceTriple U UL W,
                ∃ A : ExactTileInterfaceTriple U W Z,
                  R.point ≠ I.point ∧
                    A.point = I.point ∧
                      R.otherCA = I.point ∧ I.otherCA = R.point ∧ A.otherAB = R.point
          ∀ (r : Nat),
            ∀ (s : Nat),
              0 < r →
                0 < s →
                  package (sq (r + s) 0 0) (sq (r + s) (-(s : Int)) (-(r + s : Int)))
                    (sq (r + s) (-(r + s : Int)) s) (sq s (-(s : Int)) 0)
                    (sq r (-(r : Int)) s)
    ) := by
  classical
  intro sq ledger0 package r s hr hs
  obtain ⟨R,I,A,hR,hI,hA,hRC,hIC,hAB,_⟩ := ledger0 r s hr hs
  refine ⟨R,I,A,?_,hA.trans hI.symm,hRC.trans hI.symm,
    hIC.trans hR.symm,hAB.trans hR.symm⟩
  intro he
  rw [hR,hI] at he
  have := congrArg Zsqrtd.im he
  dsimp at this
  omega

private theorem base1 :
    (by
      classical
      exact
        let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
        (∀ (r : Nat),
            ∀ (s : Nat),
              0 < r →
                0 < s →
                  ∃ R :
                    ExactTileInterfaceTriple (sq (r + s) 0 0)
                      (sq (r + s) (-(r : Int)) (r + s)) (sq r (-(r : Int)) s),
                    ∃ I :
                      ExactTileInterfaceTriple (sq (r + s) 0 0)
                        (sq (r + s) (-(r + s : Int)) (-(r : Int))) (sq r (-(r : Int)) s),
                      ∃ A :
                        ExactTileInterfaceTriple (sq (r + s) 0 0) (sq r (-(r : Int)) s)
                          (sq s (-(s : Int)) 0),
                        R.point = ⟨0, r + s⟩ ∧
                          I.point = ⟨0, s⟩ ∧
                            A.point = ⟨0, s⟩ ∧
                              R.otherCA = ⟨0, s⟩ ∧
                                I.otherCA = ⟨0, r + s⟩ ∧ A.otherAB = ⟨0, r + s⟩) →
          let package := fun U UR UL W Z : ProtoTile =>
            ∃ R : ExactTileInterfaceTriple U UR W,
              ∃ I : ExactTileInterfaceTriple U UL W,
                ∃ A : ExactTileInterfaceTriple U W Z,
                  R.point ≠ I.point ∧
                    A.point = I.point ∧
                      R.otherCA = I.point ∧ I.otherCA = R.point ∧ A.otherAB = R.point
          ∀ (r : Nat),
            ∀ (s : Nat),
              0 < r →
                0 < s →
                  package (sq (r + s) 0 0) (sq (r + s) (-(r : Int)) (r + s))
                    (sq (r + s) (-(r + s : Int)) (-(r : Int))) (sq r (-(r : Int)) s)
                    (sq s (-(s : Int)) 0)
    ) := by
  classical
  intro sq ledger1 package r s hr hs
  obtain ⟨R,I,A,hR,hI,hA,hRC,hIC,hAB⟩ := ledger1 r s hr hs
  refine ⟨R,I,A,?_,hA.trans hI.symm,hRC.trans hI.symm,
    hIC.trans hR.symm,hAB.trans hR.symm⟩
  intro he
  rw [hR,hI] at he
  have := congrArg Zsqrtd.im he
  dsimp at this
  omega

private theorem sameobs :
    (by
      classical
      exact
        let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
          {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = { x, y }}
        (∀ (T : ProtoTile),
            ∀ (a : Int),
              ∀ (b : Int),
                ∀ (n : Int),
                  0 < n →
                    (∀ z : GaussianInt,
                        z ∈ T.cells ↔ a ≤ z.re ∧ z.re < a + n ∧ b ≤ z.im ∧ z.im < b + n) →
                      FootprintVertices T = rect a b n ∧
                        FootprintEdges T = edges (rect a b n)) →
          let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
          (∀ (n : Nat),
              ∀ (a : Int),
                ∀ (b : Int),
                  ∀ (z : GaussianInt),
                    z ∈ (sq n a b).cells ↔
                      a ≤ z.re ∧ z.re < a + n ∧ b ≤ z.im ∧ z.im < b + n) →
            (∀ (n : Nat), ∀ (a : Int), ∀ (b : Int), 0 < n → (sq n a b).cells.Nonempty) →
              (∀ (n : Nat),
                  ∀ (a : Int),
                    ∀ (b : Int),
                      0 < n →
                        TileCentroid (sq n a b) =
                          ((a : Real) + (n : Real) / 2, (b : Real) + (n : Real) / 2)) →
                ∀ (T : ProtoTile),
                  ∀ (n : Nat),
                    ∀ (a : Int),
                      ∀ (b : Int),
                        0 < n →
                          T.cells = (sq n a b).cells →
                            FootprintVertices T = rect a b n ∧
                              FootprintEdges T = edges (rect a b n) ∧
                                TileCentroid T =
                                ((a : Real) + (n : Real) / 2, (b : Real) + (n : Real) / 2)
    ) := by
  classical
  intro rect adj edges obs sq sqcell sqne sqcent T n a b hn hc
  have h := obs T a b n (by omega) (by intro z; rw [hc]; exact sqcell n a b z)
  have ht : T.cells.Nonempty := hc ▸ sqne n a b hn
  refine ⟨h.1,h.2,?_⟩
  have he : TileCentroid T = TileCentroid (sq n a b) :=
    (ProtoTileObservableExtensionality _ _ hc (by intro he; exact (ht.ne_empty he).elim)).2.2.2.2
  exact he.trans (sqcent n a b hn)

private theorem carry_squares :
    (by
      classical
      exact
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩
        let package := fun U UR UL W Z : ProtoTile =>
          ∃ R : ExactTileInterfaceTriple U UR W,
          ∃ I : ExactTileInterfaceTriple U UL W,
          ∃ A : ExactTileInterfaceTriple U W Z,
            R.point ≠ I.point ∧ A.point = I.point ∧ R.otherCA = I.point ∧
              I.otherCA = R.point ∧ A.otherAB = R.point
        let ax := fun (q : Int) (flip : Bool) (t a n : Int) =>
          (if flip then q-a-n else a)+t
        ∀ (q : Int), ∀ (flip : Bool), ∀ (t : GaussianInt), ∀ (N : Fin 5 → Nat), ∀ (X : Fin 5 →
            Int), ∀ (Y : Fin 5 → Int), (∀ k, 0 < N k) → (∀ (T : Fin 5 → ProtoTile), (∀ k, (T
            k).cells =
            (sq (N k) (ax q flip t.re (X k) (N k))
              (ax q flip t.im (Y k) (N k))).cells) → ((package (sq (N 0) (X 0) (Y 0)) (sq (N 1)
                  (X 1) (Y 1))
            (sq (N 2) (X 2) (Y 2)) (sq (N 3) (X 3) (Y 3)) (sq (N 4) (X 4) (Y 4))) → (package (T
                0) (T 1) (T 2) (T 3) (T 4)))) ) := by
  classical
  intro sq package ax q flip t N X Y hN T hc hp
  let affine := fun (q : Int) (flip : Bool) (t : GaussianInt) (z : GaussianInt) =>
    (if flip then (⟨q,q⟩ : GaussianInt) - z else z) + t
  have image (a b c : Fin 5)
      (E : ExactTileInterfaceTriple (sq (N a) (X a) (Y a))
        (sq (N b) (X b) (Y b)) (sq (N c) (X c) (Y c))) :
      ∃ E' : ExactTileInterfaceTriple (T a) (T b) (T c),
        E'.point = affine q flip t E.point ∧
        E'.otherAB = affine q flip t E.otherAB ∧
        E'.otherBC = affine q flip t E.otherBC ∧
        E'.otherCA = affine q flip t E.otherCA := by
    apply P5269T1CenteredSquareTripleTransport q flip t
      ![N a,N b,N c] ![⟨X a,Y a⟩,⟨X b,Y b⟩,⟨X c,Y c⟩]
      (by intro k; fin_cases k <;> simp only [
        ] <;> exact hN _) ![T a,T b,T c] _ E
    intro k
    fin_cases k
    · cases flip <;> exact hc a
    · cases flip <;> exact hc b
    · cases flip <;> exact hc c
  obtain ⟨R,I,A,hne,hAI,hRI,hIR,hAR⟩ := hp
  obtain ⟨R',hR,hRab,hRbc,hRca⟩ := image 0 1 3 R
  obtain ⟨I',hI,hIab,hIbc,hIca⟩ := image 0 2 3 I
  obtain ⟨A',hA,hAab,hAbc,hAca⟩ := image 0 3 4 A
  refine ⟨R',I',A',?_,?_,?_,?_,?_⟩
  · rw [hR,hI]
    intro h
    apply hne
    cases flip <;> simpa [affine] using h
  · rw [hA,hI,hAI]
  · rw [hRca,hI,hRI]
  · rw [hIca,hR,hIR]
  · rw [hAab,hR,hAR]

private theorem translate_cells :
    (by
      classical
      exact
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩
        ∀ (T : ProtoTile), ∀ (n : Nat), ∀ (a : Int), ∀ (b : Int), ∀ (u : GaussianInt), (T.cells =
            (sq n a b).cells) → ((TileTranslation T u).cells = (sq n (a+u.re) (b+u.im)).cells) )
            := by
  classical
  intro sq T n a b u hc
  change T.cells.image (GaussianTranslation u) = _
  rw [hc]
  simp only [sq,TileTranslation,Finset.image_image]
  apply Finset.image_congr
  intro z hz
  ext <;> simp [GaussianTranslation,add_assoc]

private theorem finish0 :
    (by
      classical
      exact
        let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
        let package := fun U UR UL W Z : ProtoTile =>
          ∃ R : ExactTileInterfaceTriple U UR W,
            ∃ I : ExactTileInterfaceTriple U UL W,
              ∃ A : ExactTileInterfaceTriple U W Z,
                R.point ≠ I.point ∧
                  A.point = I.point ∧
                    R.otherCA = I.point ∧ I.otherCA = R.point ∧ A.otherAB = R.point
        (∀ (r : Nat),
            ∀ (s : Nat),
              0 < r →
                0 < s →
                  package (sq (r + s) 0 0) (sq (r + s) (-(s : Int)) (-(r + s : Int)))
                    (sq (r + s) (-(r + s : Int)) s) (sq s (-(s : Int)) 0)
                    (sq r (-(r : Int)) s)) →
          let ax := fun (q : Int) (flip : Bool) (t a n : Int) =>
            (if flip then q - a - n else a) + t
          (∀ (q : Int),
              ∀ (flip : Bool),
                ∀ (t : GaussianInt),
                  ∀ (N : Fin 5 → Nat),
                    ∀ (X : Fin 5 → Int),
                      ∀ (Y : Fin 5 → Int),
                        (∀ k, 0 < N k) →
                          ∀ (T : Fin 5 → ProtoTile),
                            (∀ k,
                                (T k).cells =
                                (sq (N k) (ax q flip t.re (X k) (N k))
                                (ax q flip t.im (Y k) (N k))).cells) →
                              package (sq (N 0) (X 0) (Y 0)) (sq (N 1) (X 1) (Y 1))
                                (sq (N 2) (X 2) (Y 2)) (sq (N 3) (X 3) (Y 3))
                                (sq (N 4) (X 4) (Y 4)) →
                                package (T 0) (T 1) (T 2) (T 3) (T 4)) →
            (∀ (T : ProtoTile),
                ∀ (n : Nat),
                  ∀ (a : Int),
                    ∀ (b : Int),
                      ∀ (u : GaussianInt),
                        T.cells = (sq n a b).cells →
                          (TileTranslation T u).cells =
                            (sq n (a + u.re) (b + u.im)).cells) →
              ∀ (r : Nat),
                ∀ (s : Nat),
                  0 < r →
                    0 < s →
                      ∀ (a : Int),
                        ∀ (b : Int),
                          ∀ (flip : Bool),
                            ∀ (U : ProtoTile),
                              ∀ (W : ProtoTile),
                                ∀ (Z : ProtoTile),
                                U.cells = (sq (r + s) a b).cells →
                                W.cells =
                                (sq s (if flip then a + (r + s : Int) else a - s)
                                (if flip then b + r else b)).cells →
                                Z.cells =
                                (sq r (if flip then a + (r + s : Int) else a - r)
                                (if flip then b else b + s)).cells →
                                package U
                                (TileTranslation U
                                (if flip then ⟨s, r + s⟩
                              else ⟨-(s : Int), -(r + s : Int)⟩))
                                (TileTranslation U
                                (if flip then ⟨r + s, -(s : Int)⟩
                              else ⟨-(r + s : Int), s⟩))
                                W Z
    ) := by
  classical
  intro sq package base0 ax carry_squares translate_cells r s hr hs a b flip U W Z hU hW hZ
  refine carry_squares (r+s) flip ⟨a,b⟩ ![r+s,r+s,r+s,s,r]
    ![0,-(s:Int),-(r+s:Int),-(s:Int),-(r:Int)]
    ![0,-(r+s:Int),s,0,s] ?_
    ![U,TileTranslation U (if flip then ⟨s,r+s⟩ else ⟨-(s:Int),-(r+s:Int)⟩),
      TileTranslation U (if flip then ⟨r+s,-(s:Int)⟩ else ⟨-(r+s:Int),s⟩),W,Z] ?_
    (base0 r s hr hs)
  · intro k; fin_cases k <;> simp <;> omega
  · intro k
    fin_cases k
    · cases flip <;> simpa [ax] using hU
    · have h := translate_cells U (r+s) a b
        (if flip then ⟨s,r+s⟩ else ⟨-(s:Int),-(r+s:Int)⟩) hU
      cases flip <;> simpa [ax,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using h
    · have h := translate_cells U (r+s) a b
        (if flip then ⟨r+s,-(s:Int)⟩ else ⟨-(r+s:Int),s⟩) hU
      cases flip <;> convert h using 1 <;> congr 2 <;> dsimp [ax] <;> omega
    · cases flip <;> simpa [ax,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hW
    · cases flip <;> simpa [ax,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hZ

private theorem finish1 :
    (by
      classical
      exact
        let sq := fun n : Nat => fun a b : Int => TileTranslation (FordTile n) ⟨a, b⟩
        let package := fun U UR UL W Z : ProtoTile =>
          ∃ R : ExactTileInterfaceTriple U UR W,
            ∃ I : ExactTileInterfaceTriple U UL W,
              ∃ A : ExactTileInterfaceTriple U W Z,
                R.point ≠ I.point ∧
                  A.point = I.point ∧
                    R.otherCA = I.point ∧ I.otherCA = R.point ∧ A.otherAB = R.point
        (∀ (r : Nat),
            ∀ (s : Nat),
              0 < r →
                0 < s →
                  package (sq (r + s) 0 0) (sq (r + s) (-(r : Int)) (r + s))
                    (sq (r + s) (-(r + s : Int)) (-(r : Int))) (sq r (-(r : Int)) s)
                    (sq s (-(s : Int)) 0)) →
          let ax := fun (q : Int) (flip : Bool) (t a n : Int) =>
            (if flip then q - a - n else a) + t
          (∀ (q : Int),
              ∀ (flip : Bool),
                ∀ (t : GaussianInt),
                  ∀ (N : Fin 5 → Nat),
                    ∀ (X : Fin 5 → Int),
                      ∀ (Y : Fin 5 → Int),
                        (∀ k, 0 < N k) →
                          ∀ (T : Fin 5 → ProtoTile),
                            (∀ k,
                                (T k).cells =
                                (sq (N k) (ax q flip t.re (X k) (N k))
                                (ax q flip t.im (Y k) (N k))).cells) →
                              package (sq (N 0) (X 0) (Y 0)) (sq (N 1) (X 1) (Y 1))
                                (sq (N 2) (X 2) (Y 2)) (sq (N 3) (X 3) (Y 3))
                                (sq (N 4) (X 4) (Y 4)) →
                                package (T 0) (T 1) (T 2) (T 3) (T 4)) →
            (∀ (T : ProtoTile),
                ∀ (n : Nat),
                  ∀ (a : Int),
                    ∀ (b : Int),
                      ∀ (u : GaussianInt),
                        T.cells = (sq n a b).cells →
                          (TileTranslation T u).cells =
                            (sq n (a + u.re) (b + u.im)).cells) →
              ∀ (r : Nat),
                ∀ (s : Nat),
                  0 < r →
                    0 < s →
                      ∀ (a : Int),
                        ∀ (b : Int),
                          ∀ (flip : Bool),
                            ∀ (U : ProtoTile),
                              ∀ (W : ProtoTile),
                                ∀ (Z : ProtoTile),
                                U.cells = (sq (r + s) a b).cells →
                                W.cells =
                                (sq r (if flip then a + (r + s : Int) else a - r)
                                (if flip then b else b + s)).cells →
                                Z.cells =
                                (sq s (if flip then a + (r + s : Int) else a - s)
                                (if flip then b + r else b)).cells →
                                package U
                                (TileTranslation U
                                (if flip then ⟨r, -(r + s : Int)⟩
                              else ⟨-(r : Int), r + s⟩))
                                (TileTranslation U
                                (if flip then ⟨r + s, r⟩
                              else ⟨-(r + s : Int), -(r : Int)⟩))
                                W Z
    ) := by
  classical
  intro sq package base1 ax carry_squares translate_cells r s hr hs a b flip U W Z hU hW hZ
  refine carry_squares (r+s) flip ⟨a,b⟩ ![r+s,r+s,r+s,r,s]
    ![0,-(r:Int),-(r+s:Int),-(r:Int),-(s:Int)]
    ![0,r+s,-(r:Int),s,0] ?_
    ![U,TileTranslation U (if flip then ⟨r,-(r+s:Int)⟩ else ⟨-(r:Int),r+s⟩),
      TileTranslation U (if flip then ⟨r+s,r⟩ else ⟨-(r+s:Int),-(r:Int)⟩),W,Z] ?_
    (base1 r s hr hs)
  · intro k; fin_cases k <;> simp <;> omega
  · intro k
    fin_cases k
    · cases flip <;> simpa [ax] using hU
    · have h := translate_cells U (r+s) a b
        (if flip then ⟨r,-(r+s:Int)⟩ else ⟨-(r:Int),r+s⟩) hU
      cases flip <;> convert h using 1 <;> congr 2 <;> dsimp [ax] <;> omega
    · have h := translate_cells U (r+s) a b
        (if flip then ⟨r+s,r⟩ else ⟨-(r+s:Int),-(r:Int)⟩) hU
      cases flip <;> simpa [ax,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using h
    · cases flip <;> simpa [ax,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hW
    · cases flip <;> simpa [ax,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hZ

private theorem hrAt727 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (1 : ℕ) < P.q → 0 < P.q₁
    ) := by
  classical
  intro P hq
  by_contra h
  have hz : P.q₁ = 0 := by omega
  have hd := P.det₁
  simp [hz] at hd
  have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
  have hone := Int.eq_one_of_dvd_one (by omega : 0 ≤ (P.q:Int)) hdv
  omega

private theorem norm1 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩
        (P.q₁ ≠ 0) → (∀ (T : ProtoTile), (BandPrototile ((FordRecursiveQuadruple P) 1) T) → (∃ a
            b : Int, T.cells = (sq P.q₁ a b).cells))) ) := by
  classical
  intro P hq sq hr0 T hT
  obtain ⟨w, hw⟩ := P5269T1FordSquareNormalForm P hq 1 T hT
    (by simp [FordRecursiveQuadruple, FordCircleCoordinate, hr0] )
  exact ⟨w.re, w.im, hw⟩

private theorem norm2 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩
        (0 < P.q₂) → (∀ (T : ProtoTile), (BandPrototile ((FordRecursiveQuadruple P) 2) T) → (∃ a
            b : Int, T.cells = (sq P.q₂ a b).cells))) ) := by
  classical
  intro P hq sq hs T hT
  obtain ⟨w, hw⟩ := P5269T1FordSquareNormalForm P hq 2 T hT
    (by simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
        Fin.isValue, Matrix.cons_val, mul_self_pos, ne_eq, Int.natCast_eq_zero]; positivity)
  exact ⟨w.re, w.im, hw⟩

private theorem indices :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin (3 : ℕ)),
            ∀ (s : Fin (4 : ℕ)),
              (0 : ℤ) < (FordRecursiveQuadruple P i.succ).1 →
                (0 : ℤ) <
                    (FordRecursiveQuadruple P
                        (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ))
                          else i + (1 : Fin (3 : ℕ))).succ).1 →
                  Even s.val ∧ i = 1 ∨ ¬Even s.val ∧ i = 0
    ) := by
  classical
  intro P i s hWpos hZpos
  by_cases hE : Even s.val
  · left
    refine ⟨hE,?_⟩
    fin_cases i
    · have hh := hZpos
      rw [ite_eq_left hE] at hh
      have hi : ((0:Fin 3)-1).succ = 3 := by decide
      change 0 < (FordRecursiveQuadruple P ((0:Fin 3)-1).succ).1 at hh
      rw [hi] at hh
      exact (lt_irrefl 0 hh).elim
    · rfl
    · have hh := hWpos
      norm_num [FordRecursiveQuadruple] at hh
  · right
    refine ⟨hE,?_⟩
    fin_cases i
    · rfl
    · have hh := hZpos
      rw [ite_eq_right hE] at hh
      have hi : ((1:Fin 3)+1).succ = 3 := by decide
      change 0 < (FordRecursiveQuadruple P ((1:Fin 3)+1).succ).1 at hh
      rw [hi] at hh
      exact (lt_irrefl 0 hh).elim
    · have hh := hWpos
      norm_num [FordRecursiveQuadruple] at hh

private theorem hwaAt806 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) +
            (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q :
            ℝ) + -(↑P.q₂ : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2
            : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₂ : ℝ) + -(↑P.q : ℝ))) → (wa = a-(P.q₂:Int)) ) := by
  classical
  intro P a b wa wb hcw
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcw.1]

private theorem hwbAt810 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) +
            (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q :
            ℝ) + -(↑P.q₂ : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2
            : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₂ : ℝ) + -(↑P.q : ℝ))) → (wb = b) ) := by
  classical
  intro P a b wa wb hcw
  apply Int.cast_injective (α := Real)
  linarith [hcw.2]

private theorem hzaAt813 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) +
            (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q₁ :
            ℝ) - (↑P.q : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 :
            ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ) - (↑P.q₁ : ℝ))) → (za = a-(P.q₁:Int)) ) := by
  classical
  intro P a b za zb hcz
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcz.1]

private theorem hzbAt817 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((P.q:Real) = (P.q₁:Real)+(P.q₂:Real)) → (∀ (a : ℤ), ∀ (b :
            ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q :
            ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q₁ : ℝ) - (↑P.q : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₁ : ℝ) /
            (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ) - (↑P.q₁ :
            ℝ))) → (zb = b+(P.q₂:Int))) ) := by
  classical
  intro P hqsR a b za zb hcz
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcz.2]

private theorem hwaAt838 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) +
            (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₂ :
            ℝ) + (↑P.q : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 :
            ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ) + -(↑P.q₂ : ℝ))) → (wa = a+(P.q:Int)) ) := by
  classical
  intro P a b wa wb hcw
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcw.1]

private theorem hwbAt842 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((P.q:Real) = (P.q₁:Real)+(P.q₂:Real)) → (∀ (a : ℤ), ∀ (b :
            ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q :
            ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₂ : ℝ) + (↑P.q : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₂ : ℝ) /
            (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ) + -(↑P.q₂ :
            ℝ))) → (wb = b+(P.q₁:Int))) ) := by
  classical
  intro P hqsR a b wa wb hcw
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcw.2]

private theorem hzaAt846 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) +
            (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ)
            + (↑P.q₁ : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 :
            ℝ)) = (1 / 2 : ℝ) * ((↑P.q₁ : ℝ) - (↑P.q : ℝ))) → (za = a+(P.q:Int)) ) := by
  classical
  intro P a b za zb hcz
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcz.1]

private theorem hzbAt850 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) +
            (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ)
            + (↑P.q₁ : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 :
            ℝ)) = (1 / 2 : ℝ) * ((↑P.q₁ : ℝ) - (↑P.q : ℝ))) → (zb = b) ) := by
  classical
  intro P a b za zb hcz
  apply Int.cast_injective (α := Real)
  linarith [hcz.2]

private theorem hwaAt881 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) +
            (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q :
            ℝ) + -(↑P.q₁ : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2
            : ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ) + -(↑P.q₁ : ℝ))) → (wa = a-(P.q₁:Int)) ) := by
  classical
  intro P a b wa wb hcw
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcw.1]

private theorem hwbAt885 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((P.q:Real) = (P.q₁:Real)+(P.q₂:Real)) → (∀ (a : ℤ), ∀ (b :
            ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q :
            ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q : ℝ) + -(↑P.q₁ : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₁ : ℝ)
            / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q : ℝ) + -(↑P.q₁ :
            ℝ))) → (wb = b+(P.q₂:Int))) ) := by
  classical
  intro P hqsR a b wa wb hcw
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcw.2]

private theorem hzaAt889 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) +
            (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q :
            ℝ) + -(↑P.q₂ : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2
            : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q : ℝ) + (↑P.q₂ : ℝ))) → (za = a-(P.q₂:Int)) ) := by
  classical
  intro P a b za zb hcz
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcz.1]

private theorem hzbAt893 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) +
            (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q :
            ℝ) + -(↑P.q₂ : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2
            : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q : ℝ) + (↑P.q₂ : ℝ))) → (zb = b) ) := by
  classical
  intro P a b za zb hcz
  apply Int.cast_injective (α := Real)
  linarith [hcz.2]

private theorem hwaAt917 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) +
            (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₁ :
            ℝ) + (↑P.q : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 :
            ℝ)) = (1 / 2 : ℝ) * ((↑P.q₁ : ℝ) + -(↑P.q : ℝ))) → (wa = a+(P.q:Int)) ) := by
  classical
  intro P a b wa wb hcw
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcw.1]

private theorem hwbAt921 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (wa : ℤ), ∀ (wb : ℤ), ((↑wa : ℝ) +
            (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₁ :
            ℝ) + (↑P.q : ℝ)) ∧ (↑wb : ℝ) + (↑P.q₁ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 :
            ℝ)) = (1 / 2 : ℝ) * ((↑P.q₁ : ℝ) + -(↑P.q : ℝ))) → (wb = b) ) := by
  classical
  intro P a b wa wb hcw
  apply Int.cast_injective (α := Real)
  linarith [hcw.2]

private theorem hzaAt924 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) +
            (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₂ :
            ℝ) + (↑P.q : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 :
            ℝ)) = (1 / 2 : ℝ) * (-(↑P.q₂ : ℝ) + (↑P.q : ℝ))) → (za = a+(P.q:Int)) ) := by
  classical
  intro P a b za zb hcz
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcz.1]

private theorem hzbAt928 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((P.q:Real) = (P.q₁:Real)+(P.q₂:Real)) → (∀ (a : ℤ), ∀ (b :
            ℤ), ∀ (za : ℤ), ∀ (zb : ℤ), ((↑za : ℝ) + (↑P.q₂ : ℝ) / (2 : ℝ) - ((↑a : ℝ) + (↑P.q :
            ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * ((↑P.q₂ : ℝ) + (↑P.q : ℝ)) ∧ (↑zb : ℝ) + (↑P.q₂ : ℝ) /
            (2 : ℝ) - ((↑b : ℝ) + (↑P.q : ℝ) / (2 : ℝ)) = (1 / 2 : ℝ) * (-(↑P.q₂ : ℝ) + (↑P.q :
            ℝ))) → (zb = b+(P.q₁:Int))) ) := by
  classical
  intro P hqsR a b za zb hcz
  apply Int.cast_injective (α := Real)
  push_cast
  linarith [hcz.2]

end FordEndpointProof

namespace FordEndpointAssembly

private theorem sqobs :
    (by
      classical
      exact
        (
        let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
          {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n};
        let adj := fun x y : GaussianInt =>
          y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩;
        let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
          {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = {x, y}};
        (∀ (T : ProtoTile), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (n : ℤ), (0 : ℤ) < n → (∀ (z : GaussianInt),
            z ∈ T.cells ↔ a ≤ z.re ∧ z.re < a + n ∧ b ≤ z.im ∧ z.im < b + n) → FootprintVertices
            T = (fun (a b n : ℤ) => {z : GaussianInt | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im
            ≤ b + n}) a b n ∧ FootprintEdges T = (fun (V : Set GaussianInt) => {e : Finset
            GaussianInt | ∃ x ∈ V, ∃ y ∈ V, (fun (x y : GaussianInt) => y = x + (1 : GaussianInt)
            ∨ y = x - (1 : GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) x y ∧ e = {x, y}}) ((fun (a b n : ℤ) => {z :
            GaussianInt | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}) a b n)) → (
        let sq := fun n : Nat => fun a b : Int =>
          TileTranslation (FordTile n) ⟨a,b⟩;
        (∀ (n : Nat), ∀ (a : Int), ∀ (b : Int), ∀ (z : GaussianInt), z ∈ (sq n a b).cells ↔ a ≤
            z.re ∧ z.re < a+n ∧ b ≤ z.im ∧ z.im < b+n) → (∀ (n : Nat), ∀ (a : Int), ∀ (b : Int),
            (0 < n) → (FootprintVertices (sq n a b) = rect a b n ∧ FootprintEdges (sq n a b) =
            edges (rect a b n))))) ) := by
  classical
  intro rect adj edges obs sq sqcell n a b hn
  exact obs _ a b n (by omega) (sqcell n a b)

end FordEndpointAssembly


theorem FordOrientedChildParentEndpoints
    (P : FordFareyParameter) (hq : 1 < P.q) :
    let q := FordRecursiveQuadruple P
    ∀ (i : Fin 3) (s : Fin 4) (U W Z : ProtoTile),
      BandPrototile (q 0) U →
      BandPrototile (q i.succ) W →
      BandPrototile
        (q ((if Even s.val then i - 1 else i + 1).succ)) Z →
      0 < (q 0).1 → 0 < (q i.succ).1 →
      0 < (q ((if Even s.val then i - 1 else i + 1).succ)).1 →
      TileCentroid W - TileCentroid U = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0)
            else
              BandVectors.1 (q ((i + 1).succ)) (q 0) -
                BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0))
      let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q i.succ) (q 0)
          else BandVectors.1 (q 0) (q i.succ))
      ∃ rightData : ExactTileInterfaceTriple U (TileTranslation U uR) W,
        ∃ incomingData : ExactTileInterfaceTriple U (TileTranslation U uL) W,
          ∃ adjacentData : ExactTileInterfaceTriple U W Z,
            rightData.point ≠ incomingData.point ∧
            adjacentData.point = incomingData.point ∧
            rightData.otherCA = incomingData.point ∧
            incomingData.otherCA = rightData.point ∧
            adjacentData.otherAB = rightData.point := by
-- BODY
  classical
  -- A positive rectangle has the full induced grid graph on its vertices.
  let rect : Int → Int → Int → Set GaussianInt := fun a b n =>
    {z | a ≤ z.re ∧ z.re ≤ a + n ∧ b ≤ z.im ∧ z.im ≤ b + n}
  let adj := fun x y : GaussianInt =>
    y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  let edges : Set GaussianInt → Set (Finset GaussianInt) := fun V =>
    {e | ∃ x ∈ V, ∃ y ∈ V, adj x y ∧ e = {x, y}}
  have obs := FordEndpointProof.obs
  have edge_inter := FordEndpointProof.edge_inter
  -- Enumerate every vertex and every edge of a straight segment.
  have linepath := FordEndpointProof.linepath
  have reverse_path {V : Set GaussianInt} {E : Set (Finset GaussianInt)} {x y : GaussianInt}
      (hp : SimpleGridPathBetween V E x y) := FordEndpointProof.reverse_path (V := V) (E :=
          E) (x := x) (y := y) hp
  have fordcell := FordTileCellMembership
  let sq := fun n : Nat => fun a b : Int =>
    TileTranslation (FordTile n) ⟨a,b⟩
  have sqcell (n : Nat) (a b : Int) (z : GaussianInt) :
      z ∈ (sq n a b).cells ↔
        a ≤ z.re ∧ z.re < a+n ∧ b ≤ z.im ∧ z.im < b+n := FordEndpointProof.sqcell fordcell
            n a b z
  have sqobs := FordEndpointAssembly.sqobs obs sqcell
  have sqne (n : Nat) (a b : Int) (hn : 0 < n) : (sq n a b).cells.Nonempty :=
    ⟨⟨a,b⟩, (sqcell n a b _).mpr (by dsimp; omega)⟩
  -- A centered quarter-turn determines the square's centroid without sums.
  have hpH := FordEndpointProof.hpH edge_inter (FordEndpointProof.horizontal linepath) sqobs
  have hpV := FordEndpointProof.hpV edge_inter (FordEndpointProof.vertical linepath) sqobs
  -- The complete path ledger for rotation zero.
  have ledger0 := FordEndpointProof.ledger0 reverse_path sqobs hpH hpV
  -- The second ledger uses the same child-parent junction with parents swapped.
  let package := fun U UR UL W Z : ProtoTile =>
    ∃ R : ExactTileInterfaceTriple U UR W,
    ∃ I : ExactTileInterfaceTriple U UL W,
    ∃ A : ExactTileInterfaceTriple U W Z,
      R.point ≠ I.point ∧ A.point = I.point ∧ R.otherCA = I.point ∧
        I.otherCA = R.point ∧ A.otherAB = R.point
  let affine := fun (q : Int) (flip : Bool) (t : GaussianInt) (z : GaussianInt) =>
    (if flip then (⟨q,q⟩ : GaussianInt) - z else z) + t
  let ax := fun (q : Int) (flip : Bool) (t a n : Int) =>
    (if flip then q-a-n else a)+t
  have sameobs := FordEndpointProof.sameobs obs sqcell sqne (FordEndpointProof.sqcent
      (FordEndpointProof.fordcent fordcell))
  have carry_squares := FordEndpointProof.carry_squares
  have translate_cells := FordEndpointProof.translate_cells
  have finish0 (r s : Nat) (hr : 0 < r) (hs : 0 < s) (a b : Int)
      (flip : Bool) (U W Z : ProtoTile)
      (hU : U.cells = (sq (r+s) a b).cells)
      (hW : W.cells = (sq s (if flip then a+(r+s:Int) else a-s)
        (if flip then b+r else b)).cells)
      (hZ : Z.cells = (sq r (if flip then a+(r+s:Int) else a-r)
        (if flip then b else b+s)).cells) :
      package U
        (TileTranslation U (if flip then ⟨s,r+s⟩ else ⟨-(s:Int),-(r+s:Int)⟩))
        (TileTranslation U (if flip then ⟨r+s,-(s:Int)⟩ else ⟨-(r+s:Int),s⟩)) W Z :=
            FordEndpointProof.finish0 (FordEndpointProof.base0 ledger0) carry_squares
                translate_cells r s hr hs a b
            flip U W Z hU hW hZ
  have finish1 (r s : Nat) (hr : 0 < r) (hs : 0 < s) (a b : Int)
      (flip : Bool) (U W Z : ProtoTile)
      (hU : U.cells = (sq (r+s) a b).cells)
      (hW : W.cells = (sq r (if flip then a+(r+s:Int) else a-r)
        (if flip then b else b+s)).cells)
      (hZ : Z.cells = (sq s (if flip then a+(r+s:Int) else a-s)
        (if flip then b+r else b)).cells) :
      package U
        (TileTranslation U (if flip then ⟨r,-(r+s:Int)⟩ else ⟨-(r:Int),r+s⟩))
        (TileTranslation U (if flip then ⟨r+s,r⟩ else ⟨-(r+s:Int),-(r:Int)⟩)) W Z :=
            FordEndpointProof.finish1 (FordEndpointProof.base1
                (FordEndpointProof.ledger1 reverse_path sqobs hpH hpV ledger0)) carry_squares
                translate_cells r s hr hs a b
            flip U W Z hU hW hZ
  dsimp only
  intro i s U W Z hU hW hZ hUpos hWpos hZpos hcw hcz
  have hr : 0 < P.q₁ := FordEndpointProof.hrAt727 P hq
  have hs : 0 < P.q₂ := P.q₂_pos
  have hr0 : P.q₁ ≠ 0 := by omega
  have hqs : P.q = P.q₁ + P.q₂ := P.sum_q
  have hqsR : (P.q:Real) = (P.q₁:Real)+(P.q₂:Real) := by exact_mod_cast hqs
  obtain ⟨hproper,h10,h20,h30,_⟩ := (FordCoordinateConfiguration P).2 hq
  have hf := (VectorRecursionLaws _ hproper.1).2.2.2.2 hproper
  have h01 : BandVectors.1 ((FordRecursiveQuadruple P) 0)
      ((FordRecursiveQuadruple P) 1) = ⟨-(P.q₁:Int),P.q⟩ := FordParentVectors.firstParent P h10 hf
  have h02 : BandVectors.1 ((FordRecursiveQuadruple P) 0)
      ((FordRecursiveQuadruple P) 2) = ⟨-(P.q₂:Int),-(P.q:Int)⟩ :=
          FordParentVectors.secondParent P h20 hf
  have norm1 (T : ProtoTile) (hT : BandPrototile ((FordRecursiveQuadruple P) 1) T) :
      ∃ a b : Int, T.cells = (sq P.q₁ a b).cells := FordEndpointProof.norm1 P hq hr0 T hT
  have norm2 (T : ProtoTile) (hT : BandPrototile ((FordRecursiveQuadruple P) 2) T) :
      ∃ a b : Int, T.cells = (sq P.q₂ a b).cells := FordEndpointProof.norm2 P hq hs T hT
  obtain ⟨u, hu⟩ := P5269T1FordSquareNormalForm P hq 0 U hU hUpos
  obtain ⟨a,b,hUc⟩ : ∃ a b : Int, U.cells = (sq P.q a b).cells :=
    ⟨u.re, u.im, hu⟩
  have hcu := (sameobs U P.q a b P.q_pos hUc).2.2
  have indices := FordEndpointProof.indices P i s hWpos hZpos
  rcases indices with ⟨heven,rfl⟩ | ⟨hodd,rfl⟩
  · obtain ⟨wa,wb,hWc⟩ := norm2 W hW
    obtain ⟨za,zb,hZc⟩ := norm1 Z (by simpa [heven] using hZ)
    have hccw := (sameobs W P.q₂ wa wb hs hWc).2.2
    have hccz := (sameobs Z P.q₁ za zb hr hZc).2.2
    rw [hccw,hcu] at hcw
    rw [hccz,hcu] at hcz
    fin_cases s
    · norm_num [heven,h10,h20,h01,h02,GaussianRealPoint,pow_succ] at hcw hcz
      have hwa := FordEndpointProof.hwaAt806 P a b wa wb hcw
      have hwb := FordEndpointProof.hwbAt810 P a b wa wb hcw
      have hza := FordEndpointProof.hzaAt813 P a b za zb hcz
      have hzb := FordEndpointProof.hzbAt817 P hqsR a b za zb hcz
      subst wa wb za zb
      change package U
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^0 *
          (if Even (0:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 0)
              ((FordRecursiveQuadruple P) 2)
            else BandVectors.1 ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple P) 0))))
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^0 *
          (if Even (0:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 2)
              ((FordRecursiveQuadruple P) 0)
            else BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 2)))) W Z
      simp only [show Even (0:Nat) from by decide,ite_true,pow_zero,one_mul]
      rw [h02,h20]
      simpa only [hqs,Nat.cast_add,Bool.false_eq_true,ite_false] using finish0 P.q₁ P.q₂ hr hs a
          b false U W Z
        (by simpa [hqs] using hUc) hWc hZc
    · exact ((by decide : ¬Even (1:Nat)) heven).elim
    · norm_num [heven,h10,h20,h01,h02,GaussianRealPoint,pow_succ] at hcw hcz
      have hwa := FordEndpointProof.hwaAt838 P a b wa wb hcw
      have hwb := FordEndpointProof.hwbAt842 P hqsR a b wa wb hcw
      have hza := FordEndpointProof.hzaAt846 P a b za zb hcz
      have hzb := FordEndpointProof.hzbAt850 P a b za zb hcz
      subst wa wb za zb
      change package U
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^2 *
          (if Even (2:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 0)
              ((FordRecursiveQuadruple P) 2)
            else BandVectors.1 ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple P) 0))))
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^2 *
          (if Even (2:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 2)
              ((FordRecursiveQuadruple P) 0)
            else BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 2)))) W Z
      simp only [show Even (2:Nat) from by decide,ite_true,h02,h20]
      have dR : (⟨0,1⟩ : GaussianInt)^2 * ⟨-(P.q₂:Int),-(P.q:Int)⟩ = ⟨P.q₂,P.q⟩ := by
        ext <;> norm_num [pow_succ]
      have dL : (⟨0,1⟩ : GaussianInt)^2 * ⟨-(P.q:Int),P.q₂⟩ = ⟨P.q,-(P.q₂:Int)⟩ := by
        ext <;> norm_num [pow_succ]
      rw [dR,dL]
      simpa only [hqs,Nat.cast_add,eq_self,ite_true] using finish0 P.q₁ P.q₂ hr hs a b true U W Z
        (by simpa [hqs] using hUc) (by simpa [hqs] using hWc) (by simpa [hqs] using hZc)
    · exact ((by decide : ¬Even (3:Nat)) heven).elim
  · obtain ⟨wa,wb,hWc⟩ := norm1 W hW
    obtain ⟨za,zb,hZc⟩ := norm2 Z (by simpa [hodd] using hZ)
    have hccw := (sameobs W P.q₁ wa wb hr hWc).2.2
    have hccz := (sameobs Z P.q₂ za zb hs hZc).2.2
    rw [hccw,hcu] at hcw
    rw [hccz,hcu] at hcz
    fin_cases s
    · exact (hodd (by decide)).elim
    · norm_num [hodd,h10,h20,h01,h02,GaussianRealPoint,pow_succ] at hcw hcz
      have hwa := FordEndpointProof.hwaAt881 P a b wa wb hcw
      have hwb := FordEndpointProof.hwbAt885 P hqsR a b wa wb hcw
      have hza := FordEndpointProof.hzaAt889 P a b za zb hcz
      have hzb := FordEndpointProof.hzbAt893 P a b za zb hcz
      subst wa wb za zb
      change package U
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^1 *
          (if Even (1:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 0)
              ((FordRecursiveQuadruple P) 1)
            else BandVectors.1 ((FordRecursiveQuadruple P) 1) ((FordRecursiveQuadruple P) 0))))
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^1 *
          (if Even (1:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 1)
              ((FordRecursiveQuadruple P) 0)
            else BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 1)))) W Z
      simp only [show ¬Even (1:Nat) from by decide,ite_false,h10,h01]
      have dR : (⟨0,1⟩ : GaussianInt)^1 * ⟨P.q,P.q₁⟩ = ⟨-(P.q₁:Int),P.q⟩ := by
        ext <;> norm_num [pow_succ]
      have dL : (⟨0,1⟩ : GaussianInt)^1 * ⟨-(P.q₁:Int),P.q⟩ = ⟨-(P.q:Int),-(P.q₁:Int)⟩ := by
        ext <;> norm_num [pow_succ]
      rw [dR,dL]
      simpa only [hqs,Nat.cast_add,Bool.false_eq_true,ite_false] using finish1 P.q₁ P.q₂ hr hs a
          b false U W Z
        (by simpa [hqs] using hUc) hWc hZc
    · exact (hodd (by decide)).elim
    · norm_num [hodd,h10,h20,h01,h02,GaussianRealPoint,pow_succ] at hcw hcz
      have hwa := FordEndpointProof.hwaAt917 P a b wa wb hcw
      have hwb := FordEndpointProof.hwbAt921 P a b wa wb hcw
      have hza := FordEndpointProof.hzaAt924 P a b za zb hcz
      have hzb := FordEndpointProof.hzbAt928 P hqsR a b za zb hcz
      subst wa wb za zb
      change package U
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^3 *
          (if Even (3:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 0)
              ((FordRecursiveQuadruple P) 1)
            else BandVectors.1 ((FordRecursiveQuadruple P) 1) ((FordRecursiveQuadruple P) 0))))
        (TileTranslation U ((⟨0,1⟩ : GaussianInt)^3 *
          (if Even (3:Nat) then BandVectors.1 ((FordRecursiveQuadruple P) 1)
              ((FordRecursiveQuadruple P) 0)
            else BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 1)))) W Z
      simp only [show ¬Even (3:Nat) from by decide,ite_false,h10,h01]
      have dR : (⟨0,1⟩ : GaussianInt)^3 * ⟨P.q,P.q₁⟩ = ⟨P.q₁,-(P.q:Int)⟩ := by
        ext <;> norm_num [pow_succ]
      have dL : (⟨0,1⟩ : GaussianInt)^3 * ⟨-(P.q₁:Int),P.q⟩ = ⟨P.q,P.q₁⟩ := by
        ext <;> norm_num [pow_succ]
      rw [dR,dL]
      simpa only [hqs,Nat.cast_add,eq_self,ite_true] using finish1 P.q₁ P.q₂ hr hs a b true U W Z
        (by simpa [hqs] using hUc) (by simpa [hqs] using hWc) (by simpa [hqs] using hZc)

end ApollonianSuperharmonic

end
