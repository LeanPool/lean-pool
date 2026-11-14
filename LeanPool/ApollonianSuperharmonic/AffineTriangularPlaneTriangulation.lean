/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module
public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
-- [TABLET NODE: AffineTriangularPlaneTriangulation]
/-!
# AffineTriangularPlaneTriangulation
Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/
@[expose] public section
namespace ApollonianSuperharmonic
namespace AffineTriangulationLemmas
private theorem symm_adj :
    ∀ (a : (Int × Int)), ∀ (b : (Int × Int)), TriangularLatticeAdjacent a b ↔
        TriangularLatticeAdjacent b a := by
  classical
  intro a b
  simp only [TriangularLatticeAdjacent, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  omega
private theorem irrefl_adj :
    ∀ (a : (Int × Int)), ¬ TriangularLatticeAdjacent a a := by
  classical
  intro a
  simp [TriangularLatticeAdjacent, Prod.ext_iff]
private theorem finite_adj :
    ∀ (a : (Int × Int)), Set.Finite {b | TriangularLatticeAdjacent a b} := by
  classical
  intro a
  apply (Set.toFinite ({a + (1, 0), a + (0, 1), a + (-1, -1),
    a + (-1, 0), a + (0, -1), a + (1, 1)} : Set (Int × Int))).subset
  intro b hb
  simp only [Set.mem_ofPred_eq, TriangularLatticeAdjacent] at hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hb with h | h | h | h | h | h
  all_goals simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_add, Prod.snd_add] at h ⊢
  all_goals omega
private theorem distinct_fv :
    let fv : (Sum (Int × Int) (Int × Int)) → Fin 3 → (Int × Int) := fun
      | Sum.inl x => ![x, x + (1, 0), x - (0, 1)]
      | Sum.inr x => ![x, x - (1, 0), x + (0, 1)]
    ∀ (f : (Sum (Int × Int) (Int × Int))), Function.Injective (fv f) := by
  classical
  intro fv f i j h
  cases f <;> fin_cases i <;> fin_cases j <;>
    simp [fv, Prod.ext_iff] at h ⊢ <;> omega
private theorem edges_fv :
    let fv : (Sum (Int × Int) (Int × Int)) → Fin 3 → (Int × Int) := fun
      | Sum.inl x => ![x, x + (1, 0), x - (0, 1)]
      | Sum.inr x => ![x, x - (1, 0), x + (0, 1)]
    ∀ (f : (Sum (Int × Int) (Int × Int))), ∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) →
        (TriangularLatticeAdjacent (fv f i) (fv f j)) := by
  classical
  intro fv f i j h
  cases f <;> fin_cases i <;> fin_cases j <;>
    simp [fv, TriangularLatticeAdjacent, Prod.ext_iff] at h ⊢
private theorem two_faces :
    let fv : (Sum (Int × Int) (Int × Int)) → Fin 3 → (Int × Int) := fun
      | Sum.inl x => ![x, x + (1, 0), x - (0, 1)]
      | Sum.inr x => ![x, x - (1, 0), x + (0, 1)]
    ∀ (a : (Int × Int)), ∀ (b : (Int × Int)), (TriangularLatticeAdjacent a b) → (∃ f g : (Sum
        (Int × Int) (Int × Int)), f ≠ g ∧
        ((∃ i, fv f i = a) ∧ (∃ i, fv f i = b)) ∧
        ((∃ i, fv g i = a) ∧ (∃ i, fv g i = b)) ∧
        ∀ h : (Sum (Int × Int) (Int × Int)),
          ((∃ i, fv h i = a) ∧ (∃ i, fv h i = b)) → h = f ∨ h = g) := by
  classical
  intro fv a b hab
  have classify (a b : (Int × Int)) (f g : (Sum (Int × Int) (Int × Int)))
      (hf : f ≠ g)
      (hi : (∃ i, fv f i = a) ∧ (∃ i, fv f i = b))
      (hj : (∃ i, fv g i = a) ∧ (∃ i, fv g i = b))
      (hunique : ∀ h : (Sum (Int × Int) (Int × Int)), ∀ i j : Fin 3,
        fv h i = a → fv h j = b → h = f ∨ h = g) :
      ∃ f g : (Sum (Int × Int) (Int × Int)), f ≠ g ∧
        ((∃ i, fv f i = a) ∧ (∃ i, fv f i = b)) ∧
        ((∃ i, fv g i = a) ∧ (∃ i, fv g i = b)) ∧
        ∀ h : (Sum (Int × Int) (Int × Int)), ((∃ i, fv h i = a) ∧ (∃ i, fv h i = b)) →
          h = f ∨ h = g := by
    exact ⟨f, g, hf, hi, hj, fun h ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => hunique h i j hi hj⟩
  let incidence : (Int × Int) → (Int × Int) → Prop := fun a b =>
    ∃ f g : (Sum (Int × Int) (Int × Int)), f ≠ g ∧
      ((∃ i, fv f i = a) ∧ (∃ i, fv f i = b)) ∧
      ((∃ i, fv g i = a) ∧ (∃ i, fv g i = b)) ∧
      ∀ h, ((∃ i, fv h i = a) ∧ (∃ i, fv h i = b)) → h = f ∨ h = g
  have flip {a b : Int × Int} (h : incidence b a) : incidence a b := by
    rcases h with ⟨f, g, hfg, hf, hg, hunique⟩
    exact ⟨f, g, hfg, ⟨hf.2, hf.1⟩, ⟨hg.2, hg.1⟩,
      fun h hh => hunique h ⟨hh.2, hh.1⟩⟩
  have positive (a b : Int × Int)
      (hab : b - a = ((1, 0) : Int × Int) ∨
        b - a = ((0, 1) : Int × Int) ∨ b - a = ((1, 1) : Int × Int)) :
      incidence a b := by
    rcases hab with h | h | h
    · apply classify a b (Sum.inl a) (Sum.inr b)
      · simp
      · refine ⟨⟨0, rfl⟩, ⟨1, ?_⟩⟩
        simp [fv, Prod.ext_iff] at h ⊢
        omega
      · refine ⟨⟨1, ?_⟩, ⟨0, rfl⟩⟩
        simp [fv, Prod.ext_iff] at h ⊢
        omega
      · intro f i j hi hj
        cases f <;> fin_cases i <;> fin_cases j <;>
          simp [fv, Prod.ext_iff] at h hi hj ⊢ <;> omega
    · apply classify a b (Sum.inr a) (Sum.inl b)
      · simp
      · refine ⟨⟨0, rfl⟩, ⟨2, ?_⟩⟩
        simp [fv, Prod.ext_iff] at h ⊢
        omega
      · refine ⟨⟨2, ?_⟩, ⟨0, rfl⟩⟩
        simp [fv, Prod.ext_iff] at h ⊢
        omega
      · intro f i j hi hj
        cases f <;> fin_cases i <;> fin_cases j <;>
          simp [fv, Prod.ext_iff] at h hi hj ⊢ <;> omega
    · apply classify a b (Sum.inl (a + (0, 1))) (Sum.inr (a + (1, 0)))
      · simp
      · refine ⟨⟨2, ?_⟩, ⟨1, ?_⟩⟩
        all_goals
          first
          | solve | simp [fv, Prod.ext_iff] at h ⊢
          | simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Fin.isValue,
              Matrix.cons_val_one, add_sub_cancel_right, Matrix.cons_val_zero, Prod.fst_add,
              add_zero, Prod.snd_add, fv] at h ⊢
            omega
      · refine ⟨⟨1, ?_⟩, ⟨2, ?_⟩⟩
        all_goals
          first
          | solve | simp [fv, Prod.ext_iff] at h ⊢
          | simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Fin.isValue, Matrix.cons_val,
              Prod.fst_add, add_zero, Prod.snd_add, fv] at h ⊢
            omega
      · intro f i j hi hj
        cases f <;> fin_cases i <;> fin_cases j <;>
          simp [fv, Prod.ext_iff] at h hi hj ⊢ <;> omega
  rcases hab with h | h | h | h | h | h
  · exact positive a b (Or.inl h)
  · exact positive a b (Or.inr (Or.inl h))
  · apply flip (positive b a ?_)
    right; right
    simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at h ⊢
    omega
  · apply flip (positive b a ?_)
    left
    simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at h ⊢
    omega
  · apply flip (positive b a ?_)
    right; left
    simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at h ⊢
    omega
  · exact positive a b (Or.inr (Or.inr h))
private theorem int_walk :
    ∀ {R : (Int × Int) → (Int × Int) → Prop}, (∀ a b, R a b → R b a) → (∀ (f : Int → (Int ×
        Int)), (∀ k, R (f k) (f (k + 1))) → (∀ (m : Int), ∀ (n : Int), Relation.ReflTransGen R (f
        m) (f n))) := by
  classical
  intro R hs f step m n
  have reverse {x y : (Int × Int)} (h : Relation.ReflTransGen R x y) :
      Relation.ReflTransGen R y x := by
    induction h with
    | refl => exact .refl
    | @tail b c hbc hstep ih => exact ih.head (hs _ _ hstep)
  have forward (m n : Int) (hmn : m ≤ n) :
      Relation.ReflTransGen R (f m) (f n) := by
    induction n, hmn using Int.leInduction with
    | base => exact .refl
    | succ n hn ih => exact ih.tail (step n)
  by_cases hmn : m ≤ n
  · exact forward m n hmn
  · exact reverse (forward n m (by omega))
private theorem deletion_walk :
    (∀ (a : (Int × Int)), ∀ (b : (Int × Int)), TriangularLatticeAdjacent a b ↔
        TriangularLatticeAdjacent b a) → ((∀ {R : (Int × Int) → (Int × Int) → Prop}, (∀ a b, R a
        b → R b a) → (∀ (f : Int → (Int × Int)), (∀ k, R (f k) (f (k + 1))) → (∀ (m : Int), ∀ (n
        : Int), Relation.ReflTransGen R (f m) (f n)))) → (∀ (D : Finset (Int × Int)), (D.card <
        3) → (∀ (a : (Int × Int)), ∀ (b : (Int × Int)), (a ∉ D) → ((b ∉ D) → (∃ p : List (Int ×
        Int), p.head? = some a ∧ p.getLast? = some b ∧
        (∀ x ∈ p, x ∉ D) ∧
        ∀ x y : (Int × Int), ∀ l₁ l₂ : List (Int × Int),
          p = l₁ ++ x :: y :: l₂ → TriangularLatticeAdjacent x y))))) := by
  classical
  intro symm_adj int_walk D hD a b ha hb
  classical
  let R : (Int × Int) → (Int × Int) → Prop := fun x y => TriangularLatticeAdjacent x y ∧ x ∉ D ∧
      y ∉ D
  have symmR (x y : (Int × Int)) (h : R x y) : R y x :=
    ⟨(symm_adj x y).mp h.1, h.2.2, h.2.1⟩
  have reverse {x y : (Int × Int)} (h : Relation.ReflTransGen R x y) :
      Relation.ReflTransGen R y x := by
    induction h with
    | refl => exact .refl
    | @tail b c hbc hstep ih => exact ih.head (symmR _ _ hstep)
  have column (k : Int) : ∃ r : Int,
      (r = k - 1 ∨ r = k ∨ r = k + 1) ∧ ∀ t : Int, (r, t) ∉ D := by
    have triple : ({k - 1, k, k + 1} : Finset Int).card = 3 := by
      have h1 : k - 1 ≠ k := by omega
      have h2 : k - 1 ≠ k + 1 := by omega
      have h3 : k ≠ k + 1 := by omega
      simp [h1, h2, h3]
    have hsub : ¬ ({k - 1, k, k + 1} : Finset Int) ⊆ D.image Prod.fst := by
      intro h
      have hh := Finset.card_le_card h
      have hi := Finset.card_image_le (s := D) (f := Prod.fst)
      omega
    obtain ⟨r, hr, hd⟩ := Finset.not_subset.mp hsub
    refine ⟨r, ?_, ?_⟩
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
    · intro t ht
      exact hd (Finset.mem_image.mpr ⟨(r, t), ht, rfl⟩)
  obtain ⟨r, hr, hrclean⟩ := column a.1
  obtain ⟨s, hs, hsclean⟩ := column b.1
  obtain ⟨h, _, hh⟩ := (Set.infinite_univ : (Set.univ : Set Int).Infinite).exists_notMem_finset
    (D.image Prod.snd)
  have rowclean (k : Int) : (k, h) ∉ D := by
    intro hk
    exact hh (Finset.mem_image.mpr ⟨(k, h), hk, rfl⟩)
  have endpoint (x : (Int × Int)) (hx : x ∉ D) (r : Int)
      (hr : r = x.1 - 1 ∨ r = x.1 ∨ r = x.1 + 1)
      (hc : ∀ t : Int, (r, t) ∉ D) : Relation.ReflTransGen R x (r, x.2) := by
    rcases hr with hr | hr | hr
    · apply Relation.ReflTransGen.single
      refine ⟨?_, hx, hc _⟩
      simp [TriangularLatticeAdjacent, Prod.ext_iff]
      omega
    · have heq : x = (r, x.2) := Prod.ext hr.symm rfl
      rw [heq]
    · apply Relation.ReflTransGen.single
      refine ⟨?_, hx, hc _⟩
      simp [TriangularLatticeAdjacent, Prod.ext_iff]
      omega
  have vertical (r : Int) (hc : ∀ t : Int, (r, t) ∉ D) (m n : Int) :
      Relation.ReflTransGen R (r, m) (r, n) := by
    apply int_walk symmR (fun t => (r, t)) (m := m) (n := n)
    intro k
    refine ⟨?_, hc _, hc _⟩
    simp [TriangularLatticeAdjacent, Prod.ext_iff]
  have horizontal : Relation.ReflTransGen R (r, h) (s, h) := by
    apply int_walk symmR (fun k => (k, h)) (m := r) (n := s)
    intro k
    refine ⟨?_, rowclean _, rowclean _⟩
    simp [TriangularLatticeAdjacent, Prod.ext_iff]
  have finalStep : Relation.ReflTransGen R (s, b.2) b :=
    reverse (endpoint b hb s hs hsclean)
  have route : Relation.ReflTransGen R a b :=
    (endpoint a ha r hr hrclean).trans
      ((vertical r hrclean a.2 h).trans
        (horizontal.trans ((vertical s hsclean h b.2).trans finalStep)))
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen route
  refine ⟨a :: l, rfl, ?_, ?_, ?_⟩
  · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a l), hlast]
  · exact hl.induction (fun x => x ∉ D) (a :: l) (fun {_ _} h _ => h.2.2) (fun _ => ha)
  · intro x y l₁ l₂ heq
    exact ((List.isChain_iff_forall_rel_of_append_cons_cons.mp hl) heq).1
private theorem coord_injective :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    Function.Injective coord := by
  classical
  intro coord x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [coord] at h1 h2
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
private theorem segment_homeo :
    ∀ (a : (Real × Real)), ∀ (b : (Real × Real)), (a ≠ b) → (∃ h : (Set.Icc (0 : Real) 1) ≃ₜ
        segment Real a b,
        ((h ⟨0, by norm_num⟩ : segment Real a b) : (Real × Real)) = a ∧
        ((h ⟨1, by norm_num⟩ : segment Real a b) : (Real × Real)) = b) := by
  classical
  intro a b hne
  let g : Set.Icc (0 : Real) 1 → segment Real a b := fun t =>
    ⟨AffineMap.lineMap a b (t : Real), lineMap_mem_segment Real a b t.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro s t h
      apply Subtype.ext
      exact AffineMap.lineMap_injective Real hne (congrArg Subtype.val h)
    · intro p
      have hp : (p : (Real × Real)) ∈ AffineMap.lineMap a b '' Set.Icc (0 : Real) 1 := by
        simpa only [segment_eq_image_lineMap] using p.property
      obtain ⟨t, ht, heq⟩ := hp
      exact ⟨⟨t, ht⟩, Subtype.ext heq⟩
  let e := Equiv.ofBijective g hg
  have hc : Continuous (e : Set.Icc (0 : Real) 1 → segment Real a b) := by
    change Continuous g
    fun_prop
  refine ⟨hc.homeoOfEquivCompactToT2, ?_, ?_⟩
  · change AffineMap.lineMap a b (0 : Real) = a
    simp
  · change AffineMap.lineMap a b (1 : Real) = b
    simp
private theorem arc_homeo :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    (Function.Injective coord) → (
    let arc (a b : (Int × Int)) : Set (Real × Real) := shear '' segment Real (coord a) (coord b)
    (∀ (a : (Real × Real)), ∀ (b : (Real × Real)), (a ≠ b) → (∃ h : (Set.Icc (0 : Real) 1) ≃ₜ
        segment Real a b, ((h ⟨0, by norm_num⟩ : segment Real a b) : (Real × Real)) = a ∧ ((h ⟨1,
        by norm_num⟩ : segment Real a b) : (Real × Real)) = b)) → (∀ (a : (Int × Int)), ∀ (b :
        (Int × Int)), (a ≠ b) → (∃ h : (Set.Icc (0 : Real) 1) ≃ₜ arc a b,
        ((h ⟨0, by norm_num⟩ : arc a b) : (Real × Real)) = shear (coord a) ∧
        ((h ⟨1, by norm_num⟩ : arc a b) : (Real × Real)) = shear (coord b)))) := by
  classical
  intro coord shear coord_injective arc segment_homeo a b hne
  obtain ⟨h, h0, h1⟩ := segment_homeo (coord a) (coord b) (fun h => hne (coord_injective h))
  refine ⟨h.trans (shear.image _), ?_, ?_⟩
  · change shear ((h ⟨0, by norm_num⟩ : segment Real (coord a) (coord b)) : (Real × Real)) = _
    rw [h0]
  · change shear ((h ⟨1, by norm_num⟩ : segment Real (coord a) (coord b)) : (Real × Real)) = _
    rw [h1]
private theorem open_T :
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    IsOpen T := by
  classical
  intro T
  exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
private theorem closed_C :
    let C : Set (Real × Real) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
    IsClosed C := by
  classical
  intro C
  exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
private theorem convex_T :
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    Convex Real T := by
  classical
  intro T
  exact (convex_halfSpace_gt (LinearMap.fst Real Real Real).isLinear 0).inter
    ((convex_halfSpace_gt (LinearMap.snd Real Real Real).isLinear 0).inter
      (convex_halfSpace_lt ((LinearMap.fst Real Real Real) +
        (LinearMap.snd Real Real Real)).isLinear 1))
private theorem connected_T :
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    (Convex Real T) → (IsConnected T) := by
  classical
  intro T convex_T
  exact convex_T.isConnected ⟨(1 / 3, 1 / 3), by norm_num [T]⟩
private theorem closure_T :
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    let C : Set (Real × Real) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
    (IsClosed C) → (closure T = C) := by
  classical
  intro T C closed_C
  apply Set.Subset.antisymm
  · apply closed_C.closure_subset_iff.mpr
    intro p hp
    exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  · intro p hp
    have hsegment : openSegment Real p (1 / 3, 1 / 3) ⊆ T := by
      intro q hq
      rcases hq with ⟨a, b, ha, hb, hab, rfl⟩
      simp only [C, Set.mem_ofPred_eq] at hp
      simp only [T, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      refine ⟨?_, ?_, ?_⟩ <;>
        nlinarith [mul_nonneg ha.le hp.1, mul_nonneg ha.le hp.2.1,
          mul_nonneg ha.le (show 0 ≤ 1 - (p.1 + p.2) by linarith [hp.2.2])]
    apply closure_mono hsegment
    exact segment_subset_closure_openSegment (left_mem_segment Real p (1 / 3, 1 / 3))
private theorem boundary_T :
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    let C : Set (Real × Real) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
    (IsOpen T) → ((closure T = C) → (frontier T =
      segment Real ((0, 0) : (Real × Real)) (1, 0) ∪
      segment Real ((1, 0) : (Real × Real)) (0, 1) ∪
      segment Real ((0, 1) : (Real × Real)) (0, 0))) := by
  classical
  intro T C open_T closure_T
  rw [frontier, open_T.interior_eq, closure_T]
  ext p
  simp only [Set.mem_sdiff, C, T, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨⟨hx, hy, hsum⟩, hnot⟩
    have heq : p.2 = 0 ∨ p.1 + p.2 = 1 ∨ p.1 = 0 := by
      by_contra h
      simp only [not_or] at h
      exact hnot ⟨lt_of_le_of_ne hx (Ne.symm h.2.2),
        lt_of_le_of_ne hy (Ne.symm h.1), lt_of_le_of_ne hsum h.2.1⟩
    rcases heq with heq | heq | heq
    · left; left
      rw [segment_eq_image' Real]
      refine ⟨p.1, ⟨hx, by linarith⟩, ?_⟩
      ext <;> simp [heq]
    · left; right
      rw [segment_eq_image' Real]
      refine ⟨p.2, ⟨hy, by linarith⟩, ?_⟩
      ext <;> simp; linarith
    · right
      rw [segment_eq_image' Real]
      refine ⟨1 - p.2, ⟨by linarith, by linarith⟩, ?_⟩
      ext <;> simp [heq]
  · intro hp
    rcases hp with (hp | hp) | hp
    all_goals rw [segment_eq_image' Real] at hp
    all_goals rcases hp with ⟨t, ⟨h0, h1⟩, rfl⟩
    all_goals simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    all_goals norm_num at h0 h1 ⊢
    all_goals constructor
    all_goals assumption
private noncomputable abbrev tile :
    Sum (Int × Int) (Int × Int) → (Real × Real) ≃ₜ (Real × Real) := fun
  | Sum.inl x => {
      toFun := fun q => ((x.1 : Real) + q.1, (x.2 : Real) - q.2)
      invFun := fun p => (p.1 - (x.1 : Real), (x.2 : Real) - p.2)
      left_inv := by intro p; ext <;> dsimp <;> ring
      right_inv := by intro p; ext <;> dsimp <;> ring
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  | Sum.inr x => {
      toFun := fun q => ((x.1 : Real) - q.1, (x.2 : Real) + q.2)
      invFun := fun p => ((x.1 : Real) - p.1, p.2 - (x.2 : Real))
      left_inv := by intro p; ext <;> dsimp <;> ring
      right_inv := by intro p; ext <;> dsimp <;> ring
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
private theorem tile_segment :
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    ∀ (f : (Sum (Int × Int) (Int × Int))), ∀ (a : (Real × Real)), ∀ (b : (Real × Real)), tile f
        '' segment Real a b = segment Real (tile f a) (tile f b) := by
  classical
  intro tile f a b
  rw [segment_eq_image' Real, segment_eq_image' Real, Set.image_image]
  congr 1
  funext t
  cases f <;> ext <;>
    simp [tile, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
private theorem tile_vertices :
    let fv : (Sum (Int × Int) (Int × Int)) → Fin 3 → (Int × Int) := fun
      | Sum.inl x => ![x, x + (1, 0), x - (0, 1)]
      | Sum.inr x => ![x, x - (1, 0), x + (0, 1)]
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    ∀ (f : (Sum (Int × Int) (Int × Int))), tile f (0, 0) = coord (fv f 0) ∧
      tile f (1, 0) = coord (fv f 1) ∧
      tile f (0, 1) = coord (fv f 2) := by
  classical
  intro fv coord tile f
  cases f <;> simp [tile, fv, coord]
private theorem boundary_region :
    let fv : (Sum (Int × Int) (Int × Int)) → Fin 3 → (Int × Int) := fun
      | Sum.inl x => ![x, x + (1, 0), x - (0, 1)]
      | Sum.inr x => ![x, x - (1, 0), x + (0, 1)]
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let arc (a b : (Int × Int)) : Set (Real × Real) := shear '' segment Real (coord a) (coord b)
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    (frontier T = segment Real ((0, 0) : (Real × Real)) (1, 0) ∪ segment Real ((1, 0) : (Real ×
        Real)) (0, 1) ∪ segment Real ((0, 1) : (Real × Real)) (0, 0)) → (
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    let region (f : (Sum (Int × Int) (Int × Int))) : Set (Real × Real) := shear '' tile f '' T
    (∀ (f : (Sum (Int × Int) (Int × Int))), ∀ (a : (Real × Real)), ∀ (b : (Real × Real)), tile f
        '' segment Real a b = segment Real (tile f a) (tile f b)) → ((∀ (f : (Sum (Int × Int)
        (Int × Int))), tile f (0, 0) = coord (fv f 0) ∧ tile f (1, 0) = coord (fv f 1) ∧ tile f
        (0, 1) = coord (fv f 2)) → (∀ (f : (Sum (Int × Int) (Int × Int))), frontier (region f) =
      arc (fv f 0) (fv f 1) ∪ arc (fv f 1) (fv f 2) ∪ arc (fv f 2) (fv f 0)))) := by
  classical
  intro fv coord shear arc T boundary_T tile region tile_segment tile_vertices f
  dsimp only [region]
  rw [← shear.image_frontier, ← (tile f).image_frontier, boundary_T]
  simp only [Set.image_union, tile_segment]
  rw [(tile_vertices f).1, (tile_vertices f).2.1, (tile_vertices f).2.2]
private theorem open_region :
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    (IsOpen T) → (
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    let region (f : (Sum (Int × Int) (Int × Int))) : Set (Real × Real) := shear '' tile f '' T
    ∀ (f : (Sum (Int × Int) (Int × Int))), IsOpen (region f)) := by
  classical
  intro shear T open_T tile region f
  exact shear.isOpenMap _ ((tile f).isOpenMap _ open_T)
private theorem connected_region :
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    (IsConnected T) → (
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    let region (f : (Sum (Int × Int) (Int × Int))) : Set (Real × Real) := shear '' tile f '' T
    ∀ (f : (Sum (Int × Int) (Int × Int))), IsConnected (region f)) := by
  classical
  intro shear T connected_T tile region f
  exact (connected_T.image (tile f) (tile f).continuous.continuousOn).image
      shear shear.continuous.continuousOn
private theorem closed_cover :
    let C : Set (Real × Real) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    ∀ (p : (Real × Real)), ∃ f : (Sum (Int × Int) (Int × Int)), p ∈ tile f '' C := by
  classical
  intro C tile p
  let m : Int := ⌊p.1⌋
  let n : Int := ⌊p.2⌋
  have hm0 : (m : Real) ≤ p.1 := Int.floor_le p.1
  have hm1 : p.1 < (m : Real) + 1 := Int.lt_floor_add_one p.1
  have hn0 : (n : Real) ≤ p.2 := Int.floor_le p.2
  have hn1 : p.2 < (n : Real) + 1 := Int.lt_floor_add_one p.2
  by_cases h : p.1 - (m : Real) + ((n : Real) + 1 - p.2) ≤ 1
  · refine ⟨Sum.inl (m, n + 1), (p.1 - (m : Real), (n : Real) + 1 - p.2), ?_, ?_⟩
    · simp only [C, Set.mem_ofPred_eq]
      exact ⟨by linarith, by linarith, h⟩
    · ext <;> simp [tile]
  · refine ⟨Sum.inr (m + 1, n), ((m : Real) + 1 - p.1, p.2 - (n : Real)), ?_, ?_⟩
    · simp only [C, Set.mem_ofPred_eq]
      exact ⟨by linarith, by linarith, by linarith⟩
    · ext <;> simp [tile]
private theorem strip_unique :
    ∀ (m : Int), ∀ (n : Int), ∀ (r : Real), ((m : Real) < r ∧ r < (m : Real) + 1) → (((n : Real)
        < r ∧ r < (n : Real) + 1) → (m = n)) := by
  classical
  intro m n r hm hn
  rcases lt_trichotomy m n with h | h | h
  · have h' : (m : Real) + 1 ≤ (n : Real) := by exact_mod_cast (show m + 1 ≤ n by omega)
    linarith
  · exact h
  · have h' : (n : Real) + 1 ≤ (m : Real) := by exact_mod_cast (show n + 1 ≤ m by omega)
    linarith
private theorem tiles_disjoint :
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    (∀ (m : Int), ∀ (n : Int), ∀ (r : Real), ((m : Real) < r ∧ r < (m : Real) + 1) → (((n : Real)
        < r ∧ r < (n : Real) + 1) → (m = n))) → (Pairwise fun f g => Disjoint (tile f '' T) (tile
        g '' T)) := by
  classical
  intro T tile strip_unique f g hfg
  apply Set.disjoint_left.mpr
  rintro p ⟨u, hu, hup⟩ ⟨v, hv, hvp⟩
  have heq : tile f u = tile g v := hup.trans hvp.symm
  have hu1 : u.1 < 1 := by linarith [hu.1, hu.2.1, hu.2.2]
  have hu2 : u.2 < 1 := by linarith [hu.1, hu.2.1, hu.2.2]
  have hv1 : v.1 < 1 := by linarith [hv.1, hv.2.1, hv.2.2]
  have hv2 : v.2 < 1 := by linarith [hv.1, hv.2.1, hv.2.2]
  cases f with
  | inl x =>
    cases g with
    | inl y =>
      simp only [tile, Prod.ext_iff] at heq
      dsimp at heq
      have hx : x.1 = y.1 := strip_unique x.1 y.1 ((x.1 : Real) + u.1)
        ⟨by linarith [hu.1], by linarith⟩ ⟨by linarith [hv.1, heq.1], by linarith [heq.1]⟩
      have hy : x.2 - 1 = y.2 - 1 := strip_unique (x.2 - 1) (y.2 - 1) ((x.2 : Real) - u.2)
        ⟨by push_cast; linarith, by push_cast; linarith [hu.2.1]⟩
        ⟨by push_cast; linarith [heq.2], by push_cast; linarith [hv.2.1, heq.2]⟩
      exact hfg (congrArg Sum.inl (Prod.ext hx (by omega)))
    | inr y =>
      simp only [tile, Prod.ext_iff] at heq
      dsimp at heq
      have hx : x.1 = y.1 - 1 := strip_unique x.1 (y.1 - 1) ((x.1 : Real) + u.1)
        ⟨by linarith [hu.1], by linarith⟩
        ⟨by push_cast; linarith [heq.1], by push_cast; linarith [hv.1, heq.1]⟩
      have hy : x.2 - 1 = y.2 := strip_unique (x.2 - 1) y.2 ((x.2 : Real) - u.2)
        ⟨by push_cast; linarith, by push_cast; linarith [hu.2.1]⟩
        ⟨by linarith [hv.2.1, heq.2], by linarith [heq.2]⟩
      have hx' : (x.1 : Real) = (y.1 : Real) - 1 := by exact_mod_cast hx
      have hy' : (x.2 : Real) - 1 = (y.2 : Real) := by exact_mod_cast hy
      linarith [hu.2.2, hv.2.2, heq.1, heq.2]
  | inr x =>
    cases g with
    | inl y =>
      simp only [tile, Prod.ext_iff] at heq
      dsimp at heq
      have hx : x.1 - 1 = y.1 := strip_unique (x.1 - 1) y.1 ((x.1 : Real) - u.1)
        ⟨by push_cast; linarith, by push_cast; linarith [hu.1]⟩
        ⟨by linarith [hv.1, heq.1], by linarith [heq.1]⟩
      have hy : x.2 = y.2 - 1 := strip_unique x.2 (y.2 - 1) ((x.2 : Real) + u.2)
        ⟨by linarith [hu.2.1], by linarith⟩
        ⟨by push_cast; linarith [heq.2], by push_cast; linarith [hv.2.1, heq.2]⟩
      have hx' : (x.1 : Real) - 1 = (y.1 : Real) := by exact_mod_cast hx
      have hy' : (x.2 : Real) = (y.2 : Real) - 1 := by exact_mod_cast hy
      linarith [hu.2.2, hv.2.2, heq.1, heq.2]
    | inr y =>
      simp only [tile, Prod.ext_iff] at heq
      dsimp at heq
      have hx : x.1 - 1 = y.1 - 1 := strip_unique (x.1 - 1) (y.1 - 1) ((x.1 : Real) - u.1)
        ⟨by push_cast; linarith, by push_cast; linarith [hu.1]⟩
        ⟨by push_cast; linarith [heq.1], by push_cast; linarith [hv.1, heq.1]⟩
      have hy : x.2 = y.2 := strip_unique x.2 y.2 ((x.2 : Real) + u.2)
        ⟨by linarith [hu.2.1], by linarith⟩ ⟨by linarith [hv.2.1, heq.2], by linarith [heq.2]⟩
      exact hfg (congrArg Sum.inr (Prod.ext (by omega) hy))
private theorem regions_disjoint :
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    let region (f : (Sum (Int × Int) (Int × Int))) : Set (Real × Real) := shear '' tile f '' T
    (Pairwise fun f g => Disjoint (tile f '' T) (tile g '' T)) → (Pairwise fun f g => Disjoint
        (region f) (region g)) := by
  classical
  intro shear T tile region tiles_disjoint f g hfg
  exact (tiles_disjoint hfg).image (shear.injective.injOn (s := Set.univ))
    (Set.subset_univ _) (Set.subset_univ _)
private theorem plane_cover :
    let fv : (Sum (Int × Int) (Int × Int)) → Fin 3 → (Int × Int) := fun
      | Sum.inl x => ![x, x + (1, 0), x - (0, 1)]
      | Sum.inr x => ![x, x - (1, 0), x + (0, 1)]
    (∀ (f : (Sum (Int × Int) (Int × Int))), ∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) →
        (TriangularLatticeAdjacent (fv f i) (fv f j))) → (
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let arc (a b : (Int × Int)) : Set (Real × Real) := shear '' segment Real (coord a) (coord b)
    let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
    let C : Set (Real × Real) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
    (closure T = C) → (
    let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
      AffineTriangulationLemmas.tile
    let region (f : (Sum (Int × Int) (Int × Int))) : Set (Real × Real) := shear '' tile f '' T
    (∀ (f : (Sum (Int × Int) (Int × Int))), frontier (region f) = arc (fv f 0) (fv f 1) ∪ arc (fv
        f 1) (fv f 2) ∪ arc (fv f 2) (fv f 0)) → ((∀ (p : (Real × Real)), ∃ f : (Sum (Int × Int)
        (Int × Int)), p ∈ tile f '' C) → (Set.range (fun x => shear (coord x)) ∪
      {p | ∃ a b, TriangularLatticeAdjacent a b ∧ p ∈ arc a b} ∪
      {p | ∃ f, p ∈ region f} = Set.univ)))) := by
  classical
  intro fv edges_fv coord shear arc T C closure_T tile region boundary_region closed_cover
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨q, rfl⟩ := shear.surjective p
  obtain ⟨f, u, hu, huq⟩ := closed_cover q
  rw [← closure_T, closure_eq_self_union_frontier] at hu
  rcases hu with hu | hu
  · exact Or.inr ⟨f, ⟨q, ⟨u, hu, huq⟩, rfl⟩⟩
  · have hp : shear q ∈ frontier (region f) := by
      dsimp only [region]
      rw [← shear.image_frontier, ← (tile f).image_frontier]
      exact ⟨q, ⟨u, hu, huq⟩, rfl⟩
    rw [boundary_region] at hp
    rcases hp with (hp | hp) | hp
    · exact Or.inl (Or.inr ⟨fv f 0, fv f 1, edges_fv f 0 1 (by decide), hp⟩)
    · exact Or.inl (Or.inr ⟨fv f 1, fv f 2, edges_fv f 1 2 (by decide), hp⟩)
    · exact Or.inl (Or.inr ⟨fv f 2, fv f 0, edges_fv f 2 0 (by decide), hp⟩)
private theorem fraction_integer :
    ∀ (m : Int), ∀ (n : Int), ∀ (s : Real), (s ∈ Set.Icc (0 : Real) 1) → (((m : Real) + s = (n :
        Real)) → (s = 0 ∨ s = 1)) := by
  classical
  intro m n s hs h
  have lo : m ≤ n := by exact_mod_cast (show (m : Real) ≤ (n : Real) by linarith [hs.1])
  have hi : n ≤ m + 1 := by
    exact_mod_cast (show (n : Real) ≤ (m : Real) + 1 by linarith [hs.2])
  rcases (show n = m ∨ n = m + 1 by omega) with heq | heq
  · have h' : (n : Real) = (m : Real) := by exact_mod_cast heq
    left; linarith
  · have h' : (n : Real) = (m : Real) + 1 := by exact_mod_cast heq
    right; linarith
private theorem fraction_gap :
    ∀ (m : Int), ∀ (n : Int), ∀ (s : Real), ∀ (t : Real), (s ∈ Set.Icc (0 : Real) 1) → ((t ∈
        Set.Icc (0 : Real) 1) → (((m : Real) + s = (n : Real) + t) → ((m ≠ n) → ((s = 0 ∨ s = 1)
        ∧ (t = 0 ∨ t = 1))))) := by
  classical
  intro m n s t hs ht h hne
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · have h' : (m : Real) + 1 ≤ (n : Real) := by exact_mod_cast (show m + 1 ≤ n by omega)
    exact ⟨Or.inr (by linarith [hs.1, hs.2, ht.1, ht.2]),
      Or.inl (by linarith [hs.1, hs.2, ht.1, ht.2])⟩
  · exact (hne hmn).elim
  · have h' : (n : Real) + 1 ≤ (m : Real) := by exact_mod_cast (show n + 1 ≤ m by omega)
    exact ⟨Or.inl (by linarith [hs.1, hs.2, ht.1, ht.2]),
      Or.inr (by linarith [hs.1, hs.2, ht.1, ht.2])⟩
private theorem endpoint_parameters :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let delta : Fin 3 → (Int × Int) := ![(1, 0), (0, 1), (1, 1)]
    (∀ (m : Int), ∀ (n : Int), ∀ (s : Real), (s ∈ Set.Icc (0 : Real) 1) → (((m : Real) + s = (n :
        Real)) → (s = 0 ∨ s = 1))) → ((∀ (m : Int), ∀ (n : Int), ∀ (s : Real), ∀ (t : Real), (s ∈
        Set.Icc (0 : Real) 1) → ((t ∈ Set.Icc (0 : Real) 1) → (((m : Real) + s = (n : Real) + t)
        → ((m ≠ n) → ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)))))) → (∀ (x : (Int × Int)), ∀ (y : (Int
        × Int)), ∀ (k : Fin 3), ∀ (l : Fin 3), ∀ (s : Real), ∀ (t : Real), (s ∈ Set.Icc (0 :
        Real) 1) → ((t ∈ Set.Icc (0 : Real) 1) → ((coord x + s • (coord (x + delta k) - coord x) =
        coord y + t • (coord (y + delta l) - coord y)) → ((({x, x + delta k} : Set (Int × Int)) ≠
            {y, y + delta l}) → ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1))))))) := by
  classical
  intro coord delta fraction_integer fraction_gap x y k l s t hs ht h hne
  fin_cases k <;> fin_cases l
  all_goals simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Prod.fst_add, add_zero, Prod.snd_add, Int.cast_add, Int.cast_one, Prod.mk_sub_mk,
      sub_self, add_sub_cancel_left, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one,
      Prod.mk_add_mk, Fin.reduceFinMk, Matrix.cons_val, Prod.ext_iff, coord, delta,
      Fin.zero_eta, Int.cast_inj] at h
  · have hx : x.1 ≠ y.1 := by
      intro hx
      have hy : x.2 = y.2 := by exact_mod_cast h.2
      have heq := Prod.ext hx hy
      exact hne (by rw [heq])
    exact fraction_gap x.1 y.1 s t hs ht h.1 hx
  · exact ⟨fraction_integer x.1 y.1 s hs h.1, fraction_integer y.2 x.2 t ht h.2.symm⟩
  · have hte := fraction_integer y.2 x.2 t ht h.2.symm
    refine ⟨?_, hte⟩
    rcases hte with heq | heq
    · exact fraction_integer x.1 y.1 s hs (by linarith [h.1])
    · exact fraction_integer x.1 (y.1 + 1) s hs (by push_cast; linarith [h.1])
  · exact ⟨fraction_integer x.2 y.2 s hs h.2, fraction_integer y.1 x.1 t ht h.1.symm⟩
  · have hx : x.2 ≠ y.2 := by
      intro hx
      have hy : x.1 = y.1 := by exact_mod_cast h.1
      have heq := Prod.ext hy hx
      exact hne (by rw [heq])
    exact fraction_gap x.2 y.2 s t hs ht h.2 hx
  · have hte := fraction_integer y.1 x.1 t ht h.1.symm
    refine ⟨?_, hte⟩
    rcases hte with heq | heq
    · exact fraction_integer x.2 y.2 s hs (by linarith [h.2])
    · exact fraction_integer x.2 (y.2 + 1) s hs (by push_cast; linarith [h.2])
  · have hse := fraction_integer x.2 y.2 s hs h.2
    refine ⟨hse, ?_⟩
    rcases hse with heq | heq
    · exact fraction_integer y.1 x.1 t ht (by linarith [h.1])
    · exact fraction_integer y.1 (x.1 + 1) t ht (by push_cast; linarith [h.1])
  · have hse := fraction_integer x.1 y.1 s hs h.1
    refine ⟨hse, ?_⟩
    rcases hse with heq | heq
    · exact fraction_integer y.2 x.2 t ht (by linarith [h.2])
    · exact fraction_integer y.2 (x.2 + 1) t ht (by push_cast; linarith [h.2])
  · have hx : x.1 ≠ y.1 := by
      intro hx
      have hx' : (x.1 : Real) = (y.1 : Real) := by exact_mod_cast hx
      have hy : x.2 = y.2 := by
        exact_mod_cast (show (x.2 : Real) = (y.2 : Real) by linarith [h.2])
      have heq := Prod.ext hx hy
      exact hne (by rw [heq])
    exact fraction_gap x.1 y.1 s t hs ht h.1 hx
private theorem canonical_intersection :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    (Function.Injective coord) → (
    let delta : Fin 3 → (Int × Int) := ![(1, 0), (0, 1), (1, 1)]
    (∀ (x : (Int × Int)), ∀ (y : (Int × Int)), ∀ (k : Fin 3), ∀ (l : Fin 3), ∀ (s : Real), ∀ (t :
        Real), (s ∈ Set.Icc (0 : Real) 1) → ((t ∈ Set.Icc (0 : Real) 1) → ((coord x + s • (coord
        (x + delta k) - coord x) = coord y + t • (coord (y + delta l) - coord y)) → ((({x,
        x + delta k} : Set (Int × Int)) ≠ {y, y + delta l}) → ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t =
        1)))))) → (∀ (x : (Int × Int)), ∀ (y : (Int × Int)), ∀ (k : Fin 3), ∀ (l : Fin 3), (({x,
        x + delta k} : Set (Int × Int)) ≠ {y, y + delta l}) → (segment Real (coord x) (coord (x +
        delta k)) ∩ segment Real (coord y) (coord (y + delta l)) = coord '' (({x, x + delta k} :
        Set (Int × Int)) ∩ {y, y + delta l})))) := by
  classical
  intro coord coord_injective delta endpoint_parameters x y k l hne
  ext p
  constructor
  · rintro ⟨hp, hq⟩
    rw [segment_eq_image' Real] at hp hq
    obtain ⟨s, hs, hsp⟩ := hp
    obtain ⟨t, ht, htp⟩ := hq
    obtain ⟨hse, hte⟩ := endpoint_parameters x y k l s t hs ht (hsp.trans htp.symm) hne
    have endpoints (a b : (Int × Int)) (u : Real)
        (he : u = 0 ∨ u = 1) (heq : coord a + u • (coord b - coord a) = p) :
        p ∈ coord '' ({a, b} : Set (Int × Int)) := by
      rcases he with rfl | rfl
      · refine ⟨a, by simp, ?_⟩
        simpa using heq
      · refine ⟨b, by simp, ?_⟩
        simpa using heq
    obtain ⟨a, ha, hap⟩ := endpoints x (x + delta k) s hse hsp
    obtain ⟨b, hb, hbp⟩ := endpoints y (y + delta l) t hte htp
    have hab : a = b := coord_injective (hap.trans hbp.symm)
    exact ⟨a, ⟨ha, hab.symm ▸ hb⟩, hap⟩
  · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    constructor
    · rcases ha with rfl | rfl
      · exact left_mem_segment Real _ _
      · exact right_mem_segment Real _ _
    · rcases hb with rfl | rfl
      · exact left_mem_segment Real _ _
      · exact right_mem_segment Real _ _
private theorem orient_edge :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let delta : Fin 3 → (Int × Int) := ![(1, 0), (0, 1), (1, 1)]
    ∀ (a : (Int × Int)), ∀ (b : (Int × Int)), (TriangularLatticeAdjacent a b) → (∃ (k : Fin 3) (x
        : (Int × Int)), ({a, b} : Set (Int × Int)) = {x, x + delta k} ∧
        segment Real (coord a) (coord b) = segment Real (coord x) (coord (x + delta k))) := by
  classical
  intro coord delta a b hab
  rcases hab with h | h | h | h | h | h
  · have heq : b = a + delta 0 := by simp [delta, Prod.ext_iff] at h ⊢; omega
    subst b
    exact ⟨0, a, rfl, rfl⟩
  · have heq : b = a + delta 1 := by simp [delta, Prod.ext_iff] at h ⊢; omega
    subst b
    exact ⟨1, a, rfl, rfl⟩
  · have heq : a = b + delta 2 := by simp [delta, Prod.ext_iff] at h ⊢; omega
    subst a
    exact ⟨2, b, Set.pair_comm _ _, segment_symm Real _ _⟩
  · have heq : a = b + delta 0 := by simp [delta, Prod.ext_iff] at h ⊢; omega
    subst a
    exact ⟨0, b, Set.pair_comm _ _, segment_symm Real _ _⟩
  · have heq : a = b + delta 1 := by simp [delta, Prod.ext_iff] at h ⊢; omega
    subst a
    exact ⟨1, b, Set.pair_comm _ _, segment_symm Real _ _⟩
  · have heq : b = a + delta 2 := by simp [delta, Prod.ext_iff] at h ⊢; omega
    subst b
    exact ⟨2, a, rfl, rfl⟩
private theorem segment_intersections :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let delta : Fin 3 → (Int × Int) := ![(1, 0), (0, 1), (1, 1)]
    (∀ (x : (Int × Int)), ∀ (y : (Int × Int)), ∀ (k : Fin 3), ∀ (l : Fin 3), (({x, x + delta k} :
        Set (Int × Int)) ≠ {y, y + delta l}) → (segment Real (coord x) (coord (x + delta k)) ∩
        segment Real (coord y) (coord (y + delta l)) = coord '' (({x, x + delta k} : Set (Int ×
        Int)) ∩ {y, y + delta l}))) → ((∀ (a : (Int × Int)), ∀ (b : (Int × Int)),
        (TriangularLatticeAdjacent a b) → (∃ (k : Fin 3) (x : (Int × Int)), ({a, b} : Set (Int ×
        Int)) = {x, x + delta k} ∧ segment Real (coord a) (coord b) = segment Real (coord x)
        (coord (x + delta k)))) → (∀ (a : (Int × Int)), ∀ (b : (Int × Int)), ∀ (c : (Int × Int)),
        ∀ (d : (Int × Int)), (TriangularLatticeAdjacent a b) → ((TriangularLatticeAdjacent c d) →
        ((({a, b} : Set (Int × Int)) ≠ {c, d}) → (segment Real (coord a) (coord b) ∩ segment Real
        (coord c) (coord d) =
        coord '' (({a, b} : Set (Int × Int)) ∩ {c, d})))))) := by
  classical
  intro coord delta canonical_intersection orient_edge a b c d hab hcd hne
  obtain ⟨k, x, hp, he⟩ := orient_edge a b hab
  obtain ⟨l, y, hq, hf⟩ := orient_edge c d hcd
  rw [hp, hq] at hne
  rw [he, hf, hp, hq]
  exact canonical_intersection x y k l hne
private theorem arc_symmetric :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let arc (a b : (Int × Int)) : Set (Real × Real) := shear '' segment Real (coord a) (coord b)
    ∀ (a : Int × Int), ∀ (b : Int × Int), arc a b = arc b a := by
  classical
  intro coord shear arc a b
  dsimp [arc]
  rw [segment_symm]
private theorem arc_intersections :
    let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
    let shear : (Real × Real) ≃ₜ (Real × Real) := {
      toFun p := (p.1 - p.2 / 2, p.2)
      invFun p := (p.1 + p.2 / 2, p.2)
      left_inv p := by ext <;> simp
      right_inv p := by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let arc (a b : (Int × Int)) : Set (Real × Real) := shear '' segment Real (coord a) (coord b)
    (∀ (a : (Int × Int)), ∀ (b : (Int × Int)), ∀ (c : (Int × Int)), ∀ (d : (Int × Int)),
        (TriangularLatticeAdjacent a b) → ((TriangularLatticeAdjacent c d) → ((({a, b} : Set (Int
        × Int)) ≠ {c, d}) → (segment Real (coord a) (coord b) ∩ segment Real (coord c) (coord d)
        = coord '' (({a, b} : Set (Int × Int)) ∩ {c, d}))))) → (∀ (a : Int × Int), ∀ (b : Int ×
        Int), ∀ (c : Int × Int), ∀ (d : Int × Int), (TriangularLatticeAdjacent a b) →
        ((TriangularLatticeAdjacent c d) → ((({a, b} : Set (Int × Int)) ≠ {c, d}) → (arc a b ∩
        arc c d =
        (fun x => shear (coord x)) '' (({a, b} : Set (Int × Int)) ∩ {c, d}))))) := by
  classical
  intro coord shear arc segment_intersections a b c d hab hcd hne
  dsimp only [arc]
  rw [← Set.image_inter shear.injective, segment_intersections a b c d hab hcd hne,
    Set.image_image]
end AffineTriangulationLemmas
theorem AffineTriangularPlaneTriangulation :
    ∃ (P : PlaneTriangulation (Int × Int))
      (up down : (Int × Int) → P.Face),
      (∀ x y, P.adjacent x y ↔
        TriangularLatticeAdjacent x y) ∧
      Function.Injective up ∧ Function.Injective down ∧
      (∀ x y, up x ≠ down y) ∧
      (∀ f, (∃ x, f = up x) ∨ ∃ x, f = down x) ∧
      (∀ x,
        P.faceVertex (up x) 0 = x ∧
        P.faceVertex (up x) 1 = x + ((1, 0) : Int × Int) ∧
        P.faceVertex (up x) 2 = x - ((0, 1) : Int × Int)) ∧
      (∀ x,
        P.faceVertex (down x) 0 = x ∧
        P.faceVertex (down x) 1 = x - ((1, 0) : Int × Int) ∧
        P.faceVertex (down x) 2 = x + ((0, 1) : Int × Int)) ∧
      (∀ x, P.position x =
        (((x.1 : Real) - (x.2 : Real) / 2), (x.2 : Real))) ∧
      (∀ x y, P.edgeArc x y = segment Real (P.position x) (P.position y)) ∧
      (∀ x, P.faceRegion (up x) =
        (fun p : Real × Real =>
          (((x.1 : Real) + p.1) - ((x.2 : Real) - p.2) / 2,
            (x.2 : Real) - p.2)) ''
          {p : Real × Real | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}) ∧
      (∀ x, P.faceRegion (down x) =
        (fun p : Real × Real =>
          (((x.1 : Real) - p.1) - ((x.2 : Real) + p.2) / 2,
            (x.2 : Real) + p.2)) ''
          {p : Real × Real | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}) := by
-- BODY
  classical
  -- The tags distinguish the two translation orbits of faces.
  let fv : (Sum (Int × Int) (Int × Int)) → Fin 3 → (Int × Int) := fun
    | Sum.inl x => ![x, x + (1, 0), x - (0, 1)]
    | Sum.inr x => ![x, x - (1, 0), x + (0, 1)]
  have symm_adj (a b : (Int × Int)) := AffineTriangulationLemmas.symm_adj a b
  have irrefl_adj (a : (Int × Int)) := AffineTriangulationLemmas.irrefl_adj a
  have finite_adj (a : (Int × Int)) := AffineTriangulationLemmas.finite_adj a
  have distinct_fv (f : (Sum (Int × Int) (Int × Int))) := AffineTriangulationLemmas.distinct_fv f
  have edges_fv (f : (Sum (Int × Int) (Int × Int))) (i j : Fin 3) (h : i ≠ j) :=
      AffineTriangulationLemmas.edges_fv f i j h
  have two_faces (a b : (Int × Int)) (hab : TriangularLatticeAdjacent a b) :=
      AffineTriangulationLemmas.two_faces a b hab
  have int_walk {R : (Int × Int) → (Int × Int) → Prop}
      (hs : ∀ a b, R a b → R b a)
      (f : Int → (Int × Int)) (step : ∀ k, R (f k) (f (k + 1))) (m n : Int) :=
          AffineTriangulationLemmas.int_walk (R := R) hs f
          step m n
  -- Route surviving vertices through clean columns and a clean row.
  have deletion_walk (D : Finset (Int × Int)) (hD : D.card < 3)
      (a b : (Int × Int)) (ha : a ∉ D) (hb : b ∉ D) := AffineTriangulationLemmas.deletion_walk
          symm_adj int_walk D hD a b ha hb
  -- Construct the geometry before applying the invertible shear.
  let coord (x : (Int × Int)) : (Real × Real) := (x.1, x.2)
  let shear : (Real × Real) ≃ₜ (Real × Real) := {
    toFun p := (p.1 - p.2 / 2, p.2)
    invFun p := (p.1 + p.2 / 2, p.2)
    left_inv p := by ext <;> simp
    right_inv p := by ext <;> simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have coord_injective := AffineTriangulationLemmas.coord_injective
  let arc (a b : (Int × Int)) : Set (Real × Real) := shear '' segment Real (coord a) (coord b)
  have segment_homeo (a b : (Real × Real)) (hne : a ≠ b) :=
      AffineTriangulationLemmas.segment_homeo a b hne
  have arc_homeo (a b : (Int × Int)) (hne : a ≠ b) := AffineTriangulationLemmas.arc_homeo
      coord_injective segment_homeo a b hne
  let T : Set (Real × Real) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
  have open_T := AffineTriangulationLemmas.open_T
  have closed_C := AffineTriangulationLemmas.closed_C
  have convex_T := AffineTriangulationLemmas.convex_T
  have connected_T := AffineTriangulationLemmas.connected_T convex_T
  have closure_T := AffineTriangulationLemmas.closure_T closed_C
  have boundary_T := AffineTriangulationLemmas.boundary_T open_T
          closure_T
  let tile : (Sum (Int × Int) (Int × Int)) → (Real × Real) ≃ₜ (Real × Real) :=
    AffineTriangulationLemmas.tile
  let region (f : (Sum (Int × Int) (Int × Int))) : Set (Real × Real) := shear '' tile f '' T
  have tile_segment (f : (Sum (Int × Int) (Int × Int))) (a b : (Real × Real)) :=
      AffineTriangulationLemmas.tile_segment f a b
  have tile_vertices (f : (Sum (Int × Int) (Int × Int))) :=
      AffineTriangulationLemmas.tile_vertices f
  have boundary_region (f : (Sum (Int × Int) (Int × Int))) :=
      AffineTriangulationLemmas.boundary_region boundary_T tile_segment tile_vertices f
  have open_region (f : (Sum (Int × Int) (Int × Int))) := AffineTriangulationLemmas.open_region
      open_T f
  have connected_region (f : (Sum (Int × Int) (Int × Int))) :=
      AffineTriangulationLemmas.connected_region connected_T f
  have closed_cover (p : (Real × Real)) := AffineTriangulationLemmas.closed_cover p
  have strip_unique (m n : Int) (r : Real)
      (hm : (m : Real) < r ∧ r < (m : Real) + 1)
      (hn : (n : Real) < r ∧ r < (n : Real) + 1) := AffineTriangulationLemmas.strip_unique m n r
          hm hn
  have tiles_disjoint := AffineTriangulationLemmas.tiles_disjoint strip_unique
  have regions_disjoint := AffineTriangulationLemmas.regions_disjoint tiles_disjoint
  have plane_cover := AffineTriangulationLemmas.plane_cover edges_fv
          closure_T boundary_region closed_cover
  -- Normalize undirected edges to horizontal, vertical, or diagonal unit steps.
  let delta : Fin 3 → (Int × Int) := ![(1, 0), (0, 1), (1, 1)]
  have fraction_integer (m n : Int) (s : Real) (hs : s ∈ Set.Icc (0 : Real) 1)
      (h : (m : Real) + s = (n : Real)) := AffineTriangulationLemmas.fraction_integer m n s hs h
  have fraction_gap (m n : Int) (s t : Real)
      (hs : s ∈ Set.Icc (0 : Real) 1) (ht : t ∈ Set.Icc (0 : Real) 1)
      (h : (m : Real) + s = (n : Real) + t) (hne : m ≠ n) :=
          AffineTriangulationLemmas.fraction_gap m n s t hs ht h
          hne
  have endpoint_parameters (x y : (Int × Int)) (k l : Fin 3) (s t : Real)
      (hs : s ∈ Set.Icc (0 : Real) 1) (ht : t ∈ Set.Icc (0 : Real) 1)
      (h : coord x + s • (coord (x + delta k) - coord x) =
        coord y + t • (coord (y + delta l) - coord y))
      (hne : ({x, x + delta k} : Set (Int × Int)) ≠ {y, y + delta l}) :=
          AffineTriangulationLemmas.endpoint_parameters
          fraction_integer fraction_gap x y k l s t hs ht h hne
  have canonical_intersection (x y : (Int × Int)) (k l : Fin 3)
      (hne : ({x, x + delta k} : Set (Int × Int)) ≠ {y, y + delta l}) :=
          AffineTriangulationLemmas.canonical_intersection coord_injective endpoint_parameters
            x y k l hne
  have orient_edge (a b : (Int × Int)) (hab : TriangularLatticeAdjacent a b) :=
      AffineTriangulationLemmas.orient_edge a b hab
  have segment_intersections (a b c d : (Int × Int))
      (hab : TriangularLatticeAdjacent a b) (hcd : TriangularLatticeAdjacent c d)
      (hne : ({a, b} : Set (Int × Int)) ≠ {c, d}) :=
          AffineTriangulationLemmas.segment_intersections canonical_intersection orient_edge a
            b c d hab hcd hne
  have arc_symmetric (a b : Int × Int) := AffineTriangulationLemmas.arc_symmetric a b
  have arc_intersections (a b c d : Int × Int)
      (hab : TriangularLatticeAdjacent a b) (hcd : TriangularLatticeAdjacent c d)
      (hne : ({a, b} : Set (Int × Int)) ≠ {c, d}) := AffineTriangulationLemmas.arc_intersections
          segment_intersections a b c d hab hcd hne
  let P : PlaneTriangulation (Int × Int) := {
    adjacent := TriangularLatticeAdjacent
    Face := Sum (Int × Int) (Int × Int)
    faceVertex := fv
    position := fun x => shear (coord x)
    edgeArc := arc
    faceRegion := region
    adjacent_symmetric := symm_adj
    adjacent_irreflexive := irrefl_adj
    locally_finite := finite_adj
    three_connected := fun D hD a ha b hb => deletion_walk D hD a b ha hb
    face_vertices_distinct := distinct_fv
    face_edges := edges_fv
    every_edge_two_faces := two_faces
    position_injective := shear.injective.comp coord_injective
    arc_symmetric := arc_symmetric
    arc_homeomorph := by
      intro a b hab
      apply arc_homeo a b
      intro heq
      subst b
      exact irrefl_adj a hab
    arc_intersections := arc_intersections
    region_open := open_region
    region_connected := connected_region
    region_disjoint := regions_disjoint
    face_boundary := boundary_region
    plane_cover := plane_cover }
  refine ⟨P, Sum.inl, Sum.inr, ?_⟩
  refine ⟨(fun _ _ => Iff.rfl), (fun _ _ h => Sum.inl.inj h),
    (fun _ _ h => Sum.inr.inj h), (fun _ _ => Sum.inl_ne_inr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    cases f with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr x => exact Or.inr ⟨x, rfl⟩
  · intro x
    exact ⟨rfl, rfl, rfl⟩
  · intro x
    exact ⟨rfl, rfl, rfl⟩
  · intro x
    rfl
  · intro x y
    change shear '' segment Real (coord x) (coord y) =
      segment Real (shear (coord x)) (shear (coord y))
    rw [segment_eq_image' Real, segment_eq_image' Real, Set.image_image]
    congr 1
    funext t
    ext <;> simp [shear, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  · intro x
    change shear '' tile (Sum.inl x) '' T = _
    rw [Set.image_image]
    rfl
  · intro x
    change shear '' tile (Sum.inr x) '' T = _
    rw [Set.image_image]
    rfl
end ApollonianSuperharmonic
end
