/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Run
public import LeanPool.PlanarSeparator.PlanarSeparator.LevelSep
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Inside

/-!
# The separator program: from a plane rotation system to the numeric hypotheses

A rotation system `R` of a graph `G` with vertex weights `w` is given to the program by numbering
its vertices (`vi : V ≃ Fin n`) and its darts (`di : G.Dart ≃ Fin m`) so that the darts leaving
a vertex are numbered consecutively (`Enc`). This file proves the numeric facts the program
assumes:

* `Enc.nwf`: the numbers form a rotation system without loops (`NWf`);
* `Enc.nconn`: every vertex is reached from vertex `0` when `G` is connected (`NConn`);
* `Enc.ofs_lt`: when `m ≥ 1`, every vertex has a dart;
* `Enc.orb_iff`: the cycles of the numeric face permutation are the faces of `R`.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open Finset

variable {V : Type*} {G : SimpleGraph V} {R : Kasteleyn.RotationSystem G}

/-- **The encoding of a rotation system.** The vertices and darts are numbered by `vi` and `di`,
the darts leaving a vertex `v` getting the numbers `ofs (vi v) ≤ i < ofs (vi v + 1)`; `tl`, `rv`,
`ro` are the initial vertex, the reversal and the rotation, and `wN` the weights, in these
numbers. -/
structure Enc (R : Kasteleyn.RotationSystem G) (w : V → ℕ) (n m : ℕ) (vi : V ≃ Fin n)
    (di : G.Dart ≃ Fin m) (ofs wN tl rv ro : ℕ → ℕ) : Prop where
  tl_eq : ∀ d, tl (di d) = vi d.fst
  rv_eq : ∀ d, rv (di d) = di d.symm
  ro_eq : ∀ d, ro (di d) = di (R.rot d)
  w_eq : ∀ v, wN (vi v) = w v
  ofs_mono : ∀ u v, u ≤ v → v ≤ n → ofs u ≤ ofs v
  ofs_n : ofs n = m
  blk : ∀ d, ofs (vi d.fst) ≤ di d ∧ (di d : ℕ) < ofs (vi d.fst + 1)

theorem two_le_of {n m : ℕ} (vi : V ≃ Fin n) (di : G.Dart ≃ Fin m) (hm : 1 ≤ m) : 2 ≤ n := by
  have d := di.symm ⟨0, hm⟩
  have h1 := (vi d.fst).2
  have h2 := (vi d.snd).2
  have : (vi d.fst : ℕ) ≠ vi d.snd := fun e => d.adj.ne (vi.injective (Fin.ext e))
  omega

namespace Enc

variable {w : V → ℕ} {n m : ℕ} {vi : V ≃ Fin n} {di : G.Dart ≃ Fin m} {ofs wN tl rv ro : ℕ → ℕ}
  (hE : Enc R w n m vi di ofs wN tl rv ro)
include hE

omit hE in
theorem exists_dart {i : ℕ} (hi : i < m) : ∃ d, (di d : ℕ) = i :=
  ⟨di.symm ⟨i, hi⟩, by simp⟩

theorem nwf : NWf n m ofs tl rv ro where
  tl_lt i hi := by obtain ⟨d, rfl⟩ := exists_dart (di := di) hi; rw [hE.tl_eq]; exact (vi _).2
  rv_lt i hi := by obtain ⟨d, rfl⟩ := exists_dart (di := di) hi; rw [hE.rv_eq]; exact (di _).2
  rv_rv i hi := by obtain ⟨d, rfl⟩ := exists_dart (di := di) hi; rw [hE.rv_eq, hE.rv_eq]; simp
  ro_lt i hi := by obtain ⟨d, rfl⟩ := exists_dart (di := di) hi; rw [hE.ro_eq]; exact (di _).2
  ro_inj i hi j hj e := by
    obtain ⟨d, rfl⟩ := exists_dart (di := di) hi
    obtain ⟨d', rfl⟩ := exists_dart (di := di) hj
    rw [hE.ro_eq, hE.ro_eq, Fin.val_inj, di.apply_eq_iff_eq, (R.rot).apply_eq_iff_eq] at e
    rw [e]
  tl_ro i hi := by
    obtain ⟨d, rfl⟩ := exists_dart (di := di) hi; rw [hE.ro_eq, hE.tl_eq, hE.tl_eq, R.fst_rot]
  tl_rv i hi := by
    obtain ⟨d, rfl⟩ := exists_dart (di := di) hi
    rw [hE.rv_eq, hE.tl_eq, hE.tl_eq, Ne, Fin.val_inj, vi.apply_eq_iff_eq]
    exact d.adj.ne.symm
  ofs_mono := hE.ofs_mono
  ofs_n := hE.ofs_n
  blk i hi v hv := by
    obtain ⟨d, rfl⟩ := exists_dart (di := di) hi
    rw [hE.tl_eq]
    have hb := hE.blk d
    constructor
    · rintro rfl; exact hb
    · rintro ⟨h1, h2⟩
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := hE.ofs_mono (vi d.fst + 1) v (by omega) (by omega); omega
      · have := hE.ofs_mono (v + 1) (vi d.fst) (by omega) (vi _).2.le; omega

theorem nconn (hG : G.Connected) (hn : 0 < n) : NConn n m tl rv := by
  intro S h0 hstep v hv
  set r : V := vi.symm ⟨0, hn⟩
  have key : ∀ x, Relation.ReflTransGen G.Adj r x → S (vi x) := by
    intro x hx
    induction hx with
    | refl => simpa [r] using h0
    | @tail y z _ hyz ih =>
      have := hstep (di ⟨(y, z), hyz⟩) (di _).2 (by rw [hE.tl_eq]; exact ih)
      rwa [hE.rv_eq, hE.tl_eq] at this
  have := key (vi.symm ⟨v, hv⟩) ((SimpleGraph.reachable_iff_reflTransGen _ _).1
    (hG.preconnected _ _))
  simpa using this

/-- When there are darts, every vertex of a connected graph has one. -/
theorem ofs_lt (hG : G.Connected) (hm : 1 ≤ m) : ∀ v < n, ofs v < ofs (v + 1) := by
  intro v hv
  let : Fintype V := Fintype.ofEquiv (Fin n) vi.symm
  have h2 := two_le_of vi di hm
  set u : V := vi.symm ⟨v, hv⟩
  obtain ⟨y, hy⟩ : ∃ y : V, y ≠ u := by
    by_contra h
    push Not at h
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
    rw [Fintype.card_congr vi, Fintype.card_fin] at this
    omega
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (hG.preconnected u y)
  rcases hr.cases_head with h | ⟨z, huz, -⟩
  · exact absurd h.symm hy
  · have hb := hE.blk ⟨(u, z), huz⟩
    simp only [u, Equiv.apply_symm_apply] at hb
    omega

/-- The numeric face permutation is the face permutation of the map of `R`. -/
theorem ph_eq (d : G.Dart) : ph rv ro (di d) = di ((Map.ofRotation R).φ d) := by
  unfold ph; rw [hE.rv_eq, hE.ro_eq]; rfl

theorem ph_iter (d : G.Dart) (k : ℕ) :
    (ph rv ro)^[k] (di d) = di (((Map.ofRotation R).φ ^ k) d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hE.ph_eq, pow_succ', Equiv.Perm.mul_apply]

/-- **The faces.** Two darts lie on the same cycle of the numeric face permutation exactly when
they lie on the same face. -/
theorem orb_iff (d d' : G.Dart) :
    Orb (ph rv ro) (di d) (di d') ↔ (Map.ofRotation R).face d = (Map.ofRotation R).face d' := by
  let : Fintype G.Dart := Fintype.ofEquiv (Fin m) di.symm
  rw [Map.face_eq_face_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [hE.ph_iter, Fin.val_inj, di.apply_eq_iff_eq] at hk
    exact ⟨k, by rw [zpow_natCast, hk]⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [hE.ph_iter, hk]⟩

end Enc

/-! ### The tree, the face representatives and the coding of the stellar subdivision -/

section Build

variable {w : V → ℕ} {n m : ℕ} {vi : V ≃ Fin n} {di : G.Dart ≃ Fin m} {ofs wN tl rv ro : ℕ → ℕ}
  (hE : Enc R w n m vi di ofs wN tl rv ro) {L pr : ℕ → ℕ}
  (hpar : ∀ v < n, v ≠ 0 → pr v < m ∧ tl (pr v) = v ∧ L (parN tl rv pr v) + 1 = L v)

open StDart

variable (di) in
/-- The parent dart of a vertex other than the vertex `0`. -/
def pdart (v : V) (h : (vi v : ℕ) ≠ 0) : G.Dart := di.symm ⟨pr (vi v), (hpar _ (vi v).2 h).1⟩

include hE in
theorem pdart_fst (v : V) (h : (vi v : ℕ) ≠ 0) : (pdart di hpar v h).fst = v := by
  apply vi.injective; apply Fin.ext
  rw [← hE.tl_eq, pdart, Equiv.apply_symm_apply]; exact (hpar _ (vi v).2 h).2.1

include hE in
theorem vi_pdart_snd (v : V) (h : (vi v : ℕ) ≠ 0) :
    (vi (pdart di hpar v h).snd : ℕ) = parN tl rv pr (vi v) := by
  unfold parN
  have : pr (vi v) = di (pdart di hpar v h) := by simp [pdart]
  rw [this, hE.rv_eq, hE.tl_eq]; rfl

include hE in
variable (vi di) in
/-- **The breadth-first tree** of the graph, rooted at the vertex numbered `0`. -/
def gtree (hn : 0 < n) : GTree G where
  root := vi.symm ⟨0, hn⟩
  parent v := if h : (vi v : ℕ) = 0 then v else (pdart di hpar v h).snd
  height v := L (vi v)
  adj v hv := by
    have h : (vi v : ℕ) ≠ 0 := fun e => hv (by rw [Equiv.eq_symm_apply]; exact Fin.ext e)
    rw [dite_eq_right h]
    have := (pdart di hpar v h).adj
    rwa [pdart_fst hE] at this
  height_lt v hv := by
    have h : (vi v : ℕ) ≠ 0 := fun e => hv (by rw [Equiv.eq_symm_apply]; exact Fin.ext e)
    rw [dite_eq_right h, vi_pdart_snd hE]
    have := (hpar _ (vi v).2 h).2.2
    omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

variable (di rv ro) in
/-- The representative of a face: the dart of the face with the smallest number. -/
noncomputable def repF (f : (Map.ofRotation R).Face) : G.Dart :=
  di.symm ⟨frepF (ph rv ro) (di (faceRep R f)), lt_of_le_of_lt (frepF_le _) (di _).2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem di_repF_val (f : (Map.ofRotation R).Face) :
    (di (repF di rv ro f) : ℕ) = frepF (ph rv ro) (di (faceRep R f)) := by
  simp [repF]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
include hE in
theorem di_repF (d : G.Dart) :
    (di (repF di rv ro ((Map.ofRotation R).face d)) : ℕ) = frepF (ph rv ro) (di d) := by
  rw [di_repF_val]
  exact (frepF_eq hE.nwf.nperm (di d).2
    ((hE.orb_iff d (faceRep R _)).2 (face_faceRep R _).symm)).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
include hE in
theorem face_repF (f : (Map.ofRotation R).Face) :
    (Map.ofRotation R).face (repF di rv ro f) = f := by
  have := (hE.orb_iff (faceRep R f) (repF di rv ro f)).1 (by rw [di_repF_val]; exact frepF_orb _)
  rw [← this, face_faceRep]

variable (di) in
/-- **The coding of the stellar subdivision**: the face `old x → up (φ x) → down x` gets the
numbers `3 x, 3 x + 1, 3 x + 2`. -/
def cdE : StDart G.Dart ≃ Fin (3 * m) where
  toFun
    | old d => ⟨3 * di d, by have := (di d).2; omega⟩
    | up d => ⟨3 * di ((Map.ofRotation R).φ.symm d) + 1, by
        have := (di ((Map.ofRotation R).φ.symm d)).2; omega⟩
    | down d => ⟨3 * di d + 2, by have := (di d).2; omega⟩
  invFun y :=
    if y.1 % 3 = 0 then old (di.symm ⟨y.1 / 3, by omega⟩)
    else if y.1 % 3 = 1 then up ((Map.ofRotation R).φ (di.symm ⟨y.1 / 3, by omega⟩))
    else down (di.symm ⟨y.1 / 3, by omega⟩)
  left_inv x := by
    cases x with
    | old d =>
      simp only [Nat.mul_mod_right, ↓reduceIte, old.injEq]
      rw [Equiv.symm_apply_eq]; ext; simp only; omega
    | up d =>
      simp only [show (3 * (di ((Map.ofRotation R).φ.symm d) : ℕ) + 1) % 3 = 1 by omega,
        one_ne_zero, ↓reduceIte, up.injEq]
      rw [← Equiv.eq_symm_apply, Equiv.symm_apply_eq]; ext; simp only; omega
    | down d =>
      simp only [show (3 * (di d : ℕ) + 2) % 3 = 2 by omega, OfNat.ofNat_ne_zero,
        OfNat.ofNat_ne_one, ↓reduceIte, down.injEq]
      rw [Equiv.symm_apply_eq]; ext; simp only; omega
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    simp only
    split_ifs with h0 h1
    · simp only [Equiv.apply_symm_apply, Fin.mk.injEq]; omega
    · simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Fin.mk.injEq]; omega
    · simp only [Equiv.apply_symm_apply, Fin.mk.injEq]; omega

include hE in
variable (vi di) in
/-- **The spanning tree of the stellar subdivision**: the breadth-first tree, with the centre of
every face hanging from the initial vertex of its representative. -/
noncomputable def liftT (hn : 0 < n) : (Map.ofRotation R).stellar.SpTree :=
  liftTreeWith R (gtree vi di hE hpar hn) (repF di rv ro) (face_repF hE)

omit [DecidableEq V] in
theorem liftT_root (hn : 0 < n) : (liftT vi di hE hpar hn).root = .inl (vi.symm ⟨0, hn⟩) := rfl

omit [DecidableEq V] in
theorem inl_ne_root_iff (hn : 0 < n) (v : V) :
    (.inl v : V ⊕ _) ≠ (liftT vi di hE hpar hn).root ↔ (vi v : ℕ) ≠ 0 := by
  rw [liftT_root, Ne, Sum.inl.injEq, Equiv.eq_symm_apply, Fin.ext_iff]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem gtree_parent (hn : 0 < n) {v : V} (h : (vi v : ℕ) ≠ 0) :
    (gtree vi di hE hpar hn).parent v = (pdart di hpar v h).snd := by
  simp only [gtree, h, ↓reduceDIte]

omit [DecidableEq V] in
theorem par_inl (hn : 0 < n) {v : V} (h : (vi v : ℕ) ≠ 0)
    (h' : (.inl v : V ⊕ _) ≠ (liftT vi di hE hpar hn).root) :
    (liftT vi di hE hpar hn).par (.inl v) h' = old (pdart di hpar v h) := by
  change old _ = _
  congr 1
  ext
  · exact (pdart_fst hE hpar v h).symm
  · exact gtree_parent hE hpar hn h

omit [DecidableEq V] in
theorem isTree_old (hn : 0 < n) (d : G.Dart) : (liftT vi di hE hpar hn).IsTree (old d) ↔
    ∃ v, ∃ h : (vi v : ℕ) ≠ 0, d = pdart di hpar v h ∨ d = (pdart di hpar v h).symm := by
  constructor
  · rintro ⟨p, hp, hd⟩
    cases p with
    | inl v =>
      have h := (inl_ne_root_iff hE hpar hn v).1 hp
      rw [par_inl hE hpar hn h hp] at hd
      rcases hd with hd | hd
      · exact ⟨v, h, Or.inl (old.inj hd)⟩
      · exact ⟨v, h, Or.inr (old.inj hd)⟩
    | inr f =>
      rcases hd with hd | hd <;> cases hd
  · rintro ⟨v, h, hd⟩
    have hp := (inl_ne_root_iff hE hpar hn v).2 h
    refine ⟨.inl v, hp, ?_⟩
    rw [par_inl hE hpar hn h hp]
    rcases hd with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

omit [DecidableEq V] in
theorem isTree_up (hn : 0 < n) (d : G.Dart) : (liftT vi di hE hpar hn).IsTree (up d) ↔
    d = repF di rv ro ((Map.ofRotation R).face d) := by
  constructor
  · rintro ⟨p, hp, hd⟩
    cases p with
    | inl v =>
      have h := (inl_ne_root_iff hE hpar hn v).1 hp
      rw [par_inl hE hpar hn h hp] at hd
      rcases hd with hd | hd <;> cases hd
    | inr f =>
      rcases hd with hd | hd
      · cases hd
      · have e : d = repF di rv ro f := up.inj hd
        rw [e, face_repF hE]
  · intro hd
    refine ⟨.inr ((Map.ofRotation R).face d), Sum.inr_ne_inl, Or.inr ?_⟩
    change up d = up _
    exact congrArg up hd

omit [DecidableEq V] in
theorem isTree_down (hn : 0 < n) (d : G.Dart) : (liftT vi di hE hpar hn).IsTree (down d) ↔
    d = repF di rv ro ((Map.ofRotation R).face d) := by
  constructor
  · rintro ⟨p, hp, hd⟩
    cases p with
    | inl v =>
      have h := (inl_ne_root_iff hE hpar hn v).1 hp
      rw [par_inl hE hpar hn h hp] at hd
      rcases hd with hd | hd <;> cases hd
    | inr f =>
      rcases hd with hd | hd
      · have e : d = repF di rv ro f := down.inj hd
        rw [e, face_repF hE]
      · cases hd
  · intro hd
    refine ⟨.inr ((Map.ofRotation R).face d), Sum.inr_ne_inl, Or.inl ?_⟩
    change down d = down _
    exact congrArg down hd

theorem phi3_0 (a : ℕ) : CycleSearch.phi3 (3 * a) = 3 * a + 1 := by
  unfold CycleSearch.phi3; rw [ite_eq_left (by omega)]
theorem phi3_1 (a : ℕ) : CycleSearch.phi3 (3 * a + 1) = 3 * a + 2 := by
  unfold CycleSearch.phi3; rw [ite_eq_left (by omega)]
theorem phi3_2 (a : ℕ) : CycleSearch.phi3 (3 * a + 2) = 3 * a := by
  unfold CycleSearch.phi3; rw [ite_eq_right (by omega)]; omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem cdE_old (d : G.Dart) : (cdE (R := R) di (old d) : ℕ) = 3 * di d := rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem cdE_up (d : G.Dart) :
    (cdE (R := R) di (up d) : ℕ) = 3 * di ((Map.ofRotation R).φ.symm d) + 1 := rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem cdE_down (d : G.Dart) : (cdE (R := R) di (down d) : ℕ) = 3 * di d + 2 := rfl

omit [Fintype V] [DecidableRel G.Adj] in
include hE in
/-- The tree mark of a spoke: `1` exactly for the representative of the face. -/
theorem ind_frepF (d : G.Dart) :
    ind (di d) (frepF (ph rv ro) (di d) + 1) = if d = repF di rv ro ((Map.ofRotation R).face d)
      then 1 else 0 := by
  have h1 := frepF_le (f := ph rv ro) (di d)
  have h2 := di_repF hE d
  rw [ind_eq]
  by_cases h : d = repF di rv ro ((Map.ofRotation R).face d)
  · rw [ite_eq_left h, ite_eq_left (by rw [← h2, ← h]; omega)]
  · rw [ite_eq_right h, ite_eq_right]
    intro hlt
    apply h
    apply di.injective
    apply Fin.ext
    rw [h2]; omega

omit [DecidableEq V] in
/-- **The coded stellar subdivision.** The arrays written by the front half code the stellar
subdivision of the map of `R` with its spanning tree `liftT`. -/
theorem coded (hn : 0 < n) (mem : ℕ → ℕ)
    (hD : ∀ x < m, DFacts m rv ro (fun q => frepF (ph rv ro) q + 1) mem x)
    (htm1 : ∀ v, 1 ≤ v → v < n → mem (3 * m + 3 * pr v) = 1 ∧ mem (3 * m + 3 * rv (pr v)) = 1)
    (htm0 : ∀ x < m, (∀ v, 1 ≤ v → v < n → x ≠ pr v ∧ x ≠ rv (pr v)) →
      mem (3 * m + 3 * x) = 0) :
    CycleSearch.Coded (Map.ofRotation R).stellar (liftT vi di hE hpar hn) m (cdE (R := R) di)
      (fun x => mem x) (fun x => mem (3 * m + x)) := by
  classical
  have hphi : ∀ d, ph rv ro (di ((Map.ofRotation R).φ.symm d)) = di d := fun d => by
    rw [hE.ph_eq]; simp
  -- the tree marks of the darts of the graph
  have hold : ∀ d, (mem (3 * m + 3 * di d) = 1 ∧ (liftT vi di hE hpar hn).IsTree (old d)) ∨
      (mem (3 * m + 3 * di d) = 0 ∧ ¬ (liftT vi di hE hpar hn).IsTree (old d)) := by
    intro d
    rw [isTree_old]
    by_cases hT : ∃ v, ∃ h : (vi v : ℕ) ≠ 0, d = pdart di hpar v h ∨ d = (pdart di hpar v h).symm
    · left
      refine ⟨?_, hT⟩
      obtain ⟨v, h, hd⟩ := hT
      have hp : (di (pdart di hpar v h) : ℕ) = pr (vi v) := by simp [pdart]
      obtain ⟨t1, t2⟩ := htm1 (vi v) (by omega) (vi v).2
      rcases hd with rfl | rfl
      · rw [hp]; exact t1
      · have : (di (pdart di hpar v h).symm : ℕ) = rv (pr (vi v)) := by rw [← hp, hE.rv_eq]
        rw [this]; exact t2
    · right
      refine ⟨htm0 _ (di d).2 fun u h1 h2 => ⟨fun e => hT ?_, fun e => hT ?_⟩, hT⟩
      · refine ⟨vi.symm ⟨u, h2⟩, by simp; omega, Or.inl ?_⟩
        apply di.injective; apply Fin.ext; simp [pdart, e]
      · refine ⟨vi.symm ⟨u, h2⟩, by simp; omega, Or.inr ?_⟩
        apply di.injective; apply Fin.ext
        rw [← hE.rv_eq, e]
        simp [pdart]
  -- the tree marks of the spokes
  have hup : ∀ d, mem (3 * m + (cdE (R := R) di (up d) : ℕ)) =
      if d = repF di rv ro ((Map.ofRotation R).face d) then 1 else 0 := fun d => by
    rw [cdE_up, show 3 * m + (3 * (di ((Map.ofRotation R).φ.symm d) : ℕ) + 1) =
      3 * m + 3 * di ((Map.ofRotation R).φ.symm d) + 1 by ring, (hD _ (di _).2).2.2.2.2, hphi]
    exact ind_frepF hE d
  have hdown : ∀ d, mem (3 * m + (cdE (R := R) di (down d) : ℕ)) =
      if d = repF di rv ro ((Map.ofRotation R).face d) then 1 else 0 := fun d => by
    rw [cdE_down, show 3 * m + (3 * (di d : ℕ) + 2) = 3 * m + 3 * di d + 2 by ring,
      (hD _ (di _).2).2.2.2.1]
    exact ind_frepF hE d
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · cases x with
    | old d =>
      simp only [Map.stellar_α, Map.stα_old, Map.ofRotation_α, cdE_old]
      rw [(hD _ (di d).2).1, hE.rv_eq]
    | up d =>
      simp only [Map.stellar_α, Map.stα_up, cdE_up, cdE_down]
      rw [(hD _ (di _).2).2.1, hphi]
    | down d =>
      simp only [Map.stellar_α, Map.stα_down, cdE_up, cdE_down]
      have := (hD _ (di ((Map.ofRotation R).φ.symm d)).2).2.2.1
      rw [hphi] at this; exact this
  · cases x with
    | old d =>
      simp only [Map.stellar_φ_old, cdE_up, cdE_old, Equiv.symm_apply_apply, phi3_0]
    | up d => simp only [Map.stellar_φ_up, cdE_up, cdE_down, phi3_1]
    | down d => simp only [Map.stellar_φ_down, cdE_down, cdE_old, phi3_2]
  · cases x with
    | old d =>
      simp only [cdE_old]
      rcases hold d with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]; exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h2 h⟩
      · rw [h1]; exact ⟨fun _ => h2, fun _ => rfl⟩
    | up d =>
      rw [hup, isTree_up]
      split_ifs with h
      · exact ⟨fun h' => by simp at h', fun h' => absurd h h'⟩
      · exact ⟨fun _ => h, fun _ => rfl⟩
    | down d =>
      rw [hdown, isTree_down]
      split_ifs with h
      · exact ⟨fun h' => by simp at h', fun h' => absurd h h'⟩
      · exact ⟨fun _ => h, fun _ => rfl⟩
  · cases x with
    | old d =>
      simp only [cdE_old]
      rcases hold d with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    | up d => rw [hup]; split_ifs <;> omega
    | down d => rw [hdown]; split_ifs <;> omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
include hE in
theorem ofs_vi_lt (hofs : ∀ v < n, ofs v < ofs (v + 1)) (v : V) : ofs (vi v) < m :=
  lt_of_lt_of_le (hofs _ (vi v).2) (hE.nwf.ofs_le_m (vi v).2)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
include hE in
theorem ofs_inj (hofs : ∀ v < n, ofs v < ofs (v + 1)) {u v : ℕ} (hu : u < n) (hv : v < n)
    (e : ofs u = ofs v) : u = v := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hE.ofs_mono (u + 1) v (by omega) hv.le; have := hofs u hu; omega
  · have := hE.ofs_mono (v + 1) u (by omega) hu.le; have := hofs v hv; omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
variable (vi di rv ro) in
/-- The first dart of a vertex of the stellar subdivision: the dart `ofs v` at a vertex `v` of
the graph, the spoke to the representative at the centre of a face. -/
noncomputable def firstF (hofs : ∀ v < n, ofs v < ofs (v + 1)) :
    V ⊕ (Map.ofRotation R).Face → StDart G.Dart
  | .inl v => old (di.symm ⟨ofs (vi v), ofs_vi_lt hE hofs v⟩)
  | .inr f => down (repF di rv ro f)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem vert_firstF [Finite G.Dart] (hofs : ∀ v < n, ofs v < ofs (v + 1))
    (p : V ⊕ (Map.ofRotation R).Face) :
    (Map.ofRotation R).stellar.vert (firstF vi di rv ro hE hofs p) = p := by
  cases p with
  | inl v =>
    simp only [firstF, Map.stellar_vert_old, Map.ofRotation_vert, Sum.inl.injEq]
    apply vi.injective; apply Fin.ext
    rw [← hE.tl_eq, Equiv.apply_symm_apply]
    exact ((hE.nwf.blk _ (ofs_vi_lt hE hofs v) _ (vi v).2).2
      ⟨le_rfl, hofs _ (vi v).2⟩)
  | inr f => simp only [firstF, Map.stellar_vert_down, face_repF hE]

/-- **The face weights.** With the stellar subdivision coded by `cdE`, the face weights written by
the front half are the weights `fwt` given to the faces by the first darts of the vertices, for
the weights `wMid` of the middle levels. -/
theorem hFw (hn : 0 < n) (hofs : ∀ v < n, ofs v < ofs (v + 1)) (l₁ j j' : ℕ) (mem : ℕ → ℕ)
    (hC : CycleSearch.Coded (Map.ofRotation R).stellar (liftT vi di hE hpar hn) m
      (cdE (R := R) di) (fun x => mem x) (fun x => mem (3 * m + x)))
    (hfw1 : ∀ v < n, mem (6 * m + ofs v) = wN v * ind l₁ (L v + j) * ind (L v) (l₁ + 1 + j'))
    (hfw0 : ∀ x < m, (∀ v < n, ofs v ≠ x) → mem (6 * m + x) = 0) (x : StDart G.Dart) :
    mem (6 * m + (cdE (R := R) di x : ℕ) / 3) = Map.SpTree.fwt (Map.ofRotation R).stellar
      (firstF vi di rv ro hE hofs) (wMid (fun v => L (vi v)) l₁ j j' w)
      ((Map.ofRotation R).stellar.face x) := by
  classical
  generalize hq : (cdE (R := R) di x : ℕ) / 3 = q
  have hqm : q < m := by have := (cdE (R := R) di x).2; omega
  set e := di.symm ⟨q, hqm⟩
  have hface : (Map.ofRotation R).stellar.face x = (Map.ofRotation R).stellar.face (old e) := by
    rw [hC.face_eq_iff, hq, cdE_old]; simp [e]
  have hfv : ∀ v, (Map.ofRotation R).stellar.face (firstF vi di rv ro hE hofs (.inl v)) =
      (Map.ofRotation R).stellar.face (old e) ↔ ofs (vi v) = q := by
    intro v
    rw [hC.face_eq_iff]; simp [firstF, e]
  rw [hface]
  unfold Map.SpTree.fwt
  rw [sum_filter, Fintype.sum_sum_type]
  simp only [wMid, Sum.elim_inr, Pi.zero_apply, ite_self, sum_const_zero, add_zero, Sum.elim_inl,
    hfv]
  by_cases hex : ∃ u < n, ofs u = q
  · obtain ⟨u, hu, rfl⟩ := hex
    rw [sum_eq_single (vi.symm ⟨u, hu⟩)]
    · simp only [Equiv.apply_symm_apply, ↓reduceIte, MidL]
      rw [hfw1 u hu, ← hE.w_eq, Equiv.apply_symm_apply, ind_eq, ind_eq]
      split_ifs <;> simp_all
    · intro v _ hv
      rw [ite_eq_right]
      intro h
      exact absurd (vi.injective (Fin.ext (by
        simpa using ofs_inj hE hofs (vi v).2 hu h))) hv
    · simp
  · push Not at hex
    rw [hfw0 q hqm hex]
    exact (sum_eq_zero fun v _ => ite_eq_right (fun h => absurd h (hex _ (vi v).2))).symm

/-! ### The root paths -/

include hpar in
theorem ancN_iff {u x : ℕ} (hu : u < n) (hu0 : u ≠ 0) :
    AncN tl rv pr L u x ↔ u = x ∨ AncN tl rv pr L (parN tl rv pr u) x := by
  have hL := (hpar u hu hu0).2.2
  constructor
  · rintro ⟨k, hk, e⟩
    rcases k with _ | k
    · exact Or.inl e
    · exact Or.inr ⟨k, by omega, by rwa [Function.iterate_succ_apply] at e⟩
  · rintro (e | ⟨k, hk, e⟩)
    · exact ⟨0, Nat.zero_le _, e⟩
    · exact ⟨k + 1, by omega, by rwa [Function.iterate_succ_apply]⟩

/-- **The root paths of the graph vertices.** -/
theorem mem_anc_inl (hn : 0 < n) (hL0 : L 0 = 0) (u x : V) :
    (.inl x : V ⊕ _) ∈ (liftT vi di hE hpar hn).anc (.inl u) ↔ AncN tl rv pr L (vi u) (vi x) := by
  induction hk : L (vi u) using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases hu : (vi u : ℕ) = 0
    · have hr : (.inl u : V ⊕ _) = (liftT vi di hE hpar hn).root := by
        by_contra h; exact (inl_ne_root_iff hE hpar hn u).1 h hu
      rw [hr, Map.SpTree.anc_root, mem_singleton, ← hr, Sum.inl.injEq]
      have hL : L (vi u) = 0 := by rw [hu]; exact hL0
      constructor
      · rintro rfl; exact ⟨0, Nat.zero_le _, rfl⟩
      · rintro ⟨k', hk', e⟩
        obtain rfl : k' = 0 := by omega
        exact vi.injective (Fin.ext e.symm)
    · have hne := (inl_ne_root_iff hE hpar hn u).2 hu
      have hpi : (liftT vi di hE hpar hn).parent (.inl u) =
          .inl ((gtree vi di hE hpar hn).parent u) :=
        liftTreeWith_parent_inl (gtree vi di hE hpar hn) (fun e => hu (by
          rw [show u = vi.symm ⟨0, hn⟩ from e]; simp))
      rw [Map.SpTree.anc_of_ne _ hne, mem_insert, Sum.inl.injEq, hpi,
        gtree_parent hE hpar hn hu]
      have hp := vi_pdart_snd hE hpar u hu
      have hLp := (hpar _ (vi u).2 hu).2.2
      rw [ih _ (by rw [hp]; omega) _ rfl, ancN_iff hpar (vi u).2 hu, hp, Fin.val_inj,
        vi.apply_eq_iff_eq]
      exact or_congr eq_comm Iff.rfl

/-- **The root path of a vertex of the stellar subdivision**, through the nearest vertex of the
graph (`uN`). -/
theorem mem_anc_vert (hn : 0 < n) (hL0 : L 0 = 0) (y : StDart G.Dart) (x : V) :
    (.inl x : V ⊕ _) ∈ (liftT vi di hE hpar hn).anc ((Map.ofRotation R).stellar.vert y) ↔
      AncN tl rv pr L (uN tl rv (fun q => frepF (ph rv ro) q + 1) (cdE (R := R) di y)) (vi x) := by
  cases y with
  | old d =>
    have : uN tl rv (fun q => frepF (ph rv ro) q + 1) (cdE (R := R) di (old d)) = vi d.fst := by
      rw [cdE_old, uN, ite_eq_left (by omega), show 3 * (di d : ℕ) / 3 = di d by omega, hE.tl_eq]
    rw [this, Map.stellar_vert_old]
    exact mem_anc_inl hE hpar hn hL0 _ _
  | up d =>
    have : uN tl rv (fun q => frepF (ph rv ro) q + 1) (cdE (R := R) di (up d)) = vi d.fst := by
      rw [cdE_up, uN, ite_eq_right (by omega), ite_eq_left (by omega),
        show (3 * (di ((Map.ofRotation R).φ.symm d) : ℕ) + 1) / 3 =
          di ((Map.ofRotation R).φ.symm d) by omega, hE.rv_eq, hE.tl_eq]
      congr 2
      have h := R.fst_rot ((Map.ofRotation R).φ.symm d).symm
      have e : R.rot ((Map.ofRotation R).φ.symm d).symm = d :=
        (Map.ofRotation R).φ.apply_symm_apply d
      rw [e] at h
      exact h.symm
    rw [this, Map.stellar_vert_up]
    exact mem_anc_inl hE hpar hn hL0 _ _
  | down d =>
    have : uN tl rv (fun q => frepF (ph rv ro) q + 1) (cdE (R := R) di (down d)) =
        vi (repF di rv ro ((Map.ofRotation R).face d)).fst := by
      rw [cdE_down, uN, ite_eq_right (by omega), ite_eq_right (by omega),
        show (3 * (di d : ℕ) + 2) / 3 = di d by omega, Nat.add_sub_cancel, ← di_repF hE d,
        hE.tl_eq]
    rw [this, Map.stellar_vert_down, ← mem_anc_inl hE hpar hn hL0]
    have hne : (.inr ((Map.ofRotation R).face d) : V ⊕ _) ≠ (liftT vi di hE hpar hn).root :=
      Sum.inr_ne_inl
    rw [Map.SpTree.anc_of_ne _ hne, mem_insert, Map.SpTree.parent_of_ne _ hne]
    simp only [reduceCtorEq, false_or]
    rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem φ_fst (e : G.Dart) : ((Map.ofRotation R).φ e).fst = e.snd := R.fst_rot e.symm

include hE in
/-- **The corners of a triangle** of the stellar subdivision which are vertices of the graph: the
two ends of the dart of the graph numbered by the triple of the triangle. -/
theorem mem_corners (δ : StDart G.Dart) (v : V) :
    (.inl v : V ⊕ _) ∈ ({(Map.ofRotation R).stellar.vert δ,
      (Map.ofRotation R).stellar.vert ((Map.ofRotation R).stellar.φ δ),
      (Map.ofRotation R).stellar.vert ((Map.ofRotation R).stellar.φ
        ((Map.ofRotation R).stellar.φ δ))} : Finset _) ↔
      (vi v : ℕ) = tl ((cdE (R := R) di δ : ℕ) / 3) ∨
        (vi v : ℕ) = tl (rv ((cdE (R := R) di δ : ℕ) / 3)) := by
  have key : ∀ e : G.Dart, ((vi v : ℕ) = tl (di e) ∨ (vi v : ℕ) = tl (rv (di e))) ↔
      (v = e.fst ∨ v = e.snd) := by
    intro e
    rw [hE.rv_eq, hE.tl_eq, hE.tl_eq, Fin.val_inj, Fin.val_inj, vi.apply_eq_iff_eq,
      vi.apply_eq_iff_eq]
    rfl
  cases δ with
  | old d =>
    rw [cdE_old, show 3 * (di d : ℕ) / 3 = di d by omega, key]
    simp only [Map.stellar_φ_old, Map.stellar_φ_up, Map.stellar_vert_old, Map.stellar_vert_up,
      Map.stellar_vert_down, Map.ofRotation_vert, Equiv.symm_apply_apply, mem_insert,
      mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false, φ_fst]
  | up d =>
    rw [cdE_up, show (3 * (di ((Map.ofRotation R).φ.symm d) : ℕ) + 1) / 3 =
      di ((Map.ofRotation R).φ.symm d) by omega, key]
    have : d.fst = ((Map.ofRotation R).φ.symm d).snd := by
      rw [← φ_fst, Equiv.apply_symm_apply]
    simp [this]
    tauto
  | down d =>
    rw [cdE_down, show (3 * (di d : ℕ) + 2) / 3 = di d by omega, key]
    simp only [Map.stellar_φ_down, Map.stellar_φ_old, Map.stellar_vert_old, Map.stellar_vert_up,
      Map.stellar_vert_down, Map.ofRotation_vert, mem_insert, mem_singleton, Sum.inl.injEq,
      reduceCtorEq, false_or, φ_fst]

end Build

/-! ### The balance of the cycle and the inside marks, for a coded plane map -/

section Coded

open WordRAM Map Map.SpTree CycleSearch CycleSearch.Coded

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {T : M.SpTree} {k : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}

open Classical in
/-- **The inside marks.** The marks written by `inLoop` for the face `F` and the flag given by
`sideOf` describe the inside of the dart `a`: a face is inside `a` exactly when its mark differs
from the flag. -/
theorem inside_marks (hC : Coded M T k cd A Tm) (hM : M.IsPlane) (hk : 0 < k) {Fw : ℕ → ℕ}
    {W : ℕ} {o : List ℕ} {c₁ : Config} (hS : SB k A Tm Fw W o c₁) (hall : c₁.nreg 11 = k)
    (im : ℕ → ℕ) (a : D) (him0 : im 0 = 0)
    (himr : ∀ G < k, G ≠ 0 → im G =
      if G = (if Tm (cd a) ≠ 0 then 0 else if IsPd c₁.nmem k (cd a) then (cd a : ℕ) / 3
        else A (cd a) / 3) then 1 else im (A (pd k c₁.nmem G) / 3)) (G : M.Face) :
    im (fi cd G) ≠ (if Tm (cd a) ≠ 0 then 0 else if IsPd c₁.nmem k (cd a) then 0 else 1) ↔
      G ∈ T.inside a := by
  have hS' := hC.isSearch hk hS hall
  set F₀ := M.face (dartN (cd := cd) hk 0)
  set pdF : M.Face → D := fun F => dartN (cd := cd) hk (pd k c₁.nmem (fi cd F))
  have hfi0 : ∀ F : M.Face, F = F₀ ↔ fi cd F = 0 := by
    intro F
    constructor
    · rintro rfl; rw [hC.fi_face, cd_dartN hk (by omega)]
    · intro h; apply hC.fi_inj; rw [h, hC.fi_face, cd_dartN hk (by omega)]
  have hpdlt : ∀ F : M.Face, fi cd F ≠ 0 → pd k c₁.nmem (fi cd F) < 3 * k := by
    intro F hF
    obtain ⟨i, hi, hq⟩ := hS.exists_pos hall (hC.fi_lt F)
    have h1 : 1 ≤ i := by
      by_contra h; obtain rfl : i = 0 := by omega
      rw [hS.q0.2] at hq; exact hF hq.symm
    have := (hS.pd_ok i h1 (by omega)).2.1
    rwa [hq] at this
  have hpar : ∀ F : M.Face, F ≠ F₀ →
      fi cd (M.face (M.α (pdF F))) = A (pd k c₁.nmem (fi cd F)) / 3 := by
    intro F hF
    rw [hC.fi_face, ← hC.A_cd, cd_dartN hk (hpdlt F ((hfi0 F).not.1 hF))]
  by_cases ht : Tm (cd a) ≠ 0
  · -- a tree dart: nothing is marked, nothing is inside
    have htree : T.IsTree a := by by_contra h; exact ht ((hC.T_cd a).2 h)
    rw [inside_eq_empty hM htree]
    simp only [ht, ne_eq, notMem_empty, iff_false, not_not]
    have hzero : ∀ F : M.Face, im (fi cd F) = 0 := by
      intro F
      induction hn : Nat.find (hC.exists_ord hS hall F) using
        Nat.strong_induction_on generalizing F with
      | _ N ih =>
        by_cases hF : F = F₀
        · rw [(hfi0 F).1 hF, him0]
        · have h0 := (hfi0 F).not.1 hF
          rw [himr _ (hC.fi_lt F) h0, ite_eq_right (by simpa [ht] using h0), ← hpar F hF]
          exact ih _ (by rw [← hn]; exact hS'.ord_lt F hF) _ rfl
    exact hzero G
  · -- a dart off the tree: the marks describe the inside of the dart `pd` of the face `Fd`
    have hT0 : Tm (cd a) = 0 := by omega
    have hnt : ¬ T.IsTree a := (hC.T_cd a).1 hT0
    simp only [ht, ↓reduceIte] at himr ⊢
    obtain ⟨Fd, hFd0, hfiFd, hpdFd⟩ : ∃ Fd : M.Face, Fd ≠ F₀ ∧
        fi cd Fd = (if IsPd c₁.nmem k (cd a) then (cd a : ℕ) / 3 else A (cd a) / 3) ∧
        pdF Fd = if IsPd c₁.nmem k (cd a) then a else M.α a := by
      by_cases hp : IsPd c₁.nmem k (cd a)
      · refine ⟨M.face a, ?_, ?_, ?_⟩
        · rw [Ne, hfi0, hC.fi_face]; exact hp.1.ne'
        · rw [hC.fi_face, ite_eq_left hp]
        · simp only [pdF, hC.fi_face, ite_eq_left hp]
          rw [show pd k c₁.nmem ((cd a : ℕ) / 3) = cd a from hp.2, dartN_cd]
      · rcases hC.pdor hk hS hall hM (cd a) (cd a).2 hT0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd ⟨Nat.pos_of_ne_zero h1, h2⟩ hp
        · refine ⟨M.face (M.α a), ?_, ?_, ?_⟩
          · rw [Ne, hfi0, hC.fi_face, ← hC.A_cd]; exact h1
          · rw [hC.fi_face, ite_eq_right hp, ← hC.A_cd]
          · simp only [pdF, hC.fi_face, ite_eq_right hp]
            rw [← hC.A_cd, h2, hC.A_cd, dartN_cd]
    have hFnz : fi cd Fd ≠ 0 := (hfi0 Fd).not.1 hFd0
    have hrec : ∀ F : M.Face, F ≠ F₀ → F ≠ Fd →
        im (fi cd F) = im (fi cd (M.face (M.α (pdF F)))) := by
      intro F hF hF'
      rw [himr _ (hC.fi_lt F) ((hfi0 F).not.1 hF), ite_eq_right, hpar F hF]
      rw [← hfiFd]; exact fun e => hF' (hC.fi_inj e)
    have hone : im (fi cd Fd) = 1 := by
      rw [himr _ (hC.fi_lt Fd) hFnz, ite_eq_left hfiFd]
    have hQ := hS'.mem_inside_iff hM hFd0 (fun F => im (fi cd F) ≠ 0)
      (by rw [(hfi0 F₀).1 rfl, him0]; exact fun h => h rfl) (by rw [hone]; exact one_ne_zero)
      (fun F hF hF' => by rw [hrec F hF hF'])
    have hQ' := hS'.mem_inside_iff hM hFd0 (fun F => im (fi cd F) = 1)
      (by rw [(hfi0 F₀).1 rfl, him0]; exact zero_ne_one) hone
      (fun F hF hF' => by rw [hrec F hF hF'])
    by_cases hp : IsPd c₁.nmem k (cd a)
    · rw [ite_eq_left hp]
      have := hQ G
      rw [hpdFd, ite_eq_left hp] at this
      exact this
    · rw [ite_eq_right hp]
      have := hQ' G
      rw [hpdFd, ite_eq_right hp, inside_α hM hnt, mem_compl] at this
      rw [← not_iff_not, not_not, this]

end Coded

end SepProg

end PlanarSeparator
