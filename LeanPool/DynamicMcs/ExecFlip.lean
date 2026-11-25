/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec
public import LeanPool.DynamicMcs.Refinement

/-!
# Boolean adjacency updates realize abstract edge flips

The shape condition gives in-bounds access to every entry of the matrix.
Updating one undirected edge preserves symmetry and looplessness.
-/

@[expose] public section

namespace DynamicMcs

namespace ExecFlip

/-- `atRow` at an in-range index is the corresponding list entry. -/
lemma atRow_get_eq (row : List Bool) (j : ℕ) (hj : j < row.length) :
    atRow row j = row.get ⟨j, hj⟩ := by
  induction row generalizing j with
  | nil => exfalso; exact Nat.not_lt_zero j hj
  | cons b rest ih =>
      cases j with
      | zero => rfl
      | succ k =>
          rw [atRow]
          exact ih k (Nat.succ_lt_succ_iff.mp hj)

/-- `atRow` at an out-of-range index is `false`. -/
lemma atRow_eq_of_not_lt (row : List Bool) (j : ℕ) (hj : ¬ j < row.length) :
    atRow row j = false := by
  induction row generalizing j with
  | nil => rfl
  | cons b rest ih =>
      cases j with
      | zero => exfalso; exact hj (by simp)
      | succ k =>
          rw [atRow]
          exact ih k (by intro hk; exact hj (by simp [hk]))

/-! ## `getAdj` under well-shapedness -/

/-- For an out-of-range read (`x ≥ n` or `y ≥ n`) on a well-shaped matrix, the
adjacency reads `false`. -/
lemma getAdj_wellShaped_of_not (hshape : WellShaped n a) (x y : ℕ)
    (hout : ¬ (x < n ∧ y < n)) : getAdj a x y = false := by
  classical
  by_cases hxn : x < n
  · have hyn : ¬ y < n := by omega
    rcases hshape.2 x hxn with ⟨row, hrow, hrowlen⟩
    unfold getAdj
    rw [hrow]
    change atRow row y = false
    rw [atRow_eq_of_not_lt row y (by intro hyrow; exact hyn (by simpa [hrowlen] using hyrow))]
  · unfold getAdj
    have hlen_ge : a.length ≤ x := by
      have hnx : n ≤ x := Nat.le_of_not_gt hxn
      rw [hshape.1]
      exact hnx
    rw [show a[x]? = none by exact List.getElem?_eq_none hlen_ge]

/-! ## `setEdge` preserves well-shapedness and flips exactly the target -/

/-- `List.mapIdx` preserves list length. -/
lemma length_mapIdx_ (l : List α) (f : ℕ → α → β) : (l.mapIdx f).length = l.length := by
  simp

/-- The flip of a well-shaped matrix stays well-shaped. -/
lemma setEdge_wellShaped (hshape : WellShaped n a) (u v : ℕ) (present : Bool) :
    WellShaped n (setEdge a u v present) := by
  constructor
  · unfold setEdge
    rw [length_mapIdx_, hshape.1]
  · intro x hx
    rcases hshape.2 x hx with ⟨row, hrow, hrowlen⟩
    refine ⟨row.mapIdx (fun j b => if x = u ∧ j = v ∨ x = v ∧ j = u then present else b), ?_, ?_⟩
    · unfold setEdge
      rw [List.getElem?_mapIdx]
      rw [hrow]
      rfl
    · rw [length_mapIdx_, hrowlen]

/-- Flipping a single row: `atRow` of the mapIdx-flipped row equals the
original `atRow` except at the two columns `v` (if `x = u`) and `u` (if
`x = v`). -/
lemma row_mapIdx_flip (row : List Bool) (u v : ℕ) (present : Bool) (x y : ℕ) (hy : y < row.length) :
    atRow (row.mapIdx (fun j b => if x = u ∧ j = v ∨ x = v ∧ j = u then present else b)) y =
      (if x = u ∧ y = v ∨ x = v ∧ y = u then present else atRow row y) := by
  rw [show atRow
        (row.mapIdx (fun j b => if x = u ∧ j = v ∨ x = v ∧ j = u then present else b)) y =
      (row.mapIdx (fun j b => if x = u ∧ j = v ∨ x = v ∧ j = u then present else b))[y]'(by
        simp [hy]) by
      rw [atRow_get_eq]
      rfl]
  rw [List.getElem_mapIdx]
  rw [atRow_get_eq row y hy]
  rfl

/-- Reading the flipped matrix at an in-bounds position `(x, y)`: the value is
`present` exactly at the two target positions `(u, v)` and `(v, u)`, and is
unchanged elsewhere. -/
lemma getAdj_setEdge_of_lt (hshape : WellShaped n a) (u v : ℕ) (present : Bool) (x y : ℕ)
    (hx : x < n) (hy : y < n) :
    getAdj (setEdge a u v present) x y =
      (if x = u ∧ y = v ∨ x = v ∧ y = u then present else getAdj a x y) := by
  classical
  rcases hshape.2 x hx with ⟨rowx, hrowx, hrowxlen⟩
  have hy' : y < rowx.length := by simpa [hrowxlen] using hy
  unfold getAdj setEdge
  rw [List.getElem?_mapIdx]
  simp only [hrowx]
  simp only [Option.map]
  rw [row_mapIdx_flip rowx u v present x y hy']

/-! ## Flip preserves symmetry and loop-freeness -/

/-- `setEdge` preserves the symmetry of the adjacency matrix, provided the
matrix is well-shaped.  The flip condition is symmetric in `u`/`v` and swaps
harmlessly with the `(x, y)` ↦ `(y, x)` exchange, so the flipped matrix stays
symmetric whenever the original matrix was. -/
theorem setEdge_preserves_symm (n : ℕ) (a : Adj) (u v : ℕ) (present : Bool)
    (hshape : WellShaped n a)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i) :
    ∀ x y : ℕ,
      getAdj (setEdge a u v present) x y =
        getAdj (setEdge a u v present) y x := by
  classical
  intro x y
  by_cases hxy : x < n ∧ y < n
  · rcases hxy with ⟨hx, hy⟩
    rw [getAdj_setEdge_of_lt hshape u v present x y hx hy,
        getAdj_setEdge_of_lt hshape u v present y x hy hx]
    by_cases c : x = u ∧ y = v ∨ x = v ∧ y = u
    · have c' : y = u ∧ x = v ∨ y = v ∧ x = u := by omega
      simp [c, c']
    · have c' : ¬ (y = u ∧ x = v ∨ y = v ∧ x = u) := by omega
      simp only [c, ↓reduceIte, c']
      exact hsymm x y
  · have hset := setEdge_wellShaped hshape u v present
    rw [getAdj_wellShaped_of_not hset x y hxy,
        getAdj_wellShaped_of_not hset y x (by simpa [and_comm] using hxy)]

/-- `setEdge` preserves loop-freeness of the matrix, provided the two flipped
indices are distinct.  If `u = v`, the flip would set the diagonal entry
`(u, u)` to `present`, which breaks loop-freeness when `present = true`; we
therefore require `u ≠ v`. -/
theorem setEdge_preserves_loopless (n : ℕ) (a : Adj) (u v : ℕ) (present : Bool)
    (hshape : WellShaped n a)
    (hloop : ∀ i : ℕ, getAdj a i i = false) (huv : u ≠ v) :
    ∀ x : ℕ, getAdj (setEdge a u v present) x x = false := by
  intro x
  by_cases hxn : x < n
  · rw [getAdj_setEdge_of_lt hshape u v present x x hxn hxn]
    have hn : ¬ (x = u ∧ x = v ∨ x = v ∧ x = u) := by
      intro h
      rcases h with ⟨⟨hu, hv⟩, ⟨hv2, hu2⟩⟩ | ⟨⟨hu2, hv2⟩, ⟨hv3, hu3⟩⟩
      · exfalso; exact huv (by omega)
      · exfalso; exact huv (by omega)
    rw [ite_eq_right hn]
    exact hloop x
  · have hout : ¬ (x < n ∧ x < n) := by omega
    exact getAdj_wellShaped_of_not (setEdge_wellShaped hshape u v present) x x hout

/-! ## Edge-staying-symmetric / loop-free wrappers -/

/-- `insertEdge` (a flip with `present = true`) stays symmetric. -/
lemma insertEdge_symm (a : Adj) (u v : ℕ)
    (hshape : WellShaped n a)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i) :
    ∀ i j : ℕ, getAdj (insertEdge a u v) i j =
      getAdj (insertEdge a u v) j i := by
  simpa [insertEdge] using (setEdge_preserves_symm n a u v true hshape hsymm)

/-- `insertEdge` stays loop-free. -/
lemma insertEdge_loopless (a : Adj) (u v : ℕ)
    (hshape : WellShaped n a)
    (hloop : ∀ i : ℕ, getAdj a i i = false) (huv : u ≠ v) :
    ∀ i : ℕ, getAdj (insertEdge a u v) i i = false := by
  simpa [insertEdge] using (setEdge_preserves_loopless n a u v true hshape hloop huv)

/-- `deleteEdge` stays symmetric. -/
lemma deleteEdge_symm (a : Adj) (u v : ℕ)
    (hshape : WellShaped n a)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i) :
    ∀ i j : ℕ, getAdj (deleteEdge a u v) i j =
      getAdj (deleteEdge a u v) j i := by
  simpa [deleteEdge] using (setEdge_preserves_symm n a u v false hshape hsymm)

/-- `deleteEdge` stays loop-free. -/
lemma deleteEdge_loopless (a : Adj) (u v : ℕ)
    (hshape : WellShaped n a)
    (hloop : ∀ i : ℕ, getAdj a i i = false) (huv : u ≠ v) :
    ∀ i : ℕ, getAdj (deleteEdge a u v) i i = false := by
  simpa [deleteEdge] using (setEdge_preserves_loopless n a u v false hshape hloop huv)

/-! ## FlipOf between the abstract graphs of `a` and its executable flips -/

/-- Updating an undirected matrix entry can change only the corresponding graph edge. -/
theorem setEdge_is_flip (n : ℕ) (a : Adj) (u v : Vert n) (present : Bool)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i)
    (hloop : ∀ i : ℕ, getAdj a i i = false)
    (hshape : WellShaped n a)
    (huv : u.val ≠ v.val) :
    let G := toUGraph (n := n) a hsymm hloop
    let G' := toUGraph (n := n) (setEdge a u.val v.val present)
      (setEdge_preserves_symm n a u.val v.val present hshape hsymm)
      (setEdge_preserves_loopless n a u.val v.val present hshape hloop huv)
    UGraph.FlipOf G G' u v := by
  classical
  constructor
  · intro h
    exact huv (congrArg Fin.val h)
  · intro x y
    dsimp [toUGraph]
    have hflip : getAdj (setEdge a u.val v.val present) x.val y.val =
        (if x.val = u.val ∧ y.val = v.val ∨ x.val = v.val ∧ y.val = u.val
          then present else getAdj a x.val y.val) := by
      exact getAdj_setEdge_of_lt hshape u.val v.val present x.val y.val x.2 y.2
    rw [hflip]
    by_cases hc : x.val = u.val ∧ y.val = v.val ∨ x.val = v.val ∧ y.val = u.val
    · rcases hc with h | h
      · right; left
        exact ⟨Fin.eq_of_val_eq h.1, Fin.eq_of_val_eq h.2⟩
      · right; right
        exact ⟨Fin.eq_of_val_eq h.1, Fin.eq_of_val_eq h.2⟩
    · simp [hc]

/-- Matrix insertion realizes the abstract edge flip relation. -/
theorem insert_is_flip (n : ℕ) (a : Adj) (u v : Vert n)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i)
    (hloop : ∀ i : ℕ, getAdj a i i = false)
    (hshape : WellShaped n a)
    (huv : u.val ≠ v.val) :
    let G := toUGraph (n := n) a hsymm hloop
    let G' := toUGraph (n := n) (insertEdge a u.val v.val)
      (insertEdge_symm a u.val v.val hshape hsymm)
      (insertEdge_loopless a u.val v.val hshape hloop huv)
    UGraph.FlipOf G G' u v :=
  setEdge_is_flip n a u v true hsymm hloop hshape huv

/-- Matrix deletion realizes the abstract edge flip relation. -/
theorem delete_is_flip (n : ℕ) (a : Adj) (u v : Vert n)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i)
    (hloop : ∀ i : ℕ, getAdj a i i = false)
    (hshape : WellShaped n a)
    (huv : u.val ≠ v.val) :
    let G := toUGraph (n := n) a hsymm hloop
    let G' := toUGraph (n := n) (deleteEdge a u.val v.val)
      (deleteEdge_symm a u.val v.val hshape hsymm)
      (deleteEdge_loopless a u.val v.val hshape hloop huv)
    UGraph.FlipOf G G' u v :=
  setEdge_is_flip n a u v false hsymm hloop hshape huv

/-- After an executable edge insertion, the recomputed `mcsOrder` of the
new matrix is a valid abstract MCS ordering of the new graph, and its values
are exactly `mcsOrder` of the new matrix. -/
theorem exec_insert_recompute_valid (n : ℕ) (a : Adj) (u v : Vert n)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i)
    (hloop : ∀ i : ℕ, getAdj a i i = false)
    (hshape : WellShaped n a)
    (huv : u.val ≠ v.val) :
    let a' := insertEdge a u.val v.val
    let G' := toUGraph (n := n) a'
      (setEdge_preserves_symm n a u.val v.val true hshape hsymm)
      (setEdge_preserves_loopless n a u.val v.val true hshape hloop huv)
    ∃ (ord : List (Vert n)),
      UGraph.IsMCSOrdering G' ord ∧
        ord.map (fun w => w.val) = mcsOrder a' := by
  let a' := insertEdge a u.val v.val
  change ∃ (ord : List (Vert n)),
    UGraph.IsMCSOrdering
      (toUGraph (n := n) a'
        (insertEdge_symm a u.val v.val hshape hsymm)
        (insertEdge_loopless a u.val v.val hshape hloop huv)) ord ∧
      ord.map (fun w => w.val) = mcsOrder a'
  exact ExecBridge.mcsOrder_eq_greedySuffix a'
    (insertEdge_symm a u.val v.val hshape hsymm)
    (insertEdge_loopless a u.val v.val hshape hloop huv)
    (setEdge_wellShaped hshape u.val v.val true).1

/-- After an executable edge deletion, the recomputed `mcsOrder` of the
new matrix is a valid abstract MCS ordering of the new graph.  (The executable
recomputation needs no assumption that the edge was present.) -/
theorem exec_delete_recompute_valid (n : ℕ) (a : Adj) (u v : Vert n)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i)
    (hloop : ∀ i : ℕ, getAdj a i i = false)
    (hshape : WellShaped n a)
    (huv : u.val ≠ v.val) :
    let a' := deleteEdge a u.val v.val
    let G' := toUGraph (n := n) a'
      (deleteEdge_symm a u.val v.val hshape hsymm)
      (deleteEdge_loopless a u.val v.val hshape hloop huv)
    ∃ (ord : List (Vert n)),
      UGraph.IsMCSOrdering G' ord ∧
        ord.map (fun w => w.val) = mcsOrder a' := by
  let a' := deleteEdge a u.val v.val
  change ∃ (ord : List (Vert n)),
    UGraph.IsMCSOrdering
      (toUGraph (n := n) a'
        (deleteEdge_symm a u.val v.val hshape hsymm)
        (deleteEdge_loopless a u.val v.val hshape hloop huv)) ord ∧
      ord.map (fun w => w.val) = mcsOrder a'
  exact ExecBridge.mcsOrder_eq_greedySuffix a'
    (deleteEdge_symm a u.val v.val hshape hsymm)
    (deleteEdge_loopless a u.val v.val hshape hloop huv)
    (setEdge_wellShaped hshape u.val v.val false).1

end ExecFlip
end DynamicMcs
