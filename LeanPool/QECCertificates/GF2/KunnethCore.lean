/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.Basic

/-!
# The tensor intersection of subspaces: the dimension of `{X : columns ⊆ U ∧ rows ⊆ W}`

The whole difficulty of the dimension tensor formula $k = k_1k_2 + k_1^\top k_2^\top$ is
concentrated in one fact: **the space of matrices whose columns lie in $U$ and whose rows
lie in $W$ has dimension exactly $\dim U\cdot\dim W$** (the dimension count of a subspace
tensor intersection, that is, the dimension of $U\otimes W$).

This module proves it in one go (`finrank_colsRows`), by an **explicit equivalence**
rather than a dimension argument:

* take a basis $u$ of $U$ together with the **coordinate read-back** linear map $L$ on
  `Fin a → Vec p` (a left inverse of an independent family,
  `exists_leftInverse_of_linearIndependent`)
* the coefficient expansion `vee` ($a\times s$ coefficients ↦ $p\times s$ matrices) and
  the coordinate extraction `wedge` ($p\times s$ matrices ↦ $a\times s$ coefficients) are
  mutually inverse
* the key step: **the row condition is unaffected by `wedge`**, which translates "the
  rows all lie in $W$" into "the rows all lie in $W$", so
  $\{columns\subseteq U,\ rows\subseteq W\}\cong \{\text{rows}\subseteq W\}$, and the
  latter is isomorphic to `Fin a → W`, of dimension $a\cdot\dim W$.

The first two auxiliary facts (the dimensions of the column- and row-constrained spaces)
are `finrank_colsSub` / `finrank_rowsSub`.

## Index conventions

Matrices are always written with **product indexing**,
`VMat p s = Fin p × Fin s → ZMod 2` (the same row type as `hgpHX`), and are never
flattened into `Fin`; the structural theorem therefore needs no relabelling.
-/

@[expose] public section

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {p q r s a b : ℕ}

/-! ## 1. Product-indexed matrices and the two constrained subspaces -/

/-- A product-indexed matrix: rows `Fin p`, columns `Fin s`. -/
abbrev VMat (p s : ℕ) := Fin p × Fin s → ZMod 2

/-- Column `j` (as a `Vec p`). -/
def colOf {p s : ℕ} (X : VMat p s) (j : Fin s) : Vec p := fun i => X (i, j)

/-- Row `i` (as a `Vec s`). -/
def rowOf {p s : ℕ} (X : VMat p s) (i : Fin p) : Vec s := fun j => X (i, j)

@[simp] lemma colOf_apply {X : VMat p s} {j : Fin s} {i : Fin p} : colOf X j i = X (i, j) := rfl

@[simp] lemma rowOf_apply {X : VMat p s} {i : Fin p} {j : Fin s} : rowOf X i j = X (i, j) := rfl

@[simp] lemma colOf_add {X Y : VMat p s} {j : Fin s} : colOf (X + Y) j = colOf X j + colOf Y j :=
    rfl

@[simp] lemma colOf_smul {c : ZMod 2} {X : VMat p s} {j : Fin s} :
    colOf (c • X) j = c • colOf X j := rfl

@[simp] lemma rowOf_add {X Y : VMat p s} {i : Fin p} : rowOf (X + Y) i = rowOf X i + rowOf Y i :=
    rfl

@[simp] lemma rowOf_smul {c : ZMod 2} {X : VMat p s} {i : Fin p} :
    rowOf (c • X) i = c • rowOf X i := rfl

/-- **The column-constrained subspace**: the matrices all of whose columns lie in `U`. -/
def colsSub (U : Submodule (ZMod 2) (Vec p)) : Submodule (ZMod 2) (VMat p s) where
  carrier := {X | ∀ j, colOf X j ∈ U}
  zero_mem' := fun j => U.zero_mem
  add_mem' := fun {X Y} hX hY => fun j => by
    rw [colOf_add]; exact U.add_mem (hX j) (hY j)
  smul_mem' := fun c {X} hX => fun j => by
    rw [colOf_smul]; exact U.smul_mem c (hX j)

/-- **The row-constrained subspace**: the matrices all of whose rows lie in `W`. -/
def rowsSub (W : Submodule (ZMod 2) (Vec s)) : Submodule (ZMod 2) (VMat p s) where
  carrier := {X | ∀ i, rowOf X i ∈ W}
  zero_mem' := fun i => W.zero_mem
  add_mem' := fun {X Y} hX hY => fun i => by
    rw [rowOf_add]; exact W.add_mem (hX i) (hY i)
  smul_mem' := fun c {X} hX => fun i => by
    rw [rowOf_smul]; exact W.smul_mem c (hX i)

@[simp] lemma mem_colsSub {U : Submodule (ZMod 2) (Vec p)} {X : VMat p s} :
    X ∈ colsSub U ↔ ∀ j, colOf X j ∈ U :=
  ⟨fun h => h, fun h => h⟩

@[simp] lemma mem_rowsSub {W : Submodule (ZMod 2) (Vec s)} {X : VMat p s} :
    X ∈ rowsSub W ↔ ∀ i, rowOf X i ∈ W :=
  ⟨fun h => h, fun h => h⟩

/-! ## 2. The dimensions of the column- and row-constrained spaces -/

/-- An explicit linear equivalence between the matrices with all columns in `U` and
`Fin s → U` (reading column by column). -/
noncomputable def colsSubEquiv (U : Submodule (ZMod 2) (Vec p)) :
    ↥(colsSub (s := s) U) ≃ₗ[ZMod 2] (Fin s → U) where
  toFun X := fun j => ⟨colOf X.1 j, X.2 j⟩
  invFun f := ⟨fun ij => (f ij.2).1 ij.1, fun j => (f j).2⟩
  left_inv X := by ext ⟨i, j⟩; rfl
  right_inv f := by ext j i; rfl
  map_add' X Y := by ext j i; rfl
  map_smul' c X := by ext j i; rfl

/-- An explicit linear equivalence between the matrices with all rows in `W` and
`Fin p → W` (reading row by row). -/
noncomputable def rowsSubEquiv (W : Submodule (ZMod 2) (Vec s)) :
    ↥(rowsSub (p := p) (s := s) W) ≃ₗ[ZMod 2] (Fin p → W) where
  toFun X := fun i => ⟨rowOf X.1 i, X.2 i⟩
  invFun f := ⟨fun ij => (f ij.1).1 ij.2, fun i => (f i).2⟩
  left_inv X := by ext ⟨i, j⟩; rfl
  right_inv f := by ext i j; rfl
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl

/-- **The dimension of the column-constrained space**:
$\dim\{X : \mathrm{col}\,X\subseteq U\} = s\cdot\dim U$. -/
theorem finrank_colsSub (U : Submodule (ZMod 2) (Vec p)) :
    Module.finrank (ZMod 2) (colsSub (s := s) U) = s * Module.finrank (ZMod 2) U := by
  rw [(colsSubEquiv (s := s) U).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp

/-- **The dimension of the row-constrained space**:
$\dim\{X : \mathrm{row}\,X\subseteq W\} = p\cdot\dim W$. -/
theorem finrank_rowsSub (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) (rowsSub (p := p) W) = p * Module.finrank (ZMod 2) W := by
  rw [(rowsSubEquiv (p := p) W).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp

/-! ## 3. Coordinate read-back of an independent family (left inverse) -/

/-- The matrix representation of a linear map in the standard basis:
`L x = Σ_i x_i · L(e_i)`. -/
lemma linearMap_apply_eq_sum_single (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (x : Vec p) :
    L x = fun k => ∑ i, x i * L (Pi.single i (1 : ZMod 2)) k := by
  conv_lhs => rw [show x = ∑ i, x i • (Pi.single i (1 : ZMod 2)) from by
    funext j
    simp [Pi.single_apply]]
  funext k
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]

/-- **Left inverse of an independent family**: when `u : Fin a → Vec p` is linearly
independent, there is a linear map `L` that reads the coefficients $c$ back from any
combination $\sum_k c_k u_k$.

The construction: the combination map $\varphi(c)=\sum_k c_k u_k$ is injective by
independence, and one takes a left inverse of it on the whole space
(`LinearMap.exists_leftInverse_of_injective`: over a vector space every injective linear
map has a left inverse). -/
theorem exists_leftInverse_of_linearIndependent {u : Fin a → Vec p}
    (hu : LinearIndependent (ZMod 2) u) :
    ∃ L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2), ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c := by
  classical
  let φ : (Fin a → ZMod 2) →ₗ[ZMod 2] Vec p :=
    { toFun := fun c => ∑ k, c k • u k
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply,
          smul_eq_mul] }
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext k
    exact Fintype.linearIndependent_iff.mp hu c hc k
  obtain ⟨L, hL⟩ := φ.exists_leftInverse_of_injective hker
  exact ⟨L, fun c => LinearMap.congr_fun hL c⟩

/-! ## 4. Coefficient expansion `vee` and coordinate extraction `wedge` -/

/-- **Coefficient expansion**: expands an `a×s` coefficient matrix along the basis vectors
of `U` into a `p×s` matrix (column `j` is $\sum_k C_{kj}u_k$). -/
noncomputable def vee (u : Fin a → Vec p) : VMat a s →ₗ[ZMod 2] VMat p s where
  toFun C := fun ij => ∑ k, C (k, ij.2) * u k ij.1
  map_add' C D := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c C := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- **Coordinate extraction**: reads each column of a `p×s` matrix as coefficients, through
the left inverse `L`. -/
noncomputable def wedge (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) : VMat p s →ₗ[ZMod 2] VMat a s where
  toFun X := fun kj => L (colOf X kj.2) kj.1
  map_add' X Y := by
    ext ⟨k, j⟩
    simp only [Pi.add_apply, colOf_add, map_add, Pi.add_apply]
  map_smul' c X := by
    ext ⟨k, j⟩
    simp only [Pi.smul_apply, colOf_smul, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

@[simp] lemma vee_apply (u : Fin a → Vec p) (C : VMat a s) (i : Fin p) (j : Fin s) :
    vee u C (i, j) = ∑ k, C (k, j) * u k i := rfl

@[simp] lemma wedge_apply (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (X : VMat p s)
    (k : Fin a) (j : Fin s) : wedge L X (k, j) = L (colOf X j) k := rfl

/-- `vee` after `wedge` is the identity (on the column-constrained space): `vee` is a left
inverse of `wedge`. -/
lemma vee_wedge_of_coords {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {U : Submodule (ZMod 2) (Vec p)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s} (hX : ∀ j, colOf X j ∈ U) :
    vee u (wedge L X) = X := by
  ext ⟨i, j⟩
  simp only [vee_apply, wedge_apply]
  have h := congrFun (hcoords (colOf X j) (hX j)) i
  simpa using h

/-- `wedge` after `vee` is the identity (everywhere): `vee` is a right inverse of
`wedge`. -/
lemma wedge_vee {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    (hleft : ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c) (C : VMat a s) :
    wedge L (vee u C) = C := by
  ext ⟨k, j⟩
  simp only [wedge_apply]
  have hcol : colOf (vee u C) j = ∑ k', C (k', j) • u k' := by
    funext i
    rw [colOf_apply, vee_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul]
  rw [hcol, hleft]

/-! ## 5. The row condition under `wedge` -/

/-- **The row condition pushes forward**: if the rows of `X` all lie in `W`, then so do the
rows of `wedge L X` (substituting the matrix representation `L x = Σ_i x_i · L(e_i)` into
the row sums of `wedge`). -/
lemma rowOf_wedge_mem {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {W : Submodule (ZMod 2) (Vec s)} {X : VMat p s} (hX : ∀ i, rowOf X i ∈ W) :
    ∀ k, rowOf (wedge L X) k ∈ W := by
  intro k
  have hrow : rowOf (wedge L X) k = ∑ i : Fin p, (L (Pi.single i (1 : ZMod 2)) k) • rowOf X i := by
    funext j
    rw [rowOf_apply, wedge_apply, linearMap_apply_eq_sum_single L (colOf X j)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply, colOf_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hrow]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i)

/-- **The row condition pulls back**: if the rows of `wedge L X` all lie in `W` and the
columns of `X` all lie in `U`, then the rows of `X` all lie in `W` (using
`vee_wedge_of_coords` to write the rows of `X` as combinations of the rows of
`wedge L X`). -/
lemma rowOf_mem_of_wedge_rowOf_mem {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {U : Submodule (ZMod 2) (Vec p)} {W : Submodule (ZMod 2) (Vec s)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s}
    (hX : ∀ j, colOf X j ∈ U) (hY : ∀ k, rowOf (wedge L X) k ∈ W) :
    ∀ i, rowOf X i ∈ W := by
  intro i
  have hrow : rowOf X i = ∑ k, (u k i) • rowOf (wedge L X) k := by
    funext j
    have h := congrFun (vee_wedge_of_coords hcoords hX) (i, j)
    simp only [vee_apply, wedge_apply, rowOf_apply] at h ⊢
    rw [← h]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hrow]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hY k)

/-! ## 6. Main theorem: the dimension of the tensor intersection -/

/-- **The dimension of the tensor intersection**: the space of matrices with columns in
`U` and rows in `W` has dimension exactly $\dim U\cdot\dim W$.

This is the **only** nontrivial dimension input to the tensor formula
$k=k_1k_2+k_1^\top k_2^\top$ (the dimension of $U\otimes W$ in the language of matrices).
The proof goes through an explicit equivalence:

$$\{X:\mathrm{col}\,X\subseteq U,\ \mathrm{row}\,X\subseteq W\}\;\cong\;\mathrm{Fin}\,a\to W,
\qquad a=\dim U,$$

the forward map extracting coordinates with `wedge` and then taking rows, the backward map
forming `vee` from the `W`-combinations of the coefficient rows. -/
theorem finrank_colsRows (U : Submodule (ZMod 2) (Vec p)) (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) ↥(colsSub (s := s) U ⊓ rowsSub (s := s) W)
      = Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) W := by
  classical
  let bu : Module.Basis (Fin (Module.finrank (ZMod 2) U)) (ZMod 2) U := Module.finBasis (ZMod 2) U
  let u : Fin (Module.finrank (ZMod 2) U) → Vec p := fun k => (bu k : Vec p)
  have hu : LinearIndependent (ZMod 2) u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcU : (∑ k, c k • bu k : U) = 0 := by
      apply Subtype.ext
      simpa [u] using hc
    intro k
    exact Fintype.linearIndependent_iff.mp bu.linearIndependent c hcU k
  obtain ⟨L, hL⟩ := exists_leftInverse_of_linearIndependent hu
  have hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x := by
    intro x hx
    have hspan : x ∈ Submodule.span (ZMod 2) (Set.range u) := by
      have h1 : (⟨x, hx⟩ : U) ∈ Submodule.span (ZMod 2) (Set.range bu) := by
        rw [bu.span_eq]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := bu)
          (x := (⟨x, hx⟩ : U))).mp h1
      refine (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := u) (x := x)).mpr ⟨c, ?_⟩
      have hval := congrArg (fun y : U => (y : Vec p)) hc
      simpa [u] using hval
    obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank (ZMod 2) U) → ZMod 2, ∑ i, c i • u i = x :=
      (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := u) (x := x)).mp hspan
    rw [← hc, hL c]
  have hcolW : ∀ f : Fin (Module.finrank (ZMod 2) U) → W,
      ∀ j, colOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) j ∈ U := by
    intro f j
    have hfun : colOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) j
        = ∑ k, (((f k : W) : Vec s) j) • u k := by
      funext i
      rw [colOf_apply, vee_apply, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (show u k ∈ U from (bu k).2)
  have hrowW : ∀ f : Fin (Module.finrank (ZMod 2) U) → W,
      ∀ i, rowOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) i ∈ W := by
    intro f i
    refine rowOf_mem_of_wedge_rowOf_mem hcoords (fun j => hcolW f j) (fun k => ?_) i
    rw [wedge_vee hL]
    exact (f k).2
  have he : ↥(colsSub (s := s) U ⊓ rowsSub (s := s) W) ≃ₗ[ZMod 2]
      (Fin (Module.finrank (ZMod 2) U) → W) :=
    { toFun := fun X => fun k =>
        ⟨rowOf (wedge L X.1) k, rowOf_wedge_mem (X := X.1) (fun i => X.2.2 i) k⟩
      invFun := fun f => ⟨vee u (fun kj => ((f kj.1 : W) : Vec s) kj.2), hcolW f, hrowW f⟩
      left_inv := by
        intro X
        apply Subtype.ext
        exact vee_wedge_of_coords hcoords (fun j => X.2.1 j)
      right_inv := by
        intro f
        funext k
        apply Subtype.ext
        funext j
        simpa using congrFun (wedge_vee (s := s) hL
          (fun kj => ((f kj.1 : W) : Vec s) kj.2)) (k, j)
      map_add' := by
        intro X Y
        funext k
        apply Subtype.ext
        funext j
        change wedge L (X.1 + Y.1) (k, j) = wedge L X.1 (k, j) + wedge L Y.1 (k, j)
        rw [map_add, Pi.add_apply]
      map_smul' := by
        intro c X
        funext k
        apply Subtype.ext
        funext j
        change wedge L (c • X.1) (k, j) = c * wedge L X.1 (k, j)
        rw [map_smul, Pi.smul_apply, smul_eq_mul] }
  rw [he.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp

end QECCertificates
