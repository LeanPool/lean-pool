/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring



/-!
# The algebraic adaptive update

The supporting linear algebra is stated over a field and is specialized to
qubits (`ZMod 2`) in `Round.lean`. These are statements about unsigned Pauli
labels. The qudit extension is outside this formalization. The identification
with unitary conjugation is proved in the physical gate modules.
-/

@[expose] public section

namespace LeanPool.SingleCopyStabilizer

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate vectors indexed by the register sites. -/
abbrev Vec (𝕜 : Type*) (ι : Type*) := ι → 𝕜
/-- Pauli labels paired into X and Z coordinate vectors. -/
abbrev Label (𝕜 : Type*) (ι : Type*) := Vec 𝕜 ι × Vec 𝕜 ι

/-- The alternating X-Z pairing controlling Pauli commutation. -/
def symplectic (a b : Label 𝕜 ι) : 𝕜 :=
  a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1

/-- Pairwise vanishing of the symplectic pairing on a label space. -/
def IsIsotropic (L : Submodule 𝕜 (Label 𝕜 ι)) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, symplectic a b = 0

/-- Z labels whose paired X coordinate is zero in the label space. -/
def diagonalSpace (L : Submodule 𝕜 (Label 𝕜 ι)) : Submodule 𝕜 (Vec 𝕜 ι) where
  carrier := {s | (0, s) ∈ L}
  zero_mem' := L.zero_mem
  add_mem' ha hb := by simpa using L.add_mem ha hb
  smul_mem' c _ ha := by simpa using L.smul_mem c ha

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem mem_diagonalSpace (L : Submodule 𝕜 (Label 𝕜 ι)) (s : Vec 𝕜 ι) :
    s ∈ diagonalSpace L ↔ (0, s) ∈ L := Iff.rfl

omit [DecidableEq ι] in
/-- Commuting with a diagonal stabilizer forces orthogonality of the X label. -/
theorem x_orthogonal_diagonal {L : Submodule 𝕜 (Label 𝕜 ι)}
    (hL : IsIsotropic L) {x z s : Vec 𝕜 ι}
    (hxz : (x, z) ∈ L) (hs : s ∈ diagonalSpace L) : x ⬝ᵥ s = 0 := by
  classical
  simpa [symplectic] using hL (x, z) hxz (0, s) hs

/-- X-coordinate action of a simultaneous controlled-SUM shear. -/
def shearX (i : ι) (w x : Vec 𝕜 ι) : Vec 𝕜 ι := x - x i • w

/-- Contragradient action on Z coordinates. -/
def shearZ (i : ι) (w z : Vec 𝕜 ι) : Vec 𝕜 ι :=
  z + (w ⬝ᵥ z) • (Pi.single i 1 : Vec 𝕜 ι)

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem shearX_pivot (i : ι) {w : Vec 𝕜 ι} (hw : w i = 0)
    (x : Vec 𝕜 ι) : shearX i w x i = x i := by
  classical
  simp [shearX, hw]

@[simp] theorem shearZ_pivot (i : ι) (w z : Vec 𝕜 ι) :
    shearZ i w z i = z i + w ⬝ᵥ z := by simp [shearZ]

/-- The two shear actions preserve the X-Z pairing. -/
theorem shear_pairing (i : ι) {w : Vec 𝕜 ι} (hw : w i = 0)
    (x z : Vec 𝕜 ι) : shearX i w x ⬝ᵥ shearZ i w z = x ⬝ᵥ z := by
  simp [shearX, shearZ, dotProduct_add, sub_dotProduct, hw]
  ring

/-- The invertible dual shear when the target mask vanishes at the pivot. -/
def shearZEquiv (i : ι) (w : Vec 𝕜 ι) (hw : w i = 0) :
    Vec 𝕜 ι ≃ₗ[𝕜] Vec 𝕜 ι where
  toFun := shearZ i w
  invFun z := z - (w ⬝ᵥ z) • (Pi.single i 1 : Vec 𝕜 ι)
  left_inv z := by
    simp [shearZ, dotProduct_add, hw]
  right_inv z := by
    simp [shearZ, dotProduct_sub, hw]
  map_add' x y := by
    simp [shearZ, dotProduct_add, add_smul]
    abel
  map_smul' c x := by
    simp [shearZ, smul_add, smul_smul]

omit [Fintype ι] in
/-- A normalized sample is concentrated on the chosen pivot. -/
theorem pivot_concentrates {u : Vec 𝕜 ι} {i : ι} (hu : u i = 1) :
    shearX i (u - (Pi.single i 1 : Vec 𝕜 ι)) u = (Pi.single i 1 : Vec 𝕜 ι) := by
  classical
  simp [shearX, hu]

/-- Orthogonality is exactly what makes the transformed old Z label vanish at the pivot. -/
theorem pivot_diagonal_zero {u s : Vec 𝕜 ι} {i : ι}
    (horth : u ⬝ᵥ s = 0) : shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) s i = 0 := by
  simp [shearZ, sub_dotProduct, horth]

/-- A local Fourier/phase correction, with determinant one over any field. -/
def localCorrection (i : ι) (b : 𝕜) (a : Label 𝕜 ι) : Label 𝕜 ι :=
  (Function.update a.1 i (a.2 i + b * a.1 i),
   Function.update a.2 i (-a.1 i))

omit [Fintype ι] in
theorem localCorrection_old_diagonal {s : Vec 𝕜 ι} {i : ι} (hs : s i = 0)
    (b : 𝕜) : localCorrection i b (0, s) = (0, s) := by
  classical
  ext j <;> by_cases hj : j = i <;> simp [localCorrection, hj, hs]

omit [Fintype ι] in
theorem localCorrection_new_diagonal (i : ι) (z : Vec 𝕜 ι) :
    localCorrection i (-z i) ((Pi.single i 1 : Vec 𝕜 ι), z) =
      (0, Function.update z i (-1)) := by
  classical
  apply Prod.ext
  · funext j
    by_cases hj : j = i <;> simp [localCorrection, hj]
  · simp [localCorrection]
/-- Compose the pivot shear with its local Fourier and phase correction. -/
def adaptiveUpdate (i : ι) (u : Vec 𝕜 ι) (b : 𝕜) (a : Label 𝕜 ι) :
    Label 𝕜 ι :=
  localCorrection i b (shearX i (u - (Pi.single i 1 : Vec 𝕜 ι)) a.1,
    shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) a.2)

theorem adaptiveUpdate_preserves_diagonal {u s : Vec 𝕜 ι} {i : ι}
    (horth : u ⬝ᵥ s = 0) (b : 𝕜) :
    adaptiveUpdate i u b (0, s) = (0, shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) s) := by
  simp only [adaptiveUpdate, shearX, Pi.zero_apply, zero_smul, sub_zero]
  exact localCorrection_old_diagonal (pivot_diagonal_zero horth) b

theorem adaptiveUpdate_creates_diagonal {u v : Vec 𝕜 ι} {i : ι} (hu : u i = 1) :
    adaptiveUpdate i u (-(shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) v) i) (u, v) =
      (0, Function.update (shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) v) i (-1)) := by
  simp only [adaptiveUpdate, pivot_concentrates hu]
  exact localCorrection_new_diagonal i _

/-- The linear map implementing the observed symplectic update. -/
def adaptiveUpdateMap (i : ι) (u : Vec 𝕜 ι) (b : 𝕜) :
    Label 𝕜 ι →ₗ[𝕜] Label 𝕜 ι where
  toFun := adaptiveUpdate i u b
  map_add' a c := by
    ext j <;> by_cases hj : j = i <;>
      simp [adaptiveUpdate, localCorrection, shearX, shearZ, hj,
        dotProduct_add, add_smul] <;> ring
  map_smul' c a := by
    ext j <;> by_cases hj : j = i <;>
      simp [adaptiveUpdate, localCorrection, shearX, shearZ, hj] <;> ring

omit [DecidableEq ι] in
theorem symplectic_eq_sum (a c : Label 𝕜 ι) :
    symplectic a c = ∑ j, (a.1 j * c.2 j - a.2 j * c.1 j) := by
  classical
  simp [symplectic, dotProduct, Finset.sum_sub_distrib]

theorem localCorrection_symplectic (i : ι) (b : 𝕜) (a c : Label 𝕜 ι) :
    symplectic (localCorrection i b a) (localCorrection i b c) = symplectic a c := by
  simp only [symplectic_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · simp [localCorrection, hj]
    ring
  · simp [localCorrection, hj]

theorem adaptiveUpdate_symplectic (i : ι) (u : Vec 𝕜 ι) (b : 𝕜)
    (hu : u i = 1) (a c : Label 𝕜 ι) :
    symplectic (adaptiveUpdate i u b a) (adaptiveUpdate i u b c) = symplectic a c := by
  have hw : (u - (Pi.single i 1 : Vec 𝕜 ι)) i = 0 := by simp [hu]
  rw [adaptiveUpdate, adaptiveUpdate, localCorrection_symplectic]
  unfold symplectic
  dsimp only
  rw [shear_pairing i hw]
  rw [dotProduct_comm (shearZ _ _ _), shear_pairing i hw, dotProduct_comm c.1 a.2]

omit [DecidableEq ι] in
theorem symplectic_nondegenerate (a : Label 𝕜 ι)
    (h : ∀ c, symplectic a c = 0) : a = 0 := by
  classical
  apply Prod.ext
  · funext i
    simpa [symplectic] using h (0, Pi.single i 1)
  · funext i
    simpa [symplectic] using h (Pi.single i 1, 0)

theorem adaptiveUpdate_injective (i : ι) (u : Vec 𝕜 ι) (b : 𝕜) (hu : u i = 1) :
    Function.Injective (adaptiveUpdateMap i u b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  apply symplectic_nondegenerate a
  intro c
  rw [← adaptiveUpdate_symplectic i u b hu]
  change symplectic ((adaptiveUpdateMap i u b) a) _ = 0
  rw [ha]
  simp [symplectic]

/-- The image label space after the observed adaptive update. -/
def updatedSpace (L : Submodule 𝕜 (Label 𝕜 ι)) (i : ι)
    (u : Vec 𝕜 ι) (b : 𝕜) : Submodule 𝕜 (Label 𝕜 ι) :=
  L.map (adaptiveUpdateMap i u b)

theorem updatedSpace_isotropic (L : Submodule 𝕜 (Label 𝕜 ι)) (hL : IsIsotropic L)
    (i : ι) (u : Vec 𝕜 ι) (b : 𝕜) (hu : u i = 1) :
    IsIsotropic (updatedSpace L i u b) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
  change symplectic (adaptiveUpdate i u b a) (adaptiveUpdate i u b c) = 0
  rw [adaptiveUpdate_symplectic i u b hu]
  exact hL a ha c hc

theorem updatedSpace_finrank (L : Submodule 𝕜 (Label 𝕜 ι))
    (i : ι) (u : Vec 𝕜 ι) (b : 𝕜) (hu : u i = 1) :
    Module.finrank 𝕜 (updatedSpace L i u b) = Module.finrank 𝕜 L := by
  exact (Submodule.equivMapOfInjective (adaptiveUpdateMap i u b)
    (adaptiveUpdate_injective i u b hu) L).finrank_eq.symm

/-- Every choice of the local correction does not decrease diagonal dimension.
Only orthogonality is needed, not membership of the sample in the X projection;
this distinction is essential to the low-nullity proof. -/
theorem diagonal_finrank_monotone
    (L : Submodule 𝕜 (Label 𝕜 ι)) (u : Vec 𝕜 ι) (i : ι) (b : 𝕜)
    (hu : u i = 1) (horth : ∀ s ∈ diagonalSpace L, u ⬝ᵥ s = 0) :
    Module.finrank 𝕜 (diagonalSpace L) ≤
      Module.finrank 𝕜 (diagonalSpace (updatedSpace L i u b)) := by
  let e := shearZEquiv i (u - (Pi.single i 1 : Vec 𝕜 ι)) (by simp [hu])
  have hle : (diagonalSpace L).map e.toLinearMap ≤
      diagonalSpace (updatedSpace L i u b) := by
    rintro s ⟨t, ht, rfl⟩
    exact ⟨(0, t), ht, adaptiveUpdate_preserves_diagonal (horth t ht) b⟩
  have hdim := Submodule.finrank_mono hle
  simpa only [LinearEquiv.finrank_map_eq] using hdim

omit [Fintype ι] in
/-- The newly created diagonal label is outside the span of all old labels,
because the entire old subspace vanishes at the pivot. -/
theorem new_diagonal_independent {D : Submodule 𝕜 (Vec 𝕜 ι)} {i : ι}
    (hD : ∀ s ∈ D, s i = 0) (z : Vec 𝕜 ι) :
    Function.update z i (-1) ∉ D := by
  classical
  intro hz
  have h := hD _ hz
  simp at h

/-- Exact algebraic content of the increase in diagonal-stabilizer dimension.
`L'` can be any submodule containing the updated labels; no dimension increase
is assumed. The result is deduced from the explicit fresh pivot coordinate. -/
theorem diagonal_finrank_strict_progress
    (L L' : Submodule 𝕜 (Label 𝕜 ι)) (u v : Vec 𝕜 ι) (i : ι)
    (hu : u i = 1) (huv : (u, v) ∈ L)
    (horth : ∀ s ∈ diagonalSpace L, u ⬝ᵥ s = 0)
    (hupdate : ∀ a ∈ L,
      adaptiveUpdate i u (-(shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) v) i) a ∈ L') :
    Module.finrank 𝕜 (diagonalSpace L) < Module.finrank 𝕜 (diagonalSpace L') := by
  let e := shearZEquiv i (u - (Pi.single i 1 : Vec 𝕜 ι)) (by simp [hu])
  let D := (diagonalSpace L).map e.toLinearMap
  have hle : D ≤ diagonalSpace L' := by
    rintro s ⟨t, ht, rfl⟩
    have h := hupdate (0, t) ht
    rw [adaptiveUpdate_preserves_diagonal (horth t ht)] at h
    exact h
  have hzero : ∀ s ∈ D, s i = 0 := by
    rintro s ⟨t, ht, rfl⟩
    exact pivot_diagonal_zero (horth t ht)
  let z := Function.update (shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) v) i (-1)
  have hz : z ∈ diagonalSpace L' := by
    have h := hupdate (u, v) huv
    rw [adaptiveUpdate_creates_diagonal hu] at h
    exact h
  have hn : z ∉ D := new_diagonal_independent hzero _
  have hlt : D < diagonalSpace L' := lt_of_le_of_ne hle (by
    intro heq
    exact hn (heq.symm ▸ hz))
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  simpa only [D, LinearEquiv.finrank_map_eq] using hdim

/-- For an isotropic space and a genuine nonzero stabilizer X label,
there exists a local slope which strictly increases diagonal dimension. -/
theorem exists_diagonal_finrank_progress
    (L : Submodule 𝕜 (Label 𝕜 ι)) (hL : IsIsotropic L)
    (u v : Vec 𝕜 ι) (i : ι) (hu : u i = 1) (huv : (u, v) ∈ L) :
    ∃ b : 𝕜, Module.finrank 𝕜 (diagonalSpace L) <
      Module.finrank 𝕜 (diagonalSpace (updatedSpace L i u b)) := by
  refine ⟨-(shearZ i (u - (Pi.single i 1 : Vec 𝕜 ι)) v) i, ?_⟩
  apply diagonal_finrank_strict_progress L _ u v i hu huv
  · intro s hs
    exact x_orthogonal_diagonal hL huv hs
  · intro a ha
    exact ⟨a, ha, rfl⟩

end LeanPool.SingleCopyStabilizer
