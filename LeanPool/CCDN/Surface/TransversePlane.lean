/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Plane.FiniteFieldBadPlanes
import LeanPool.CCDN.Algebra.PrimitiveNormalization
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import LeanPool.CCDN.Determinant.PlaneMultiplicity
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Noether.ShearNormalization
import LeanPool.CCDN.Noether.UniversalPlaneSpecialization

/-! Irreducible plane sections transverse to a prescribed direction.
The avoidance condition also ensures that a second equation restricts
nontrivially, by requiring its value at the plane's base point to be nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The algebra map restricting a polynomial to the plane parametrized by
`(s, t) ↦ a + s b + t c`, sending `Xᵢ` to `aᵢ + bᵢ X 0 + cᵢ X 1`. -/
def affinePlaneMap {K σ : Type*} [CommRing K] (a b c : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1)

/-- Evaluating the restriction of `f` to the plane `a + s b + t c` at `z` gives the value of
`f` at `a + z 0 • b + z 1 • c`. -/
lemma affinePlaneMap_eval {K σ : Type*} [CommRing K] (a b c : σ → K)
    (f : MvPolynomial σ K) (z : Fin 2 → K) :
    eval z (affinePlaneMap a b c f) =
      eval (fun i => a i + b i * z 0 + c i * z 1) f := by
  have he : (eval z).comp (affinePlaneMap a b c).toRingHom =
      eval (fun i => a i + b i * z 0 + c i * z 1) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [affinePlaneMap]
    · intro i; simp [affinePlaneMap]
  exact RingHom.congr_fun he f

/-- Restricting a polynomial to an affine plane does not increase its total degree. -/
lemma affinePlaneMap_totalDegree_le {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    (affinePlaneMap a b c f).totalDegree ≤ f.totalDegree := by
  change (eval₂Hom C (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1) f).totalDegree ≤ _
  apply linear_eval₂_totalDegree_le (RingHom.id K) _ _ f
  intro i
  have hx (j : Fin 2) : (X j : MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
    simpa [X] using totalDegree_monomial_le (Finsupp.single j 1) (1 : K)
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simpa using hx 0)
  · exact (totalDegree_mul _ _).trans (by simpa using hx 1)

private lemma affinePlaneMap_rename {K σ τ : Type*} [CommRing K]
    (e : σ → τ) (a b c : τ → K) (f : MvPolynomial σ K) :
    affinePlaneMap a b c (rename e f) =
      affinePlaneMap (a ∘ e) (b ∘ e) (c ∘ e) f := by
  change eval₂Hom _ _ (rename e f) = eval₂Hom _ _ f
  simp only [eval₂Hom_rename, Function.comp_def]

private lemma map_affinePlaneMap {K L σ : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (a b c : σ → K) (f : MvPolynomial σ K) :
    map φ (affinePlaneMap a b c f) =
      affinePlaneMap (φ ∘ a) (φ ∘ b) (φ ∘ c) (map φ f) := by
  have he : (map φ).comp (affinePlaneMap a b c).toRingHom =
      (affinePlaneMap (φ ∘ a) (φ ∘ b) (φ ∘ c)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [affinePlaneMap]
    · intro i; simp [affinePlaneMap]
  exact RingHom.congr_fun he f

private lemma universalPlaneSection_eq_affinePlaneMap {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (u : PlaneParameters σ → K) :
    universalPlaneSection f u = bivariatePolynomialEquiv K
      (affinePlaneMap (fun i => u (i,0)) (fun i => u (i,1)) (fun i => u (i,2)) f) := by
  have he : eval u = planeParameterEval (RingHom.id K)
      (fun i => u (i,0)) (fun i => u (i,1)) (fun i => u (i,2)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [planeParameterEval]
    · intro i
      rcases i with ⟨i,j⟩
      fin_cases j <;> simp [planeParameterEval]
  rw [universalPlaneSection, he, universalPlanePolynomial_specialize]
  rfl

/-- The `3 × 3` matrix with columns `b`, `c` and `v`; over a field, its determinant is nonzero
exactly when `b`, `c` and `v` are linearly independent. -/
def planeDirectionMatrix {K : Type*} [CommRing K] (b c v : Fin 3 → K) :
    Matrix (Fin 3) (Fin 3) K :=
  fun i j => ![b i, c i, v i] j

private def planeTransversalityPolynomial (v : Fin 3 → ℚ) :
    MvPolynomial (PlaneParameters (Fin 3)) ℚ :=
  (planeDirectionMatrix (fun i => X (i,1)) (fun i => X (i,2)) (fun i => C (v i))).det

private lemma planeTransversalityPolynomial_eval (v : Fin 3 → ℚ)
    (u : PlaneParameters (Fin 3) → ℚ) :
    eval u (planeTransversalityPolynomial v) =
      (planeDirectionMatrix (fun i => u (i,1)) (fun i => u (i,2)) v).det := by
  rw [planeTransversalityPolynomial, RingHom.map_det]
  congr 1
  ext i j
  fin_cases j <;> simp [planeDirectionMatrix, Matrix.map_apply]

private lemma planeTransversalityPolynomial_ne_zero (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    planeTransversalityPolynomial v ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  intro he
  have hz (b c : Fin 3 → ℚ) : (planeDirectionMatrix b c v).det = 0 := by
    let u : PlaneParameters (Fin 3) → ℚ := fun i => ![0, b i.1, c i.1] i.2
    have hh := congrArg (eval u) he
    rw [planeTransversalityPolynomial_eval, map_zero] at hh
    exact hh
  fin_cases j
  · have hh := hz ![0,1,0] ![0,0,1]
    exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hh)
  · have hh := hz ![1,0,0] ![0,0,1]
    exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hh)
  · have hh := hz ![1,0,0] ![0,1,0]
    exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hh)

/-- The integer specialization theorem, reindexed to three
coordinates, can avoid any nonzero rational parameter polynomial. -/
private theorem exists_good_rational_plane_avoiding
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree)
    (P : MvPolynomial (PlaneParameters (Fin 3)) ℚ) (hP : P ≠ 0) :
    ∃ a b c : Fin 3 → ℚ,
      eval (fun i => ![a i.1, b i.1, c i.1] i.2) P ≠ 0 ∧
      Irreducible (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)) ∧
      (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)).totalDegree = f.totalDegree := by
  classical
  let e : Fin 3 ≃ Option (Fin 2) := finSuccEquiv' 0
  let ep : PlaneParameters (Fin 3) ≃ PlaneParameters (Option (Fin 2)) :=
    Equiv.prodCongr e (Equiv.refl _)
  let F := rename e f
  have hF : AbsolutelyIrreducible F := by
    rw [AbsolutelyIrreducible, show F = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv _ e)).mpr hir
  have hFd : F.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  obtain ⟨PZ, t, _, ht, hmodel⟩ := exists_primitive_integer_model P hP
  have hPZ : PZ ≠ 0 := by
    intro h
    rw [h, map_zero] at hmodel
    exact mul_ne_zero (C_eq_zero.not.mpr ht) hP hmodel.symm
  have hren : rename ep PZ ≠ 0 :=
    (map_ne_zero_iff _ (rename_injective ep ep.injective)).mpr hPZ
  obtain ⟨u, _, hu, _, hdeg, hgood⟩ :=
    exists_integer_geometrically_good_plane_avoiding F hF (hFd ▸ hd) (rename ep PZ) hren
  let a : Fin 3 → ℤ := fun i => u (e i,0)
  let b : Fin 3 → ℤ := fun i => u (e i,1)
  let c : Fin 3 → ℤ := fun i => u (e i,2)
  let q : MvPolynomial (Fin 2) ℤ := affinePlaneMap a b c f
  have hsection : universalPlaneSection F u = bivariatePolynomialEquiv ℤ q := by
    rw [universalPlaneSection_eq_affinePlaneMap]
    congr 1
    exact affinePlaneMap_rename e _ _ _ f
  rw [hsection, bivariatePolynomialEquiv_map] at hgood hdeg
  have hqir : AbsolutelyIrreducible q :=
    (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv _)).mp hgood
  have hqd : q.totalDegree = f.totalDegree := by
    rw [bivariateTotalDegree_equiv] at hdeg
    have hm : (map (Int.castRingHom (AlgebraicClosure ℚ)) q).totalDegree = q.totalDegree :=
        totalDegree_map_of_injective Int.cast_injective _
    simpa only [hm, hFd] using hdeg
  refine ⟨(Int.castRingHom ℚ) ∘ a, (Int.castRingHom ℚ) ∘ b,
    (Int.castRingHom ℚ) ∘ c, ?_, ?_, ?_⟩
  · have hu' : eval (fun i => ![a i.1, b i.1, c i.1] i.2) PZ ≠ 0 := by
      have he : (fun i : PlaneParameters (Fin 3) => ![a i.1, b i.1, c i.1] i.2) =
          u ∘ ep := by
        funext i
        rcases i with ⟨i,j⟩
        fin_cases j <;> rfl
      rw [he]
      simpa only [eval_rename] using hu
    have hmap : eval
        (fun i => ![((Int.castRingHom ℚ) ∘ a) i.1,
          ((Int.castRingHom ℚ) ∘ b) i.1, ((Int.castRingHom ℚ) ∘ c) i.1] i.2)
        (map (Int.castRingHom ℚ) PZ) ≠ 0 := by
      have hh : (Int.castRingHom ℚ)
          (eval (fun i => ![a i.1, b i.1, c i.1] i.2) PZ) ≠ 0 :=
        (map_ne_zero_iff _ Int.cast_injective).mpr hu'
      rw [map_eval] at hh
      convert hh using 1
      congr 2
      funext i
      rcases i with ⟨i,j⟩
      fin_cases j <;> rfl
    rw [hmodel, map_mul, eval_C] at hmap
    exact (mul_ne_zero_iff.mp hmap).2
  · rw [← map_affinePlaneMap]
    exact rational_irreducible_of_charZero_map q hqir
  · rw [← map_affinePlaneMap]
    exact (rational_map_totalDegree q).trans hqd

/-- A geometrically irreducible surface admits a transverse plane
whose restriction of any prescribed nonzero second equation is nonzero. -/
theorem exists_surface_transverse_plane
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (v : Fin 3 → ℚ) (hv : v ≠ 0)
    (g : MvPolynomial (Fin 3) ℚ) (hg : g ≠ 0) :
    ∃ a b c : Fin 3 → ℚ,
      (planeDirectionMatrix b c v).det ≠ 0 ∧
      Irreducible (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)) ∧
      (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)).totalDegree = f.totalDegree ∧
      affinePlaneMap a b c g ≠ 0 := by
  let P := planeTransversalityPolynomial v * rename (fun i : Fin 3 => (i, (0 : Fin 3))) g
  have hP : P ≠ 0 := mul_ne_zero (planeTransversalityPolynomial_ne_zero v hv)
    ((map_ne_zero_iff _ (rename_injective _ (by intro i j h; exact congrArg Prod.fst h))).mpr hg)
  obtain ⟨a,b,c,havoid,hgood,hdegree⟩ := exists_good_rational_plane_avoiding f hir hd P hP
  rw [show P = _ * _ from rfl, map_mul, planeTransversalityPolynomial_eval, eval_rename] at havoid
  obtain ⟨htrans, hbase⟩ := mul_ne_zero_iff.mp havoid
  refine ⟨a,b,c,htrans,hgood,hdegree,?_⟩
  intro hz
  have hh := affinePlaneMap_eval a b c g (0 : Fin 2 → ℚ)
  rw [hz, map_zero] at hh
  change eval a g ≠ 0 at hbase
  apply hbase
  simpa using hh.symm

end
end CCDN
