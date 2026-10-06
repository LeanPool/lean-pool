/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureTestCutoff
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureTestOperators

/-!
# Associated-pressure momentum integrand

Product-coordinate momentum expressions and their algebraic estimates.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- The compact Helmholtz test obtained by cutting off both potentials in
the decomposition used for `thm:assoc-pressure`. -/
@[expose]
def associatedPressureHelmholtzTestCutoff
    (φ : Vec3 × ℝ → Vec3) (n : ℕ) : Vec3 × ℝ → Vec3 :=
  fun z => associatedPressureTestCurl
      (associatedPressureHelmholtzCutoffVectorPotential φ n) z +
    associatedPressureTestGradient
      (associatedPressureHelmholtzScalarPotentialCutoff φ n) z

/-- Each cutoff Helmholtz test remains in the original compact test class. -/
theorem associatedPressureHelmholtzTestCutoff_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    associatedPressureHelmholtzTestCutoff φ n ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
  let v : Vec3 × ℝ → Vec3 := associatedPressureTestCurl
    (associatedPressureHelmholtzCutoffVectorPotential φ n)
  let g : Vec3 × ℝ → Vec3 := associatedPressureTestGradient
    (associatedPressureHelmholtzScalarPotentialCutoff φ n)
  have hv := associatedPressureTestCurl_mem_spaceTimeTestFunction
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction
      hφ n)
  have hg := associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction
    hφ n
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzTestCutoff φ n) := by
    apply contDiff_pi.2
    intro i
    have hvi := CKN.component_mem_spaceTimeTestFunction hv i
    have hgi := CKN.component_mem_spaceTimeTestFunction hg i
    change ContDiff ℝ (⊤ : ℕ∞) (fun z => v z i + g z i)
    exact hvi.1.add hgi.1
  have hcompact : HasCompactSupport
      (associatedPressureHelmholtzTestCutoff φ n) := by
    change HasCompactSupport (v + g)
    exact hv.2.1.add hg.2.1
  have hclosed : IsClosed (tsupport v ∪ tsupport g) :=
    (isClosed_tsupport v).union (isClosed_tsupport g)
  have htsupport : tsupport (associatedPressureHelmholtzTestCutoff φ n) ⊆
      tsupport v ∪ tsupport g := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      have hvzero : v z = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hzv
        exact hnot (Or.inl hzv))
      have hgzero : g z = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hzg
        exact hnot (Or.inr hzg))
      exact hz (by simp [associatedPressureHelmholtzTestCutoff, v, g,
        hvzero, hgzero])
    · exact hclosed
  refine ⟨hcont, hcompact, ?_⟩
  have hvclass := associatedPressureTestCurl_mem_spaceTimeTestFunction
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction
      hφ n)
  have hgclass := associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction
    hφ n
  exact htsupport.trans (Set.union_subset hvclass.2.2 hgclass.2.2)

/-- The full velocity--gradient--pressure momentum integrand in product
coordinates, used by `thm:assoc-pressure`. -/
@[expose]
def associatedPressureMomentumProductIntegrand
    (u : Vec3 × ℝ → Vec3) (Du : Vec3 × ℝ → Fin 3 → Vec3)
    (p : Vec3 × ℝ → ℝ) (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  -(∑ i : Fin 3, u z i * CKN.timePartialProd (fun q => φ q i) z)
    - ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * CKN.spatialPartialProd (fun q => φ q i) j z
    + ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * CKN.spatialPartialProd (fun q => φ q i) j z
        - p z * ∑ i : Fin 3, CKN.spatialPartialProd (fun q => φ q i) i z

/-- The absolute value of a difference is bounded by the sum of the absolute values. -/
theorem associatedPressureAbs_sub_le (a b : ℝ) :
    |a - b| ≤ |a| + |b| := by
  calc
    |a - b| = |a + (-b)| := congrArg abs (sub_eq_add_neg a b)
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

private theorem associatedPressureMomentumFourTerm_abs_le
    (a b c d : ℝ) :
    |-a - b + c - d| ≤ |a| + |b| + |c| + |d| := by
  have hab : |(-a) + (-b)| ≤ |a| + |b| := by
    calc
      |(-a) + (-b)| ≤ |-a| + |-b| := abs_add_le _ _
      _ = |a| + |b| := by rw [abs_neg, abs_neg]
  have habc : |(-a) + (-b) + c| ≤ |a| + |b| + |c| := by
    calc
      |(-a) + (-b) + c| ≤ |(-a) + (-b)| + |c| := abs_add_le _ _
      _ ≤ |a| + |b| + |c| := add_le_add_left hab _
  calc
    |-a - b + c - d| = |(-a) + (-b) + c + (-d)| := by
      congr 1
    _ ≤ |(-a) + (-b) + c| + |-d| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| + |d| := by
      rw [abs_neg]
      exact add_le_add_left habc _

/-- The common integrable majorant used to remove the spatial cutoffs in
`thm:assoc-pressure`. -/
@[expose]
def associatedPressureMomentumProfileMajorant
    (C : ℝ) (S : Vec3 × ℝ → ℝ) (u : Vec3 × ℝ → Vec3)
    (Du : Vec3 × ℝ → Fin 3 → Vec3) (p : Vec3 × ℝ → ℝ) :
    Vec3 × ℝ → ℝ := fun z => C * (
      (∑ i : Fin 3, |u z i| * S z) +
      (∑ i : Fin 3, ∑ j : Fin 3, |u z i * u z j| * S z) +
      (∑ i : Fin 3, ∑ j : Fin 3, |Du z i j| * S z) +
      3 * (|p z| * S z))

/-- A derivative profile bound controls the complete momentum integrand in
`thm:assoc-pressure`. -/
theorem associatedPressureMomentumProductIntegrand_abs_le_profileMajorant
    {C : ℝ} {S : Vec3 × ℝ → ℝ}
    {u : Vec3 × ℝ → Vec3} {Du : Vec3 × ℝ → Fin 3 → Vec3}
    {p : Vec3 × ℝ → ℝ} {Φ : Vec3 × ℝ → Vec3}
    (hTime : ∀ z i, |CKN.timePartialProd (fun q => Φ q i) z| ≤ C * S z)
    (hSpace : ∀ z i j,
      |CKN.spatialPartialProd (fun q => Φ q i) j z| ≤ C * S z) :
    ∀ z, |associatedPressureMomentumProductIntegrand u Du p Φ z| ≤
      associatedPressureMomentumProfileMajorant C S u Du p z := by
  intro z
  let dTime (i : Fin 3) := CKN.timePartialProd (fun q => Φ q i) z
  let dSpace (i j : Fin 3) := CKN.spatialPartialProd (fun q => Φ q i) j z
  let U := ∑ i : Fin 3, |u z i| * S z
  let N := ∑ i : Fin 3, ∑ j : Fin 3, |u z i * u z j| * S z
  let V := ∑ i : Fin 3, ∑ j : Fin 3, |Du z i j| * S z
  let P := |p z| * S z
  have hU : |∑ i : Fin 3, u z i * dTime i| ≤ C * U := by
    calc
      _ ≤ ∑ i : Fin 3, |u z i * dTime i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, |u z i| * (C * S z) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hTime z i) (abs_nonneg _)
      _ = C * U := by
        dsimp [U]
        calc
          _ = ∑ i : Fin 3, C * (|u z i| * S z) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = C * ∑ i : Fin 3, |u z i| * S z := by rw [Finset.mul_sum]
  have hN : |∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z j * dSpace i j| ≤ C * N := by
    calc
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3,
          u z i * u z j * dSpace i j| :=
        Finset.abs_sum_le_sum_abs
          (fun i : Fin 3 => ∑ j : Fin 3,
            u z i * u z j * dSpace i j) Finset.univ
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |u z i * u z j * dSpace i j| := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.abs_sum_le_sum_abs
          (fun j : Fin 3 => u z i * u z j * dSpace i j) Finset.univ
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |u z i * u z j| * (C * S z) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hSpace z i j) (abs_nonneg _)
      _ = C * N := by
        dsimp [N]
        calc
          _ = ∑ i : Fin 3, ∑ j : Fin 3,
              C * (|u z i * u z j| * S z) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = C * ∑ i : Fin 3, ∑ j : Fin 3,
              |u z i * u z j| * S z := by
            simp only [Finset.mul_sum]
  have hV : |∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j| ≤ C * V := by
    calc
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, Du z i j * dSpace i j| :=
        Finset.abs_sum_le_sum_abs
          (fun i : Fin 3 => ∑ j : Fin 3, Du z i j * dSpace i j)
          Finset.univ
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |Du z i j * dSpace i j| := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.abs_sum_le_sum_abs
          (fun j : Fin 3 => Du z i j * dSpace i j) Finset.univ
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |Du z i j| * (C * S z) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hSpace z i j) (abs_nonneg _)
      _ = C * V := by
        dsimp [V]
        calc
          _ = ∑ i : Fin 3, ∑ j : Fin 3,
              C * (|Du z i j| * S z) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = C * ∑ i : Fin 3, ∑ j : Fin 3,
              |Du z i j| * S z := by
            simp only [Finset.mul_sum]
  have hdiv : |∑ i : Fin 3, dSpace i i| ≤ 3 * (C * S z) := by
    calc
      _ ≤ ∑ i : Fin 3, |dSpace i i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, C * S z := by
        apply Finset.sum_le_sum
        intro i hi
        exact hSpace z i i
      _ = 3 * (C * S z) := by simp
  have hP : |p z * ∑ i : Fin 3, dSpace i i| ≤ 3 * C * P := by
    rw [abs_mul]
    calc
      |p z| * |∑ i : Fin 3, dSpace i i| ≤ |p z| * (3 * (C * S z)) :=
        mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)
      _ = 3 * C * P := by dsimp [P]; ring
  have htriangle := associatedPressureMomentumFourTerm_abs_le
    (∑ i : Fin 3, u z i * dTime i)
    (∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * dSpace i j)
    (∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j)
    (p z * ∑ i : Fin 3, dSpace i i)
  rw [associatedPressureMomentumProductIntegrand]
  change |-(∑ i : Fin 3, u z i * dTime i) -
      (∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * dSpace i j) +
      (∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j) -
      p z * ∑ i : Fin 3, dSpace i i| ≤ _
  calc
    _ ≤ |∑ i : Fin 3, u z i * dTime i| +
        |∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * dSpace i j| +
        |∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j| +
        |p z * ∑ i : Fin 3, dSpace i i| := htriangle
    _ ≤ C * U + C * N + C * V + 3 * C * P := by
      calc
        _ = (|∑ i : Fin 3, u z i * dTime i| +
            |∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * dSpace i j|) +
            (|∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * dSpace i j| +
             |p z * ∑ i : Fin 3, dSpace i i|) := by ring
        _ ≤ (C * U + C * N) + (C * V + 3 * C * P) :=
          add_le_add (add_le_add hU hN) (add_le_add hV hP)
        _ = C * U + C * N + C * V + 3 * C * P := by ring
    _ = associatedPressureMomentumProfileMajorant C S u Du p z := by
      dsimp [associatedPressureMomentumProfileMajorant, U, N, V, P]
      ring

/-- The product-coordinate time derivative distributes over addition of smooth functions. -/
theorem associatedPressureTimePartialProd_add
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) :
    CKN.timePartialProd (fun q => f q + g q) z =
      CKN.timePartialProd f z + CKN.timePartialProd g z := by
  change CKN.timePartial (fun q => f q + g q) z = _
  exact CKN.timePartial_add_at
    ((hf.differentiable (by simp)) z) ((hg.differentiable (by simp)) z)

/-- The product-coordinate spatial derivative distributes over addition of smooth functions. -/
theorem associatedPressureSpatialPartialProd_add
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (fun q => f q + g q) i z =
      CKN.spatialPartialProd f i z + CKN.spatialPartialProd g i z := by
  change CKN.spatialPartial (fun q => f q + g q) i z = _
  exact CKN.spatialPartial_add_at
    ((hf.differentiable (by simp)) z) ((hg.differentiable (by simp)) z) i

/-- The product-coordinate momentum functional is linear in its test field,
as used in `thm:assoc-pressure`. -/
theorem associatedPressureMomentumProductIntegrand_add
    {u : Vec3 × ℝ → Vec3} {Du : Vec3 × ℝ → Fin 3 → Vec3}
    {p : Vec3 × ℝ → ℝ} {φ ψ : Vec3 × ℝ → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : Vec3 × ℝ) :
    associatedPressureMomentumProductIntegrand u Du p (fun q => φ q + ψ q) z =
      associatedPressureMomentumProductIntegrand u Du p φ z +
        associatedPressureMomentumProductIntegrand u Du p ψ z := by
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => φ q i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => ψ q i) :=
    (contDiff_apply ℝ ℝ i).comp hψ
  have htime (i : Fin 3) :
      CKN.timePartialProd (fun q => φ q i + ψ q i) z =
        CKN.timePartialProd (fun q => φ q i) z +
          CKN.timePartialProd (fun q => ψ q i) z :=
    associatedPressureTimePartialProd_add (hφi i) (hψi i) z
  have hspace (i j : Fin 3) :
      CKN.spatialPartialProd (fun q => φ q i + ψ q i) j z =
        CKN.spatialPartialProd (fun q => φ q i) j z +
          CKN.spatialPartialProd (fun q => ψ q i) j z :=
    associatedPressureSpatialPartialProd_add (hφi i) (hψi i) j z
  simp only [associatedPressureMomentumProductIntegrand, Pi.add_apply,
    htime, hspace, mul_add, Finset.sum_add_distrib]
  ring

/-- The pressure contribution vanishes on a curl test in `thm:assoc-pressure`. -/
theorem associatedPressureMomentumProductIntegrand_pressureless_curl
    {u : Vec3 × ℝ → Vec3} {Du : Vec3 × ℝ → Fin 3 → Vec3}
    {p : Vec3 × ℝ → ℝ} {A : Vec3 × ℝ → Vec3}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (z : Vec3 × ℝ) :
    associatedPressureMomentumProductIntegrand u Du p
      (associatedPressureTestCurl A) z =
      -(∑ i : Fin 3, u z i * CKN.timePartialProd
        (fun q => associatedPressureTestCurl A q i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          u z i * u z j * CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl A q i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          Du z i j * CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl A q i) j z := by
  have hcurl : ∑ i : Fin 3,
      CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) i z = 0 := by
    have htest := associatedPressureTestCurl_divergence hA z
    change (∑ i : Fin 3,
      CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) i z) = 0 at htest
    exact htest
  simp [associatedPressureMomentumProductIntegrand, hcurl]

end CKN.Leray

end
