/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalH1
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalSequenceAlgebra

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorJointLimit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Joint local limits of finite correctors

Componentwise gradient Cauchy convergence for every slope determines one
unique family of normalized projective local `H¹` carriers.  Its scalar-value
and Hilbert-vector-gradient projections are linear in the slope.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- Componentwise local gradient Cauchy convergence for every boundary
slope. -/
@[expose]
def FiniteAffineCorrectionLocalCauchy {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) : Prop :=
  ∀ e : Vec d,
    NormalizedLocalGradientCauchy (finiteAffineCorrectionLocalSequence a e)

namespace NormalizedLocalH1Carrier

/-- Addition of normalized local carriers, defined componentwise. -/
@[expose]
noncomputable def addCarrier {d : ℕ}
    (z w : NormalizedLocalH1Carrier d) : NormalizedLocalH1Carrier d where
  value := z.value + w.value
  gradient := z.gradient + w.gradient
  graph n := by
    change
      (z.valueComponent n + w.valueComponent n,
        z.gradientComponent n + w.gradientComponent n) ∈
          h1GraphClosedSubmodule (U := localGradientCube d n)
    exact (h1GraphClosedSubmodule (U := localGradientCube d n)).add_mem
      (z.graph n) (w.graph n)
  unitMeanZero := by
    change scalarIntegralCLM (U := localGradientCube d 0)
      (z.valueComponent 0 + w.valueComponent 0) = 0
    unfold valueComponent
    rw [map_add, z.unitMeanZero, w.unitMeanZero, add_zero]

/-- Scalar multiplication of a normalized local carrier, defined
componentwise. -/
@[expose]
noncomputable def smulCarrier {d : ℕ} (c : ℝ)
    (z : NormalizedLocalH1Carrier d) : NormalizedLocalH1Carrier d where
  value := c • z.value
  gradient := c • z.gradient
  graph n := by
    change
      (c • z.valueComponent n, c • z.gradientComponent n) ∈
        h1GraphClosedSubmodule (U := localGradientCube d n)
    exact (h1GraphClosedSubmodule (U := localGradientCube d n)).smul_mem
      c (z.graph n)
  unitMeanZero := by
    change scalarIntegralCLM (U := localGradientCube d 0)
      (c • z.valueComponent 0) = 0
    unfold valueComponent
    rw [map_smul, z.unitMeanZero, smul_zero]

@[simp] theorem addCarrier_valueComponent {d : ℕ}
    (z w : NormalizedLocalH1Carrier d) (n : ℕ) :
    (addCarrier z w).valueComponent n =
      z.valueComponent n + w.valueComponent n :=
  rfl

@[simp] theorem addCarrier_gradientComponent {d : ℕ}
    (z w : NormalizedLocalH1Carrier d) (n : ℕ) :
    (addCarrier z w).gradientComponent n =
      z.gradientComponent n + w.gradientComponent n :=
  rfl

@[simp] theorem smulCarrier_valueComponent {d : ℕ} (c : ℝ)
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    (smulCarrier c z).valueComponent n = c • z.valueComponent n :=
  rfl

@[simp] theorem smulCarrier_gradientComponent {d : ℕ} (c : ℝ)
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    (smulCarrier c z).gradientComponent n = c • z.gradientComponent n :=
  rfl

end NormalizedLocalH1Carrier

/-- Additive normalized local pair limits combine to the normalized local
limit of the sum-slope finite correctors. -/
theorem IsNormalizedLocalLimit.finiteAffineCorrection_add {d : ℕ}
    [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d} {e e' : Vec d}
    {z w : NormalizedLocalH1Carrier d}
    (hz : IsNormalizedLocalLimit
      (finiteAffineCorrectionLocalSequence a e) z)
    (hw : IsNormalizedLocalLimit
      (finiteAffineCorrectionLocalSequence a e') w) :
    IsNormalizedLocalLimit
      (finiteAffineCorrectionLocalSequence a (e + e'))
      (NormalizedLocalH1Carrier.addCarrier z w) := by
  intro n
  have hsum := (hz n).add (hw n)
  change Filter.Tendsto
    (fun k => normalizedLocalPair
      (finiteAffineCorrectionLocalSequence a (e + e')) n k)
    Filter.atTop _
  simpa only [normalizedLocalPair_finiteAffineCorrection_add,
    NormalizedLocalH1Carrier.addCarrier_valueComponent,
    NormalizedLocalH1Carrier.addCarrier_gradientComponent,
    Prod.mk_add_mk] using hsum

/-- Homogeneous normalized local pair limits combine to the normalized local
limit of the scaled-slope finite correctors. -/
theorem IsNormalizedLocalLimit.finiteAffineCorrection_smul {d : ℕ}
    [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d} {e : Vec d}
    {z : NormalizedLocalH1Carrier d} (c : ℝ)
    (hz : IsNormalizedLocalLimit
      (finiteAffineCorrectionLocalSequence a e) z) :
    IsNormalizedLocalLimit
      (finiteAffineCorrectionLocalSequence a (c • e))
      (NormalizedLocalH1Carrier.smulCarrier c z) := by
  intro n
  have hscaled := (hz n).const_smul c
  change Filter.Tendsto
    (fun k => normalizedLocalPair
      (finiteAffineCorrectionLocalSequence a (c • e)) n k)
    Filter.atTop _
  simpa only [normalizedLocalPair_finiteAffineCorrection_smul,
    NormalizedLocalH1Carrier.smulCarrier_valueComponent,
    NormalizedLocalH1Carrier.smulCarrier_gradientComponent,
    Prod.smul_mk] using hscaled

/-- A joint normalized local limit is a family satisfying the literal local
limit characterization at every slope. -/
@[expose]
def IsFiniteAffineCorrectionJointLocalLimit {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d) : Prop :=
  ∀ e : Vec d,
    IsNormalizedLocalLimit
      (finiteAffineCorrectionLocalSequence a e) (Phi e)

/-- A componentwise Cauchy family has one and only one joint normalized local
limit family. -/
theorem existsUnique_finiteAffineCorrectionJointLocalLimit {d : ℕ}
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) :
    ∃! Phi : Vec d → NormalizedLocalH1Carrier d,
      IsFiniteAffineCorrectionJointLocalLimit a Phi := by
  let Phi : Vec d → NormalizedLocalH1Carrier d := fun e =>
    normalizedCorrectorLocalLimit
      (finiteAffineCorrectionLocalSequence a e) (hCauchy e)
  refine ⟨Phi, ?_, ?_⟩
  · intro e
    exact normalizedCorrectorLocalLimit_isLimit
      (finiteAffineCorrectionLocalSequence a e) (hCauchy e)
  · intro Psi hPsi
    funext e
    exact (isNormalizedLocalLimit_iff_eq
      (finiteAffineCorrectionLocalSequence a e) (hCauchy e) (Psi e)).mp
        (hPsi e)

/-- The joint normalized local corrector family selected from its unique
characterization. -/
@[expose]
noncomputable def finiteAffineCorrectionJointLocalLimit {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) :
    Vec d → NormalizedLocalH1Carrier d :=
  Classical.choose (existsUnique_finiteAffineCorrectionJointLocalLimit a hCauchy)

/-- The selected joint family satisfies the literal local-limit
characterization. -/
theorem finiteAffineCorrectionJointLocalLimit_isLimit {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) :
    IsFiniteAffineCorrectionJointLocalLimit a
      (finiteAffineCorrectionJointLocalLimit a hCauchy) :=
  (Classical.choose_spec
    (existsUnique_finiteAffineCorrectionJointLocalLimit a hCauchy)).1

/-- The literal characterization identifies exactly the selected joint
family. -/
theorem isFiniteAffineCorrectionJointLocalLimit_iff_eq {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (Phi : Vec d → NormalizedLocalH1Carrier d) :
    IsFiniteAffineCorrectionJointLocalLimit a Phi ↔
      Phi = finiteAffineCorrectionJointLocalLimit a hCauchy := by
  constructor
  · intro hPhi
    exact (Classical.choose_spec
      (existsUnique_finiteAffineCorrectionJointLocalLimit a hCauchy)).2
        Phi hPhi
  · rintro rfl
    exact finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy

/-- The selected joint normalized local corrector family is additive in the
slope. -/
theorem finiteAffineCorrectionJointLocalLimit_add {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) (e e' : Vec d) :
    finiteAffineCorrectionJointLocalLimit a hCauchy (e + e') =
      NormalizedLocalH1Carrier.addCarrier
        (finiteAffineCorrectionJointLocalLimit a hCauchy e)
        (finiteAffineCorrectionJointLocalLimit a hCauchy e') := by
  have hlimit :=
    (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy e).finiteAffineCorrection_add
        (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy e')
  exact (existsUnique_normalizedLocalLimit
    (finiteAffineCorrectionLocalSequence a (e + e'))
    (hCauchy (e + e'))).unique
      (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy (e + e'))
      hlimit

/-- The selected joint normalized local corrector family is homogeneous in
the slope. -/
theorem finiteAffineCorrectionJointLocalLimit_smul {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) (c : ℝ) (e : Vec d) :
    finiteAffineCorrectionJointLocalLimit a hCauchy (c • e) =
      NormalizedLocalH1Carrier.smulCarrier c
        (finiteAffineCorrectionJointLocalLimit a hCauchy e) := by
  have hlimit :=
    (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy e).finiteAffineCorrection_smul c
  exact (existsUnique_normalizedLocalLimit
    (finiteAffineCorrectionLocalSequence a (c • e))
    (hCauchy (c • e))).unique
      (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy (c • e))
      hlimit

end

end HighContrast
end HCPolySupport
