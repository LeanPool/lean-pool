/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/OrderMatrixRecursive.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.OrderNormalForm

/-!
# Order Matrix Recursive
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrderNormalForm
open UniformOracle TableIndices IndexMatrix IndexedOrder CertificateMatrix

private def combine (v : ℕ) : ℕ :=
  let t := (Nat.unpair v).1
  let h := (Nat.unpair (Nat.unpair v).2).1
  let c₀ := (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1
  let c₁ := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).1
  let a := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2).1
  let b := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2).2
  if t = 1 ∧ h = 1 ∧ (c₀ ≠ 1 ∨ c₁ ≠ 1 ∨ a = b) then 1 else 0

private theorem combine_primrec : Primrec combine := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  let t := f
  let h := f.comp s
  let c₀ := f.comp (s.comp s)
  let c₁ := f.comp (s.comp (s.comp s))
  let a := f.comp (s.comp (s.comp (s.comp s)))
  let b := s.comp (s.comp (s.comp (s.comp s)))
  have hp := (Primrec.eq.comp c₀ (Primrec.const 1)).not.or
    ((Primrec.eq.comp c₁ (Primrec.const 1)).not.or (Primrec.eq.comp a b))
  exact Primrec.ite ((Primrec.eq.comp t (Primrec.const 1)).and
    ((Primrec.eq.comp h (Primrec.const 1)).and hp)) (Primrec.const 1) (Primrec.const 0)

theorem orderMatrix_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (if orderMatrix Y (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2 then 1 else 0)) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  let e₀ := f
  let e₁ := f.comp s
  let d := f.comp (s.comp s)
  let q := f.comp (s.comp (s.comp s))
  let r := s.comp (s.comp (s.comp s))
  let n := f.comp q
  let challenge := s.comp q
  let m := f.comp challenge
  let a := f.comp (s.comp challenge)
  let b := f.comp (s.comp (s.comp challenge))
  let z := f.comp (s.comp (s.comp (s.comp challenge)))
  let w := s.comp (s.comp (s.comp (s.comp challenge)))
  let answer := f.comp r
  let cert := f.comp (s.comp r)
  let trial := s.comp (s.comp r)
  have mk : ∀ (fn fa fz : ℕ → ℕ), Primrec fn → Primrec fa → Primrec fz →
      Nat.RecursiveIn O (fun v => Part.some
        (if Certificate Y (machine (Nat.unpair (Nat.unpair v).2).1)
          (machine (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1)
          (fn v) (fa v) (fz v) then 1 else 0)) := by
    intro fn fa fz hn ha hz
    exact (total_comp (certificate_recursive Y)
      (total_pair (total_primrec e₁) (total_pair (total_primrec d)
        (total_pair (total_primrec hn) (total_pair (total_primrec ha) (total_primrec hz)))))).of_eq
      (fun v => by simp)
  have ht := mk _ _ _ n answer cert
  have hc₀ := mk _ _ _ m a z
  have hc₁ := mk _ _ _ m b w
  have hr := total_comp (run_uniform_recursive Y)
    (total_pair (total_primrec e₀) (total_pair (total_primrec n) (total_primrec trial)))
  have hans := total_primrec (O := O) (Primrec.encode.comp (Primrec.option_some.comp answer))
  have heq := total_primrec (O := O)
    (Primrec.ite (Primrec.eq.comp f s) (Primrec.const 1) (Primrec.const 0))
  have hout := total_comp heq (total_pair hr hans)
  exact (total_comp (total_primrec combine_primrec)
    (total_pair ht (total_pair hout (total_pair hc₀ (total_pair hc₁
      (total_pair (total_primrec a) (total_primrec b))))))).of_eq (fun v => by
        simp only [combine, orderMatrix, Nat.unpair_pair, Encodable.encode_injective.eq_iff]
        simp [and_assoc, imp_iff_not_or])

end TuringRigidity.OrderNormalForm

end OAI
