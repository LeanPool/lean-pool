/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Defs
public import LeanPool.PolylogIntegrals.Proofs.A001
public import LeanPool.PolylogIntegrals.Proofs.A002
public import LeanPool.PolylogIntegrals.Proofs.A003
public import LeanPool.PolylogIntegrals.Proofs.A004
public import LeanPool.PolylogIntegrals.Proofs.A005
public import LeanPool.PolylogIntegrals.Proofs.A006
public import LeanPool.PolylogIntegrals.Proofs.A007
public import LeanPool.PolylogIntegrals.Proofs.A008
public import LeanPool.PolylogIntegrals.Proofs.A009
public import LeanPool.PolylogIntegrals.Proofs.A010
public import LeanPool.PolylogIntegrals.Proofs.A011
public import LeanPool.PolylogIntegrals.Proofs.A012
public import LeanPool.PolylogIntegrals.Proofs.A013
public import LeanPool.PolylogIntegrals.Proofs.A014
public import LeanPool.PolylogIntegrals.Proofs.A015
public import LeanPool.PolylogIntegrals.Proofs.A016

/-!
# The sixteen identities of *PolyLog Integrals* (rainrzk, 2022)

Each theorem restates one identity from the upstream tutorial (`blueprint/Polylog.pdf` in
https://github.com/rainrzk/LeanPolyLog). Two differ from that PDF:
* A004 uses the corrected value π²/24 (see `blueprint/ERRATA.md`).
* A014 uses the equivalent simplified form, which avoids `Li₃(1+i)` outside the unit disk.

Lean checks proofs, not whether a statement says what was meant. Every statement here therefore
has a numerical twin in the upstream `tests/check_statements.py`, checked to 60 digits.

Every statement is proven. The proofs live in `LeanPool/PolylogIntegrals/Proofs/` and are only
referenced here,
so this file stays a readable list of what is claimed. Upstream `tests/Axioms.lean` checks
that each one depends only on the standard axioms; Lean Pool also audits the compiled environment.
-/

open Real

namespace LeanPolyLog

/-- A001: `Li₂(i) = -π²/48 + iG`. -/
public theorem A001 : Li 2 Complex.I = ((-π ^ 2 / 48 : ℝ) : ℂ) + (G : ℂ) * Complex.I :=
  Proofs.A001

/-- A002: `Li₂(1/(1+i)) = 5π²/96 - log²2/8 + i(π log 2 / 8 - G)`. -/
public theorem A002 : Li 2 (1 / (1 + Complex.I)) =
    ((5 * π ^ 2 / 96 - Real.log 2 ^ 2 / 8 : ℝ) : ℂ)
      + ((π / 8 * Real.log 2 - G : ℝ) : ℂ) * Complex.I :=
  Proofs.A002

/-- A003: `Li₂((√5-1)/2) = π²/10 - log²((1+√5)/2)`. -/
public theorem A003 :
    Lir 2 ((Real.sqrt 5 - 1) / 2) = π ^ 2 / 10 - Real.log ((1 + Real.sqrt 5) / 2) ^ 2 :=
  Proofs.A003

/-- A004 (corrected): `∫₀¹ log(1+x²)/x dx = π²/24`. -/
public theorem A004 : ∫ x in (0 : ℝ)..1, Real.log (1 + x ^ 2) / x = π ^ 2 / 24 :=
  Proofs.A004

/-- A005: `∫₀¹ log²(1+x²)/x³ dx = π²/12 - log²2`. -/
public theorem A005 :
    ∫ x in (0 : ℝ)..1, Real.log (1 + x ^ 2) ^ 2 / x ^ 3 = π ^ 2 / 12 - Real.log 2 ^ 2 :=
  Proofs.A005

/-- A006 (first half): `∫₀^{π/4} log cos x dx = G/2 - (π/4) log 2`. -/
public theorem A006_cos :
    ∫ x in (0 : ℝ)..(π / 4), Real.log (Real.cos x) = G / 2 - π / 4 * Real.log 2 :=
  Proofs.A006_cos

/-- A006 (second half): `∫₀^{π/4} log sin x dx = -G/2 - (π/4) log 2`. -/
public theorem A006_sin :
    ∫ x in (0 : ℝ)..(π / 4), Real.log (Real.sin x) = -G / 2 - π / 4 * Real.log 2 :=
  Proofs.A006_sin

/-- A007: `∫₀^{π/4} x log cos x dx = πG/8 - (π²/32) log 2 - (21/128) ζ(3)`. -/
public theorem A007 : ∫ x in (0 : ℝ)..(π / 4), x * Real.log (Real.cos x) =
    π * G / 8 - π ^ 2 / 32 * Real.log 2 - 21 / 128 * zeta3 :=
  Proofs.A007

/-- A008: `∫₀^{π/4} x log(1 + tan x) dx = (π²/64) log 2 - πG/8 + 21ζ(3)/64`. -/
public theorem A008 : ∫ x in (0 : ℝ)..(π / 4), x * Real.log (1 + Real.tan x) =
    π ^ 2 / 64 * Real.log 2 - π * G / 8 + 21 * zeta3 / 64 :=
  Proofs.A008

/-- A009: `∫₀^{π/2} x² cot x dx = (π²/4) log 2 - (7/8) ζ(3)`. -/
public theorem A009 :
    ∫ x in (0 : ℝ)..(π / 2), x ^ 2 * Real.cot x = π ^ 2 / 4 * Real.log 2 - 7 / 8 * zeta3 :=
  Proofs.A009

/-- A010: `∫₀^{π/4} x² tan² x dx = -G + π²/16 - π³/192 + (π/4) log 2`. -/
public theorem A010 : ∫ x in (0 : ℝ)..(π / 4), x ^ 2 * Real.tan x ^ 2 =
    -G + π ^ 2 / 16 - π ^ 3 / 192 + π / 4 * Real.log 2 :=
  Proofs.A010

/-- A011: `∫₀¹ Li₂(x) / (x √(1-x²)) dx = (3/8) π² log 2 - (7/16) ζ(3)`. -/
public theorem A011 : ∫ x in (0 : ℝ)..1, Lir 2 x / (x * Real.sqrt (1 - x ^ 2)) =
    3 / 8 * π ^ 2 * Real.log 2 - 7 / 16 * zeta3 :=
  Proofs.A011

/-- A012: `∫₀¹ arctan x / (x+1) · log x dx = -π³/64 + (G/2) log 2`. -/
public theorem A012 :
    ∫ x in (0 : ℝ)..1, Real.arctan x / (x + 1) * Real.log x = -π ^ 3 / 64 + G / 2 * Real.log 2 :=
  Proofs.A012

/-- A013: `∫₀¹ arctan x / (x+1) · log² x dx = -(π²/24) G - (π³/32) log 2 + (21π/64) ζ(3)`. -/
public theorem A013 : ∫ x in (0 : ℝ)..1, Real.arctan x / (x + 1) * Real.log x ^ 2 =
    -π ^ 2 / 24 * G - π ^ 3 / 32 * Real.log 2 + 21 * π / 64 * zeta3 :=
  Proofs.A013

/-- A014 (simplified form):
`∫₀¹ log x · log(1+x) / (1+x²) dx = 11π³/128 + (3π/32) log²2 - 2G log 2 - 3 Im Li₃((1+i)/2)`. -/
public theorem A014 : ∫ x in (0 : ℝ)..1, Real.log x * Real.log (x + 1) / (x ^ 2 + 1) =
    11 * π ^ 3 / 128 + 3 * π / 32 * Real.log 2 ^ 2 - 2 * G * Real.log 2
      - 3 * (Li 3 ((1 + Complex.I) / 2)).im :=
  Proofs.A014

/-- A015: `∫₀^{π/2} x log² sin x dx = Li₄(1/2) - 19π⁴/2880 + log⁴2/24 + π² log²2/12`. -/
public theorem A015 : ∫ x in (0 : ℝ)..(π / 2), x * Real.log (Real.sin x) ^ 2 =
    Lir 4 (1 / 2) - 19 * π ^ 4 / 2880 + Real.log 2 ^ 4 / 24 + π ^ 2 * Real.log 2 ^ 2 / 12 :=
  Proofs.A015

/-- A016: `∫₀¹ Li₃(x) / (x √(1-x²)) dx = Li₄(1/2)/2 + 41π⁴/5760 + log⁴2/48 + π² log²2/6`. -/
public theorem A016 : ∫ x in (0 : ℝ)..1, Lir 3 x / (x * Real.sqrt (1 - x ^ 2)) =
    Lir 4 (1 / 2) / 2 + 41 * π ^ 4 / 5760 + Real.log 2 ^ 4 / 48 + π ^ 2 * Real.log 2 ^ 2 / 6 :=
  Proofs.A016

end LeanPolyLog
