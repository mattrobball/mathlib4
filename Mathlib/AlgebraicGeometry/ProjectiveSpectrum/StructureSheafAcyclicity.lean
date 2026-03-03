/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.TwistedCohomology

/-!
# Acyclicity of the structure sheaf on projective space

This file proves the higher cohomology vanishing for the structure sheaf on
projective n-space over a commutative ring `R`:
  `Hᵖ(algebraicComplex, 𝒪) = 0` for `p > 0`

This is a direct corollary of the twisted sheaf acyclicity `algebraicComplex_shift_acyclic_pos`
at `d = 0`, since `GradedModule.shift 𝒜 0 = 𝒜` definitionally.

## Main results

* `algebraicComplex_acyclic_pos`: `Hᵖ = 0` for `p > 0`

## References

* [Stacks Project, Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)
-/

noncomputable section

open MvPolynomial CategoryTheory CategoryTheory.Limits Finset

namespace AlgebraicGeometry.Proj

universe u

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

private abbrev 𝒜 (n : ℕ) (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

local instance : SetLike.GradedSMul (𝒜 n R) (𝒜 n R) :=
  SetLike.GradedMul.toGradedSMul _

/-- `Hᵖ(algebraicComplex) = 0` for `p > 0`: the higher cohomology of the
structure sheaf on projective n-space vanishes. This is a corollary of
`algebraicComplex_shift_acyclic_pos` at `d = 0`. -/
theorem algebraicComplex_acyclic_pos (p : ℕ) :
    IsZero ((algebraicComplex n R (𝒜 n R)).homology (p + 1)) :=
  algebraicComplex_shift_acyclic_pos 0 (le_refl 0) p

end AlgebraicGeometry.Proj
