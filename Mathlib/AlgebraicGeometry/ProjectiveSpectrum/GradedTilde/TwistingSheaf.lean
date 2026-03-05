/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.GradedTilde
public import Mathlib.Algebra.Module.GradedModule.Shift

/-!
# The twisting sheaf `M̃(d)` on `Proj(A)`

Given a graded ring `A = ⨁ᵢ 𝒜 i` and a graded `A`-module `M = ⨁ᵢ 𝓜 i`, the
**twisted tilde sheaf** `M̃(d)` on `Proj(A)` is defined as the graded tilde of the
`d`-shifted module `M(d)`, where `M(d)ₙ = Mₙ₊ₐ`.

When `M = A` (the ring viewed as a module over itself), this gives the **structure
twisting sheaf** `𝒪_A(d)`, whose sections on `D₊(f)` consist of degree-`d` elements
of the localization `A_f`.

## Main definitions

* `GradedModule.twistingSheaf`: The twisted tilde sheaf `M̃(d)` on `Proj(A)`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]
* [Jean-Pierre Serre, *Faisceaux algébriques cohérents*][Ser55]
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry

universe u
variable {R : Type*} {A : Type u} {M : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable (𝓜 : ℕ → Submodule R M) [SetLike.GradedSMul 𝒜 𝓜]

open TopCat CategoryTheory

namespace GradedModule

/-- The twisted tilde sheaf `M̃(d)` on `Proj(A)`: the graded tilde of the `d`-shifted
module `M(d)`, where `M(d)ₙ = Mₙ₊ₐ`. -/
def twistingSheaf (d : ℕ) : Sheaf AddCommGrpCat (ProjectiveSpectrum.top 𝒜) :=
  tilde 𝒜 (GradedModule.shift 𝓜 d)

end GradedModule

end AlgebraicGeometry
