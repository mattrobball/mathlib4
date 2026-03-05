/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.TwistedCohomology
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Serre duality perfect pairing on projective space

This file constructs the **Serre duality perfect pairing** for projective `n`-space
over a commutative ring `R`:

```
  H⁰(Pⁿ, 𝒪(d)) ⊗_R Hⁿ(Pⁿ, 𝒪(-n-1-d)) → Hⁿ(Pⁿ, 𝒪(-n-1)) ≅ R
```

Under the isomorphisms `H⁰(𝒪(d)) ≅ 𝒜_d` and `Hⁿ(𝒪(-n-1-d)) ≅ 𝒜_d`, the cup product
pairing becomes the **coefficient inner product**: `⟨f, p⟩ = Σ_α coeff(f,α) · coeff(p,α)`,
which pairs degree-`d` monomials orthonormally. This is a perfect pairing because the
monomial basis is self-dual.

## Main results

* `serrePairingPoly` — the bilinear coefficient inner product on `𝒜_d`
* `serrePerfectPairing` — this pairing is a `PerfectPairing R (𝒜_d) (𝒜_d)`

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

/-! ### Degree-d monomial Finset -/

/-- The finset of `Finsupp`s with total degree `d` over `Fin (n + 1)`.
These index the monomial basis of `𝒜_d`. -/
private def degreeFinset (n : ℕ) (d : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  Finset.finsuppAntidiag Finset.univ d

private theorem univ_sum_eq_degree (α : Fin (n + 1) →₀ ℕ) :
    Finset.univ.sum (⇑α) = α.degree :=
  (Finset.sum_subset (Finset.subset_univ α.support)
    (fun _ _ hi => Finsupp.notMem_support_iff.mp hi)).symm

private theorem mem_degreeFinset {d : ℕ} {α : Fin (n + 1) →₀ ℕ} :
    α ∈ degreeFinset n d ↔ α.degree = d := by
  simp only [degreeFinset, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  exact (univ_sum_eq_degree α) ▸ Iff.rfl

private theorem monomial_mem_homogeneous {d : ℕ} {α : Fin (n + 1) →₀ ℕ}
    (hα : α ∈ degreeFinset n d) (r : R) :
    MvPolynomial.monomial α r ∈ (𝒜 n R) d :=
  (MvPolynomial.mem_homogeneousSubmodule d _).mpr
    (MvPolynomial.isHomogeneous_monomial r (mem_degreeFinset.mp hα))

private theorem support_subset_degreeFinset {d : ℕ}
    (p : ↥((𝒜 n R) d)) : p.val.support ⊆ degreeFinset n d := by
  intro α hα
  rw [mem_degreeFinset]
  have hp := (MvPolynomial.mem_homogeneousSubmodule d _).mp p.2
  exact (congr_fun Finsupp.degree_eq_weight_one α).trans
    (hp (Finsupp.mem_support_iff.mp hα))

/-! ### Coefficient pairing -/

/-- The **coefficient inner product** on `𝒜_d`: pairs two homogeneous polynomials by
`⟨f, p⟩ = Σ_{|α|=d} coeff(α, f) · coeff(α, p)`. This is the algebraic manifestation
of the Serre duality pairing on projective space. -/
def serrePairingPoly (n : ℕ) (R : Type u) [CommRing R] (d : ℕ) :
    ↥((𝒜 n R) d) →ₗ[R] ↥((𝒜 n R) d) →ₗ[R] R :=
  LinearMap.mk₂ R
    (fun f p => (degreeFinset n d).sum
      (fun α => MvPolynomial.coeff α f.val * MvPolynomial.coeff α p.val))
    (fun f₁ f₂ p => by
      show _ = (degreeFinset n d).sum _ + (degreeFinset n d).sum _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by
        simp only [Submodule.coe_add, MvPolynomial.coeff_add]; ring)
    (fun r f p => by
      show _ = r • (degreeFinset n d).sum _
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun α _ => by
        simp only [SetLike.val_smul, MvPolynomial.coeff_smul, smul_eq_mul]; ring)
    (fun f p₁ p₂ => by
      show _ = (degreeFinset n d).sum _ + (degreeFinset n d).sum _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by
        simp only [Submodule.coe_add, MvPolynomial.coeff_add]; ring)
    (fun r f p => by
      show _ = r • (degreeFinset n d).sum _
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun α _ => by
        simp only [SetLike.val_smul, MvPolynomial.coeff_smul, smul_eq_mul]; ring)

/-! ### Symmetry and monomial extraction -/

theorem serrePairingPoly_comm (d : ℕ) (f p : ↥((𝒜 n R) d)) :
    serrePairingPoly n R d f p = serrePairingPoly n R d p f := by
  simp only [serrePairingPoly, LinearMap.mk₂_apply]
  congr 1; ext α; ring

/-- Evaluating the pairing against a monomial extracts the corresponding coefficient. -/
theorem serrePairingPoly_monomial (d : ℕ) (f : ↥((𝒜 n R) d))
    (α : Fin (n + 1) →₀ ℕ) (hα : α ∈ degreeFinset n d) :
    serrePairingPoly n R d f ⟨MvPolynomial.monomial α 1,
      monomial_mem_homogeneous hα 1⟩ = MvPolynomial.coeff α f.val := by
  simp only [serrePairingPoly, LinearMap.mk₂_apply]
  rw [Finset.sum_eq_single α]
  · simp [MvPolynomial.coeff_monomial]
  · intro β _ hβ
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hβ), mul_zero]
  · intro habs; exact absurd hα habs

/-! ### Injectivity -/

private theorem serrePairingPoly_injective (d : ℕ) :
    Function.Injective (serrePairingPoly n R d) := by
  intro f g hfg
  have h : ∀ α ∈ degreeFinset n d,
      MvPolynomial.coeff α f.val = MvPolynomial.coeff α g.val := by
    intro α hα
    have := congr_fun (congr_arg DFunLike.coe hfg)
      ⟨MvPolynomial.monomial α 1, monomial_mem_homogeneous hα 1⟩
    simp only [serrePairingPoly_monomial d _ α hα] at this
    exact this
  refine Subtype.ext (MvPolynomial.ext _ _ fun β => ?_)
  by_cases hβ : β ∈ degreeFinset n d
  · exact h β hβ
  · have hf : MvPolynomial.coeff β f.val = 0 := by
      by_contra hne
      exact hβ (support_subset_degreeFinset f (Finsupp.mem_support_iff.mpr hne))
    have hg : MvPolynomial.coeff β g.val = 0 := by
      by_contra hne
      exact hβ (support_subset_degreeFinset g (Finsupp.mem_support_iff.mpr hne))
    rw [hf, hg]

/-! ### Surjectivity -/

/-- A homogeneous polynomial of degree `d` is the sum of its monomial terms
over the degree-`d` finset. -/
private theorem poly_eq_sum_degreeFinset (d : ℕ) (p : ↥((𝒜 n R) d)) :
    p.val = (degreeFinset n d).sum
      fun α => MvPolynomial.monomial α (MvPolynomial.coeff α p.val) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p.val]
  apply Finset.sum_subset (support_subset_degreeFinset p)
  intro α _ hα
  rw [MvPolynomial.notMem_support_iff.mp hα, MvPolynomial.monomial_zero]

/-- The coefficient of `fval = Σ_α monomial(α, c_α)` at β equals `c_β`,
when summing over a set of distinct multi-indices. -/
private theorem coeff_sum_monomial_degreeFinset (d : ℕ) (c : (Fin (n + 1) →₀ ℕ) → R)
    (β : Fin (n + 1) →₀ ℕ) (hβ : β ∈ degreeFinset n d) :
    MvPolynomial.coeff β ((degreeFinset n d).sum
      fun α => MvPolynomial.monomial α (c α)) = c β := by
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single β]
  · simp [MvPolynomial.coeff_monomial]
  · intro α _ hαβ; rw [MvPolynomial.coeff_monomial, if_neg hαβ]
  · intro habs; exact absurd hβ habs

private theorem serrePairingPoly_surjective (d : ℕ) :
    Function.Surjective (serrePairingPoly n R d) := by
  intro φ
  -- c(α) = φ(monomial α 1) for α ∈ degreeFinset, 0 otherwise
  set c : (Fin (n + 1) →₀ ℕ) → R := fun α =>
    if h : α ∈ degreeFinset n d then
      φ ⟨MvPolynomial.monomial α 1, monomial_mem_homogeneous h 1⟩
    else 0
  -- Construct f = Σ_α monomial(α, c(α))
  set fval := (degreeFinset n d).sum fun α => MvPolynomial.monomial α (c α) with hfval_def
  have hfval : fval ∈ (𝒜 n R) d := Submodule.sum_mem _ fun α hα =>
    monomial_mem_homogeneous hα _
  set f : ↥((𝒜 n R) d) := ⟨fval, hfval⟩
  -- c simplifies for α ∈ degreeFinset
  have hc : ∀ (α : Fin (n + 1) →₀ ℕ) (hα : α ∈ degreeFinset n d),
      c α = φ ⟨MvPolynomial.monomial α 1, monomial_mem_homogeneous hα 1⟩ :=
    fun α hα => dif_pos hα
  -- coeff(α, fval) = c(α) for α ∈ degreeFinset
  have hcoeff : ∀ α ∈ degreeFinset n d, MvPolynomial.coeff α f.val = c α :=
    fun α hα => coeff_sum_monomial_degreeFinset d c α hα
  -- Agreement on monomials: serrePairingPoly f (monomial α 1) = φ (monomial α 1)
  have h_agree : ∀ (α : Fin (n + 1) →₀ ℕ) (hα : α ∈ degreeFinset n d),
      serrePairingPoly n R d f ⟨MvPolynomial.monomial α 1,
        monomial_mem_homogeneous hα 1⟩ =
      φ ⟨MvPolynomial.monomial α 1, monomial_mem_homogeneous hα 1⟩ := by
    intro α hα
    rw [serrePairingPoly_monomial d f α hα, hcoeff α hα, hc α hα]
  -- Show serrePairingPoly f p = φ p for all p by writing p as monomial sum
  refine ⟨f, LinearMap.ext fun p => ?_⟩
  -- Strategy: both sides equal Σ_α c(α) * coeff(α, p.val)
  -- LHS = Σ coeff(α,f.val) * coeff(α,p.val) = Σ c(α) * coeff(α,p.val)
  -- RHS = φ(Σ coeff(α,p) • monomial α 1) = Σ coeff(α,p) * c(α)
  trans ((degreeFinset n d).sum fun α => c α * MvPolynomial.coeff α p.val)
  · -- LHS = target: substitute coeff(α, f.val) → c(α)
    simp only [serrePairingPoly, LinearMap.mk₂_apply]
    exact Finset.sum_congr rfl fun α hα => by rw [hcoeff α hα]
  · -- target = RHS
    -- For any α, monomial α (coeff α p.val) ∈ 𝒜_d (zero outside degreeFinset)
    have hterm_mem : ∀ α, MvPolynomial.monomial α (MvPolynomial.coeff α p.val) ∈
        (𝒜 n R) d := fun α => by
      by_cases h : MvPolynomial.coeff α p.val = 0
      · rw [h, MvPolynomial.monomial_zero]; exact zero_mem _
      · exact monomial_mem_homogeneous
          (support_subset_degreeFinset p (Finsupp.mem_support_iff.mpr h)) _
    -- Express p as sum of monomial elements in the submodule
    have hpelem : p = (degreeFinset n d).sum fun α =>
        (⟨MvPolynomial.monomial α (MvPolynomial.coeff α p.val),
          hterm_mem α⟩ : ↥((𝒜 n R) d)) :=
      Subtype.ext (by
        simp only [Submodule.coe_sum]
        exact poly_eq_sum_degreeFinset d p)
    -- Use conv to only rewrite p in φ's argument, preserving p.val in the sum
    conv_rhs => rw [hpelem, map_sum]
    exact Finset.sum_congr rfl fun α hα => by
      -- monomial α r = r • monomial α 1
      have hmk : (⟨MvPolynomial.monomial α (MvPolynomial.coeff α p.val),
            monomial_mem_homogeneous hα _⟩ : ↥((𝒜 n R) d)) =
          MvPolynomial.coeff α p.val •
            ⟨MvPolynomial.monomial α 1, monomial_mem_homogeneous hα 1⟩ :=
        Subtype.ext (show MvPolynomial.monomial α (MvPolynomial.coeff α p.val) =
          MvPolynomial.coeff α p.val • MvPolynomial.monomial α 1 by
          rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial,
            mul_one])
      rw [hmk, LinearMap.map_smul, hc α hα, smul_eq_mul, mul_comm]

/-! ### Perfect pairing -/

/-- The coefficient inner product on `𝒜_d` is a **perfect pairing**: the induced maps
`𝒜_d → Dual(𝒜_d)` and `𝒜_d → Dual(𝒜_d)` are both bijective. This is the polynomial-level
manifestation of Serre duality on projective `n`-space. -/
noncomputable def serrePerfectPairing (n : ℕ) (R : Type u) [CommRing R] (d : ℕ) :
    PerfectPairing R ↥((𝒜 n R) d) ↥((𝒜 n R) d) where
  toLinearMap := serrePairingPoly n R d
  bijective_left := ⟨serrePairingPoly_injective d, serrePairingPoly_surjective d⟩
  bijective_right := by
    rw [show (serrePairingPoly n R d).flip = serrePairingPoly n R d from
      LinearMap.ext fun f => LinearMap.ext fun p => serrePairingPoly_comm d p f]
    exact ⟨serrePairingPoly_injective d, serrePairingPoly_surjective d⟩

/-! ### Multiplication by homogeneous polynomial on localized modules -/

section MulByHomogeneous

variable {d_nat : ℕ} {e : ℤ} {S : Finset (Fin (n + 1))}

/-- Membership proof for the numerator of `mulByHomogeneous`: if `g ∈ 𝒜_{d_nat}` and
`m ∈ (intShift 𝒜 e)_k`, then `g * m ∈ (intShift 𝒜 (e + d_nat))_k`. -/
private theorem mul_mem_intShift (g : ↥((𝒜 n R) d_nat))
    {k : ℕ} {m : MvPolynomial (Fin (n + 1)) R}
    (hm : m ∈ GradedModule.intShift (𝒜 n R) e k) :
    g.val * m ∈ GradedModule.intShift (𝒜 n R) (e + ↑d_nat) k := by
  simp only [GradedModule.intShift] at hm ⊢
  split_ifs at hm with h
  · rw [if_pos (by omega : 0 ≤ (↑k : ℤ) + (e + ↑d_nat))]
    have hkey : d_nat + ((↑k : ℤ) + e).toNat = ((↑k : ℤ) + (e + ↑d_nat)).toNat := by omega
    rw [← hkey]
    exact SetLike.GradedMul.mul_mem g.2 hm
  · rw [Submodule.mem_bot] at hm
    rw [hm, mul_zero]
    split_ifs <;> exact zero_mem _

/-- Multiplication by a homogeneous polynomial `g ∈ 𝒜_d` on localized modules
with degree shift: sends sections of `𝒪(e)` to sections of `𝒪(e + d)`.

Construction: at the `NumDenSameDeg` level, `m / f^k ↦ (g * m) / f^k`. The numerator
shifts from `(intShift 𝒜 e)_k` to `(intShift 𝒜 (e + d))_k` by graded multiplication.
Well-definedness and additivity follow from `val(mul_g(x)) = g • val(x)` in
`LocalizedModule` plus `val_injective`. -/
noncomputable def mulByHomogeneous (g : ↥((𝒜 n R) d_nat)) :
    HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.intShift (𝒜 n R) e) (coordProd n R S) →+
    HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.intShift (𝒜 n R) (e + ↑d_nat)) (coordProd n R S) where
  toFun := Quotient.map'
    (fun p => ⟨p.deg, ⟨g.val * ↑p.num, mul_mem_intShift g p.num.2⟩, p.den, p.den_mem⟩)
    (fun p q h => by
      -- Both sides = g • embedding(·); use smul'_mk to unfold, then apply h
      show HomogeneousLocalizedModule.NumDenSameDeg.embedding _ _ _ _ =
        HomogeneousLocalizedModule.NumDenSameDeg.embedding _ _ _ _
      simp only [HomogeneousLocalizedModule.NumDenSameDeg.embedding]
      rw [show g.val * (p.num : MvPolynomial _ R) =
          g.val • (p.num : MvPolynomial _ R) from (smul_eq_mul _ _).symm,
        show g.val * (q.num : MvPolynomial _ R) =
          g.val • (q.num : MvPolynomial _ R) from (smul_eq_mul _ _).symm,
        ← LocalizedModule.smul'_mk, ← LocalizedModule.smul'_mk]
      exact congr_arg _ h)
  map_zero' := HomogeneousLocalizedModule.ext _ <| by
    -- 0 = mk (0 : NumDenSameDeg); val (map' 0) = mk (g*0) 1 = mk 0 1 = 0
    rw [HomogeneousLocalizedModule.val_zero]
    change HomogeneousLocalizedModule.val (Quotient.map' _ _ (Quotient.mk'' (0 : _))) = 0
    rw [Quotient.map'_mk'', HomogeneousLocalizedModule.val_mk]
    simp [mul_zero, LocalizedModule.zero_mk]
  map_add' x y := by
    induction x, y using Quotient.inductionOn₂' with | _ p q =>
    change HomogeneousLocalizedModule.mk _ =
      HomogeneousLocalizedModule.mk _ + HomogeneousLocalizedModule.mk _
    rw [← HomogeneousLocalizedModule.mk_add]
    apply HomogeneousLocalizedModule.val_injective
    simp only [HomogeneousLocalizedModule.val_mk, LocalizedModule.mk_add_mk,
      LocalizedModule.mk_eq, HomogeneousLocalizedModule.NumDenSameDeg.num_add,
      HomogeneousLocalizedModule.NumDenSameDeg.den_add]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_eq_mul, smul_add, ← mul_smul]
    ring

end MulByHomogeneous

/-! ### Cup product on cochains -/

section CupProduct

variable {d_nat : ℕ} {e : ℤ}

/-- The **cup product** on `p`-cochains: given `g ∈ 𝒜_d`, multiply each local section
pointwise to get a map from `p`-cochains of `𝒪(e)` to `p`-cochains of `𝒪(e + d)`. -/
noncomputable def cupCochain (g : ↥((𝒜 n R) d_nat)) (p : ℕ)
    (c : (algebraicComplex n R (GradedModule.intShift (𝒜 n R) e)).X p) :
    (algebraicComplex n R (GradedModule.intShift (𝒜 n R) (e + ↑d_nat))).X p :=
  fun S => mulByHomogeneous g (c S)

/-- `mulByHomogeneous g` commutes with `coordRestrict j` (= `awayMap`):
ring multiplication by a global polynomial commutes with localization restriction. -/
private theorem mulByHomogeneous_comp_coordRestrict (g : ↥((𝒜 n R) d_nat))
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.intShift (𝒜 n R) e) (coordProd n R (TopCat.eraseNth T hT j).1)) :
    mulByHomogeneous g (coordRestrict n R _ T hT j x) =
    coordRestrict n R _ T hT j (mulByHomogeneous g x) := by
  induction x using Quotient.inductionOn' with | _ q =>
  apply HomogeneousLocalizedModule.val_injective
  -- Unfold mulByHomogeneous (a Quotient.map') and coordRestrict (= awayMap) through
  -- their coercion layers, then reduce to LocalizedModule.mk via val_mk/val_awayMap_mk
  simp only [coordRestrict, mulByHomogeneous, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalizedModule.awayMap_mk, Quotient.map'_mk'',
    HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.awayMap_mk_coe_num,
    HomogeneousLocalizedModule.awayMap_mk_coe_den]
  -- Both sides are LocalizedModule.mk; numerators differ by mul_left_comm
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul]
  ring

/-- The cup product commutes with the Čech differential: `mulByHomogeneous` commutes
with `awayMap` (restriction maps), so `cup_g ∘ δ = δ ∘ cup_g` on cochains. -/
theorem cupCochain_comp_algebraicδ (g : ↥((𝒜 n R) d_nat)) (p : ℕ)
    (f : (algebraicComplex n R (GradedModule.intShift (𝒜 n R) e)).X p) :
    cupCochain (n := n) g (p + 1)
      (algebraicδ n R (GradedModule.intShift (𝒜 n R) e) p f) =
    algebraicδ n R (GradedModule.intShift (𝒜 n R) (e + ↑d_nat)) p
      (cupCochain g p f) := by
  funext ⟨T, hT⟩
  change mulByHomogeneous g
    (∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
      coordRestrict n R (GradedModule.intShift (𝒜 n R) e) T hT j
        (f (TopCat.eraseNth T hT j))) =
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
      coordRestrict n R (GradedModule.intShift (𝒜 n R) (e + ↑d_nat)) T hT j
        (mulByHomogeneous g (f (TopCat.eraseNth T hT j)))
  rw [map_sum]
  congr 1; ext j
  rw [AddMonoidHom.map_zsmul, mulByHomogeneous_comp_coordRestrict]

end CupProduct

end AlgebraicGeometry.Proj
