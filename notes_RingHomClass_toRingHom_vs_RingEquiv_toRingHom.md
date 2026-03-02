# `RingHomClass.toRingHom` vs `RingEquiv.toRingHom`: The Morphism Class Refactor

Notes compiled from public Zulip discussions (mathlib4 stream) and GitHub issues, March 2026.

---

## 1. The Two Definitions Today

### `RingHomClass.toRingHom` (Mathlib/Algebra/Ring/Hom/Defs.lean:335)

```lean
@[coe]
def RingHomClass.toRingHom (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

instance : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩
```

- Generic: works for *any* type `F` with `[RingHomClass F α β]`.
- This is the **default coercion** from `F` to `α →+* β`.
- Used extensively in the semilinear map ecosystem (e.g., `LinearEquiv`, `AlgEquiv` land here through the class hierarchy).

### `RingEquiv.toRingHom` (Mathlib/Algebra/Ring/Equiv.lean:748)

```lean
def toRingHom (e : R ≃+* S) : R →+* S :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }

@[simp] theorem toRingHom_eq_coe (f : R ≃+* S) : f.toRingHom = ↑f := rfl
@[simp, norm_cast] theorem coe_toRingHom (f : R ≃+* S) : ⇑(f : R →+* S) = f := rfl
```

- Concrete: only for `R ≃+* S`.
- Enables dot notation: `e.toRingHom`.
- Has dedicated simp lemmas for `refl`, `trans`, injectivity, etc.

### How they relate

The coercion `(e : R →+* S)` for `e : R ≃+* S` goes through `RingHomClass.toRingHom` via the `CoeTC` instance. The simp lemma `toRingHom_eq_coe` bridges `RingEquiv.toRingHom` to the coercion. But the two definitions are **not definitionally equal** — they build the `RingHom` from different intermediate structures (one via `MulEquiv.toMonoidHom`/`AddEquiv.toAddMonoidHom`, the other via the class coercions `(f : α →* β)` and `(f : α →+ β)`).

---

## 2. The Zulip Discussion (Nov–Dec 2025)

Thread: [RingHomClass.toRingHom vs RingEquiv.toRingHom](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/RingHomClass.2EtoRingHom.20vs.20RingEquiv.2EtoRingHom.html) — 14 messages.

### Trigger

**Nailin Guan** (Nov 28, 2025) noticed inconsistent usage: semilinear equivalences consistently use `RingHomClass.toRingHom` everywhere, while `ModuleCat.restrictScalars_isEquivalence_of_ringEquiv` uses `RingEquiv.toRingHom`. Which should be preferred?

### Positions

| Participant | Position |
|---|---|
| **Anne Baanen** | `RingEquiv.toRingHom` should be preferred — better simplification |
| **Junyan Xu** | The project is *eliminating* `RingEquiv.toRingHom`, possibly making it an abbreviation of `RingHomClass.toRingHom` |
| **Christian Merten** | `RingEquiv.toRingHom` will stay, with `RingHomClass.toRingHom e` simplifying *to* `RingEquiv.toRingHom e` automatically |
| **Andrew Yang** | The plan is eventually eliminating `RingHomClass.toRingHom` entirely, leaving only concrete projections. References the broader morphism hierarchy refactor. |
| **Jireh Loreaux** | Definitions should **not** take morphism classes as parameters (see Section 3). Prefers explicit chains like `AlgEquiv.toRingEquiv.toRingHom` despite non-defeq issues. |

### The `AlgEquiv` Diamond

**Junyan Xu** raised a concrete technical problem: for `e : A ≃ₐ[R] B`, the two paths

```
e.toAlgHom.toRingHom    vs    e.toRingEquiv.toRingHom
```

are **not reducibly equal**. If `RingHomClass.toRingHom` is removed, and operations like `RingHom.ker` only accept explicit `RingHom`, then applying `RingHom.ker` to an `AlgEquiv` requires choosing one of these paths — and lemmas stated using the other path won't apply without explicit conversion.

**Anne Baanen** proposed that `RingEquiv.toRingHom` and `AlgEquiv.toRingEquiv` become *primary coercions*, so users write `RingHom.ker (↑e)` with the coercion resolving unambiguously.

**Junyan Xu** countered that this doesn't solve the diamond; you'd still need bridging lemmas. They suggest keeping `RingHomClass.toRingHom` as the canonical form with simp lemmas to normalize both paths.

### Consensus Direction

No final consensus on the `toRingHom` question in isolation, but broad agreement on the overarching principle: **the real problem is definitions parameterized over morphism classes** (see next section).

---

## 3. The Morphism Hierarchy Refactor (GitHub #31365)

Issue: [Fixing Mathlib's morphism hierarchy](https://github.com/leanprover-community/mathlib4/issues/31365), opened by Jireh Loreaux, Nov 7, 2025.

### Core Problems

1. **Type inference pain**: Lean struggles to infer types involving morphism classes, requiring frequent type ascriptions.

2. **Self-coercion non-defeq**: A `RingHom` can be coerced to `RingHom` via `RingHomClass.toRingHom`, producing a term where `f ≠ ↑f` syntactically (and they're not defeq).

3. **Definition proliferation**: When a definition like `RingHom.ker` accepts `[RingHomClass F α β]`, it becomes a "definition schema" — one definition per instance. For `f : A →ₐ[R] B`:
   - `RingHom.ker f` (through `AlgHomClass → RingHomClass`)
   - `RingHom.ker (↑f : A →+* B)` (explicit coercion first)

   These produce **different terms** that are not trivially equal, requiring extra API to bridge them.

### Proposed Solution (Four Tasks)

| Task | Description | Status |
|---|---|---|
| **Task 0** | Ban new definitions from accepting morphism class terms | Policy — immediate |
| **Task 1** | Refactor existing defs (`RingHom.ker`, `LinearMap.range`, etc.) to require explicit morphism types | In progress |
| **Task 2** | Standardize coercion naming: `FooHom.ofClass` (from `FooHomClass` instance). Provides memorable naming, consistency, and dot notation (`.ofClass f`). | In progress |
| **Task 3** | Remove `@[coe]` / `CoeTC` attributes from `FooHom.ofClass` (keep the defs, drop automatic coercion) | Blocked on Tasks 1 & 2 |

### Sequencing Rationale

Tasks 1 and 2 can proceed in parallel. Task 3 must wait for both — otherwise, removing coercions before refactoring definitions would silently break uses that relied on the automatic coercion to synthesize the explicit morphism.

### Nuance

Coercions remain useful *in proofs* (e.g., `AlgEquiv.spectrum_eq` coerces to access `.symm` on abstract equivalences). The refactor targets *definitions*, not proof-mode usage.

---

## 4. The FunLike Background

The `FunLike` / `DFunLike` framework (originally by Anne Baanen) provides the morphism class infrastructure. Key historical milestones:

- **PR #8386** (merged): Refactored `FunLike` to use **unbundled inheritance** (classes take `FunLike` as a parameter rather than extending it), because the bundled hierarchy was too large and slowed coercion resolution.

- **Lean PR #2174** (merged, Mar 2023): Introduced `semiOutParam` to fix typeclass inference loops in the morphism class hierarchy (e.g., the `OrderMonoidWithZeroHomClass` disaster).

- **FunLike issues thread**: Long-running discussion on inference failures, naming conventions, and the general difficulty of making the class hierarchy performant.

---

## 5. Related Ongoing Refactors

### Refactoring `AlgEquiv` (#29354)

- **Monica Omar** is refactoring `AlgEquiv` to support non-unital structures.
- Hit pre-existing diamond problems (subalgebra with two distinct algebra instances on localized structures).
- Exploring `NonUnitalNonAssocSemiring` + `Module` vs `DistribMulAction` as base constraints.
- Benchmark impact: ~0.49% instruction count increase.
- Thread: [Refactoring `AlgEquiv`](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Refactoring.20.60AlgEquiv.60.20(.2329354).html)

### Refactoring Algebraic Properties of Bundled Maps (#33477)

- **Moritz Doll** proposing typeclasses for `FunLike` + algebraic operations to deduplicate lemmas like `(f + g) x = f x + g x` across function types.
- Performance concern: +1.6% instructions, +2.3% wall-clock.
- Thread: [Refactoring algebraic properties of bundled maps](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Refactoring.20algebraic.20properties.20of.20bundled.20maps.html)

---

## 6. Practical Implications for Downstream Code

### Current Best Practice (until refactor lands)

1. **In definitions**: Accept concrete morphism types (`R →+* S`, not `[RingHomClass F R S]`).
2. **For coercion in proofs**: Use `(↑e : R →+* S)` for `e : R ≃+* S`; this goes through `RingHomClass.toRingHom`.
3. **For dot notation**: `e.toRingHom` is fine and simp-normalizes to the coercion.
4. **Semilinear maps**: The ecosystem already standardized on `RingHomClass.toRingHom` for the `σ` parameter of `LinearMap`/`LinearEquiv` — don't fight it.

### After Refactor (#31365)

1. `RingHom.ker` etc. will only accept `R →+* S`.
2. To apply to an `AlgEquiv`, you'll write `RingHom.ker (e.toRingEquiv.toRingHom)` or `RingHom.ker (.ofClass e)`.
3. Automatic coercion via `CoeTC` may be removed; explicit conversion will be required.
4. `RingEquiv.toRingHom` stays as the primary concrete projection.
5. `RingHomClass.toRingHom` may be renamed to `RingHom.ofClass` and lose its `@[coe]` attribute.

---

## 7. Key Takeaways

- The `toRingHom` question is a microcosm of a much larger architectural issue: **how should the morphism hierarchy handle coercion between levels?**
- The community is converging on: **definitions should be concrete, coercions should be explicit, and class-polymorphic defs are an anti-pattern.**
- The transition is gradual and requires careful sequencing to avoid silent regressions.
- Performance is a real constraint — every hierarchy change has measurable build-time impact.

---

## Sources

- [Zulip: RingHomClass.toRingHom vs RingEquiv.toRingHom](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/RingHomClass.2EtoRingHom.20vs.20RingEquiv.2EtoRingHom.html)
- [GitHub #31365: Fixing Mathlib's morphism hierarchy](https://github.com/leanprover-community/mathlib4/issues/31365)
- [Zulip: FunLike issues](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/FunLike.20issues.html)
- [GitHub PR #8386: Refactor FunLike to unbundled inheritance](https://github.com/leanprover-community/mathlib4/pull/8386)
- [Zulip: Refactoring `AlgEquiv` (#29354)](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Refactoring.20.60AlgEquiv.60.20(.2329354).html)
- [Zulip: Refactoring algebraic properties of bundled maps](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Refactoring.20algebraic.20properties.20of.20bundled.20maps.html)
- [Mathlib docs: Ring.Hom.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Hom/Defs.html)
- [Mathlib docs: Ring.Equiv](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Equiv.html)
