# clifford-maxwell

A formal proof in **Lean 4** (with Mathlib) that Maxwell's equations of
electromagnetism can be expressed as a single equation in Clifford
(geometric) algebra, and that grade decomposition recovers the four
classical equations.

## Goal

In geometric algebra the four Maxwell equations collapse into one:

```
∇⋆ F = J
```

where `∇⋆` is the spacetime vector derivative, `F` is the electromagnetic
field bivector (encoding both **E** and **B**), and `J` is the
four-current.  Decomposing both sides by grade yields the familiar
divergence and curl equations of classical electrodynamics.

This project aims to **formally verify** that derivation end-to-end in
Lean 4, producing a machine-checked proof chain from Clifford algebra
axioms to the four Maxwell PDEs.

## Current status — ~40% complete

The algebraic scaffolding is solid and fully proven (no `sorry`).
The physics layer — the part that actually makes this about
electromagnetism rather than abstract algebra — is entirely missing.

### What is done

| Component | Status | Lines |
|---|---|---|
| **Grade selection** (`gradeSelect`, `gradeSelectL`) | Complete | ~110 |
| Linearity, idempotency, orthogonality lemmas | Complete | |
| Interaction with generators (vectors, scalars, 1) | Complete | ~70 |
| Membership characterisation (`mem_rMultivector_iff_gradeSelect`) | Complete | ~25 |
| **Wedge product** (`⋏`) via exterior transport | Complete | ~100 |
| Wedge associativity, distributivity, anticommutativity | Complete | |
| **Maxwell skeleton** (`D F = J` ⇒ graded equations) | Complete | ~80 |
| Split into grades 0–3, linear-D variant | Complete | |
| **Homogeneous elements** (`IsHomogeneous`) | Complete | ~85 |
| Closure under add, smul, neg, sub, sum | Complete | |
| **Grade involution, reversion, Clifford conjugate** | Complete | ~85 |
| **Grade-sum decomposition** | Complete | ~55 |

All 792 lines compile cleanly with `lake build`.

### What remains

These are listed roughly in order of increasing difficulty.

| Task | Difficulty | Notes |
|---|---|---|
| **Inner / contraction product** on Clifford elements | Medium | Mathlib's `Contraction` module is already imported but unused. |
| **Grade arithmetic for Clifford multiplication** (grade-r × grade-s lands in specific grades) | Hard | Key missing piece. The wedge–contraction decomposition `ab = a⌋b + a∧b` needs to be formalised. |
| **Minkowski quadratic form** `Q` with signature (−,+,+,+) on ℝ⁴ | Medium | Needs a concrete `QuadraticForm ℝ (Fin 4 → ℝ)` instance. |
| **Vector derivative operator** `∇⋆` as a genuine differential operator | Hard | Requires either smooth-manifold calculus or a workable discrete/formal substitute. |
| **The key physics theorem**: `∇⋆ F` lives in grades 1 ⊕ 3 when `F` is grade-2 and `∇⋆` is grade-1 | Very hard | Two prior attempts (by Claude Opus 4.6 and Gemini 3 Pro Preview) were reverted. |
| **Match graded components to classical PDEs** (Gauss, Faraday, etc.) | Hard | Requires all of the above plus coordinate extraction. |

The Maxwell skeleton theorems (Part E) are currently tautological — they
say "if `D F = J` then `proj_r(D F) = proj_r(J)`", which is just
`congrArg`.  The real content is proving that `D F` *only has* grade-1
and grade-3 parts when `F` is a bivector and `D` is a vector derivative.

### Honest assessment

The completed work is a well-structured algebraic toolkit: grade
projection, wedge product, homogeneity, conjugation.  This is genuine
and nontrivial Lean/Mathlib work, but it is the *easier* half.  The
missing pieces — grade arithmetic for the Clifford product, a concrete
Minkowski form, and a differential operator — are where the real
difficulty lies.  Two serious attempts at the grade-splitting proof have
already failed and been reverted.

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
(v4.16.0) and an internet connection for the first build (to fetch
Mathlib).

```sh
lake build
```

The first build will download ~1 GB of Mathlib oleans and take several
minutes.  Subsequent builds are fast.

## Structure

This is a single-file project:

```
MaxwellGA.lean          # All definitions and proofs (792 lines)
lakefile.lean           # Build configuration (depends on Mathlib v4.16.0)
lake-manifest.json      # Dependency lockfile
lean-toolchain          # Lean version pin (v4.16.0)
```

### Sections within MaxwellGA.lean

- **A** — Grade-r submodules (`rMultivector`)
- **B** — Grade selection (`gradeSelect`, `gradeSelectL`) + lemmas
- **C** — Named projections (`proj0`–`proj4`)
- **D** — Wedge product (`⋏`) + algebraic properties
- **E** — Maxwell skeleton (one-line equation ⇒ graded equations)
- **F** — Homogeneous elements (`IsHomogeneous`)
- **G** — Grade involution, reversion, Clifford conjugate
- **H** — Wedge anticommutativity for vectors
- **I** — Maxwell refinements (source-free case, residuals)
- **J** — Grade-sum decomposition

## License

[CC0 1.0 Universal](LICENSE.txt) — public domain.
