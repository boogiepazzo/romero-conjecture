# romero-conjecture

Lean 4 / mathlib formalizations of named open conjectures, each with a faithful
formal statement and machine-checked partial results.

## Status

**No open conjecture is resolved in this repository. `SOLVED_COUNT = 0`.**

Every file header carries `STATUS: IN PROGRESS / NOT YET SOLVED`. The conjectures
themselves appear only as `def … : Prop`. What is proved are special cases,
reductions, reformulations and sanity lemmas. Many of the proved special cases
are known theorems re-formalized here; they are not new mathematics.

## Tracker

| Conjecture | Files | Issue | Machine-checked so far |
|---|---|---|---|
| Jeśmanowicz' conjecture (1955/56) | `Jesmanowicz.lean`, `JesmanowiczAllN.lean`, `JesmanowiczFamilies.lean`, `JesmanowiczDemjanenko.lean` | [#1](https://github.com/boogiepazzo/romero-conjecture/issues/1) | (3,4,5) and (5,12,13) for every n; Lu's family (4k²−1, 4k, 4k²+1) and (7,24,25) for n = 1; Dem'janenko's family (2k+1, 2k(k+1), 2k(k+1)+1) for n = 1 when 4 ∤ k (the case 4 ∣ k is only reduced to an unproved residual statement); for n > 1, a nontrivial solution has x < z < y or y < z < x |
| Elliott–Halberstam conjecture (1968/70), von Mangoldt form | `ElliottHalberstam.lean` | [#2](https://github.com/boogiepazzo/romero-conjecture/issues/2) | Trivial bounds; monotonicity in the level; reductions to natural exponents, large x, and levels tending to 1 |
| Hot spots conjecture (Rauch, 1974), heat conduction | `HotSpots.lean` | [#3](https://github.com/boogiepazzo/romero-conjecture/issues/3) | Zero mean and sign change of Neumann eigenfunctions; the interval case in full |
| Goldbach's conjecture (1742), von Mangoldt-weighted form | `Goldbach.lean` | [#5](https://github.com/boogiepazzo/romero-conjecture/issues/5) | Positivity criteria for the weighted counts; explicit bound on the prime-power contribution; equivalent forms; verification to 10⁴ (evidence only) |
| Legendre's conjecture, Chebyshev θ / ψ form | `Legendre.lean` | [#6](https://github.com/boogiepazzo/romero-conjecture/issues/6) | θ, ψ and prime-counting reformulations; Oppermann ⇒ Legendre; Andrica ⇒ Legendre; Legendre ⇒ gap ≤ 4√p + 1; verification for n ≤ 20000 (evidence only) |
| Pólya's eigenvalue conjecture (1954/61), heat equation | `Polya.lean` | [#8](https://github.com/boogiepazzo/romero-conjecture/issues/8) | The interval case in full (classical formulation); lattice-point bound for the rectangle's model spectrum; product sines are eigenfunctions of the rectangle |

All files live in `RomeroConjecture/`.

## What "machine-checked" means here

- `lake build` passes on everything imported by `RomeroConjecture.lean`.
- No `sorry`, no added `axiom`, no `native_decide` in imported files.
- `#print axioms` on the audited theorems shows at most `propext`,
  `Classical.choice` and `Quot.sound`.
- Numerical verifications use `decide +kernel` with a verified checker. They are
  labelled as evidence only and are far below the published verification ranges.

A file that exists in `RomeroConjecture/` but is not imported by
`RomeroConjecture.lean` is a work-in-progress snapshot and is not covered by
these guarantees.

## Caveats

- **Statement fidelity.** `HotSpots.lean` uses a weak (variational) Neumann
  formulation because mathlib has no Sobolev spaces; its equivalence with the
  standard definition is argued informally in the header, not formalized.
  `Polya.lean` uses classical Dirichlet eigenfunctions and a counting bound
  over linearly independent families; on domains with irregular boundary
  points this can differ from the textbook spectrum. Its rectangle result is
  for the explicit model spectrum, without a completeness theorem.
- **Open status.** Each issue records a brief literature check, not an
  exhaustive one. For the hot spots conjecture, several unrefereed 2026
  preprints claim large parts of the planar case; see issue #3. Likewise an
  unrefereed October 2026 preprint claims Pólya's inequality for simply
  connected planar domains; see issue #8.
- **Attribution and priority.** File headers and issues record who formulated
  each conjecture, who proved the special cases re-formalized here, and where
  dates or attributions are uncertain or rest on secondary sources (for example
  the 1955/56 dating of Jeśmanowicz' paper, and the attribution of the
  (5,12,13) all-n case).

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` and mathlib in `lake-manifest.json`.

```bash
lake exe cache get
```

```bash
lake build
```

To check a single file and see its `#print axioms` output:

```bash
lake env lean RomeroConjecture/Jesmanowicz.lean
```
