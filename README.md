# romero-conjecture

Lean 4 / mathlib formalizations of named open conjectures, with machine-checked
partial results.

**Honesty policy.** Nothing here is claimed as a resolution of an open conjecture
unless the tracker below says `SOLVED`. Every file states its status in its header.
All proved statements are `sorry`-free and depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), checked with `#print axioms`.

`START_TIME` of the current campaign: 2026-11-24T23:01:03Z. `SOLVED_COUNT = 0`.

## Tracker

| # | Conjecture | File | Status |
|---|------------|------|--------|
| 1 | Jeśmanowicz' conjecture (1956) | `RomeroConjecture/Jesmanowicz.lean`, `RomeroConjecture/JesmanowiczAllN.lean`, `RomeroConjecture/JesmanowiczFamilies.lean` | IN PROGRESS / NOT YET SOLVED. Proved: (3,4,5) and (5,12,13) for all n; Lu's family (4k²−1, 4k, 4k²+1) and (7,24,25) for n = 1; a general reduction for n > 1 (known results, re-formalized) |
| 2 | Elliott–Halberstam conjecture (1968) | `RomeroConjecture/ElliottHalberstam.lean` | IN PROGRESS / NOT YET SOLVED |
| 3 | Hot spots conjecture (Rauch, 1974) | `RomeroConjecture/HotSpots.lean` | IN PROGRESS / NOT YET SOLVED |
| 4 | Goldbach's conjecture (1742), von Mangoldt-weighted form | `RomeroConjecture/Goldbach.lean` | IN PROGRESS / NOT YET SOLVED |
| 5 | Legendre's conjecture (Landau's problems, 1912), Chebyshev θ / ψ form | `RomeroConjecture/Legendre.lean` | IN PROGRESS / NOT YET SOLVED |

Withdrawn: Navier–Stokes existence and smoothness (issue 4, dropped at the owner's request).

## Building

```bash
lake exe cache get
```

```bash
lake build
```
