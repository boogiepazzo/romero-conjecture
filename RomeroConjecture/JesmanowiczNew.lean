/-
# Jeśmanowicz' conjecture for the triples `(33, 56, 65)` and `(57, 176, 185)`, every `n ≥ 1`

STATUS: IN PROGRESS / NOT YET SOLVED

(The status line refers to Jeśmanowicz' conjecture as a whole, which is OPEN and is NOT
proved here; see `RomeroConjecture/Jesmanowicz.lean` for the statement
`Jesmanowicz.JesmanowiczConjecture`. This file settles two individual triples only.)

## What IS proved in this file (machine-checked, no `sorry`, no extra axioms)

* `jesmanowiczFor_33_56_65 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 33 56 65 n` —
  for every `n ≥ 1`, the only solution in positive integers of
  `(33 n)^x + (56 n)^y = (65 n)^z` is `x = y = z = 2`.
  (`jesmanowiczFor_56_33_65` : the same with the legs swapped.)
* `jesmanowiczFor_57_176_185 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 57 176 185 n` —
  for every `n ≥ 1`, the only solution in positive integers of
  `(57 n)^x + (176 n)^y = (185 n)^z` is `x = y = z = 2`.
  (`jesmanowiczFor_176_57_185` : the same with the legs swapped.)

In the usual parametrization `(f² - g², 2fg, f² + g²)` these are `(f, g) = (7, 4)` and
`(f, g) = (11, 8)`. Both have the shape `g = 2^r`, `f = 2^r + 3` with `f` and
`f + g = 2^(r+1) + 3` prime (`r = 2, 3`); the odd leg is `3 (f + g)`.

Auxiliary results (each fully proved):

* `jesmanowicz_33_56_65`, `jesmanowicz_57_176_185` : the primitive case `n = 1`
  (`33^x + 56^y = 65^z`, resp. `57^x + 176^y = 185^z`, forces `x = y = z = 2`).
  These `n = 1` statements are NOT new (see the novelty assessment).
* `t33_eleven_pow_dvd_sq_sub`, `t57_nineteen_pow_dvd_sq_sub` : if `11^x ∣ (65^w)² - B²`
  (resp. `19^x ∣ (185^w)² - B²`) with `B < c^w` not divisible by the prime, then `x ≤ 2w`.
* `t33_two_pow_dvd_pow_sub_one`, `t57_two_pow_dvd_pow_sub_one` : lifting the exponent at 2:
  `2^k ∣ 65^z - 1 ⇒ k < z + 6`, `2^k ∣ 185^z - 1 ⇒ k < z + 3` (`z > 0`).
* `t33_sq_add_ne`, `t57_sq_add_ne` : `B² + 56^y p^E = (65^Z)²` (resp.
  `B² + 176^y p^E = (185^Z)²`) is impossible for `y > 2Z`, `E ≥ 1`, `p` a prime not dividing
  `2·7·B` (resp. `2·11·B`), `B ≡ 1 (mod 4)` and `B` a nonzero square mod `7` (resp. `11`).
* `no_solution_33_56_65_y_lt_z_lt_x`, `no_solution_33_56_65_x_lt_z_lt_y`,
  `no_solution_57_176_185_y_lt_z_lt_x`, `no_solution_57_176_185_x_lt_z_lt_y` :
  the two configurations `y < z < x` and `x < z < y` are impossible for `n > 1`.

## Proof outline (elementary; worked out by the formalizer, not transcribed from a paper)

Notation: `(a, b, c) = (33, 56, 65)`; the proof for `(57, 176, 185)` is parallel and the
differences are given in brackets.

* `n = 1`. Mod 5 gives `x ≡ 2 (mod 4)`; mod 13 then gives `y` even; mod 3 gives `z ≡ y`
  even. [For `(57,176,185)`: mod 5, mod 16, mod 3.] With `x = 2X`, `z = 2Z`, `A = 65^Z`,
  `B = 33^X`: `A ≡ B ≡ 1 (mod 4)`, so `(A + B)/2` is odd and
  `(A - B)/2 · (A + B)/2 = 2^(3y-2) 7^y` forces `(A - B)/2 = 2^(3y-2)`, `(A + B)/2 = 7^y`.
  For `y ≥ 4` this contradicts `A - B ≡ 1 - 33 (mod 64)` [resp. `11^y < 2^(4y-2)`];
  `y = 2` gives `B = 33`, `A = 65`.
* `n > 1`. By `IsSolution.strict_cases_of_one_lt` (Le 1999, Deng 2014, Yang–Fu 2015;
  formalized in `JesmanowiczDemjanenko.lean`) a solution other than `(2,2,2)` has
  `y < z < x` or `x < z < y`.
  - `y < z < x`. Cancel `n^y`: `33^x n^(x-z) + q = 65^z` with `q n^(z-y) = 56^y`,
    `gcd(q, n) = 1`, hence `q ∈ {1, 7^y, 8^y}`. Mod 3 gives `q ≡ 2^z`, mod 11 gives
    `q ≡ (-1)^z`. If `q = 1`: `z` even. If `q = 7^y`: `z` even and `7^y ≡ 1 (mod 11)`,
    so `10 ∣ y`. If `q = 8^y`: then `n = 7^k`, `y = k (z - y)`, and mod 3 gives `z - y`
    even, so `y, z` are even. In every case `q = B²` and `z = 2w`, and
    `11^x ∣ (65^w - B)(65^w + B)` with `x > 2w` is impossible because `11` divides only
    one factor and `11^(2w+1) > 2·65^w`. [For `(57,176,185)`: `q ∈ {1, 11^y, 16^y}`,
    mod 3 and mod 19 (`14` is a non-residue mod 19, powers of `11` are residues), prime
    `19` with `19^(2w+1) > 2·185^w`; `16^y` is always a square.]
  - `x < z < y`. Cancel `n^x`: `q + 56^y n^(y-z) = 65^z` with `q n^(z-x) = 33^x`,
    `gcd(q, n) = 1`, hence `q ∈ {1, 3^x, 11^x}`.
    If `q = 1`: `2^(3y) ∣ 65^z - 1`, but `v_2(65^z - 1) = 6 + v_2(z) < 6 + z`
    (mathlib's `Nat.multiplicity_pow_two_sub_pow`), contradicting `y > z ≥ 2`.
    If `q = 3^x` (then `n = 11^k`) or `q = 11^x` (then `n = 3^k`): mod 16 gives `4 ∣ x`,
    mod 11 resp. mod 3 gives `z` even. So `q = B²` with `B ≡ 1 (mod 4)` a nonzero square
    mod 7, `z = 2Z`, and `B² + 56^y p^E = (65^Z)²` with `p ∈ {11, 3}`, `E ≥ 1`. As above
    `d = (A - B)/2` and `B + d` (odd) satisfy `d (B + d) = 2^(3y-2) 7^y p^E`. Then
    `2^(3y-2) ∣ d`; `7^y ∣ d` is impossible by size (`d < 65^Z`, `y > 2Z`);
    `p^E ∣ d` gives `B + d = 7^y < d`; so `d = 2^(3y-2)` and `B + 2^(3y-2) = 7^y p^E`,
    i.e. `B ≡ -2 (mod 7)`, a non-residue: contradiction. [For `(57,176,185)`:
    `q ∈ {1, 3^x, 19^x}`, `v_2(185^z - 1) = 3 + v_2(z)`, mod 16 and mod 19 resp. mod 3,
    and the final contradiction is mod 11: `-2^(4y-2)` is a non-residue mod 11.]

## Novelty assessment (read this before citing the result as new)

Claim made here, and nothing stronger: **the all-`n` statements for `(33, 56, 65)` and
`(57, 176, 185)` were NOT FOUND in the literature that was searched.** This is not a
certificate of novelty. The method is the standard one of this literature (Deng–Cohen
style cofactor analysis); what is possibly new is only that these two triples had not been
written up. Specifically:

What is certainly NOT new:
* The `n = 1` case of both triples. R. Styer, arXiv:2402.04428 (2024), states (abstract)
  that the primitive Jeśmanowicz conjecture holds whenever `a ≤ 10^6` or `b ≤ 10^6`.
* For `n > 1`: by Le (1999) and Deng (2014) / Yang–Fu (2015) a solution other than
  `(2,2,2)` needs `rad(n) ∣ b` (case `y < z < x`) or `rad(n) ∣ a` (case `x < z < y`).
  So only `n` whose prime factors all divide `56` or all divide `33` (resp. `176`, `57`)
  were at issue; the content of this file for `n > 1` is the treatment of those `n`.

Sources checked (what they cover, and why the two triples are outside):
* Le–Scott–Styer survey, arXiv:1808.06557, §2.2 (non-primitive cases). It lists the pairs
  `(f, g)` with the conjecture verified for all `n > 1`: `(2^k, 1)` (Deng–Cohen, Yang–Tang,
  Gou–Zhang, Tang–Yang, Deng, Tang–Weng, Zhang–Zhang, Miyazaki), `(6,1)`, `(10,1)`,
  `(12,1)`, `(14,1)`, `(5,2)`, `(7,2)`, `(49,2)`, `(9,2)`, `(11,2)`, `(8,3)`, `(9,4)`,
  `(g+1, g)` for `g = 2,…,7, 10, 17, 19, 25, 28, 45`, `(2^k, 2^k - 1)` with `2^k - 1` prime,
  `(2^k + 1, 2^k)` with `2^k + 1` prime, plus conditional results for `g = 1`.
  `(7, 4)` and `(11, 8)` are not in the list. (So e.g. `(20,21,29)`, `(28,45,53)`,
  `(36,77,85)`, `(48,55,73)`, `(65,72,97)`, `(16,63,65)` ARE already known for all `n`.)
* Soydan–Demirci–Cangül–Togbé survey, arXiv:1706.05480, §3: Deng–Cohen 1998 (odd leg a
  prime power plus a condition on `n`; the triples `(3,4,5)`, `(5,12,13)`, `(7,24,25)`,
  `(9,40,41)`, `(11,60,61)`), Le 1999, Yang–Fu 2015, Yang–Tang / Tang–Weng (Fermat numbers),
  Zhang–Zhang 2014, Deng 2014, Ma–Wu 2015 (`g = 1`), Miyazaki 2015 (a leg a power of 2).
  None applies: neither `33`, `56`, `57`, `176` is a prime power, and `g ≠ 1`.
* Nguyen–Nguyen–Quy, arXiv:2102.10921: `g = 2`, `f` an odd prime `< 100`. Not applicable.
* Feng–Luo, AIMS Math. 7 (2022) 8609–8621; Fan–Luo, AIMS Math. 8 (2023) 14232–14252;
  Guan, Adv. Math. (China) 50 (2021) 519–528: triples
  `((q^{2l} - p^{2k})/2, p^k q^l, (q^{2l} + p^{2k})/2)` with `p^k = 2^{m₁} - a^{m₂}`,
  `q^l = 2^{m₁} + a^{m₂}`, i.e. `f = 2^{m₁}` a power of 2. Here the odd legs are `3·11` and
  `3·19`, which would need `2^{m₁} = 7` resp. `11`. Not applicable.
* Fujita–Le, Bull. Aust. Math. Soc. 104 (2021) 29–39 (`g = 1`); Kitayama–Tagawa–Urahashi,
  Period. Math. Hungar. 86 (2023) 442–453 (`g = 1`, `f = 2p^α`); Balfaqih–Kamarulhaili
  2019/2020 (`(132, 4355, 4357)`; `g = 1`); Chen 2018 and Fu–Deng 2015 (`g = 2`,
  conditional on `n`); Yang–Fu 2017 (`(2^r + 1, 2^r)`). Not applicable.
* zbMATH Open API full-text search for "Jeśmanowicz" (about 110 records, up to 2026): no
  record mentions either triple. Web searches for the explicit equations
  `(33n)^x + (56n)^y = (65n)^z` and `(57n)^x + (176n)^y = (185n)^z` (also in Chinese):
  no hit.

Caveats (plainly):
* Only abstracts, zbMATH summaries, survey texts and the open-access Fan–Luo paper were
  read; most primary papers were not read in full, so a general theorem covering these
  triples under a formulation I did not recognize cannot be excluded.
* Many single-triple results of this kind appeared in Chinese university journals and
  master's theses that are not (or poorly) indexed by zbMATH or web search (the survey
  cites several such for other triples); CNKI was not searched. A paper on `(33,56,65)` or
  `(57,176,185)` there, in particular after 2018, would not have been found.
* Not accessed: N.-J. Deng, "On the Diophantine equation `(an)^x + (bn)^y = (cn)^z`",
  JP J. Algebra Number Theory Appl. 65 (2026) 361–375 (no abstract found); the Semantic
  Scholar page for Balfaqih–Kamarulhaili 2020 (the zbMATH summary was read instead).
* Honest confidence: "probably not previously written up; mathematically routine".

## What is NOT proved

* Jeśmanowicz' conjecture itself (OPEN).
* Any infinite family; any other triple.
-/
import RomeroConjecture.Jesmanowicz
import RomeroConjecture.JesmanowiczAllN
import RomeroConjecture.JesmanowiczFamilies
import RomeroConjecture.JesmanowiczDemjanenko

namespace Jesmanowicz

/-! ## The triple `(33, 56, 65)` -/

/-! ### Residue tables -/

theorem t33_two_pow_mod_three (z : ℕ) :
    (z % 2 = 0 → 2 ^ z % 3 = 1) ∧ (z % 2 = 1 → 2 ^ z % 3 = 2) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_two_pow_mod_seven (z : ℕ) : 2 ^ z % 7 = 1 ∨ 2 ^ z % 7 = 2 ∨ 2 ^ z % 7 = 4 := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_ten_pow_mod_eleven (z : ℕ) :
    (z % 2 = 0 → 10 ^ z % 11 = 1) ∧ (z % 2 = 1 → 10 ^ z % 11 = 10) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_three_pow_mod_eleven (x : ℕ) :
    3 ^ x % 11 = 1 ∨ 3 ^ x % 11 = 3 ∨ 3 ^ x % 11 = 9 ∨ 3 ^ x % 11 = 5 ∨ 3 ^ x % 11 = 4 := by
  induction x with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_seven_pow_mod_eleven (y : ℕ) :
    (y % 10 = 0 → 7 ^ y % 11 = 1) ∧ (y % 10 = 1 → 7 ^ y % 11 = 7) ∧
    (y % 10 = 2 → 7 ^ y % 11 = 5) ∧ (y % 10 = 3 → 7 ^ y % 11 = 2) ∧
    (y % 10 = 4 → 7 ^ y % 11 = 3) ∧ (y % 10 = 5 → 7 ^ y % 11 = 10) ∧
    (y % 10 = 6 → 7 ^ y % 11 = 4) ∧ (y % 10 = 7 → 7 ^ y % 11 = 6) ∧
    (y % 10 = 8 → 7 ^ y % 11 = 9) ∧ (y % 10 = 9 → 7 ^ y % 11 = 8) := by
  induction y with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_three_pow_mod_sixteen (x : ℕ) :
    (x % 4 = 0 → 3 ^ x % 16 = 1) ∧ (x % 4 = 1 → 3 ^ x % 16 = 3) ∧
    (x % 4 = 2 → 3 ^ x % 16 = 9) ∧ (x % 4 = 3 → 3 ^ x % 16 = 11) := by
  induction x with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_eleven_pow_mod_sixteen (x : ℕ) :
    (x % 4 = 0 → 11 ^ x % 16 = 1) ∧ (x % 4 = 1 → 11 ^ x % 16 = 11) ∧
    (x % 4 = 2 → 11 ^ x % 16 = 9) ∧ (x % 4 = 3 → 11 ^ x % 16 = 3) := by
  induction x with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_seven_pow_mod_thirteen (x : ℕ) :
    (x % 12 = 0 → 7 ^ x % 13 = 1) ∧ (x % 12 = 1 → 7 ^ x % 13 = 7) ∧
    (x % 12 = 2 → 7 ^ x % 13 = 10) ∧ (x % 12 = 3 → 7 ^ x % 13 = 5) ∧
    (x % 12 = 4 → 7 ^ x % 13 = 9) ∧ (x % 12 = 5 → 7 ^ x % 13 = 11) ∧
    (x % 12 = 6 → 7 ^ x % 13 = 12) ∧ (x % 12 = 7 → 7 ^ x % 13 = 6) ∧
    (x % 12 = 8 → 7 ^ x % 13 = 3) ∧ (x % 12 = 9 → 7 ^ x % 13 = 8) ∧
    (x % 12 = 10 → 7 ^ x % 13 = 4) ∧ (x % 12 = 11 → 7 ^ x % 13 = 2) := by
  induction x with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t33_four_pow_mod_thirteen (y : ℕ) :
    (y % 6 = 0 → 4 ^ y % 13 = 1) ∧ (y % 6 = 1 → 4 ^ y % 13 = 4) ∧
    (y % 6 = 2 → 4 ^ y % 13 = 3) ∧ (y % 6 = 3 → 4 ^ y % 13 = 12) ∧
    (y % 6 = 4 → 4 ^ y % 13 = 9) ∧ (y % 6 = 5 → 4 ^ y % 13 = 10) := by
  induction y with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-! ### Size lemmas -/

theorem t33_two_mul_65_pow_lt (w : ℕ) : 2 * 65 ^ w < 11 ^ (2 * w + 1) := by
  induction w with
  | zero => norm_num
  | succ k ih =>
    have e1 : 65 ^ (k + 1) = 65 * 65 ^ k := by ring
    have e2 : 11 ^ (2 * (k + 1) + 1) = 121 * 11 ^ (2 * k + 1) := by ring
    omega

theorem t33_four_mul_65_pow_lt (Z : ℕ) : 4 * 65 ^ Z < 56 ^ (2 * Z + 1) := by
  induction Z with
  | zero => norm_num
  | succ k ih =>
    have e1 : 65 ^ (k + 1) = 65 * 65 ^ k := by ring
    have e2 : 56 ^ (2 * (k + 1) + 1) = 3136 * 56 ^ (2 * k + 1) := by ring
    omega

theorem t33_seven_pow_lt (k : ℕ) : 7 ^ (k + 3) < 3 * 2 ^ (3 * k + 7) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 7 ^ (k + 1 + 3) = 7 * 7 ^ (k + 3) := by ring
    have e2 : 2 ^ (3 * (k + 1) + 7) = 8 * 2 ^ (3 * k + 7) := by ring
    omega

/-! ### The primitive case `33^x + 56^y = 65^z` -/

theorem isPrimitivePythagorean_33_56_65 : IsPrimitivePythagorean 33 56 65 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by norm_num⟩

/-- The only positive integer solution of `33^x + 56^y = 65^z` is `x = y = z = 2`. -/
theorem jesmanowicz_33_56_65 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 33 ^ x + 56 ^ y = 65 ^ z) : x = 2 ∧ y = 2 ∧ z = 2 := by
  -- mod 5: `x ≡ 2 (mod 4)`
  have hx4 : x % 4 = 2 := by
    have h1 : 33 ^ x % 5 = 3 ^ x % 5 := by rw [Nat.pow_mod]
    have h2 : 56 ^ y % 5 = 1 := by rw [Nat.pow_mod]; norm_num
    have h3 : 65 ^ z % 5 = 0 := by
      obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
      rw [pow_succ]; omega
    have := three_pow_mod_five x
    omega
  -- mod 13: `y` even
  have hye : y % 2 = 0 := by
    have h1 : 33 ^ x % 13 = 7 ^ x % 13 := by rw [Nat.pow_mod]
    have h2 : 56 ^ y % 13 = 4 ^ y % 13 := by rw [Nat.pow_mod]
    have h3 : 65 ^ z % 13 = 0 := by
      obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
      rw [pow_succ]; omega
    have h7 := t33_seven_pow_mod_thirteen x
    have h4 := t33_four_pow_mod_thirteen y
    omega
  -- mod 3: `z` even
  have hze : z % 2 = 0 := by
    have h1 : 33 ^ x % 3 = 0 := by
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
      rw [pow_succ]; omega
    have h2 : 56 ^ y % 3 = 2 ^ y % 3 := by rw [Nat.pow_mod]
    have h3 : 65 ^ z % 3 = 2 ^ z % 3 := by rw [Nat.pow_mod]
    have h4 := t33_two_pow_mod_three y
    have h5 := t33_two_pow_mod_three z
    omega
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, y = 2 * v + 2 := ⟨(y - 2) / 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, X = 2 * j + 1 := ⟨X / 2, by omega⟩
  rw [pow_mul' 33, pow_mul' 65] at h
  have hA64 : 65 ^ Z % 64 = 1 := by rw [Nat.pow_mod]; norm_num
  have hB64 : 33 ^ (2 * j + 1) % 64 = 33 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have h56pos : 0 < 56 ^ (2 * v + 2) := by positivity
  have hBpos : 0 < 33 ^ (2 * j + 1) := by positivity
  have hBA : 33 ^ (2 * j + 1) < 65 ^ Z := by
    by_contra hle
    have : (65 ^ Z) ^ 2 ≤ (33 ^ (2 * j + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨A, hA⟩ : ∃ A, A = 65 ^ Z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 33 ^ (2 * j + 1) := ⟨_, rfl⟩
  rw [← hA, ← hB] at h hBA
  rw [← hA] at hA64
  rw [← hB] at hB64 hBpos
  obtain ⟨d, hd⟩ : ∃ d, A = B + 2 * d := ⟨(A - B) / 2, by omega⟩
  have hdpos : 0 < d := by omega
  have e56 : 56 ^ (2 * v + 2) = 4 * (2 ^ (6 * v + 4) * 7 ^ (2 * v + 2)) := by
    rw [show (56 : ℕ) = 2 ^ 3 * 7 by norm_num, mul_pow, ← pow_mul]; ring
  have hfac : d * (B + d) = 2 ^ (6 * v + 4) * 7 ^ (2 * v + 2) := by
    have e1 : (B + 2 * d) ^ 2 = B ^ 2 + 4 * (d * (B + d)) := by ring
    rw [hd] at h
    omega
  have hP : 2 ^ (6 * v + 4) ∣ d := by
    have hc : Nat.Coprime (2 ^ (6 * v + 4)) (B + d) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    exact hc.dvd_of_dvd_mul_right ⟨7 ^ (2 * v + 2), hfac⟩
  have hp7 : Nat.Prime 7 := by norm_num
  have hQ : 7 ^ (2 * v + 2) ∣ d ∨ 7 ^ (2 * v + 2) ∣ B + d :=
    prime_pow_dvd_or hp7 ⟨2 ^ (6 * v + 4), by rw [hfac]; ring⟩ (by
      rintro ⟨h1, h2⟩
      have h3 : 7 ∣ B := (Nat.dvd_add_left h1).1 h2
      rw [hB] at h3
      have := hp7.dvd_of_dvd_pow h3
      omega)
  have hc27 : Nat.Coprime (2 ^ (6 * v + 4)) (7 ^ (2 * v + 2)) :=
    Nat.Coprime.pow _ _ (by norm_num)
  rcases hQ with hQ | hQ
  · exfalso
    obtain ⟨-, h2⟩ := eq_of_mul_eq_of_dvd (P := 2 ^ (6 * v + 4) * 7 ^ (2 * v + 2)) (Q := 1)
      (d := d) (s := B + d) (by positivity) (by norm_num) (by rw [mul_one]; exact hfac)
      (hc27.mul_dvd_of_dvd_of_dvd hP hQ) (one_dvd _)
    clear * - h2 hdpos hBpos
    omega
  · obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd (by positivity) (by positivity) hfac hP hQ
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · norm_num at h1 h2
      have hB33 : 33 ^ (2 * j + 1) = 33 ^ 1 := by
        clear * - h1 h2 hB
        omega
      have hA65 : 65 ^ Z = 65 ^ 1 := by
        clear * - h1 h2 hd hA
        omega
      have hj : 2 * j + 1 = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 33) hB33
      have hZ1 : Z = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 65) hA65
      clear * - hj hZ1
      omega
    · exfalso
      obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
      have e : 2 ^ (6 * (v' + 1) + 4) = 32 * 2 ^ (6 * v' + 5) := by ring
      clear * - e h1 hd hA64 hB64
      omega

/-- Jeśmanowicz' conjecture holds for the triple `(33, 56, 65)` with `n = 1`. -/
theorem jesmanowiczFor_33_56_65_one : JesmanowiczFor 33 56 65 1 := by
  intro x y z hs
  obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
  exact jesmanowicz_33_56_65 hx hy hz h

/-! ### Three key lemmas for `n > 1` -/

/-- If `11^x ∣ (65^w)² - B²` with `11 ∤ B` and `B < 65^w`, then `x ≤ 2w` (the power of `11`
divides one of the two factors `65^w ∓ B`, which are smaller than `2·65^w < 11^(2w+1)`). -/
theorem t33_eleven_pow_dvd_sq_sub {x w B : ℕ} (hB : ¬ 11 ∣ B) (hBA : B < 65 ^ w)
    (h : 11 ^ x ∣ (65 ^ w) ^ 2 - B ^ 2) : x ≤ 2 * w := by
  have hlt := t33_two_mul_65_pow_lt w
  obtain ⟨A, hA⟩ : ∃ A, A = 65 ^ w := ⟨_, rfl⟩
  rw [← hA] at hBA h hlt
  obtain ⟨D, rfl⟩ : ∃ D, A = B + D := ⟨A - B, by omega⟩
  have e : (B + D) ^ 2 - B ^ 2 = D * (2 * B + D) := by
    have : (B + D) ^ 2 = B ^ 2 + D * (2 * B + D) := by ring
    omega
  rw [e] at h
  have hle : 11 ^ x ≤ 2 * B + D := by
    rcases prime_pow_dvd_or (by norm_num : Nat.Prime 11) h (by rintro ⟨h1, h2⟩; omega)
      with h1 | h1
    · exact (Nat.le_of_dvd (by omega) h1).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h1
  have h5 : 11 ^ x < 11 ^ (2 * w + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5
  omega

/-- Lifting the exponent at `2`: if `2^k ∣ 65^z - 1` with `z > 0`, then `k < z + 6`. -/
theorem t33_two_pow_dvd_pow_sub_one {k z : ℕ} (hz : 0 < z) (h : 2 ^ k ∣ 65 ^ z - 1) :
    k < z + 6 := by
  rcases Nat.mod_two_eq_zero_or_one z with hze | hzo
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hlte := Nat.multiplicity_pow_two_sub_pow (x := 65) (y := 1) (by norm_num)
      (by norm_num) (by norm_num) (n := z) (by omega) (Nat.even_iff.2 hze)
    rw [one_pow] at hlte
    have hlt : 1 < 65 ^ z := Nat.one_lt_pow (by omega) (by norm_num)
    have hne : 65 ^ z - 1 ≠ 0 := by omega
    have hk := (multiplicity_dvd_iff_le hne).1 h
    have h1 : multiplicity 2 (65 + 1) ≤ 1 :=
      multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
    have h2 : multiplicity 2 (65 - 1) ≤ 6 :=
      multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
    have hz' := multiplicity_lt_self (p := 2) (n := z) hz
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, z = 2 * j + 1 := ⟨z / 2, by omega⟩
    have h65 : 65 ^ (2 * j + 1) % 128 = 65 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    by_contra hlt
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 7 := ⟨k - 7, by omega⟩
    have h128 : 128 ∣ 65 ^ (2 * j + 1) - 1 := (Dvd.intro (2 ^ k') (by ring)).trans h
    obtain ⟨M, hM⟩ : ∃ M, M = 65 ^ (2 * j + 1) := ⟨_, rfl⟩
    rw [← hM] at h65 h128
    clear * - h65 h128
    omega

/-- The core of the case `x < z < y`: `B² + 56^y p^E = (65^Z)²` is impossible when `y > 2Z`,
`p ∉ {2, 7}` is a prime not dividing `B`, `E ≥ 1`, `B ≡ 1 (mod 4)` and `B ≡ 1, 2, 4 (mod 7)`. -/
theorem t33_sq_add_ne {p E y Z B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hpB : ¬ p ∣ B) (hB4 : B % 4 = 1) (hB7 : B % 7 = 1 ∨ B % 7 = 2 ∨ B % 7 = 4)
    (hE : 0 < E) (hy : 2 * Z < y) (h : B ^ 2 + 56 ^ y * p ^ E = (65 ^ Z) ^ 2) : False := by
  have hA4 : 65 ^ Z % 4 = 1 := by rw [Nat.pow_mod]; norm_num
  have hpE : 0 < p ^ E := pow_pos hp.pos E
  have h56 : 0 < 56 ^ y := by positivity
  have hBA : B < 65 ^ Z := by
    by_contra hle
    have h1 : (65 ^ Z) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 0 < 56 ^ y * p ^ E := Nat.mul_pos h56 hpE
    omega
  have hZ : 0 < Z := by
    rcases Nat.eq_zero_or_pos Z with rfl | hZ
    · simp at hBA; omega
    · exact hZ
  have hsize := t33_four_mul_65_pow_lt Z
  have hmono : 56 ^ (2 * Z + 1) ≤ 56 ^ y := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 3 := ⟨y - 3, by omega⟩
  have hk7 := t33_seven_pow_lt k
  obtain ⟨A, hA⟩ : ∃ A, A = 65 ^ Z := ⟨_, rfl⟩
  rw [← hA] at h hA4 hBA hsize
  obtain ⟨d, rfl⟩ : ∃ d, A = B + 2 * d := ⟨(A - B) / 2, by omega⟩
  have hd : 0 < d := by omega
  have e56 : 56 ^ (k + 3) = 4 * (2 ^ (3 * k + 7) * 7 ^ (k + 3)) := by
    rw [show (56 : ℕ) = 2 ^ 3 * 7 by norm_num, mul_pow, ← pow_mul]; ring
  have hfac : d * (B + d) = 2 ^ (3 * k + 7) * 7 ^ (k + 3) * p ^ E := by
    have e1 : (B + 2 * d) ^ 2 = B ^ 2 + 4 * (d * (B + d)) := by ring
    have e2 : 56 ^ (k + 3) * p ^ E = 4 * (2 ^ (3 * k + 7) * 7 ^ (k + 3) * p ^ E) := by
      rw [e56]; ring
    omega
  have hP : 2 ^ (3 * k + 7) ∣ d := by
    have hc : Nat.Coprime (2 ^ (3 * k + 7)) (B + d) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    exact hc.dvd_of_dvd_mul_right ⟨7 ^ (k + 3) * p ^ E, by rw [hfac]; ring⟩
  have hp7' : Nat.Prime 7 := by norm_num
  have hQ : 7 ^ (k + 3) ∣ d ∨ 7 ^ (k + 3) ∣ B + d :=
    prime_pow_dvd_or hp7' ⟨2 ^ (3 * k + 7) * p ^ E, by rw [hfac]; ring⟩
      (by rintro ⟨h1, h2⟩; omega)
  have hR : p ^ E ∣ d ∨ p ^ E ∣ B + d :=
    prime_pow_dvd_or hp ⟨2 ^ (3 * k + 7) * 7 ^ (k + 3), by rw [hfac]; ring⟩
      (by rintro ⟨h1, h2⟩; exact hpB ((Nat.dvd_add_left h1).1 h2))
  have hc27 : Nat.Coprime (2 ^ (3 * k + 7)) (7 ^ (k + 3)) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have hc2p : Nat.Coprime (2 ^ (3 * k + 7)) (p ^ E) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hc7p : Nat.Coprime (7 ^ (k + 3)) (p ^ E) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp7' hp).2 (Ne.symm hp7))
  have hPpos : 0 < 2 ^ (3 * k + 7) := by positivity
  have hQpos : 0 < 7 ^ (k + 3) := by positivity
  rcases hQ with hQ | hQ
  · -- `2^(3y-2) 7^y ∣ d`: too big
    have h1 := Nat.le_of_dvd hd (hc27.mul_dvd_of_dvd_of_dvd hP hQ)
    omega
  · rcases hR with hR | hR
    · -- `d = 2^(3y-2) p^E`, `B + d = 7^y`: impossible by size
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd (P := 2 ^ (3 * k + 7) * p ^ E) (Q := 7 ^ (k + 3))
        (Nat.mul_pos hPpos hpE) hQpos (by rw [hfac]; ring)
        (hc2p.mul_dvd_of_dvd_of_dvd hP hR) hQ
      have h3 : 3 ≤ p ^ E := by
        have h4 : p ≤ p ^ E := Nat.le_self_pow (by omega) _
        have h5 := hp.two_le
        omega
      have h4 : 2 ^ (3 * k + 7) * 3 ≤ 2 ^ (3 * k + 7) * p ^ E := Nat.mul_le_mul_left _ h3
      omega
    · -- `d = 2^(3y-2)`, `B + d = 7^y p^E`: impossible mod 7
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd (P := 2 ^ (3 * k + 7)) (Q := 7 ^ (k + 3) * p ^ E)
        hPpos (Nat.mul_pos hQpos hpE) (by rw [hfac]; ring) hP
        (hc7p.mul_dvd_of_dvd_of_dvd hQ hR)
      have e7 : 7 ^ (k + 3) * p ^ E = 7 * (7 ^ (k + 2) * p ^ E) := by ring
      have e2 : 2 ^ (3 * k + 7) % 7 = 2 := by
        rw [show 3 * k + 7 = 3 * (k + 2) + 1 by ring, pow_succ, pow_mul, Nat.mul_mod,
          Nat.pow_mod]
        norm_num
      omega

/-! ### The two impossible configurations for `n > 1` -/

/-- Case `y < z < x` for `(33, 56, 65)` (after cancelling `n^y`); `z = y + b`, `x = z + a`. -/
theorem no_solution_33_56_65_y_lt_z_lt_x {n y a b : ℕ} (hn : 1 < n) (hy : 0 < y) (ha : 0 < a)
    (hb : 0 < b)
    (h : 33 ^ (y + b + a) * n ^ (b + a) + 56 ^ y = 65 ^ (y + b) * n ^ b) : False := by
  obtain ⟨t, ht⟩ : ∃ t, y + b + a = t + 1 := ⟨y + b + a - 1, by omega⟩
  have h33x : 33 ^ (y + b + a) = 33 * 33 ^ t := by rw [ht]; ring
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hnb : n ^ b ∣ 56 ^ y := by
    have h1 : n ^ b ∣ 33 ^ (y + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 33 ^ (y + b + a) * n ^ (b + a) + 56 ^ y := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_right h1).1 h2
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ b := by positivity
  have h' : 33 ^ (y + b + a) * n ^ a + q = 65 ^ (y + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (65 ^ (y + b)), ← h]; ring
  have hnpow : 1 < n ^ b := Nat.one_lt_pow (by omega) hn
  have hna : ∀ p, p ∣ n → p ∣ 33 ^ (y + b + a) * n ^ a := fun p hp =>
    Dvd.dvd.mul_left (hp.trans (dvd_pow_self n (by omega))) _
  have h2qn : 2 ∣ q → ¬ 2 ∣ n := fun h2q h2n => by
    have h1 : 2 ∣ 65 ^ (y + b) := by rw [← h']; exact dvd_add (hna 2 h2n) h2q
    have := Nat.prime_two.dvd_of_dvd_pow h1; omega
  have h7qn : 7 ∣ q → ¬ 7 ∣ n := fun h7q h7n => by
    have h1 : 7 ∣ 65 ^ (y + b) := by rw [← h']; exact dvd_add (hna 7 h7n) h7q
    have := hp7.dvd_of_dvd_pow h1; omega
  have e56 : 56 ^ y = 2 ^ (3 * y) * 7 ^ y := by
    rw [show (56 : ℕ) = 2 ^ 3 * 7 by norm_num, mul_pow, ← pow_mul]
  have e33 : 33 ^ (y + b + a) = 11 ^ (y + b + a) * 3 ^ (y + b + a) := by
    rw [← mul_pow]; norm_num
  have hmod3 : q % 3 = 2 ^ (y + b) % 3 := by
    have h1 : 65 ^ (y + b) % 3 = 2 ^ (y + b) % 3 := by rw [Nat.pow_mod]
    rw [← h1, ← h', h33x, mul_assoc]
    omega
  have hmod11 : q % 11 = 10 ^ (y + b) % 11 := by
    have h1 : 65 ^ (y + b) % 11 = 10 ^ (y + b) % 11 := by rw [Nat.pow_mod]
    rw [← h1, ← h', h33x, mul_assoc]
    omega
  have h23 := t33_two_pow_mod_three (y + b)
  have hprodpos : 0 < 33 ^ (y + b + a) * n ^ a := by positivity
  -- conclusion once `z = y + b` is even and `q` is a square
  have hfin : ∀ w B, y + b = 2 * w → q = B ^ 2 → ¬ 11 ∣ B → False := by
    intro w B hw hB hB11
    have hd : 11 ^ (y + b + a) ∣ (65 ^ w) ^ 2 - B ^ 2 :=
      ⟨3 ^ (y + b + a) * n ^ a, by rw [← pow_mul', ← hw, ← hB, ← mul_assoc, ← e33]; omega⟩
    have hBA : B < 65 ^ w := by
      by_contra hle
      have h1 : (65 ^ w) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [← pow_mul', ← hw, ← hB] at h1
      omega
    have := t33_eleven_pow_dvd_sq_sub hB11 hBA hd
    omega
  have hq56 : q ∣ 2 ^ (3 * y) * 7 ^ y := by rw [← e56, hq]; exact Dvd.intro_left _ rfl
  have hn56 : n ^ b ∣ 2 ^ (3 * y) * 7 ^ y := by rw [← e56, hq]; exact Dvd.intro _ rfl
  have cop2 : ∀ m : ℕ, ¬ 2 ∣ m → ∀ i, Nat.Coprime (2 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
  have cop7 : ∀ m : ℕ, ¬ 7 ∣ m → ∀ i, Nat.Coprime (7 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp7).2 hm)
  have hn2 : ¬ 2 ∣ n → ¬ 2 ∣ n ^ b := fun h1 h2 => h1 (Nat.prime_two.dvd_of_dvd_pow h2)
  have hn7 : ¬ 7 ∣ n → ¬ 7 ∣ n ^ b := fun h1 h2 => h1 (hp7.dvd_of_dvd_pow h2)
  have h11pow : ∀ c m : ℕ, c < 11 → 0 < c → ¬ 11 ∣ c ^ m := fun c m hc hc0 hd => by
    have := hp11.dvd_of_dvd_pow hd
    have := Nat.le_of_dvd hc0 this
    omega
  by_cases h2q : 2 ∣ q <;> by_cases h7q : 7 ∣ q
  · -- `n` coprime to `56`: `n = 1`
    have hc : Nat.Coprime (2 ^ (3 * y) * 7 ^ y) (n ^ b) :=
      Nat.Coprime.mul_left (cop2 _ (hn2 (h2qn h2q)) _) (cop7 _ (hn7 (h7qn h7q)) _)
    have h1 := Nat.Coprime.eq_one_of_dvd hc.symm hn56
    omega
  · -- `q = 8^y`, `n^b = 7^y`
    have h8q : 2 ^ (3 * y) ∣ q :=
      (cop2 _ (hn2 (h2qn h2q)) (3 * y)).dvd_of_dvd_mul_left
        (by rw [← hq, e56]; exact Dvd.intro _ rfl)
    have hq8 : q ∣ 2 ^ (3 * y) := (cop7 _ h7q y).symm.dvd_of_dvd_mul_right hq56
    have hqe : q = 2 ^ (3 * y) := Nat.dvd_antisymm hq8 h8q
    have hnb7 : n ^ b = 7 ^ y := by
      have h2pos : 0 < 2 ^ (3 * y) := by positivity
      apply Nat.eq_of_mul_eq_mul_right h2pos
      rw [mul_comm (7 ^ y), ← e56, hq, hqe]
    have hn7' : n ∣ 7 ^ y := by rw [← hnb7]; exact dvd_pow_self n (by omega)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp7).1 hn7'
    have hkb : k * b = y := by
      rw [← pow_mul] at hnb7
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 7) hnb7
    have h23y := t33_two_pow_mod_three (3 * y)
    rw [hqe] at hmod3
    have hbe : b % 2 = 0 := by
      clear * - hmod3 h23 h23y
      omega
    obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
    have hu : y = 2 * (k * b') := by rw [← hkb]; ring
    refine hfin (k * b' + b') (2 ^ (3 * (k * b'))) (by omega) ?_ (h11pow 2 _ (by norm_num)
      (by norm_num))
    rw [hqe, hu, ← pow_mul]; ring
  · -- `q = 7^y`
    have h7q' : 7 ^ y ∣ q :=
      (cop7 _ (hn7 (h7qn h7q)) y).dvd_of_dvd_mul_left
        (by rw [← hq, e56]; exact Dvd.intro_left _ rfl)
    have hq7 : q ∣ 7 ^ y := (cop2 _ h2q (3 * y)).symm.dvd_of_dvd_mul_left hq56
    have hqe : q = 7 ^ y := Nat.dvd_antisymm hq7 h7q'
    rw [hqe] at hmod3 hmod11
    have h73 : 7 ^ y % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have h10 := t33_ten_pow_mod_eleven (y + b)
    have h7 := t33_seven_pow_mod_eleven y
    have hye : y % 10 = 0 ∧ (y + b) % 2 = 0 := by
      clear * - hmod3 hmod11 h73 h10 h7 h23
      omega
    obtain ⟨u, rfl⟩ : ∃ u, y = 2 * u := ⟨y / 2, by omega⟩
    exact hfin ((2 * u + b) / 2) (7 ^ u) (by omega) (by rw [hqe, pow_mul'])
      (h11pow 7 _ (by norm_num) (by norm_num))
  · -- `q = 1`
    have hc : Nat.Coprime (2 ^ (3 * y) * 7 ^ y) q :=
      Nat.Coprime.mul_left (cop2 _ h2q _) (cop7 _ h7q _)
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd hc.symm hq56
    rw [hq1] at hmod3
    have hze : (y + b) % 2 = 0 := by
      clear * - hmod3 h23
      omega
    exact hfin ((y + b) / 2) 1 (by omega) (by rw [hq1]; norm_num) (by norm_num)

/-- Case `x < z < y` for `(33, 56, 65)` (after cancelling `n^x`); `z = x + b`, `y = z + a`. -/
theorem no_solution_33_56_65_x_lt_z_lt_y {n x a b : ℕ} (hn : 1 < n) (hx : 0 < x) (ha : 0 < a)
    (hb : 0 < b)
    (h : 33 ^ x + 56 ^ (x + b + a) * n ^ (b + a) = 65 ^ (x + b) * n ^ b) : False := by
  obtain ⟨t, ht⟩ : ∃ t, x + b + a = t + 2 := ⟨x + b + a - 2, by omega⟩
  have h56y : 56 ^ (x + b + a) = 16 * (196 * 56 ^ t) := by rw [ht]; ring
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hnb : n ^ b ∣ 33 ^ x := by
    have h1 : n ^ b ∣ 56 ^ (x + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 33 ^ x + 56 ^ (x + b + a) * n ^ (b + a) := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_left h1).1 h2
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ b := by positivity
  have h' : q + 56 ^ (x + b + a) * n ^ a = 65 ^ (x + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (65 ^ (x + b)), ← h]; ring
  have hnpow : 1 < n ^ b := Nat.one_lt_pow (by omega) hn
  have hna : ∀ p, p ∣ n → p ∣ 56 ^ (x + b + a) * n ^ a := fun p hp =>
    Dvd.dvd.mul_left (hp.trans (dvd_pow_self n (by omega))) _
  have h3qn : 3 ∣ q → ¬ 3 ∣ n := fun h3q h3n => by
    have h1 : 3 ∣ 65 ^ (x + b) := by rw [← h']; exact dvd_add h3q (hna 3 h3n)
    have := hp3.dvd_of_dvd_pow h1; omega
  have h11qn : 11 ∣ q → ¬ 11 ∣ n := fun h11q h11n => by
    have h1 : 11 ∣ 65 ^ (x + b) := by rw [← h']; exact dvd_add h11q (hna 11 h11n)
    have := hp11.dvd_of_dvd_pow h1; omega
  have e33 : 33 ^ x = 3 ^ x * 11 ^ x := by rw [← mul_pow]; norm_num
  have hmod16 : q % 16 = 1 := by
    have h1 : 65 ^ (x + b) % 16 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [← h', h56y, mul_assoc] at h1
    omega
  have hq33 : q ∣ 3 ^ x * 11 ^ x := by rw [← e33, hq]; exact Dvd.intro_left _ rfl
  have hn33 : n ^ b ∣ 3 ^ x * 11 ^ x := by rw [← e33, hq]; exact Dvd.intro _ rfl
  have cop3 : ∀ m : ℕ, ¬ 3 ∣ m → ∀ i, Nat.Coprime (3 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp3).2 hm)
  have cop11 : ∀ m : ℕ, ¬ 11 ∣ m → ∀ i, Nat.Coprime (11 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp11).2 hm)
  have hn3 : ¬ 3 ∣ n → ¬ 3 ∣ n ^ b := fun h1 h2 => h1 (hp3.dvd_of_dvd_pow h2)
  have hn11 : ¬ 11 ∣ n → ¬ 11 ∣ n ^ b := fun h1 h2 => h1 (hp11.dvd_of_dvd_pow h2)
  by_cases h3q : 3 ∣ q <;> by_cases h11q : 11 ∣ q
  · -- `n` coprime to `33`: `n = 1`
    have hc : Nat.Coprime (3 ^ x * 11 ^ x) (n ^ b) :=
      Nat.Coprime.mul_left (cop3 _ (hn3 (h3qn h3q)) _) (cop11 _ (hn11 (h11qn h11q)) _)
    have h1 := Nat.Coprime.eq_one_of_dvd hc.symm hn33
    omega
  · -- `q = 3^x`, `n^b = 11^x`, `n = 11^k`
    have h3q' : 3 ^ x ∣ q :=
      (cop3 _ (hn3 (h3qn h3q)) x).dvd_of_dvd_mul_left
        (by rw [← hq, e33]; exact Dvd.intro _ rfl)
    have hq3 : q ∣ 3 ^ x := (cop11 _ h11q x).symm.dvd_of_dvd_mul_right hq33
    have hqe : q = 3 ^ x := Nat.dvd_antisymm hq3 h3q'
    have hnb11 : n ^ b = 11 ^ x := by
      have h3pos : 0 < 3 ^ x := by positivity
      apply Nat.eq_of_mul_eq_mul_right h3pos
      rw [mul_comm (11 ^ x), ← e33, hq, hqe]
    have hn11' : n ∣ 11 ^ x := by rw [← hnb11]; exact dvd_pow_self n (by omega)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp11).1 hn11'
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hn
      · exact hk
    rw [hqe] at hmod16 h'
    have h316 := t33_three_pow_mod_sixteen x
    have hx4 : x % 4 = 0 := by
      clear * - h316 hmod16
      omega
    -- mod 11: `z` even
    have hze : (x + b) % 2 = 0 := by
      have h1 : 65 ^ (x + b) % 11 = 10 ^ (x + b) % 11 := by rw [Nat.pow_mod]
      have h2 := t33_ten_pow_mod_eleven (x + b)
      have h3 := t33_three_pow_mod_eleven x
      have h4 : 11 ∣ 56 ^ (x + b + a) * (11 ^ k) ^ a :=
        Dvd.dvd.mul_left ((dvd_pow_self 11 (by omega)).trans (dvd_pow_self _ (by omega))) _
      clear * - h1 h2 h3 h4 h'
      omega
    obtain ⟨X, rfl⟩ : ∃ X, x = 4 * X := ⟨x / 4, by omega⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, 4 * X + b = 2 * Z := ⟨(4 * X + b) / 2, by omega⟩
    refine t33_sq_add_ne (p := 11) (E := k * a) (y := 4 * X + b + a) (Z := Z) (B := 9 ^ X)
      hp11 (by norm_num) (by norm_num) ?_ ?_ ?_ (Nat.mul_pos hk ha) (by omega) ?_
    · intro hd
      have := hp11.dvd_of_dvd_pow hd
      omega
    · rw [Nat.pow_mod]; norm_num
    · have h1 : 9 ^ X % 7 = 2 ^ X % 7 := by rw [Nat.pow_mod]
      rw [h1]; exact t33_two_pow_mod_seven X
    · have e9 : (9 ^ X) ^ 2 = 3 ^ (4 * X) := by
        rw [← pow_mul, show 4 * X = 2 * (X * 2) by ring, pow_mul 3 2]; norm_num
      rw [← pow_mul' 65, ← hZ, ← h', e9, pow_mul 11 k a]
  · -- `q = 11^x`, `n^b = 3^x`, `n = 3^k`
    have h11q' : 11 ^ x ∣ q :=
      (cop11 _ (hn11 (h11qn h11q)) x).dvd_of_dvd_mul_left
        (by rw [← hq, e33]; exact Dvd.intro_left _ rfl)
    have hq11 : q ∣ 11 ^ x := (cop3 _ h3q x).symm.dvd_of_dvd_mul_left hq33
    have hqe : q = 11 ^ x := Nat.dvd_antisymm hq11 h11q'
    have hnb3 : n ^ b = 3 ^ x := by
      have h11pos : 0 < 11 ^ x := by positivity
      apply Nat.eq_of_mul_eq_mul_right h11pos
      rw [← e33, hq, hqe]
    have hn3' : n ∣ 3 ^ x := by rw [← hnb3]; exact dvd_pow_self n (by omega)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp3).1 hn3'
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hn
      · exact hk
    rw [hqe] at hmod16 h'
    have h1116 := t33_eleven_pow_mod_sixteen x
    have hx4 : x % 4 = 0 := by
      clear * - h1116 hmod16
      omega
    -- mod 3: `z ≡ x (mod 2)`
    have hze : (x + b) % 2 = 0 := by
      have h1 : 65 ^ (x + b) % 3 = 2 ^ (x + b) % 3 := by rw [Nat.pow_mod]
      have h1' : 11 ^ x % 3 = 2 ^ x % 3 := by rw [Nat.pow_mod]
      have h2 := t33_two_pow_mod_three (x + b)
      have h3 := t33_two_pow_mod_three x
      have h4 : 3 ∣ 56 ^ (x + b + a) * (3 ^ k) ^ a :=
        Dvd.dvd.mul_left ((dvd_pow_self 3 (by omega)).trans (dvd_pow_self _ (by omega))) _
      clear * - h1 h1' h2 h3 h4 h' hx4
      omega
    obtain ⟨X, rfl⟩ : ∃ X, x = 4 * X := ⟨x / 4, by omega⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, 4 * X + b = 2 * Z := ⟨(4 * X + b) / 2, by omega⟩
    refine t33_sq_add_ne (p := 3) (E := k * a) (y := 4 * X + b + a) (Z := Z) (B := 121 ^ X)
      hp3 (by norm_num) (by norm_num) ?_ ?_ ?_ (Nat.mul_pos hk ha) (by omega) ?_
    · intro hd
      have := hp3.dvd_of_dvd_pow hd
      omega
    · rw [Nat.pow_mod]; norm_num
    · have h1 : 121 ^ X % 7 = 2 ^ X % 7 := by rw [Nat.pow_mod]
      rw [h1]; exact t33_two_pow_mod_seven X
    · have e121 : (121 ^ X) ^ 2 = 11 ^ (4 * X) := by
        rw [← pow_mul, show 4 * X = 2 * (X * 2) by ring, pow_mul 11 2]; norm_num
      rw [← pow_mul' 65, ← hZ, ← h', e121, pow_mul 3 k a]
  · -- `q = 1`: lifting the exponent at 2
    have hc : Nat.Coprime (3 ^ x * 11 ^ x) q :=
      Nat.Coprime.mul_left (cop3 _ h3q _) (cop11 _ h11q _)
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd hc.symm hq33
    rw [hq1] at h'
    have e : 2 ^ (3 * (x + b + a)) * (7 ^ (x + b + a) * n ^ a)
        = 56 ^ (x + b + a) * n ^ a := by
      rw [← mul_assoc, pow_mul, ← mul_pow]; norm_num
    have hd : 2 ^ (3 * (x + b + a)) ∣ 65 ^ (x + b) - 1 :=
      ⟨7 ^ (x + b + a) * n ^ a, by rw [e]; clear * - h'; omega⟩
    have := t33_two_pow_dvd_pow_sub_one (z := x + b) (by omega) hd
    clear * - this ha hb hx
    omega

/-! ### The main theorem -/

/-- **Jeśmanowicz' conjecture for the triple `(33, 56, 65)` and every `n ≥ 1`**: the only
positive solution of `(33 n)^x + (56 n)^y = (65 n)^z` is `x = y = z = 2`. -/
theorem jesmanowiczFor_33_56_65 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 33 56 65 n := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  swap
  · obtain rfl : n = 1 := by omega
    exact jesmanowiczFor_33_56_65_one
  intro x y z hs
  rcases hs.strict_cases_of_one_lt isPrimitivePythagorean_33_56_65 hn1 with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · -- `x < z < y`
    exfalso
    obtain ⟨hx, hy, hz, heq⟩ := hs
    obtain ⟨b, rfl⟩ : ∃ b, z = x + b := ⟨z - x, by omega⟩
    obtain ⟨a, rfl⟩ : ∃ a, y = x + b + a := ⟨y - (x + b), by omega⟩
    refine no_solution_33_56_65_x_lt_z_lt_y (n := n) (x := x) (a := a) (b := b) hn1 hx
      (by omega) (by omega) ?_
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ x by positivity)
    calc n ^ x * (33 ^ x + 56 ^ (x + b + a) * n ^ (b + a))
        = (33 * n) ^ x + (56 * n) ^ (x + b + a) := by ring
      _ = (65 * n) ^ (x + b) := heq
      _ = n ^ x * (65 ^ (x + b) * n ^ b) := by ring
  · -- `y < z < x`
    exfalso
    obtain ⟨hx, hy, hz, heq⟩ := hs
    obtain ⟨b, rfl⟩ : ∃ b, z = y + b := ⟨z - y, by omega⟩
    obtain ⟨a, rfl⟩ : ∃ a, x = y + b + a := ⟨x - (y + b), by omega⟩
    refine no_solution_33_56_65_y_lt_z_lt_x (n := n) (y := y) (a := a) (b := b) hn1 hy
      (by omega) (by omega) ?_
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ y by positivity)
    calc n ^ y * (33 ^ (y + b + a) * n ^ (b + a) + 56 ^ y)
        = (33 * n) ^ (y + b + a) + (56 * n) ^ y := by ring
      _ = (65 * n) ^ (y + b) := heq
      _ = n ^ y * (65 ^ (y + b) * n ^ b) := by ring

/-- The same for the swapped triple `(56, 33, 65)`. -/
theorem jesmanowiczFor_56_33_65 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 56 33 65 n :=
  jesmanowiczFor_swap.1 (jesmanowiczFor_33_56_65 n hn)

/-! ## The triple `(57, 176, 185)` -/

/-! ### Residue tables -/

theorem t57_nine_pow_mod_sixteen (z : ℕ) :
    (z % 2 = 0 → 9 ^ z % 16 = 1) ∧ (z % 2 = 1 → 9 ^ z % 16 = 9) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t57_nine_pow_mod_eleven (u : ℕ) :
    9 ^ u % 11 = 1 ∨ 9 ^ u % 11 = 9 ∨ 9 ^ u % 11 = 4 ∨ 9 ^ u % 11 = 3 ∨ 9 ^ u % 11 = 5 := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t57_nine_pow_mod_nineteen (u : ℕ) :
    9 ^ u % 19 = 1 ∨ 9 ^ u % 19 = 9 ∨ 9 ^ u % 19 = 5 ∨ 9 ^ u % 19 = 7 ∨ 9 ^ u % 19 = 6 ∨
    9 ^ u % 19 = 16 ∨ 9 ^ u % 19 = 11 ∨ 9 ^ u % 19 = 4 ∨ 9 ^ u % 19 = 17 := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t57_eleven_pow_mod_nineteen (y : ℕ) :
    11 ^ y % 19 = 1 ∨ 11 ^ y % 19 = 11 ∨ 11 ^ y % 19 = 7 := by
  induction y with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- `14` is a quadratic non-residue mod `19`: odd powers are non-residues, even powers
are residues. -/
theorem t57_fourteen_pow_mod_nineteen (z : ℕ) :
    (z % 2 = 0 → (14 ^ z % 19 = 1 ∨ 14 ^ z % 19 = 4 ∨ 14 ^ z % 19 = 5 ∨ 14 ^ z % 19 = 6 ∨
      14 ^ z % 19 = 7 ∨ 14 ^ z % 19 = 9 ∨ 14 ^ z % 19 = 11 ∨ 14 ^ z % 19 = 16 ∨
      14 ^ z % 19 = 17)) ∧
    (z % 2 = 1 → (14 ^ z % 19 = 2 ∨ 14 ^ z % 19 = 3 ∨ 14 ^ z % 19 = 8 ∨ 14 ^ z % 19 = 10 ∨
      14 ^ z % 19 = 12 ∨ 14 ^ z % 19 = 13 ∨ 14 ^ z % 19 = 14 ∨ 14 ^ z % 19 = 15 ∨
      14 ^ z % 19 = 18)) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem t57_two_pow_mod_eleven (k : ℕ) :
    2 ^ (4 * k + 10) % 11 = 1 ∨ 2 ^ (4 * k + 10) % 11 = 5 ∨ 2 ^ (4 * k + 10) % 11 = 3 ∨
    2 ^ (4 * k + 10) % 11 = 4 ∨ 2 ^ (4 * k + 10) % 11 = 9 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e : 2 ^ (4 * (k + 1) + 10) = 16 * 2 ^ (4 * k + 10) := by ring
    omega

/-! ### Size lemmas -/

theorem t57_two_mul_185_pow_lt (w : ℕ) : 2 * 185 ^ w < 19 ^ (2 * w + 1) := by
  induction w with
  | zero => norm_num
  | succ k ih =>
    have e1 : 185 ^ (k + 1) = 185 * 185 ^ k := by ring
    have e2 : 19 ^ (2 * (k + 1) + 1) = 361 * 19 ^ (2 * k + 1) := by ring
    omega

theorem t57_four_mul_185_pow_lt (Z : ℕ) : 4 * 185 ^ Z < 176 ^ (2 * Z + 1) := by
  induction Z with
  | zero => norm_num
  | succ k ih =>
    have e1 : 185 ^ (k + 1) = 185 * 185 ^ k := by ring
    have e2 : 176 ^ (2 * (k + 1) + 1) = 30976 * 176 ^ (2 * k + 1) := by ring
    omega

theorem t57_eleven_pow_lt (k : ℕ) : 11 ^ (k + 3) < 3 * 2 ^ (4 * k + 10) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 11 ^ (k + 1 + 3) = 11 * 11 ^ (k + 3) := by ring
    have e2 : 2 ^ (4 * (k + 1) + 10) = 16 * 2 ^ (4 * k + 10) := by ring
    omega

theorem t57_eleven_pow_lt' (v : ℕ) : 11 ^ (2 * (v + 1) + 2) < 2 ^ (8 * (v + 1) + 6) := by
  induction v with
  | zero => norm_num
  | succ k ih =>
    have e1 : 11 ^ (2 * (k + 1 + 1) + 2) = 121 * 11 ^ (2 * (k + 1) + 2) := by ring
    have e2 : 2 ^ (8 * (k + 1 + 1) + 6) = 256 * 2 ^ (8 * (k + 1) + 6) := by ring
    omega

/-! ### The primitive case `57^x + 176^y = 185^z` -/

theorem isPrimitivePythagorean_57_176_185 : IsPrimitivePythagorean 57 176 185 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by norm_num⟩

/-- The only positive integer solution of `57^x + 176^y = 185^z` is `x = y = z = 2`. -/
theorem jesmanowicz_57_176_185 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 57 ^ x + 176 ^ y = 185 ^ z) : x = 2 ∧ y = 2 ∧ z = 2 := by
  -- mod 5: `x ≡ 2 (mod 4)`
  have hx4 : x % 4 = 2 := by
    have h1 : 57 ^ x % 5 = 2 ^ x % 5 := by rw [Nat.pow_mod]
    have h2 : 176 ^ y % 5 = 1 := by rw [Nat.pow_mod]; norm_num
    have h3 : 185 ^ z % 5 = 0 := by
      obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
      rw [pow_succ]; omega
    have := two_pow_mod_five x
    omega
  -- mod 16: `z ≡ x (mod 2)`
  have hze : z % 2 = 0 := by
    have h1 : 57 ^ x % 16 = 9 ^ x % 16 := by rw [Nat.pow_mod]
    have h2 : 176 ^ y % 16 = 0 := by
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      rw [pow_succ]; omega
    have h3 : 185 ^ z % 16 = 9 ^ z % 16 := by rw [Nat.pow_mod]
    have h4 := t57_nine_pow_mod_sixteen x
    have h5 := t57_nine_pow_mod_sixteen z
    omega
  -- mod 3: `y ≡ z (mod 2)`
  have hye : y % 2 = 0 := by
    have h1 : 57 ^ x % 3 = 0 := by
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
      rw [pow_succ]; omega
    have h2 : 176 ^ y % 3 = 2 ^ y % 3 := by rw [Nat.pow_mod]
    have h3 : 185 ^ z % 3 = 2 ^ z % 3 := by rw [Nat.pow_mod]
    have h4 := t33_two_pow_mod_three y
    have h5 := t33_two_pow_mod_three z
    omega
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, y = 2 * v + 2 := ⟨(y - 2) / 2, by omega⟩
  rw [pow_mul' 57, pow_mul' 185] at h
  have hA4 : 185 ^ Z % 4 = 1 := by rw [Nat.pow_mod]; norm_num
  have hB4 : 57 ^ X % 4 = 1 := by rw [Nat.pow_mod]; norm_num
  have h176pos : 0 < 176 ^ (2 * v + 2) := by positivity
  have hBpos : 0 < 57 ^ X := by positivity
  have hBA : 57 ^ X < 185 ^ Z := by
    by_contra hle
    have : (185 ^ Z) ^ 2 ≤ (57 ^ X) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨A, hA⟩ : ∃ A, A = 185 ^ Z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 57 ^ X := ⟨_, rfl⟩
  rw [← hA, ← hB] at h hBA
  rw [← hA] at hA4
  rw [← hB] at hB4 hBpos
  obtain ⟨d, hd⟩ : ∃ d, A = B + 2 * d := ⟨(A - B) / 2, by omega⟩
  have hdpos : 0 < d := by omega
  have e176 : 176 ^ (2 * v + 2) = 4 * (2 ^ (8 * v + 6) * 11 ^ (2 * v + 2)) := by
    rw [show (176 : ℕ) = 2 ^ 4 * 11 by norm_num, mul_pow, ← pow_mul]; ring
  have hfac : d * (B + d) = 2 ^ (8 * v + 6) * 11 ^ (2 * v + 2) := by
    have e1 : (B + 2 * d) ^ 2 = B ^ 2 + 4 * (d * (B + d)) := by ring
    rw [hd] at h
    omega
  have hP : 2 ^ (8 * v + 6) ∣ d := by
    have hc : Nat.Coprime (2 ^ (8 * v + 6)) (B + d) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    exact hc.dvd_of_dvd_mul_right ⟨11 ^ (2 * v + 2), hfac⟩
  have hp11 : Nat.Prime 11 := by norm_num
  have hQ : 11 ^ (2 * v + 2) ∣ d ∨ 11 ^ (2 * v + 2) ∣ B + d :=
    prime_pow_dvd_or hp11 ⟨2 ^ (8 * v + 6), by rw [hfac]; ring⟩ (by
      rintro ⟨h1, h2⟩
      have h3 : 11 ∣ B := (Nat.dvd_add_left h1).1 h2
      rw [hB] at h3
      have := hp11.dvd_of_dvd_pow h3
      omega)
  have hc211 : Nat.Coprime (2 ^ (8 * v + 6)) (11 ^ (2 * v + 2)) :=
    Nat.Coprime.pow _ _ (by norm_num)
  rcases hQ with hQ | hQ
  · exfalso
    obtain ⟨-, h2⟩ := eq_of_mul_eq_of_dvd (P := 2 ^ (8 * v + 6) * 11 ^ (2 * v + 2)) (Q := 1)
      (d := d) (s := B + d) (by positivity) (by norm_num) (by rw [mul_one]; exact hfac)
      (hc211.mul_dvd_of_dvd_of_dvd hP hQ) (one_dvd _)
    clear * - h2 hdpos hBpos
    omega
  · obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd (by positivity) (by positivity) hfac hP hQ
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · norm_num at h1 h2
      have hB57 : 57 ^ X = 57 ^ 1 := by
        clear * - h1 h2 hB
        omega
      have hA185 : 185 ^ Z = 185 ^ 1 := by
        clear * - h1 h2 hd hA
        omega
      have hX1 : X = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 57) hB57
      have hZ1 : Z = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 185) hA185
      clear * - hX1 hZ1
      omega
    · exfalso
      obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
      have e := t57_eleven_pow_lt' v'
      clear * - e h1 h2
      omega

/-- Jeśmanowicz' conjecture holds for the triple `(57, 176, 185)` with `n = 1`. -/
theorem jesmanowiczFor_57_176_185_one : JesmanowiczFor 57 176 185 1 := by
  intro x y z hs
  obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
  exact jesmanowicz_57_176_185 hx hy hz h

/-! ### Three key lemmas for `n > 1` -/

/-- If `19^x ∣ (185^w)² - B²` with `19 ∤ B` and `B < 185^w`, then `x ≤ 2w`. -/
theorem t57_nineteen_pow_dvd_sq_sub {x w B : ℕ} (hB : ¬ 19 ∣ B) (hBA : B < 185 ^ w)
    (h : 19 ^ x ∣ (185 ^ w) ^ 2 - B ^ 2) : x ≤ 2 * w := by
  have hlt := t57_two_mul_185_pow_lt w
  obtain ⟨A, hA⟩ : ∃ A, A = 185 ^ w := ⟨_, rfl⟩
  rw [← hA] at hBA h hlt
  obtain ⟨D, rfl⟩ : ∃ D, A = B + D := ⟨A - B, by omega⟩
  have e : (B + D) ^ 2 - B ^ 2 = D * (2 * B + D) := by
    have : (B + D) ^ 2 = B ^ 2 + D * (2 * B + D) := by ring
    omega
  rw [e] at h
  have hle : 19 ^ x ≤ 2 * B + D := by
    rcases prime_pow_dvd_or (by norm_num : Nat.Prime 19) h (by rintro ⟨h1, h2⟩; omega)
      with h1 | h1
    · exact (Nat.le_of_dvd (by omega) h1).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h1
  have h5 : 19 ^ x < 19 ^ (2 * w + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5
  omega

/-- Lifting the exponent at `2`: if `2^k ∣ 185^z - 1` with `z > 0`, then `k < z + 3`. -/
theorem t57_two_pow_dvd_pow_sub_one {k z : ℕ} (hz : 0 < z) (h : 2 ^ k ∣ 185 ^ z - 1) :
    k < z + 3 := by
  rcases Nat.mod_two_eq_zero_or_one z with hze | hzo
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hlte := Nat.multiplicity_pow_two_sub_pow (x := 185) (y := 1) (by norm_num)
      (by norm_num) (by norm_num) (n := z) (by omega) (Nat.even_iff.2 hze)
    rw [one_pow] at hlte
    have hlt : 1 < 185 ^ z := Nat.one_lt_pow (by omega) (by norm_num)
    have hne : 185 ^ z - 1 ≠ 0 := by omega
    have hk := (multiplicity_dvd_iff_le hne).1 h
    have h1 : multiplicity 2 (185 + 1) ≤ 1 :=
      multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
    have h2 : multiplicity 2 (185 - 1) ≤ 3 :=
      multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
    have hz' := multiplicity_lt_self (p := 2) (n := z) hz
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, z = 2 * j + 1 := ⟨z / 2, by omega⟩
    have h185 : 185 ^ (2 * j + 1) % 16 = 9 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    by_contra hlt
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 4 := ⟨k - 4, by omega⟩
    have h16 : 16 ∣ 185 ^ (2 * j + 1) - 1 := (Dvd.intro (2 ^ k') (by ring)).trans h
    obtain ⟨M, hM⟩ : ∃ M, M = 185 ^ (2 * j + 1) := ⟨_, rfl⟩
    rw [← hM] at h185 h16
    clear * - h185 h16
    omega

/-- The core of the case `x < z < y`: `B² + 176^y p^E = (185^Z)²` is impossible when
`y > 2Z`, `p ∉ {2, 11}` is a prime not dividing `B`, `E ≥ 1`, `B ≡ 1 (mod 4)` and `B` is a
nonzero quadratic residue mod `11`. -/
theorem t57_sq_add_ne {p E y Z B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp11 : p ≠ 11)
    (hpB : ¬ p ∣ B) (hB4 : B % 4 = 1)
    (hB11 : B % 11 = 1 ∨ B % 11 = 3 ∨ B % 11 = 4 ∨ B % 11 = 5 ∨ B % 11 = 9)
    (hE : 0 < E) (hy : 2 * Z < y) (h : B ^ 2 + 176 ^ y * p ^ E = (185 ^ Z) ^ 2) : False := by
  have hA4 : 185 ^ Z % 4 = 1 := by rw [Nat.pow_mod]; norm_num
  have hpE : 0 < p ^ E := pow_pos hp.pos E
  have h176 : 0 < 176 ^ y := by positivity
  have hBA : B < 185 ^ Z := by
    by_contra hle
    have h1 : (185 ^ Z) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 0 < 176 ^ y * p ^ E := Nat.mul_pos h176 hpE
    omega
  have hZ : 0 < Z := by
    rcases Nat.eq_zero_or_pos Z with rfl | hZ
    · simp at hBA; omega
    · exact hZ
  have hsize := t57_four_mul_185_pow_lt Z
  have hmono : 176 ^ (2 * Z + 1) ≤ 176 ^ y := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 3 := ⟨y - 3, by omega⟩
  have hk11 := t57_eleven_pow_lt k
  have h2k := t57_two_pow_mod_eleven k
  obtain ⟨A, hA⟩ : ∃ A, A = 185 ^ Z := ⟨_, rfl⟩
  rw [← hA] at h hA4 hBA hsize
  obtain ⟨d, rfl⟩ : ∃ d, A = B + 2 * d := ⟨(A - B) / 2, by omega⟩
  have hd : 0 < d := by omega
  have e176 : 176 ^ (k + 3) = 4 * (2 ^ (4 * k + 10) * 11 ^ (k + 3)) := by
    rw [show (176 : ℕ) = 2 ^ 4 * 11 by norm_num, mul_pow, ← pow_mul]; ring
  have hfac : d * (B + d) = 2 ^ (4 * k + 10) * 11 ^ (k + 3) * p ^ E := by
    have e1 : (B + 2 * d) ^ 2 = B ^ 2 + 4 * (d * (B + d)) := by ring
    have e2 : 176 ^ (k + 3) * p ^ E = 4 * (2 ^ (4 * k + 10) * 11 ^ (k + 3) * p ^ E) := by
      rw [e176]; ring
    omega
  have hP : 2 ^ (4 * k + 10) ∣ d := by
    have hc : Nat.Coprime (2 ^ (4 * k + 10)) (B + d) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    exact hc.dvd_of_dvd_mul_right ⟨11 ^ (k + 3) * p ^ E, by rw [hfac]; ring⟩
  have hp11' : Nat.Prime 11 := by norm_num
  have hQ : 11 ^ (k + 3) ∣ d ∨ 11 ^ (k + 3) ∣ B + d :=
    prime_pow_dvd_or hp11' ⟨2 ^ (4 * k + 10) * p ^ E, by rw [hfac]; ring⟩
      (by rintro ⟨h1, h2⟩; omega)
  have hR : p ^ E ∣ d ∨ p ^ E ∣ B + d :=
    prime_pow_dvd_or hp ⟨2 ^ (4 * k + 10) * 11 ^ (k + 3), by rw [hfac]; ring⟩
      (by rintro ⟨h1, h2⟩; exact hpB ((Nat.dvd_add_left h1).1 h2))
  have hc211 : Nat.Coprime (2 ^ (4 * k + 10)) (11 ^ (k + 3)) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have hc2p : Nat.Coprime (2 ^ (4 * k + 10)) (p ^ E) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hc11p : Nat.Coprime (11 ^ (k + 3)) (p ^ E) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp11' hp).2 (Ne.symm hp11))
  have hPpos : 0 < 2 ^ (4 * k + 10) := by positivity
  have hQpos : 0 < 11 ^ (k + 3) := by positivity
  rcases hQ with hQ | hQ
  · -- `2^(4y-2) 11^y ∣ d`: too big
    have h1 := Nat.le_of_dvd hd (hc211.mul_dvd_of_dvd_of_dvd hP hQ)
    omega
  · rcases hR with hR | hR
    · -- `d = 2^(4y-2) p^E`, `B + d = 11^y`: impossible by size
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd (P := 2 ^ (4 * k + 10) * p ^ E)
        (Q := 11 ^ (k + 3)) (Nat.mul_pos hPpos hpE) hQpos (by rw [hfac]; ring)
        (hc2p.mul_dvd_of_dvd_of_dvd hP hR) hQ
      have h3 : 3 ≤ p ^ E := by
        have h4 : p ≤ p ^ E := Nat.le_self_pow (by omega) _
        have h5 := hp.two_le
        omega
      have h4 : 2 ^ (4 * k + 10) * 3 ≤ 2 ^ (4 * k + 10) * p ^ E := Nat.mul_le_mul_left _ h3
      omega
    · -- `d = 2^(4y-2)`, `B + d = 11^y p^E`: impossible mod 11
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd (P := 2 ^ (4 * k + 10))
        (Q := 11 ^ (k + 3) * p ^ E) hPpos (Nat.mul_pos hQpos hpE) (by rw [hfac]; ring) hP
        (hc11p.mul_dvd_of_dvd_of_dvd hQ hR)
      have e11 : 11 ^ (k + 3) * p ^ E = 11 * (11 ^ (k + 2) * p ^ E) := by ring
      clear * - h1 h2 e11 h2k hB11
      omega

/-! ### The two impossible configurations for `n > 1` -/

/-- Case `y < z < x` for `(57, 176, 185)` (after cancelling `n^y`); `z = y + b`,
`x = z + a`. -/
theorem no_solution_57_176_185_y_lt_z_lt_x {n y a b : ℕ} (hn : 1 < n) (hy : 0 < y)
    (ha : 0 < a) (hb : 0 < b)
    (h : 57 ^ (y + b + a) * n ^ (b + a) + 176 ^ y = 185 ^ (y + b) * n ^ b) : False := by
  obtain ⟨t, ht⟩ : ∃ t, y + b + a = t + 1 := ⟨y + b + a - 1, by omega⟩
  have h57x : 57 ^ (y + b + a) = 57 * 57 ^ t := by rw [ht]; ring
  have hp11 : Nat.Prime 11 := by norm_num
  have hp19 : Nat.Prime 19 := by norm_num
  have hnb : n ^ b ∣ 176 ^ y := by
    have h1 : n ^ b ∣ 57 ^ (y + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 57 ^ (y + b + a) * n ^ (b + a) + 176 ^ y := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_right h1).1 h2
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ b := by positivity
  have h' : 57 ^ (y + b + a) * n ^ a + q = 185 ^ (y + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (185 ^ (y + b)), ← h]; ring
  have hnpow : 1 < n ^ b := Nat.one_lt_pow (by omega) hn
  have hna : ∀ p, p ∣ n → p ∣ 57 ^ (y + b + a) * n ^ a := fun p hp =>
    Dvd.dvd.mul_left (hp.trans (dvd_pow_self n (by omega))) _
  have h2qn : 2 ∣ q → ¬ 2 ∣ n := fun h2q h2n => by
    have h1 : 2 ∣ 185 ^ (y + b) := by rw [← h']; exact dvd_add (hna 2 h2n) h2q
    have := Nat.prime_two.dvd_of_dvd_pow h1; omega
  have h11qn : 11 ∣ q → ¬ 11 ∣ n := fun h11q h11n => by
    have h1 : 11 ∣ 185 ^ (y + b) := by rw [← h']; exact dvd_add (hna 11 h11n) h11q
    have := hp11.dvd_of_dvd_pow h1; omega
  have e176 : 176 ^ y = 2 ^ (4 * y) * 11 ^ y := by
    rw [show (176 : ℕ) = 2 ^ 4 * 11 by norm_num, mul_pow, ← pow_mul]
  have e57 : 57 ^ (y + b + a) = 19 ^ (y + b + a) * 3 ^ (y + b + a) := by
    rw [← mul_pow]; norm_num
  have hmod3 : q % 3 = 2 ^ (y + b) % 3 := by
    have h1 : 185 ^ (y + b) % 3 = 2 ^ (y + b) % 3 := by rw [Nat.pow_mod]
    rw [← h1, ← h', h57x, mul_assoc]
    omega
  have hmod19 : q % 19 = 14 ^ (y + b) % 19 := by
    have h1 : 185 ^ (y + b) % 19 = 14 ^ (y + b) % 19 := by rw [Nat.pow_mod]
    rw [← h1, ← h', h57x, mul_assoc]
    omega
  have h23 := t33_two_pow_mod_three (y + b)
  have hprodpos : 0 < 57 ^ (y + b + a) * n ^ a := by positivity
  -- conclusion once `z = y + b` is even and `q` is a square
  have hfin : ∀ w B, y + b = 2 * w → q = B ^ 2 → ¬ 19 ∣ B → False := by
    intro w B hw hB hB19
    have hd : 19 ^ (y + b + a) ∣ (185 ^ w) ^ 2 - B ^ 2 :=
      ⟨3 ^ (y + b + a) * n ^ a, by rw [← pow_mul', ← hw, ← hB, ← mul_assoc, ← e57]; omega⟩
    have hBA : B < 185 ^ w := by
      by_contra hle
      have h1 : (185 ^ w) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [← pow_mul', ← hw, ← hB] at h1
      omega
    have := t57_nineteen_pow_dvd_sq_sub hB19 hBA hd
    omega
  have hq176 : q ∣ 2 ^ (4 * y) * 11 ^ y := by rw [← e176, hq]; exact Dvd.intro_left _ rfl
  have hn176 : n ^ b ∣ 2 ^ (4 * y) * 11 ^ y := by rw [← e176, hq]; exact Dvd.intro _ rfl
  have cop2 : ∀ m : ℕ, ¬ 2 ∣ m → ∀ i, Nat.Coprime (2 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
  have cop11 : ∀ m : ℕ, ¬ 11 ∣ m → ∀ i, Nat.Coprime (11 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp11).2 hm)
  have hn2 : ¬ 2 ∣ n → ¬ 2 ∣ n ^ b := fun h1 h2 => h1 (Nat.prime_two.dvd_of_dvd_pow h2)
  have hn11 : ¬ 11 ∣ n → ¬ 11 ∣ n ^ b := fun h1 h2 => h1 (hp11.dvd_of_dvd_pow h2)
  have h19pow : ∀ c m : ℕ, c < 19 → 0 < c → ¬ 19 ∣ c ^ m := fun c m hc hc0 hd => by
    have := hp19.dvd_of_dvd_pow hd
    have := Nat.le_of_dvd hc0 this
    omega
  by_cases h2q : 2 ∣ q <;> by_cases h11q : 11 ∣ q
  · -- `n` coprime to `176`: `n = 1`
    have hc : Nat.Coprime (2 ^ (4 * y) * 11 ^ y) (n ^ b) :=
      Nat.Coprime.mul_left (cop2 _ (hn2 (h2qn h2q)) _) (cop11 _ (hn11 (h11qn h11q)) _)
    have h1 := Nat.Coprime.eq_one_of_dvd hc.symm hn176
    omega
  · -- `q = 16^y`, a square
    have h16q : 2 ^ (4 * y) ∣ q :=
      (cop2 _ (hn2 (h2qn h2q)) (4 * y)).dvd_of_dvd_mul_left
        (by rw [← hq, e176]; exact Dvd.intro _ rfl)
    have hq16 : q ∣ 2 ^ (4 * y) := (cop11 _ h11q y).symm.dvd_of_dvd_mul_right hq176
    have hqe : q = 2 ^ (4 * y) := Nat.dvd_antisymm hq16 h16q
    have h23y := t33_two_pow_mod_three (4 * y)
    rw [hqe] at hmod3
    have hze : (y + b) % 2 = 0 := by
      clear * - hmod3 h23 h23y
      omega
    refine hfin ((y + b) / 2) (2 ^ (2 * y)) (by omega) ?_ (h19pow 2 _ (by norm_num)
      (by norm_num))
    rw [hqe, ← pow_mul]; ring
  · -- `q = 11^y`
    have h11q' : 11 ^ y ∣ q :=
      (cop11 _ (hn11 (h11qn h11q)) y).dvd_of_dvd_mul_left
        (by rw [← hq, e176]; exact Dvd.intro_left _ rfl)
    have hq11 : q ∣ 11 ^ y := (cop2 _ h2q (4 * y)).symm.dvd_of_dvd_mul_left hq176
    have hqe : q = 11 ^ y := Nat.dvd_antisymm hq11 h11q'
    rw [hqe] at hmod3 hmod19
    have h113 : 11 ^ y % 3 = 2 ^ y % 3 := by rw [Nat.pow_mod]
    have h23y := t33_two_pow_mod_three y
    have h14 := t57_fourteen_pow_mod_nineteen (y + b)
    have h11 := t57_eleven_pow_mod_nineteen y
    have hye : y % 2 = 0 ∧ (y + b) % 2 = 0 := by
      clear * - hmod3 hmod19 h113 h23y h14 h11 h23
      omega
    obtain ⟨u, rfl⟩ : ∃ u, y = 2 * u := ⟨y / 2, by omega⟩
    exact hfin ((2 * u + b) / 2) (11 ^ u) (by omega) (by rw [hqe, pow_mul'])
      (h19pow 11 _ (by norm_num) (by norm_num))
  · -- `q = 1`
    have hc : Nat.Coprime (2 ^ (4 * y) * 11 ^ y) q :=
      Nat.Coprime.mul_left (cop2 _ h2q _) (cop11 _ h11q _)
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd hc.symm hq176
    rw [hq1] at hmod3
    have hze : (y + b) % 2 = 0 := by
      clear * - hmod3 h23
      omega
    exact hfin ((y + b) / 2) 1 (by omega) (by rw [hq1]; norm_num) (by norm_num)

/-- Case `x < z < y` for `(57, 176, 185)` (after cancelling `n^x`); `z = x + b`,
`y = z + a`. -/
theorem no_solution_57_176_185_x_lt_z_lt_y {n x a b : ℕ} (hn : 1 < n) (hx : 0 < x)
    (ha : 0 < a) (hb : 0 < b)
    (h : 57 ^ x + 176 ^ (x + b + a) * n ^ (b + a) = 185 ^ (x + b) * n ^ b) : False := by
  obtain ⟨t, ht⟩ : ∃ t, x + b + a = t + 1 := ⟨x + b + a - 1, by omega⟩
  have h176y : 176 ^ (x + b + a) = 16 * (11 * 176 ^ t) := by rw [ht]; ring
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hp19 : Nat.Prime 19 := by norm_num
  have hnb : n ^ b ∣ 57 ^ x := by
    have h1 : n ^ b ∣ 176 ^ (x + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 57 ^ x + 176 ^ (x + b + a) * n ^ (b + a) := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_left h1).1 h2
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ b := by positivity
  have h' : q + 176 ^ (x + b + a) * n ^ a = 185 ^ (x + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (185 ^ (x + b)), ← h]; ring
  have hnpow : 1 < n ^ b := Nat.one_lt_pow (by omega) hn
  have hna : ∀ p, p ∣ n → p ∣ 176 ^ (x + b + a) * n ^ a := fun p hp =>
    Dvd.dvd.mul_left (hp.trans (dvd_pow_self n (by omega))) _
  have h3qn : 3 ∣ q → ¬ 3 ∣ n := fun h3q h3n => by
    have h1 : 3 ∣ 185 ^ (x + b) := by rw [← h']; exact dvd_add h3q (hna 3 h3n)
    have := hp3.dvd_of_dvd_pow h1; omega
  have h19qn : 19 ∣ q → ¬ 19 ∣ n := fun h19q h19n => by
    have h1 : 19 ∣ 185 ^ (x + b) := by rw [← h']; exact dvd_add h19q (hna 19 h19n)
    have := hp19.dvd_of_dvd_pow h1; omega
  have e57 : 57 ^ x = 3 ^ x * 19 ^ x := by rw [← mul_pow]; norm_num
  have hmod16 : q % 16 = 9 ^ (x + b) % 16 := by
    have h1 : 185 ^ (x + b) % 16 = 9 ^ (x + b) % 16 := by rw [Nat.pow_mod]
    rw [← h1, ← h', h176y, mul_assoc]
    omega
  have h916 := t57_nine_pow_mod_sixteen (x + b)
  have hq57 : q ∣ 3 ^ x * 19 ^ x := by rw [← e57, hq]; exact Dvd.intro_left _ rfl
  have hn57 : n ^ b ∣ 3 ^ x * 19 ^ x := by rw [← e57, hq]; exact Dvd.intro _ rfl
  have cop3 : ∀ m : ℕ, ¬ 3 ∣ m → ∀ i, Nat.Coprime (3 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp3).2 hm)
  have cop19 : ∀ m : ℕ, ¬ 19 ∣ m → ∀ i, Nat.Coprime (19 ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp19).2 hm)
  have hn3 : ¬ 3 ∣ n → ¬ 3 ∣ n ^ b := fun h1 h2 => h1 (hp3.dvd_of_dvd_pow h2)
  have hn19 : ¬ 19 ∣ n → ¬ 19 ∣ n ^ b := fun h1 h2 => h1 (hp19.dvd_of_dvd_pow h2)
  by_cases h3q : 3 ∣ q <;> by_cases h19q : 19 ∣ q
  · -- `n` coprime to `57`: `n = 1`
    have hc : Nat.Coprime (3 ^ x * 19 ^ x) (n ^ b) :=
      Nat.Coprime.mul_left (cop3 _ (hn3 (h3qn h3q)) _) (cop19 _ (hn19 (h19qn h19q)) _)
    have h1 := Nat.Coprime.eq_one_of_dvd hc.symm hn57
    omega
  · -- `q = 3^x`, `n^b = 19^x`, `n = 19^k`
    have h3q' : 3 ^ x ∣ q :=
      (cop3 _ (hn3 (h3qn h3q)) x).dvd_of_dvd_mul_left
        (by rw [← hq, e57]; exact Dvd.intro _ rfl)
    have hq3 : q ∣ 3 ^ x := (cop19 _ h19q x).symm.dvd_of_dvd_mul_right hq57
    have hqe : q = 3 ^ x := Nat.dvd_antisymm hq3 h3q'
    have hnb19 : n ^ b = 19 ^ x := by
      have h3pos : 0 < 3 ^ x := by positivity
      apply Nat.eq_of_mul_eq_mul_right h3pos
      rw [mul_comm (19 ^ x), ← e57, hq, hqe]
    have hn19' : n ∣ 19 ^ x := by rw [← hnb19]; exact dvd_pow_self n (by omega)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp19).1 hn19'
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hn
      · exact hk
    rw [hqe] at hmod16 h'
    have h316 := t33_three_pow_mod_sixteen x
    have hx2 : x % 2 = 0 ∧ ((x + b) % 2 = 0 → x % 4 = 0) := by
      clear * - h316 hmod16 h916
      omega
    -- mod 19: `z ≡ x (mod 2)`
    have hze : (x + b) % 2 = 0 := by
      obtain ⟨u, hu⟩ : ∃ u, x = 2 * u := ⟨x / 2, by omega⟩
      have h1 : 185 ^ (x + b) % 19 = 14 ^ (x + b) % 19 := by rw [Nat.pow_mod]
      have h2 := t57_fourteen_pow_mod_nineteen (x + b)
      have h3 : 3 ^ x % 19 = 9 ^ u % 19 := by rw [hu, pow_mul]; norm_num
      have h5 := t57_nine_pow_mod_nineteen u
      have h4 : 19 ∣ 176 ^ (x + b + a) * (19 ^ k) ^ a :=
        Dvd.dvd.mul_left ((dvd_pow_self 19 (by omega)).trans (dvd_pow_self _ (by omega))) _
      clear * - h1 h2 h3 h4 h5 h'
      omega
    have hx4 : x % 4 = 0 := hx2.2 hze
    obtain ⟨X, rfl⟩ : ∃ X, x = 4 * X := ⟨x / 4, by omega⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, 4 * X + b = 2 * Z := ⟨(4 * X + b) / 2, by omega⟩
    refine t57_sq_add_ne (p := 19) (E := k * a) (y := 4 * X + b + a) (Z := Z) (B := 9 ^ X)
      hp19 (by norm_num) (by norm_num) ?_ ?_ ?_ (Nat.mul_pos hk ha) (by omega) ?_
    · intro hd
      have := hp19.dvd_of_dvd_pow hd
      omega
    · rw [Nat.pow_mod]; norm_num
    · have := t57_nine_pow_mod_eleven X
      omega
    · have e9 : (9 ^ X) ^ 2 = 3 ^ (4 * X) := by
        rw [← pow_mul, show 4 * X = 2 * (X * 2) by ring, pow_mul 3 2]; norm_num
      rw [← pow_mul' 185, ← hZ, ← h', e9, pow_mul 19 k a]
  · -- `q = 19^x`, `n^b = 3^x`, `n = 3^k`
    have h19q' : 19 ^ x ∣ q :=
      (cop19 _ (hn19 (h19qn h19q)) x).dvd_of_dvd_mul_left
        (by rw [← hq, e57]; exact Dvd.intro_left _ rfl)
    have hq19 : q ∣ 19 ^ x := (cop3 _ h3q x).symm.dvd_of_dvd_mul_left hq57
    have hqe : q = 19 ^ x := Nat.dvd_antisymm hq19 h19q'
    have hnb3 : n ^ b = 3 ^ x := by
      have h19pos : 0 < 19 ^ x := by positivity
      apply Nat.eq_of_mul_eq_mul_right h19pos
      rw [← e57, hq, hqe]
    have hn3' : n ∣ 3 ^ x := by rw [← hnb3]; exact dvd_pow_self n (by omega)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp3).1 hn3'
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hn
      · exact hk
    rw [hqe] at hmod16 h'
    -- mod 3: `z` even
    have hze : (x + b) % 2 = 0 := by
      have h1 : 185 ^ (x + b) % 3 = 2 ^ (x + b) % 3 := by rw [Nat.pow_mod]
      have h1' : 19 ^ x % 3 = 1 := by rw [Nat.pow_mod]; norm_num
      have h2 := t33_two_pow_mod_three (x + b)
      have h4 : 3 ∣ 176 ^ (x + b + a) * (3 ^ k) ^ a :=
        Dvd.dvd.mul_left ((dvd_pow_self 3 (by omega)).trans (dvd_pow_self _ (by omega))) _
      clear * - h1 h1' h2 h4 h'
      omega
    have h1916 : 19 ^ x % 16 = 3 ^ x % 16 := by rw [Nat.pow_mod]
    have h316 := t33_three_pow_mod_sixteen x
    have hx4 : x % 4 = 0 := by
      clear * - h316 h1916 hmod16 h916 hze
      omega
    obtain ⟨X, rfl⟩ : ∃ X, x = 4 * X := ⟨x / 4, by omega⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, 4 * X + b = 2 * Z := ⟨(4 * X + b) / 2, by omega⟩
    refine t57_sq_add_ne (p := 3) (E := k * a) (y := 4 * X + b + a) (Z := Z) (B := 361 ^ X)
      hp3 (by norm_num) (by norm_num) ?_ ?_ ?_ (Nat.mul_pos hk ha) (by omega) ?_
    · intro hd
      have := hp3.dvd_of_dvd_pow hd
      omega
    · rw [Nat.pow_mod]; norm_num
    · have h1 : 361 ^ X % 11 = 9 ^ X % 11 := by rw [Nat.pow_mod]
      have := t57_nine_pow_mod_eleven X
      omega
    · have e361 : (361 ^ X) ^ 2 = 19 ^ (4 * X) := by
        rw [← pow_mul, show 4 * X = 2 * (X * 2) by ring, pow_mul 19 2]; norm_num
      rw [← pow_mul' 185, ← hZ, ← h', e361, pow_mul 3 k a]
  · -- `q = 1`: lifting the exponent at 2
    have hc : Nat.Coprime (3 ^ x * 19 ^ x) q :=
      Nat.Coprime.mul_left (cop3 _ h3q _) (cop19 _ h19q _)
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd hc.symm hq57
    rw [hq1] at h'
    have e : 2 ^ (4 * (x + b + a)) * (11 ^ (x + b + a) * n ^ a)
        = 176 ^ (x + b + a) * n ^ a := by
      rw [← mul_assoc, pow_mul, ← mul_pow]; norm_num
    have hd : 2 ^ (4 * (x + b + a)) ∣ 185 ^ (x + b) - 1 :=
      ⟨11 ^ (x + b + a) * n ^ a, by rw [e]; clear * - h'; omega⟩
    have := t57_two_pow_dvd_pow_sub_one (z := x + b) (by omega) hd
    clear * - this ha hb hx
    omega

/-! ### The main theorem for `(57, 176, 185)` -/

/-- **Jeśmanowicz' conjecture for the triple `(57, 176, 185)` and every `n ≥ 1`**: the only
positive solution of `(57 n)^x + (176 n)^y = (185 n)^z` is `x = y = z = 2`. -/
theorem jesmanowiczFor_57_176_185 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 57 176 185 n := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  swap
  · obtain rfl : n = 1 := by omega
    exact jesmanowiczFor_57_176_185_one
  intro x y z hs
  rcases hs.strict_cases_of_one_lt isPrimitivePythagorean_57_176_185 hn1 with
    h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · -- `x < z < y`
    exfalso
    obtain ⟨hx, hy, hz, heq⟩ := hs
    obtain ⟨b, rfl⟩ : ∃ b, z = x + b := ⟨z - x, by omega⟩
    obtain ⟨a, rfl⟩ : ∃ a, y = x + b + a := ⟨y - (x + b), by omega⟩
    refine no_solution_57_176_185_x_lt_z_lt_y (n := n) (x := x) (a := a) (b := b) hn1 hx
      (by omega) (by omega) ?_
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ x by positivity)
    calc n ^ x * (57 ^ x + 176 ^ (x + b + a) * n ^ (b + a))
        = (57 * n) ^ x + (176 * n) ^ (x + b + a) := by ring
      _ = (185 * n) ^ (x + b) := heq
      _ = n ^ x * (185 ^ (x + b) * n ^ b) := by ring
  · -- `y < z < x`
    exfalso
    obtain ⟨hx, hy, hz, heq⟩ := hs
    obtain ⟨b, rfl⟩ : ∃ b, z = y + b := ⟨z - y, by omega⟩
    obtain ⟨a, rfl⟩ : ∃ a, x = y + b + a := ⟨x - (y + b), by omega⟩
    refine no_solution_57_176_185_y_lt_z_lt_x (n := n) (y := y) (a := a) (b := b) hn1 hy
      (by omega) (by omega) ?_
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ y by positivity)
    calc n ^ y * (57 ^ (y + b + a) * n ^ (b + a) + 176 ^ y)
        = (57 * n) ^ (y + b + a) + (176 * n) ^ y := by ring
      _ = (185 * n) ^ (y + b) := heq
      _ = n ^ y * (185 ^ (y + b) * n ^ b) := by ring

/-- The same for the swapped triple `(176, 57, 185)`. -/
theorem jesmanowiczFor_176_57_185 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 176 57 185 n :=
  jesmanowiczFor_swap.1 (jesmanowiczFor_57_176_185 n hn)

/-! ### Axiom audit -/

#print axioms jesmanowicz_33_56_65
#print axioms jesmanowiczFor_33_56_65_one
#print axioms t33_eleven_pow_dvd_sq_sub
#print axioms t33_two_pow_dvd_pow_sub_one
#print axioms t33_sq_add_ne
#print axioms no_solution_33_56_65_y_lt_z_lt_x
#print axioms no_solution_33_56_65_x_lt_z_lt_y
#print axioms jesmanowiczFor_33_56_65
#print axioms jesmanowiczFor_56_33_65
#print axioms jesmanowicz_57_176_185
#print axioms t57_nineteen_pow_dvd_sq_sub
#print axioms t57_two_pow_dvd_pow_sub_one
#print axioms t57_sq_add_ne
#print axioms no_solution_57_176_185_y_lt_z_lt_x
#print axioms no_solution_57_176_185_x_lt_z_lt_y
#print axioms jesmanowiczFor_57_176_185
#print axioms jesmanowiczFor_176_57_185

end Jesmanowicz
