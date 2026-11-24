/-
# Jeśmanowicz' conjecture: an infinite family, more triples, and a reduction for `n > 1`

STATUS: IN PROGRESS / NOT YET SOLVED

(The status line refers to Jeśmanowicz' conjecture as a whole, which is OPEN and is NOT
proved here; see `RomeroConjecture/Jesmanowicz.lean` for the statement
`Jesmanowicz.JesmanowiczConjecture`.)

Everything in this file is a RE-FORMALIZATION OF KNOWN RESULTS; nothing here is new
mathematics.

## What IS proved in this file (machine-checked, no `sorry`, no extra axioms)

1. **Lu's infinite family, `n = 1`** (W. T. Lu, "On the Pythagorean numbers `4n² − 1`,
   `4n` and `4n² + 1`", Acta Sci. Natur. Univ. Szechuan 2 (1959), 39–42).
   * `lu_core` : if `a + 1 = 4k²`, `k ≥ 1`, then `a^x + (4k)^y = (a+2)^z` with
     `x, y, z > 0` forces `x = y = z = 2`.
   * `jesmanowiczFor_lu (k) (hk : 1 ≤ k) :
       JesmanowiczFor (4*k^2 - 1) (4*k) (4*k^2 + 1) 1` — the whole family.
   * `jesmanowiczFor_lu_swap` — the same with the legs swapped.
   * `isPrimitivePythagorean_lu` — these are indeed primitive Pythagorean triples.
2. **Further single triples, `n = 1`.**
   * `jesmanowiczFor_15_8_17_one`, `jesmanowiczFor_8_15_17_one` : the triple `(8, 15, 17)`
     (it is the member `k = 2` of Lu's family).
   * `jesmanowicz_7_24_25`, `jesmanowiczFor_7_24_25_one`, `jesmanowiczFor_24_7_25_one` :
     `7^x + 24^y = 25^z ⇒ x = y = z = 2` (this triple is NOT in Lu's family; it is in
     Dem'janenko's family `c = b + 1`, which as a family is not formalized here).
3. **`(5, 12, 13)` for every `n ≥ 1`** (the result is due to Deng–Cohen, Bull. Austral.
   Math. Soc. 57 (1998), 515–524).
   * `jesmanowiczFor_5_12_13 (n) (hn : 0 < n) : JesmanowiczFor 5 12 13 n`,
     `jesmanowiczFor_12_5_13`.
   * auxiliary: `five_pow_dvd_sq_sub`, `four_pow_dvd_sq_sub`,
     `no_solution_5_12_13_y_le_z_lt_x`, `no_solution_5_12_13_x_le_z_lt_y`.
4. **A general reduction, valid for every primitive triple and every `n > 1`.**
   * `IsSolution.eq_of_z_lt` : a solution with `z < x` and `z < y` has `x = y`.
   * `pow_add_pow_not_dvd` : for `x ≠ 2`, `a^x + b^x` divides no power of `c`.
   * `IsSolution.not_z_lt_both` : there is NO solution with `z < min x y`.
   * `IsSolution.cases_of_one_lt` : every solution is `(2,2,2)`, or has `x ≤ z < y`,
     or has `y ≤ z < x`.
   In the literature this is: M.-H. Le (Bull. Austral. Math. Soc. 59 (1999), 477–480)
   for the three-case classification, and M.-J. Deng (Bull. Aust. Math. Soc. 89 (2014),
   316–321) / H. Yang and R.-Q. Fu (J. Number Theory 156 (2015), 183–194) for the removal
   of the case `z < min x y`. NOTE: the literature states the sharper `x > z > y` or
   `y > z > x`; the boundary cases `z = x < y` and `z = y < x` are NOT excluded here.

## Proof outlines (all elementary)

* Lu's family. Put `M = 4k²`, so `a = M − 1`, `c = M + 1`, `b = 4k`, `b² = 4M`.
  Mod 4 gives `x` even. The binomial congruence `(1 + u)^n ≡ 1 + n u (mod u²)`
  (`int_sq_dvd_one_add_pow_sub`, used with `u = ±M`) gives `b^y ≡ (x + z) M (mod M²)`;
  hence `y ≥ 2` (the case `y = 1` forces `k = 1`, i.e. Sierpiński's `(3,4,5)`), and then
  `z` is even. With `x = 2X`, `z = 2Z`: `(c^Z − a^X)(c^Z + a^X) = b^y`. One of the two
  factors is `≡ 2 (mod M)`, and a positive divisor of `(4k)^y` that is `≡ 2 (mod 4k²)`
  equals `2` (`eq_two_of_dvd_four_mul_pow`). The sum is `> 2`, so `X` is odd and
  `c^Z − a^X = 2`, whence `a^X + 1 = b^y / 4`; comparing with `a^X + 1 ≡ X M (mod M²)`
  gives `y = 2`, then `X = 1`, `Z = 1`.
* `(7, 24, 25)`. Mod 4, 7, 5, 16 give `x = 2X` with `X` odd, `y` even, `z = 2Z`;
  factoring `25^{2Z} − 7^{2X}` gives `7^X + 3^y = 2^{3y−2}`, and factoring once more
  (as `y` is even) gives `4·8^v = 3^{v+1} + 1` with `y = 2(v+1)`, so `v = 0` (mod 8).
* Reduction for `n > 1`. If `z < x < y`, cancel `n^z`: `n^{x−z} (a^x + b^y n^{y−x}) = c^z`
  with coprime factors, so `a^x + b^y n^{y−x} = d^z` with `d ∣ c`, `d < c`, hence
  `2d ≤ c`; but `a, b < d` (as `x, y > z`), contradicting `a² + b² = c²`. If `x = y > z`
  then `a^x + b^x ∣ c^z`, `x ≥ 3`: impossible for `x` odd (`a + b` is coprime to `c`),
  for `4 ∣ x` (`a^x + b^x ≡ 2 a^x` modulo primes of `c`), and for `x = 2t`, `t ≥ 3` odd
  (lifting the exponent, `Nat.multiplicity_pow_add_pow`, gives `a^x + b^x ∣ c² t`, which
  is too small).
* `(5, 12, 13)`, all `n`. Case `z < min x y` reduces via `IsSolution.eq_of_z_lt` to the
  `n = 1` theorem. In the cases `y ≤ z < x` and `x ≤ z < y`, after cancelling, the
  cofactor `q` of `n^{z−y}` in `12^y` is one of `1, 3^y, 4^y, 12^y` (resp. the cofactor in
  `5^x` is `1`); congruences mod 5 (resp. mod 3, 8) make `z` even, and then `5^x` (resp.
  `4^y`) divides a difference of two squares `13^z − B²`, which is impossible by size
  since `x > z` (resp. `y > z`). One residual subcase (`q = 3^y`, `y` odd) forces `n = 2`,
  `z = 3y`, `x = 3y + 1` and dies mod 3.

## Sources and honesty statement

* The proofs above were worked out by the formalizer from scratch; NONE of the original
  proofs (Lu 1959, Deng–Cohen 1998, Le 1999, Deng 2014, Yang–Fu 2015) was read or
  transcribed, so the arguments here may differ from the published ones. The results
  themselves are known and are attributed as above.
* Sources actually consulted (only for the statements/attributions, via a web search and
  one fetched page): the arXiv note 2102.10921 ("A note on Jeśmanowicz' conjecture for
  non-primitive Pythagorean triples"), which states the lemma "`x > z > y` or `y > z > x`"
  and attributes it to Deng (2014) and Yang–Fu (2015), and Le's (1999) three-case
  theorem; and search-result snippets confirming the bibliographic data of Lu (1959).
  The attribution of `(5, 12, 13)` for all `n` to Deng–Cohen (1998) is taken from the
  header of `JesmanowiczAllN.lean` and from memory; that paper was not consulted.

## What is NOT proved

* Jeśmanowicz' conjecture itself (OPEN).
* Any other infinite family (Dem'janenko's `c = b + 1`, Miyazaki's, Terai's, …), any
  infinite family for `n > 1`, and `(7, 24, 25)` / `(8, 15, 17)` for `n > 1`.
* The sharp form `x > z > y` or `y > z > x` of the reduction (the boundary cases
  `z = x`, `z = y` are open here for general triples).
-/
import RomeroConjecture.Jesmanowicz
import RomeroConjecture.JesmanowiczAllN

namespace Jesmanowicz

/-! ### Lu's family `(4k² - 1, 4k, 4k² + 1)`, `n = 1` -/

/-- First-order binomial congruence: `(1 + u)^n ≡ 1 + n u (mod u²)`. -/
theorem int_sq_dvd_one_add_pow_sub (u : ℤ) (n : ℕ) : u ^ 2 ∣ (1 + u) ^ n - 1 - n * u := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(1 + u) * q + n, ?_⟩
    push_cast
    have e : (1 + u) ^ (n + 1) = (1 + u) * (1 + u) ^ n := by ring
    rw [e]
    linear_combination (1 + u) * hq

/-- If `T > 0`, `T ≡ 2 (mod 4k²)` and `T ∣ (4k)^y`, then `T = 2`. -/
theorem eq_two_of_dvd_four_mul_pow {k y : ℕ} {T : ℤ} (hT : 0 < T)
    (hmod : (4 * (k : ℤ) ^ 2) ∣ T - 2) (hdvd : T ∣ (4 * (k : ℤ)) ^ y) : T = 2 := by
  obtain ⟨j, hj⟩ := hmod
  have hTe : T = 2 * (1 + 2 * (k : ℤ) ^ 2 * j) := by linear_combination hj
  have hT'pos : 0 < 1 + 2 * (k : ℤ) ^ 2 * j := by
    rw [hTe] at hT; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = 1 + 2 * (k : ℤ) ^ 2 * j :=
    ⟨(1 + 2 * (k : ℤ) ^ 2 * j).toNat, Int.toNat_of_nonneg hT'pos.le⟩
  have htd : (t : ℤ) ∣ ((4 * k : ℕ) : ℤ) ^ y := by
    rw [ht]; push_cast
    exact (Dvd.intro_left 2 hTe.symm).trans hdvd
  have htd' : t ∣ (4 * k) ^ y := by exact_mod_cast htd
  have hcop : Nat.Coprime t (4 * k) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    set g := Nat.gcd t (4 * k) with hg
    have hgt : (g : ℤ) ∣ (t : ℤ) := by exact_mod_cast Nat.gcd_dvd_left t (4 * k)
    have hgk : (g : ℤ) ∣ 4 * (k : ℤ) := by exact_mod_cast Nat.gcd_dvd_right t (4 * k)
    have h1 : (g : ℤ) ∣ 2 := by
      have h2 : (g : ℤ) ∣ 2 * (t : ℤ) - 4 * (k : ℤ) * (k * j) :=
        dvd_sub (Dvd.dvd.mul_left hgt 2) (Dvd.dvd.mul_right hgk _)
      have e : 2 * (t : ℤ) - 4 * (k : ℤ) * (k * j) = 2 := by rw [ht]; ring
      rwa [e] at h2
    have h1' : g ∣ 2 := by exact_mod_cast h1
    have hg2 : g = 1 ∨ g = 2 := (Nat.dvd_prime Nat.prime_two).1 h1'
    rcases hg2 with h | h
    · exact h
    · exfalso
      rw [h] at hgt
      obtain ⟨r, hr⟩ := hgt
      rw [ht, mul_assoc] at hr
      obtain ⟨w, hw⟩ : ∃ w, w = (k : ℤ) ^ 2 * j := ⟨_, rfl⟩
      rw [← hw] at hr
      omega
  have ht1 : t = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right y hcop) htd'
  rw [hTe, ← ht, ht1]; norm_num

/-- **Lu's family, core statement.** If `a + 1 = 4k²` (`k ≥ 1`), then
`a^x + (4k)^y = (a + 2)^z` in positive integers forces `x = y = z = 2`. -/
theorem lu_core {k a x y z : ℕ} (hk : 0 < k) (ha : a + 1 = 4 * k ^ 2)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : a ^ x + (4 * k) ^ y = (a + 2) ^ z) : x = 2 ∧ y = 2 ∧ z = 2 := by
  have hk2 : 0 < k ^ 2 := by positivity
  have ha3 : 3 ≤ a := by omega
  -- `x` is even (mod 4)
  have hxe : x % 2 = 0 := by
    by_contra hxo
    obtain ⟨j, rfl⟩ : ∃ j, x = 2 * j + 1 := ⟨x / 2, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have h1 : a ^ (2 * j + 1) % 4 = 3 := by
      rw [Nat.pow_mod, show a % 4 = 3 by omega]; exact three_pow_mod_four_odd j
    have h2 : (a + 2) ^ z % 4 = 1 := by
      rw [Nat.pow_mod, show (a + 2) % 4 = 1 by omega]; simp
    have h3 : (4 * k) ^ (y' + 1) = 4 * (k * (4 * k) ^ y') := by ring
    omega
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  have hX : 0 < X := by omega
  -- integer set-up
  set M : ℤ := 4 * (k : ℤ) ^ 2 with hM
  have hMpos : 0 < M := by positivity
  have haZ : (a : ℤ) = M - 1 := by rw [hM]; have := ha; zify at this; linarith
  have hZ : (a : ℤ) ^ (2 * X) + (4 * (k : ℤ)) ^ y = ((a : ℤ) + 2) ^ z := by exact_mod_cast h
  have hc : (a : ℤ) + 2 = 1 + M := by rw [haZ]; ring
  have hA : (a : ℤ) = -(1 + -M) := by rw [haZ]; ring
  have hP : ∀ n : ℕ, M ^ 2 ∣ ((a : ℤ) + 2) ^ n - 1 - n * M := fun n => by
    rw [hc]; exact int_sq_dvd_one_add_pow_sub M n
  have hQe : ∀ n : ℕ, M ^ 2 ∣ (a : ℤ) ^ (2 * n) - 1 + (2 * n : ℕ) * M := fun n => by
    have := int_sq_dvd_one_add_pow_sub (-M) (2 * n)
    rw [hA, Even.neg_pow ⟨n, by ring⟩]
    convert this using 1
    · ring
    · ring
  have hQo : ∀ n : ℕ, n % 2 = 1 → M ^ 2 ∣ (a : ℤ) ^ n + 1 - n * M := fun n hn => by
    have := int_sq_dvd_one_add_pow_sub (-M) n
    rw [neg_sq] at this
    rw [hA, Odd.neg_pow (Nat.odd_iff.2 hn)]
    have e : -(1 + -M) ^ n + 1 - (n : ℤ) * M = -((1 + -M) ^ n - 1 - n * -M) := by ring
    rw [e]; exact (dvd_neg).2 this
  have hMM : M ∣ M ^ 2 := Dvd.intro_left M (by ring)
  have h2MM : 2 * M ∣ M ^ 2 := ⟨2 * (k : ℤ) ^ 2, by rw [hM]; ring⟩
  -- `M² ∣ b^y - (z + x) M`
  have hkey : M ^ 2 ∣ (4 * (k : ℤ)) ^ y - ((z : ℤ) + (2 * X : ℕ)) * M := by
    have e : (4 * (k : ℤ)) ^ y - ((z : ℤ) + (2 * X : ℕ)) * M
        = (((a : ℤ) + 2) ^ z - 1 - z * M) - ((a : ℤ) ^ (2 * X) - 1 + (2 * X : ℕ) * M) := by
      linear_combination hZ
    rw [e]; exact dvd_sub (hP z) (hQe X)
  -- `y ≥ 2`
  have hy2 : 2 ≤ y := by
    by_contra hlt
    obtain rfl : y = 1 := by omega
    rw [pow_one] at hkey
    have h1 : M ∣ 4 * (k : ℤ) := by
      have := dvd_add (hMM.trans hkey) (Dvd.intro_left ((z : ℤ) + (2 * X : ℕ)) rfl)
      simpa using this
    obtain ⟨q, hq⟩ := h1
    have hkq : (k : ℤ) * q = 1 := by
      have hk0 : (4 * (k : ℤ)) ≠ 0 := by positivity
      apply mul_left_cancel₀ hk0
      rw [hM] at hq; linear_combination -hq
    have hk1 : k = 1 := by
      have := Int.eq_one_or_neg_one_of_mul_eq_one hkq
      omega
    subst hk1
    obtain rfl : a = 3 := by omega
    have := sierpinski_3_4_5 (x := 2 * X) (y := 1) (by omega) (by omega) hz (by simpa using h)
    omega
  -- `z` is even
  have hze : z % 2 = 0 := by
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
    have hb : 2 * M ∣ (4 * (k : ℤ)) ^ (y' + 2) :=
      ⟨2 * (4 * (k : ℤ)) ^ y', by rw [hM]; ring⟩
    have h1 : 2 * M ∣ ((z : ℤ) + (2 * X : ℕ)) * M := by
      have := dvd_sub hb (h2MM.trans hkey)
      simpa using this
    have h2 : (2 : ℤ) ∣ (z : ℤ) + (2 * X : ℕ) := by
      obtain ⟨q, hq⟩ := h1
      exact ⟨q, mul_right_cancel₀ hMpos.ne' (by linear_combination hq)⟩
    omega
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  have hZpos : 0 < Z := by omega
  -- factorisation
  have hfac : (((a : ℤ) + 2) ^ Z - (a : ℤ) ^ X) * (((a : ℤ) + 2) ^ Z + (a : ℤ) ^ X)
      = (4 * (k : ℤ)) ^ y := by
    rw [pow_mul', pow_mul'] at hZ; linear_combination -hZ
  have hcZ : M ∣ ((a : ℤ) + 2) ^ Z - 1 := by
    have := dvd_add (hMM.trans (hP Z)) (Dvd.intro_left (Z : ℤ) rfl)
    simpa using this
  have haXpos : (0 : ℤ) < (a : ℤ) ^ X := by positivity
  have hcZge : (a : ℤ) + 2 ≤ ((a : ℤ) + 2) ^ Z := by
    have : a + 2 ≤ (a + 2) ^ Z := Nat.le_self_pow (by omega) _
    exact_mod_cast this
  have haN : (0 : ℤ) ≤ a := by positivity
  have hSpos : 0 < ((a : ℤ) + 2) ^ Z + (a : ℤ) ^ X := by linarith
  rcases Nat.mod_two_eq_zero_or_one X with hXe | hXo
  · -- `X` even: the sum is `≡ 2 (mod M)` and divides `b^y`, so equals `2`: absurd
    exfalso
    obtain ⟨W, rfl⟩ : ∃ W, X = 2 * W := ⟨X / 2, by omega⟩
    have haX : M ∣ (a : ℤ) ^ (2 * W) - 1 := by
      have := dvd_sub (hMM.trans (hQe W)) (Dvd.intro_left ((2 * W : ℕ) : ℤ) rfl)
      simpa using this
    have hS2 := eq_two_of_dvd_four_mul_pow (k := k) (y := y) hSpos
      (by
        have := dvd_add hcZ haX
        have e : ((a : ℤ) + 2) ^ Z - 1 + ((a : ℤ) ^ (2 * W) - 1)
            = ((a : ℤ) + 2) ^ Z + (a : ℤ) ^ (2 * W) - 2 := by ring
        rw [← hM, ← e]; exact this)
      (Dvd.intro_left _ hfac)
    linarith
  · -- `X` odd: the difference equals `2`
    have hQX := hQo X hXo
    have haX : M ∣ (a : ℤ) ^ X + 1 := by
      have := dvd_add (hMM.trans hQX) (Dvd.intro_left (X : ℤ) rfl)
      simpa using this
    have hDpos : 0 < ((a : ℤ) + 2) ^ Z - (a : ℤ) ^ X := by
      have hpos : (0 : ℤ) < (4 * (k : ℤ)) ^ y := by positivity
      rw [← hfac] at hpos
      exact pos_of_mul_pos_left hpos hSpos.le
    have hD2 := eq_two_of_dvd_four_mul_pow (k := k) (y := y) hDpos
      (by
        have := dvd_sub hcZ haX
        have e : ((a : ℤ) + 2) ^ Z - 1 - ((a : ℤ) ^ X + 1)
            = ((a : ℤ) + 2) ^ Z - (a : ℤ) ^ X - 2 := by ring
        rw [← hM, ← e]; exact this)
      (Dvd.intro _ hfac)
    -- `4 (a^X + 1) = b^y`
    have h4 : 4 * ((a : ℤ) ^ X + 1) = (4 * (k : ℤ)) ^ y := by
      rw [← hfac, hD2]; linarith
    have hy2' : y = 2 := by
      by_contra hne
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 3 := ⟨y - 3, by omega⟩
      have h5 : (a : ℤ) ^ X + 1 = 2 * M * (2 * k * (4 * (k : ℤ)) ^ y') := by
        have : (4 : ℤ) * ((a : ℤ) ^ X + 1) = 4 * (2 * M * (2 * k * (4 * (k : ℤ)) ^ y')) := by
          rw [h4, hM]; ring
        linarith
      have h6 : 2 * M ∣ (X : ℤ) * M := by
        have := dvd_sub (Dvd.intro _ h5.symm) (h2MM.trans hQX)
        simpa using this
      have h7 : (2 : ℤ) ∣ (X : ℤ) := by
        obtain ⟨q, hq⟩ := h6
        exact ⟨q, mul_right_cancel₀ hMpos.ne' (by linear_combination hq)⟩
      omega
    subst hy2'
    have h8 : (a : ℤ) ^ X = a := by rw [haZ, hM] at h4 ⊢; linarith
    have hX1 : X = 1 := by
      have : a ^ X = a ^ 1 := by rw [pow_one]; exact_mod_cast h8
      exact Nat.pow_right_injective (by omega : 2 ≤ a) this
    subst hX1
    have h9 : ((a : ℤ) + 2) ^ Z = a + 2 := by rw [pow_one] at hD2; linarith
    have hZ1 : Z = 1 := by
      have : (a + 2) ^ Z = (a + 2) ^ 1 := by rw [pow_one]; exact_mod_cast h9
      exact Nat.pow_right_injective (by omega : 2 ≤ a + 2) this
    subst hZ1
    exact ⟨rfl, rfl, rfl⟩

/-- The triples of Lu's family are primitive Pythagorean triples. -/
theorem isPrimitivePythagorean_lu (k : ℕ) (hk : 1 ≤ k) :
    IsPrimitivePythagorean (4 * k ^ 2 - 1) (4 * k) (4 * k ^ 2 + 1) := by
  have hk2 : 0 < k ^ 2 := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a + 1 = 4 * k ^ 2 := ⟨4 * k ^ 2 - 1, by omega⟩
  rw [show 4 * k ^ 2 - 1 = a by omega, show 4 * k ^ 2 + 1 = a + 2 by omega]
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · show Nat.gcd a (4 * k) = 1
    have h1 : Nat.gcd a (4 * k) ∣ a := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd a (4 * k) ∣ a + 1 := by
      rw [ha]; exact (Nat.gcd_dvd_right _ _).trans ⟨k, by ring⟩
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h2)
  · have e : (4 * k) ^ 2 = 4 * (a + 1) := by rw [ha]; ring
    rw [e]; ring

/-- **Lu (1959), re-formalized.** Jeśmanowicz' conjecture holds (with `n = 1`) for every
triple `(4k² - 1, 4k, 4k² + 1)`, `k ≥ 1`. -/
theorem jesmanowiczFor_lu (k : ℕ) (hk : 1 ≤ k) :
    JesmanowiczFor (4 * k ^ 2 - 1) (4 * k) (4 * k ^ 2 + 1) 1 := by
  intro x y z hs
  obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
  have hk2 : 0 < k ^ 2 := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a + 1 = 4 * k ^ 2 := ⟨4 * k ^ 2 - 1, by omega⟩
  rw [show 4 * k ^ 2 - 1 = a by omega, show 4 * k ^ 2 + 1 = a + 2 by omega] at h
  exact lu_core hk ha hx hy hz h

/-- Lu's family with the legs swapped. -/
theorem jesmanowiczFor_lu_swap (k : ℕ) (hk : 1 ≤ k) :
    JesmanowiczFor (4 * k) (4 * k ^ 2 - 1) (4 * k ^ 2 + 1) 1 :=
  jesmanowiczFor_swap.1 (jesmanowiczFor_lu k hk)

/-! ### The triple `(8, 15, 17)`, `n = 1` (member `k = 2` of Lu's family) -/

theorem isPrimitivePythagorean_8_15_17 : IsPrimitivePythagorean 8 15 17 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by norm_num⟩

theorem jesmanowiczFor_15_8_17_one : JesmanowiczFor 15 8 17 1 := by
  have := jesmanowiczFor_lu 2 (by norm_num)
  norm_num at this
  exact this

theorem jesmanowiczFor_8_15_17_one : JesmanowiczFor 8 15 17 1 :=
  jesmanowiczFor_swap.1 jesmanowiczFor_15_8_17_one

/-! ### The triple `(7, 24, 25)`, `n = 1` -/

theorem isPrimitivePythagorean_7_24_25 : IsPrimitivePythagorean 7 24 25 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by norm_num⟩

theorem three_pow_mod_seven (y : ℕ) :
    (y % 6 = 0 → 3 ^ y % 7 = 1) ∧ (y % 6 = 1 → 3 ^ y % 7 = 3) ∧
    (y % 6 = 2 → 3 ^ y % 7 = 2) ∧ (y % 6 = 3 → 3 ^ y % 7 = 6) ∧
    (y % 6 = 4 → 3 ^ y % 7 = 4) ∧ (y % 6 = 5 → 3 ^ y % 7 = 5) := by
  induction y with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem four_pow_mod_seven (z : ℕ) : 4 ^ z % 7 = 1 ∨ 4 ^ z % 7 = 4 ∨ 4 ^ z % 7 = 2 := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem four_pow_mod_five (u : ℕ) :
    (u % 2 = 0 → 4 ^ u % 5 = 1) ∧ (u % 2 = 1 → 4 ^ u % 5 = 4) := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem nine_pow_mod_sixteen (z : ℕ) :
    (z % 2 = 0 → 9 ^ z % 16 = 1) ∧ (z % 2 = 1 → 9 ^ z % 16 = 9) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- The only positive integer solution of `7^x + 24^y = 25^z` is `x = y = z = 2`. -/
theorem jesmanowicz_7_24_25 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 7 ^ x + 24 ^ y = 25 ^ z) : x = 2 ∧ y = 2 ∧ z = 2 := by
  -- `x` even (mod 4)
  have hxe : x % 2 = 0 := by
    by_contra hxo
    obtain ⟨j, rfl⟩ : ∃ j, x = 2 * j + 1 := ⟨x / 2, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have h1 : 7 ^ (2 * j + 1) % 4 = 3 := by
      rw [Nat.pow_mod]; exact three_pow_mod_four_odd j
    have h2 : 25 ^ z % 4 = 1 := by rw [Nat.pow_mod]; simp
    have h3 : 24 ^ (y' + 1) = 24 * 24 ^ y' := by ring
    omega
  -- `y` even (mod 7)
  have hye : y % 2 = 0 := by
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    have h1 : 7 ^ (x' + 1) = 7 * 7 ^ x' := by ring
    have h2 : 24 ^ y % 7 = 3 ^ y % 7 := by rw [Nat.pow_mod]
    have h3 : 25 ^ z % 7 = 4 ^ z % 7 := by rw [Nat.pow_mod]
    have h4 := three_pow_mod_seven y
    have h5 := four_pow_mod_seven z
    omega
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, y = 2 * (v + 1) := ⟨y / 2 - 1, by omega⟩
  have h49 : 7 ^ (2 * X) = 49 ^ X := by rw [pow_mul]; norm_num
  have h576 : 24 ^ (2 * (v + 1)) = 576 * 576 ^ v := by
    rw [pow_mul, pow_succ]; norm_num; ring
  -- `X` odd (mod 5)
  have hXo : X % 2 = 1 := by
    obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
    have h1 : 49 ^ X % 5 = 4 ^ X % 5 := by rw [Nat.pow_mod]
    have h2 : 576 ^ v % 5 = 1 := by rw [Nat.pow_mod]; simp
    have h3 : 25 ^ (z' + 1) = 25 * 25 ^ z' := by ring
    have h4 := four_pow_mod_five X
    omega
  -- `z` even (mod 16)
  have hze : z % 2 = 0 := by
    by_contra hzo
    have h1 : 49 ^ X % 16 = 1 := by rw [Nat.pow_mod]; simp
    have h2 : 25 ^ z % 16 = 9 ^ z % 16 := by rw [Nat.pow_mod]
    have h3 := nine_pow_mod_sixteen z
    omega
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  rw [pow_mul' 7, pow_mul' 25] at h
  have hA4 : 25 ^ Z % 4 = 1 := by rw [Nat.pow_mod]; simp
  have hA3 : 25 ^ Z % 3 = 1 := by rw [Nat.pow_mod]; simp
  have hB3 : 7 ^ X % 3 = 1 := by rw [Nat.pow_mod]; simp
  have hB4 : 7 ^ X % 4 = 3 := by
    obtain ⟨j, rfl⟩ : ∃ j, X = 2 * j + 1 := ⟨X / 2, by omega⟩
    rw [Nat.pow_mod]; exact three_pow_mod_four_odd j
  have h24pos : 0 < 24 ^ (2 * (v + 1)) := by positivity
  have hBpos : 0 < 7 ^ X := by positivity
  have hBA : 7 ^ X < 25 ^ Z := by
    by_contra hle
    have : (25 ^ Z) ^ 2 ≤ (7 ^ X) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨d, hd⟩ : ∃ d, 25 ^ Z = 7 ^ X + 2 * d := ⟨(25 ^ Z - 7 ^ X) / 2, by omega⟩
  have e24 : 24 ^ (2 * (v + 1)) = 4 * (2 ^ (6 * v + 4) * 3 ^ (2 * v + 2)) := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, mul_pow, ← pow_mul]; ring
  have hfac : d * (7 ^ X + d) = 2 ^ (6 * v + 4) * 3 ^ (2 * v + 2) := by
    rw [hd, e24] at h; nlinarith
  have hd3 : 3 ^ (2 * v + 2) ∣ d := by
    have hc : Nat.Coprime (3 ^ (2 * v + 2)) (7 ^ X + d) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
    exact hc.dvd_of_dvd_mul_right (Dvd.intro_left _ hfac.symm)
  have hs2 : 2 ^ (6 * v + 4) ∣ 7 ^ X + d := by
    have hc : Nat.Coprime (2 ^ (6 * v + 4)) d :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    exact hc.dvd_of_dvd_mul_left (Dvd.intro _ hfac.symm)
  obtain ⟨hd', hs⟩ := eq_of_mul_eq_of_dvd (P := 3 ^ (2 * v + 2)) (Q := 2 ^ (6 * v + 4))
    (by positivity) (by positivity) (by rw [hfac, mul_comm]) hd3 hs2
  -- now `7^X + (3^(v+1))² = (4·8^v)²`
  have eP : 2 ^ (6 * v + 4) = (4 * 8 ^ v) ^ 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]; ring
  have eQ : 3 ^ (2 * v + 2) = (3 ^ (v + 1)) ^ 2 := by ring
  rw [eP] at hs
  rw [eQ] at hd'
  have hQ7 := three_pow_mod_seven (v + 1)
  have hQ8 := three_pow_mod_eight (v + 1)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 3 ^ (v + 1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = 4 * 8 ^ v := ⟨_, rfl⟩
  rw [← hQ] at hd' hQ7 hQ8
  rw [← hP] at hs
  have hQP : Q < P := by
    by_contra hle
    have : P ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨e, he⟩ : ∃ e, P = Q + e := ⟨P - Q, by omega⟩
  have hepos : 0 < e := by omega
  have hfac2 : e * (2 * Q + e) = 7 ^ X := by
    rw [he, hd'] at hs; nlinarith
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 (Dvd.intro _ hfac2)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 (Dvd.intro_left _ hfac2)
  have he1 : e = 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simpa using hi
    · exfalso
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp at hj; omega
      · obtain ⟨r, hr⟩ : 7 ∣ e := by rw [hi]; exact dvd_pow_self 7 (by omega)
        obtain ⟨r', hr'⟩ : 7 ∣ 2 * Q + e := by rw [hj]; exact dvd_pow_self 7 (by omega)
        omega
  subst he1
  have hv : v = 0 := by
    by_contra hv
    obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
    have : 8 ^ (v' + 1) = 8 * 8 ^ v' := by ring
    clear * - this hP he hQ8
    omega
  subst hv
  have hQ3 : Q = 3 := by simpa using hQ
  have hd9 : d = 9 := by rw [hd', hQ3]; norm_num
  have hs16 : 7 ^ X + d = 16 := by rw [hs, he, hQ3]; norm_num
  have hB7 : 7 ^ X = 7 ^ 1 := by clear * - hd9 hs16; omega
  have hX1 : X = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 7) hB7
  subst hX1
  have hA25 : 25 ^ Z = 25 ^ 1 := by clear * - hd9 hd; omega
  have hZ1 : Z = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 25) hA25
  subst hZ1
  exact ⟨rfl, rfl, rfl⟩

/-- Jeśmanowicz' conjecture holds for the triple `(7, 24, 25)` with `n = 1`. -/
theorem jesmanowiczFor_7_24_25_one : JesmanowiczFor 7 24 25 1 := by
  intro x y z hs
  obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
  exact jesmanowicz_7_24_25 hx hy hz h

theorem jesmanowiczFor_24_7_25_one : JesmanowiczFor 24 7 25 1 :=
  jesmanowiczFor_swap.1 jesmanowiczFor_7_24_25_one

/-! ### A general reduction for `n > 1`: the case `z < min x y` with `x ≠ y` -/

/-- Core of the reduction: for a primitive triple and `n > 1` there is no relation
`a^(z+i) n^i + b^(z+i+j) n^(i+j) = c^z` with `z, i, j > 0`. -/
theorem no_solution_z_lt_x_lt_y {a b c n z i j : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 1 < n) (hz : 0 < z) (hi : 0 < i) (hj : 0 < j)
    (heq : a ^ (z + i) * n ^ i + b ^ (z + i + j) * n ^ (i + j) = c ^ z) : False := by
  obtain ⟨ha, hb, hc, hcop, hp⟩ := h
  have hfac : (a ^ (z + i) + b ^ (z + i + j) * n ^ j) * n ^ i = c ^ z := by
    rw [← heq]; ring
  -- `n` is coprime to the cofactor
  have hcopn : Nat.Coprime (a ^ (z + i) + b ^ (z + i + j) * n ^ j) n := by
    apply Nat.Coprime.symm
    apply Nat.coprime_of_dvd
    intro p hpp hpn hpQ
    have hpc : p ∣ c :=
      hpp.dvd_of_dvd_pow ((hpn.trans (dvd_pow_self n (by omega))).trans (Dvd.intro_left _ hfac))
    have hpa : p ∣ a := by
      have h1 : p ∣ b ^ (z + i + j) * n ^ j :=
        Dvd.dvd.mul_left (hpn.trans (dvd_pow_self n (by omega))) _
      exact hpp.dvd_of_dvd_pow ((Nat.dvd_add_left h1).1 hpQ)
    have hpb : p ∣ b := by
      have h1 : p ∣ a ^ 2 := Dvd.dvd.pow hpa (by norm_num)
      have h2 : p ∣ a ^ 2 + b ^ 2 := by rw [hp]; exact Dvd.dvd.pow hpc (by norm_num)
      exact hpp.dvd_of_dvd_pow ((Nat.dvd_add_right h1).1 h2)
    have := Nat.dvd_gcd hpa hpb
    rw [hcop] at this
    exact hpp.one_lt.ne' (Nat.dvd_one.1 this)
  -- hence the cofactor is a perfect `z`-th power `d^z`, with `d ∣ c`
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow
    (Nat.isUnit_iff.2 (Nat.Coprime.pow_right i hcopn)) hfac
  have hdc : d ∣ c := by
    have : d ^ z ∣ c ^ z := by rw [← hd]; exact Dvd.intro _ hfac
    exact (Nat.pow_dvd_pow_iff (by omega)).1 this
  obtain ⟨e, he⟩ := hdc
  have hnpow : 1 < n ^ i := Nat.one_lt_pow (by omega) hn
  have hapos : 0 < a ^ (z + i) := by positivity
  have hbpos : 0 < b ^ (z + i + j) * n ^ j := by positivity
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · rw [zero_pow (by omega)] at hd; omega
    · exact hd0
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · exfalso
      interval_cases e
      · omega
      · rw [mul_one] at he
        rw [hd, he] at hfac
        have : d ^ z * n ^ i = d ^ z * 1 := by rw [hfac, mul_one]
        have := Nat.eq_of_mul_eq_mul_left (by positivity) this
        omega
    · exact hge
  have had : a < d := by
    by_contra hle
    have h1 : d ^ z ≤ a ^ z := Nat.pow_le_pow_left (by omega) z
    have h2 : a ^ z ≤ a ^ (z + i) := Nat.pow_le_pow_right ha (by omega)
    omega
  have hbd : b < d := by
    by_contra hle
    have h1 : d ^ z ≤ b ^ z := Nat.pow_le_pow_left (by omega) z
    have h2 : b ^ z ≤ b ^ (z + i + j) := Nat.pow_le_pow_right hb (by omega)
    have h3 : b ^ (z + i + j) ≤ b ^ (z + i + j) * n ^ j :=
      Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hcd : 2 * d ≤ c := by rw [he]; nlinarith
  nlinarith

/-- **Reduction for `n > 1`.** For a primitive triple and `n > 1`, a solution of
`(a n)^x + (b n)^y = (c n)^z` with `z < x` and `z < y` must have `x = y`. -/
theorem IsSolution.eq_of_z_lt {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 1 < n) (hs : IsSolution a b c n x y z) (hzx : z < x) (hzy : z < y) : x = y := by
  have hc := hs.cancel (by omega) hzx.le hzy.le
  obtain ⟨-, -, hz, -⟩ := hs
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exfalso
    obtain ⟨i, rfl⟩ : ∃ i, x = z + i := ⟨x - z, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, y = z + i + j := ⟨y - (z + i), by omega⟩
    refine no_solution_z_lt_x_lt_y h hn hz (i := i) (j := j) (by omega) (by omega) ?_
    rw [← hc]
    congr 3 <;> omega
  · exact hxy
  · exfalso
    obtain ⟨i, rfl⟩ : ∃ i, y = z + i := ⟨y - z, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, x = z + i + j := ⟨x - (z + i), by omega⟩
    refine no_solution_z_lt_x_lt_y (isPrimitivePythagorean_swap.1 h) hn hz (i := i) (j := j)
      (by omega) (by omega) ?_
    rw [← hc, add_comm]
    congr 3 <;> omega

/-! ### The triple `(5, 12, 13)` for every `n ≥ 1` -/

theorem two_mul_thirteen_pow_lt (w : ℕ) : 2 * 13 ^ w < 5 ^ (2 * w + 1) := by
  induction w with
  | zero => norm_num
  | succ k ih =>
    have e1 : 13 ^ (k + 1) = 13 * 13 ^ k := by ring
    have e2 : 5 ^ (2 * (k + 1) + 1) = 25 * 5 ^ (2 * k + 1) := by ring
    omega

theorem two_pow_mod_five (y : ℕ) :
    (y % 4 = 0 → 2 ^ y % 5 = 1) ∧ (y % 4 = 1 → 2 ^ y % 5 = 2) ∧
    (y % 4 = 2 → 2 ^ y % 5 = 4) ∧ (y % 4 = 3 → 2 ^ y % 5 = 3) := by
  induction y with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem three_pow_mod_five (y : ℕ) :
    (y % 4 = 0 → 3 ^ y % 5 = 1) ∧ (y % 4 = 1 → 3 ^ y % 5 = 3) ∧
    (y % 4 = 2 → 3 ^ y % 5 = 4) ∧ (y % 4 = 3 → 3 ^ y % 5 = 2) := by
  induction y with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- If `5^x ∣ (13^w)² - B²` with `B < 13^w`, then `x ≤ 2w` (the power of `5` divides one
of the two factors `13^w ∓ B`, which are smaller than `2·13^w < 5^(2w+1)`). -/
theorem five_pow_dvd_sq_sub {x w B : ℕ} (hBA : B < 13 ^ w)
    (h : 5 ^ x ∣ (13 ^ w) ^ 2 - B ^ 2) : x ≤ 2 * w := by
  have h13 : ¬ 5 ∣ 13 ^ w := fun hd => by
    have := Nat.prime_five.dvd_of_dvd_pow hd; omega
  have hlt := two_mul_thirteen_pow_lt w
  obtain ⟨A, hA⟩ : ∃ A, A = 13 ^ w := ⟨_, rfl⟩
  rw [← hA] at hBA h h13 hlt
  obtain ⟨D, rfl⟩ : ∃ D, A = B + D := ⟨A - B, by omega⟩
  have e : (B + D) ^ 2 - B ^ 2 = D * (2 * B + D) := by
    have : (B + D) ^ 2 = B ^ 2 + D * (2 * B + D) := by ring
    omega
  rw [e] at h
  have hle : 5 ^ x ≤ 2 * B + D := by
    rcases prime_pow_dvd_or Nat.prime_five h (by rintro ⟨h1, h2⟩; omega) with h1 | h1
    · exact (Nat.le_of_dvd (by omega) h1).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h1
  have h5 : 5 ^ x < 5 ^ (2 * w + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5
  omega

/-- If `4^y ∣ (13^w)² - B²` with `B ≡ 1 (mod 4)` and `B < 13^w`, then `y ≤ 2w`. -/
theorem four_pow_dvd_sq_sub {y w B : ℕ} (hB : B % 4 = 1) (hBA : B < 13 ^ w)
    (h : 4 ^ y ∣ (13 ^ w) ^ 2 - B ^ 2) : y ≤ 2 * w := by
  have h4 := thirteen_pow_mod_four w
  have h16 : 13 ^ w ≤ 2 ^ (4 * w) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) w
  obtain ⟨A, hA⟩ : ∃ A, A = 13 ^ w := ⟨_, rfl⟩
  rw [← hA] at hBA h h4 h16
  obtain ⟨D, rfl⟩ : ∃ D, A = B + D := ⟨A - B, by omega⟩
  obtain ⟨E, hE, hEodd⟩ : ∃ E, 2 * B + D = 2 * E ∧ E % 2 = 1 :=
    ⟨B + D / 2, by omega, by omega⟩
  have e : (B + D) ^ 2 - B ^ 2 = 2 * (D * E) := by
    have h1 : (B + D) ^ 2 = B ^ 2 + D * (2 * B + D) := by ring
    rw [hE] at h1
    have h2 : D * (2 * E) = 2 * (D * E) := by ring
    omega
  rw [e] at h
  by_contra hlt
  have h1 : 2 * 2 ^ (4 * w + 1) ∣ 2 * (D * E) := by
    have e2 : 2 * 2 ^ (4 * w + 1) = 4 ^ (2 * w + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
    rw [e2]; exact (pow_dvd_pow 4 (by omega)).trans h
  have h2 : 2 ^ (4 * w + 1) ∣ D * E := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hc : Nat.Coprime (2 ^ (4 * w + 1)) E :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  have h3 := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h2)
  have h5 : 2 ^ (4 * w + 1) = 2 * 2 ^ (4 * w) := by ring
  omega

theorem coprime_four_of_not_two_dvd {m : ℕ} (h : ¬ 2 ∣ m) : Nat.Coprime m 4 := by
  have : Nat.Coprime m (2 ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h).symm
  simpa using this

theorem coprime_three_of_not_three_dvd {m : ℕ} (h : ¬ 3 ∣ m) : Nat.Coprime m 3 :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm

/-- Case `y ≤ z < x` for `(5, 12, 13)` (after cancelling `n^y`); `z = y + b`, `x = z + a`. -/
theorem no_solution_5_12_13_y_le_z_lt_x {n y a b : ℕ} (hn : 1 < n) (hy : 0 < y) (ha : 0 < a)
    (h : 5 ^ (y + b + a) * n ^ (b + a) + 12 ^ y = 13 ^ (y + b) * n ^ b) : False := by
  obtain ⟨t, ht⟩ : ∃ t, y + b + a = t + 1 := ⟨y + b + a - 1, by omega⟩
  have h5x : 5 ^ (y + b + a) = 5 * 5 ^ t := by rw [ht]; ring
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- `y = z`
    simp only [add_zero, pow_zero, mul_one, zero_add] at h h5x
    have h12 : 12 ^ y % 5 = 2 ^ y % 5 := by rw [Nat.pow_mod]
    have h13 := thirteen_pow_mod_five y
    have h2 := two_pow_mod_five y
    have hmod : 12 ^ y % 5 = 13 ^ y % 5 := by
      rw [← h, h5x, mul_assoc, Nat.mul_add_mod]
    have hye : y % 2 = 0 := by omega
    obtain ⟨w, rfl⟩ : ∃ w, y = 2 * w := ⟨y / 2, by omega⟩
    have hd : 5 ^ (2 * w + a) ∣ (13 ^ w) ^ 2 - (12 ^ w) ^ 2 :=
      ⟨n ^ a, by rw [← pow_mul', ← pow_mul']; omega⟩
    have := five_pow_dvd_sq_sub (Nat.pow_lt_pow_left (by norm_num) (by omega)) hd
    omega
  have hnb : n ^ b ∣ 12 ^ y := by
    have h1 : n ^ b ∣ 5 ^ (y + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 5 ^ (y + b + a) * n ^ (b + a) + 12 ^ y := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_right h1).1 h2
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ b := by positivity
  have h' : 5 ^ (y + b + a) * n ^ a + q = 13 ^ (y + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (13 ^ (y + b)), ← h]; ring
  have hnpow : 1 < n ^ b := Nat.one_lt_pow (by omega) hn
  have hna : ∀ p, p ∣ n → p ∣ 5 ^ (y + b + a) * n ^ a := fun p hp =>
    Dvd.dvd.mul_left (hp.trans (dvd_pow_self n (by omega))) _
  have h2qn : 2 ∣ q → ¬ 2 ∣ n := fun h2q h2n => by
    have h1 : 2 ∣ 13 ^ (y + b) := by rw [← h']; exact dvd_add (hna 2 h2n) h2q
    have := Nat.prime_two.dvd_of_dvd_pow h1; omega
  have h3qn : 3 ∣ q → ¬ 3 ∣ n := fun h3q h3n => by
    have h1 : 3 ∣ 13 ^ (y + b) := by rw [← h']; exact dvd_add (hna 3 h3n) h3q
    have := Nat.prime_three.dvd_of_dvd_pow h1; omega
  have e12 : 12 ^ y = 4 ^ y * 3 ^ y := by rw [← mul_pow]; norm_num
  have hmod5 : q % 5 = 13 ^ (y + b) % 5 := by
    rw [← h', h5x, mul_assoc, Nat.mul_add_mod]
  have h13 := thirteen_pow_mod_five (y + b)
  have hprodpos : 0 < 5 ^ (y + b + a) * n ^ a := by positivity
  -- conclusion once `z = y + b` is even and `q` is a square
  have hfin : ∀ w B, y + b = 2 * w → q = B ^ 2 → False := by
    intro w B hw hB
    have hd : 5 ^ (y + b + a) ∣ (13 ^ w) ^ 2 - B ^ 2 :=
      ⟨n ^ a, by rw [← pow_mul', ← hw, ← hB]; omega⟩
    have hBA : B < 13 ^ w := by
      by_contra hle
      have h1 : (13 ^ w) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [← pow_mul', ← hw, ← hB] at h1
      omega
    have := five_pow_dvd_sq_sub hBA hd
    omega
  have hq12 : q ∣ 4 ^ y * 3 ^ y := by rw [← e12, hq]; exact Dvd.intro_left _ rfl
  have hn12 : n ^ b ∣ 4 ^ y * 3 ^ y := by rw [← e12, hq]; exact Dvd.intro _ rfl
  by_cases h2q : 2 ∣ q <;> by_cases h3q : 3 ∣ q
  · -- `n` coprime to `12`: `n = 1`
    have hc : Nat.Coprime n 12 := by
      have := (coprime_four_of_not_two_dvd (h2qn h2q)).mul_right
        (coprime_three_of_not_three_dvd (h3qn h3q))
      simpa using this
    have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow b y hc) (Dvd.intro _ hq.symm)
    omega
  · -- `q = 4^y`
    have h4q : 4 ^ y ∣ q := by
      have hc : Nat.Coprime (4 ^ y) (n ^ b) :=
        (Nat.Coprime.pow b y (coprime_four_of_not_two_dvd (h2qn h2q))).symm
      exact hc.dvd_of_dvd_mul_left (by rw [← hq, e12]; exact Dvd.intro _ rfl)
    have hq4 : q ∣ 4 ^ y :=
      (Nat.Coprime.pow_right y (coprime_three_of_not_three_dvd h3q)).dvd_of_dvd_mul_right hq12
    have hqe : q = 4 ^ y := Nat.dvd_antisymm hq4 h4q
    have h4 := four_pow_mod_five y
    rw [hqe] at hmod5
    refine hfin ((y + b) / 2) (2 ^ y) (by omega) ?_
    rw [hqe, ← pow_mul', pow_mul]; norm_num
  · -- `q = 3^y`, `n^b = 4^y`
    have h3q' : 3 ^ y ∣ q := by
      have hc : Nat.Coprime (3 ^ y) (n ^ b) :=
        (Nat.Coprime.pow b y (coprime_three_of_not_three_dvd (h3qn h3q))).symm
      exact hc.dvd_of_dvd_mul_left (by rw [← hq, e12]; exact Dvd.intro_left _ rfl)
    have hq3 : q ∣ 3 ^ y :=
      (Nat.Coprime.pow_right y (coprime_four_of_not_two_dvd h2q)).dvd_of_dvd_mul_left hq12
    have hqe : q = 3 ^ y := Nat.dvd_antisymm hq3 h3q'
    have hnb4 : n ^ b = 4 ^ y := by
      have h3pos : 0 < 3 ^ y := by positivity
      apply Nat.eq_of_mul_eq_mul_right h3pos
      rw [← e12, hq, hqe]
    have h3 := three_pow_mod_five y
    rw [hqe] at hmod5
    rcases Nat.mod_two_eq_zero_or_one y with hye | hyo
    · obtain ⟨u, rfl⟩ : ∃ u, y = 2 * u := ⟨y / 2, by omega⟩
      exact hfin ((2 * u + b) / 2) (3 ^ u) (by omega) (by rw [hqe, pow_mul'])
    · -- `y` odd: then `a = 1`, `n = 2`, `b = 2y`, and a contradiction mod 3
      obtain ⟨j, rfl⟩ : ∃ j, y = 2 * j + 1 := ⟨y / 2, by omega⟩
      have h2n : 2 ∣ n := by
        have h1 : 2 ∣ n ^ b := by
          rw [hnb4]; exact Dvd.dvd.pow (by norm_num) (by omega)
        exact Nat.prime_two.dvd_of_dvd_pow h1
      have hq4 : q % 4 = 3 := by rw [hqe]; exact three_pow_mod_four_odd j
      have hz4 := thirteen_pow_mod_four (2 * j + 1 + b)
      have hm : (5 ^ (2 * j + 1 + b + a) * n ^ a) % 4 = 2 := by omega
      have ha1 : a = 1 := by
        by_contra hne
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
        obtain ⟨m, rfl⟩ := h2n
        have e : 5 ^ (2 * j + 1 + b + (a' + 2)) * (2 * m) ^ (a' + 2)
            = 4 * (5 ^ (2 * j + 1 + b + (a' + 2)) * (m ^ 2 * (2 * m) ^ a')) := by ring
        omega
      subst ha1
      have hn4 : n % 4 = 2 := by
        rw [pow_one, Nat.mul_mod, five_pow_mod_four, one_mul, Nat.mod_mod] at hm
        exact hm
      have hn2 : n = 2 := by
        have h1 : n ∣ 2 ^ (2 * (2 * j + 1)) := by
          have : (4 : ℕ) ^ (2 * j + 1) = 2 ^ (2 * (2 * j + 1)) := by rw [pow_mul]; norm_num
          rw [← this, ← hnb4]; exact dvd_pow_self n (by omega)
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · interval_cases k
          · omega
          · simpa using hk
        · exfalso
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
          have : 2 ^ (k' + 2) = 4 * 2 ^ k' := by ring
          omega
      subst hn2
      have hb2 : b = 2 * (2 * j + 1) := by
        have : (4 : ℕ) ^ (2 * j + 1) = 2 ^ (2 * (2 * j + 1)) := by rw [pow_mul]; norm_num
        rw [this] at hnb4
        exact Nat.pow_right_injective (le_refl 2) hnb4
      subst hb2
      have hA : 5 ^ (2 * j + 1 + 2 * (2 * j + 1) + 1) % 3 = 1 := by
        rw [show 2 * j + 1 + 2 * (2 * j + 1) + 1 = 2 * (3 * j + 2) by ring, pow_mul,
          Nat.pow_mod]
        norm_num
      have hC := thirteen_pow_mod_three (2 * j + 1 + 2 * (2 * j + 1))
      have hB : (3 : ℕ) ^ (2 * j + 1) = 3 * 3 ^ (2 * j) := by ring
      rw [hqe, pow_one] at h'
      clear * - hA hB hC h'
      omega
  · -- `q = 1`
    have hc : Nat.Coprime q 12 := by
      have := (coprime_four_of_not_two_dvd h2q).mul_right (coprime_three_of_not_three_dvd h3q)
      simpa using this
    have hq1 : q = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right y hc) (Dvd.intro_left _ hq.symm)
    rw [hq1] at hmod5
    exact hfin ((y + b) / 2) 1 (by omega) (by rw [hq1]; norm_num)

/-- Case `x ≤ z < y` for `(5, 12, 13)` (after cancelling `n^x`); `z = x + b`, `y = z + a`. -/
theorem no_solution_5_12_13_x_le_z_lt_y {n x a b : ℕ} (hn : 1 < n) (hx : 0 < x) (ha : 0 < a)
    (h : 5 ^ x + 12 ^ (x + b + a) * n ^ (b + a) = 13 ^ (x + b) * n ^ b) : False := by
  have e12 : ∀ m, 12 ^ m = 4 ^ m * 3 ^ m := fun m => by rw [← mul_pow]; norm_num
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- `x = z`
    simp only [add_zero, pow_zero, mul_one, zero_add] at h
    have hxe : x % 2 = 0 := by
      by_contra hxo
      obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
      have h1 := five_pow_mod_three_odd k
      have h2 := thirteen_pow_mod_three (2 * k + 1)
      have h3 : 12 ^ (2 * k + 1 + a) * n ^ a = 3 * (4 * 12 ^ (2 * k + a) * n ^ a) := by ring
      omega
    obtain ⟨w, rfl⟩ : ∃ w, x = 2 * w := ⟨x / 2, by omega⟩
    have hd : 4 ^ (2 * w + a) ∣ (13 ^ w) ^ 2 - (5 ^ w) ^ 2 :=
      ⟨3 ^ (2 * w + a) * n ^ a, by rw [← pow_mul', ← pow_mul', ← mul_assoc, ← e12]; omega⟩
    have := four_pow_dvd_sq_sub (five_pow_mod_four w)
      (Nat.pow_lt_pow_left (by norm_num) (by omega)) hd
    omega
  have hnb : n ^ b ∣ 5 ^ x := by
    have h1 : n ^ b ∣ 12 ^ (x + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 5 ^ x + 12 ^ (x + b + a) * n ^ (b + a) := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_left h1).1 h2
  have hn5 : n ∣ 5 ^ x := (dvd_pow_self n (by omega)).trans hnb
  have h5n : 5 ∣ n := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hn5
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at hk; omega
    · rw [hk]; exact dvd_pow_self 5 (by omega)
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ b := by positivity
  have h' : q + 12 ^ (x + b + a) * n ^ a = 13 ^ (x + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (13 ^ (x + b)), ← h]; ring
  have hq1 : q = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (Dvd.intro_left _ hq.symm)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hj
    · exfalso
      have h1 : 5 ∣ q := by rw [hj]; exact dvd_pow_self 5 (by omega)
      have h2 : 5 ∣ 12 ^ (x + b + a) * n ^ a :=
        Dvd.dvd.mul_left (h5n.trans (dvd_pow_self n (by omega))) _
      have h3 : 5 ∣ 13 ^ (x + b) := by rw [← h']; exact dvd_add h1 h2
      have := Nat.prime_five.dvd_of_dvd_pow h3; omega
  subst hq1
  have hze : (x + b) % 2 = 0 := by
    by_contra hzo
    have h1 := (thirteen_pow_mod_eight (x + b)).2 (by omega)
    obtain ⟨t, ht⟩ : ∃ t, x + b + a = t + 2 := ⟨x + b + a - 2, by omega⟩
    have h2 : 12 ^ (x + b + a) * n ^ a = 8 * (18 * 12 ^ t * n ^ a) := by rw [ht]; ring
    omega
  obtain ⟨w, hw⟩ : ∃ w, x + b = 2 * w := ⟨(x + b) / 2, by omega⟩
  have hd : 4 ^ (x + b + a) ∣ (13 ^ w) ^ 2 - 1 ^ 2 :=
    ⟨3 ^ (x + b + a) * n ^ a, by rw [← pow_mul', ← hw, ← mul_assoc, ← e12]; omega⟩
  have hBA : 1 < 13 ^ w := Nat.one_lt_pow (by omega) (by norm_num)
  have := four_pow_dvd_sq_sub (B := 1) (by norm_num) hBA hd
  omega

/-- **Deng–Cohen (1998), re-formalized.** Jeśmanowicz' conjecture holds for the triple
`(5, 12, 13)` and every `n ≥ 1`. -/
theorem jesmanowiczFor_5_12_13 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 5 12 13 n := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  swap
  · obtain rfl : n = 1 := by omega
    exact jesmanowiczFor_5_12_13_one
  intro x y z hs
  by_cases hxz : x ≤ z
  · by_cases hyz : y ≤ z
    · exact hs.eq_two_of_le isPrimitivePythagorean_5_12_13 hn hxz hyz
    · -- `x ≤ z < y`
      exfalso
      obtain ⟨hx, hy, hz, heq⟩ := hs
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hxz
      obtain ⟨a, rfl⟩ : ∃ a, y = x + b + a := ⟨y - (x + b), by omega⟩
      refine no_solution_5_12_13_x_le_z_lt_y (n := n) (x := x) (a := a) (b := b) hn1 hx
        (by omega) ?_
      apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ x by positivity)
      calc n ^ x * (5 ^ x + 12 ^ (x + b + a) * n ^ (b + a))
          = (5 * n) ^ x + (12 * n) ^ (x + b + a) := by ring
        _ = (13 * n) ^ (x + b) := heq
        _ = n ^ x * (13 ^ (x + b) * n ^ b) := by ring
  · exfalso
    by_cases hyz : y ≤ z
    · -- `y ≤ z < x`
      obtain ⟨hx, hy, hz, heq⟩ := hs
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hyz
      obtain ⟨a, rfl⟩ : ∃ a, x = y + b + a := ⟨x - (y + b), by omega⟩
      refine no_solution_5_12_13_y_le_z_lt_x (n := n) (y := y) (a := a) (b := b) hn1 hy
        (by omega) ?_
      apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ y by positivity)
      calc n ^ y * (5 ^ (y + b + a) * n ^ (b + a) + 12 ^ y)
          = (5 * n) ^ (y + b + a) + (12 * n) ^ y := by ring
        _ = (13 * n) ^ (y + b) := heq
        _ = n ^ y * (13 ^ (y + b) * n ^ b) := by ring
    · -- `z < x`, `z < y`: then `x = y` and `5^x + 12^x` is a power of `13`
      have hxy := hs.eq_of_z_lt isPrimitivePythagorean_5_12_13 hn1 (by omega) (by omega)
      subst hxy
      have hz2 := hs.two_le_z isPrimitivePythagorean_5_12_13 hn
      have hc := hs.cancel hn (by omega) (by omega)
      obtain ⟨hx, -, hz, -⟩ := hs
      have hfac : (5 ^ x + 12 ^ x) * n ^ (x - z) = 13 ^ z := by rw [← hc]; ring
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 13)).1 (Dvd.intro _ hfac)
      have h5pos : 0 < 5 ^ x := by positivity
      have h12pos : 0 < 12 ^ x := by positivity
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp at hj; omega
      · have := jesmanowicz_5_12_13 hx hx hjpos hj
        omega

/-- The same for the swapped triple `(12, 5, 13)`. -/
theorem jesmanowiczFor_12_5_13 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 12 5 13 n :=
  jesmanowiczFor_swap.1 (jesmanowiczFor_5_12_13 n hn)

/-! ### The general reduction for `n > 1`, completed: `z < min x y` is impossible -/

/-- A prime dividing the hypotenuse of a primitive triple does not divide the leg `a`. -/
theorem IsPrimitivePythagorean.not_dvd_left {a b c p : ℕ} (h : IsPrimitivePythagorean a b c)
    (hpp : p.Prime) (hpc : p ∣ c) : ¬ p ∣ a := by
  obtain ⟨-, -, -, hcop, hp⟩ := h
  intro hpa
  have hpb : p ∣ b := by
    have h1 : p ∣ a ^ 2 := Dvd.dvd.pow hpa (by norm_num)
    have h2 : p ∣ a ^ 2 + b ^ 2 := by rw [hp]; exact Dvd.dvd.pow hpc (by norm_num)
    exact hpp.dvd_of_dvd_pow ((Nat.dvd_add_right h1).1 h2)
  have := Nat.dvd_gcd hpa hpb
  rw [hcop] at this
  exact hpp.one_lt.ne' (Nat.dvd_one.1 this)

/-- For a primitive triple and an exponent `x ≠ 2`, `a^x + b^x` has a prime factor not
dividing `c`; equivalently it divides no power of `c`. -/
theorem pow_add_pow_not_dvd {a b c x m : ℕ} (h : IsPrimitivePythagorean a b c)
    (hx : 0 < x) (hx2 : x ≠ 2) : ¬ a ^ x + b ^ x ∣ c ^ m := by
  intro hdvd
  have hcodd := h.c_odd
  have ha2 := h.two_le_left
  have hb2 := h.two_le_right
  have hnl := fun p hpp hpc => h.not_dvd_left (p := p) hpp hpc
  have hnr := fun p hpp hpc => (isPrimitivePythagorean_swap.1 h).not_dvd_left (p := p) hpp hpc
  obtain ⟨-, -, hc, -, hp⟩ := h
  have hp2 : ∀ p, p.Prime → p ∣ c → p ≠ 2 := by rintro p hpp hpc rfl; omega
  have hNc : ∀ p, p.Prime → p ∣ a ^ x + b ^ x → p ∣ c := fun p hpp hpN =>
    hpp.dvd_of_dvd_pow (hpN.trans hdvd)
  rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
  swap
  · -- `x` odd: `a + b ∣ a^x + b^x`, but `a + b` is coprime to `c`
    have h1 : a + b ∣ a ^ x + b ^ x := Odd.nat_add_dvd_pow_add_pow a b (Nat.odd_iff.2 hxo)
    obtain ⟨p, hpp, hpab⟩ := Nat.exists_prime_and_dvd (show a + b ≠ 1 by omega)
    have hpc := hNc p hpp (hpab.trans h1)
    have h2 : p ∣ c ^ 2 + 2 * a * b := by
      have : c ^ 2 + 2 * a * b = (a + b) * (a + b) := by rw [← hp]; ring
      rw [this]; exact Dvd.dvd.mul_right hpab _
    have h3 : p ∣ 2 * a * b := (Nat.dvd_add_right (Dvd.dvd.pow hpc (by norm_num))).1 h2
    rcases (hpp.dvd_mul).1 h3 with h4 | h4
    · rcases (hpp.dvd_mul).1 h4 with h5 | h5
      · exact hp2 p hpp hpc ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h5)
      · exact hnl p hpp hpc h5
    · exact hnr p hpp hpc h4
  obtain ⟨t, rfl⟩ : ∃ t, x = 2 * t := ⟨x / 2, by omega⟩
  have hupos : 0 < a ^ 2 := pow_pos (by omega) 2
  have hvpos : 0 < b ^ 2 := pow_pos (by omega) 2
  have hN1 : a ^ (2 * t) + b ^ (2 * t) ≠ 1 := by
    have h1 : 0 < a ^ (2 * t) := pow_pos (by omega) _
    have h2 : 0 < b ^ (2 * t) := pow_pos (by omega) _
    omega
  rcases Nat.mod_two_eq_zero_or_one t with hte | hto
  · -- `x ≡ 0 (mod 4)`: `a^x + b^x ≡ 2 a^x` modulo any prime dividing `c`
    obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s := ⟨t / 2, by omega⟩
    obtain ⟨p, hpp, hpN⟩ := Nat.exists_prime_and_dvd hN1
    have hpc := hNc p hpp hpN
    have hpuv : (p : ℤ) ∣ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
      have : p ∣ a ^ 2 + b ^ 2 := by rw [hp]; exact Dvd.dvd.pow hpc (by norm_num)
      exact_mod_cast this
    have h1 : (p : ℤ) ∣ ((a : ℤ) ^ 2) ^ (2 * s) - ((b : ℤ) ^ 2) ^ (2 * s) := by
      have h2 : ((a : ℤ) ^ 2) ^ 2 - ((b : ℤ) ^ 2) ^ 2
          ∣ (((a : ℤ) ^ 2) ^ 2) ^ s - (((b : ℤ) ^ 2) ^ 2) ^ s := sub_dvd_pow_sub_pow _ _ s
      have e3 : (((a : ℤ) ^ 2) ^ 2) ^ s - (((b : ℤ) ^ 2) ^ 2) ^ s
          = ((a : ℤ) ^ 2) ^ (2 * s) - ((b : ℤ) ^ 2) ^ (2 * s) := by ring
      rw [e3] at h2
      exact (hpuv.trans ⟨(a : ℤ) ^ 2 - (b : ℤ) ^ 2, by ring⟩).trans h2
    have h2 : (p : ℤ) ∣ ((a : ℤ) ^ 2) ^ (2 * s) + ((b : ℤ) ^ 2) ^ (2 * s) := by
      have e : ((a : ℤ) ^ 2) ^ (2 * s) + ((b : ℤ) ^ 2) ^ (2 * s)
          = ((a ^ (2 * (2 * s)) + b ^ (2 * (2 * s)) : ℕ) : ℤ) := by
        push_cast; rw [← pow_mul, ← pow_mul]
      rw [e]; exact_mod_cast hpN
    have h3 : (p : ℤ) ∣ ((2 * (a ^ 2) ^ (2 * s) : ℕ) : ℤ) := by
      have := dvd_add h1 h2
      push_cast
      convert this using 1; ring
    have h4 : p ∣ 2 * (a ^ 2) ^ (2 * s) := by exact_mod_cast h3
    rcases (hpp.dvd_mul).1 h4 with h5 | h5
    · exact hp2 p hpp hpc ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h5)
    · exact hnl p hpp hpc (hpp.dvd_of_dvd_pow (hpp.dvd_of_dvd_pow h5))
  · -- `x = 2t`, `t ≥ 3` odd: lifting the exponent gives `a^x + b^x ∣ c² t`, too small
    have ht3 : 3 ≤ t := by omega
    have hodd : Odd t := Nat.odd_iff.2 hto
    rw [pow_mul, pow_mul] at hdvd hNc
    have hNne : (a ^ 2) ^ t + (b ^ 2) ^ t ≠ 0 := by
      have h1 : 0 < (a ^ 2) ^ t := pow_pos hupos _
      omega
    have hdvd2 : (a ^ 2) ^ t + (b ^ 2) ^ t ∣ (a ^ 2 + b ^ 2) * t := by
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro p k hpp hpk
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      have hpN : p ∣ (a ^ 2) ^ t + (b ^ 2) ^ t := (dvd_pow_self p (by omega)).trans hpk
      have hpc := hNc p hpp hpN
      have : Fact p.Prime := ⟨hpp⟩
      have hpodd : Odd p := hpp.odd_of_ne_two (hp2 p hpp hpc)
      have hpuv : p ∣ a ^ 2 + b ^ 2 := by rw [hp]; exact Dvd.dvd.pow hpc (by norm_num)
      have hpu : ¬ p ∣ a ^ 2 := fun hd => hnl p hpp hpc (hpp.dvd_of_dvd_pow hd)
      have hlte := Nat.multiplicity_pow_add_pow hpodd hpuv hpu hodd
      have hk' := (multiplicity_dvd_iff_le hNne).1 hpk
      rw [hlte] at hk'
      calc p ^ k ∣ p ^ (multiplicity p (a ^ 2 + b ^ 2) + multiplicity p t) := pow_dvd_pow p hk'
        _ = p ^ multiplicity p (a ^ 2 + b ^ 2) * p ^ multiplicity p t := pow_add _ _ _
        _ ∣ (a ^ 2 + b ^ 2) * t :=
          mul_dvd_mul (pow_multiplicity_dvd _ _) (pow_multiplicity_dvd _ _)
    have hle := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd2
    have key : ∀ w, 4 ≤ w → w * t < w ^ t := by
      intro w hw
      obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
      have h1 : 4 ^ r ≤ w ^ r := Nat.pow_le_pow_left hw r
      have h2 : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
      have h3 : 2 ^ (r + 1) ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : (2 : ℕ) ^ (2 * r) = 4 ^ r := by rw [pow_mul]; norm_num
      rw [pow_succ']
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have hu := key (a ^ 2) (by nlinarith)
    have hv := key (b ^ 2) (by nlinarith)
    rw [add_mul] at hle
    omega

/-- **Reduction for `n > 1`** (known in the literature, see the header). For a primitive
triple and `n > 1` there is no solution of `(a n)^x + (b n)^y = (c n)^z` with
`z < min x y`. -/
theorem IsSolution.not_z_lt_both {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 1 < n) (hs : IsSolution a b c n x y z) : ¬ (z < x ∧ z < y) := by
  rintro ⟨hzx, hzy⟩
  have hxy := hs.eq_of_z_lt h hn hzx hzy
  subst hxy
  have hz2 := hs.two_le_z h (by omega)
  have hc := hs.cancel (by omega) hzx.le hzx.le
  obtain ⟨hx, -, -, -⟩ := hs
  exact pow_add_pow_not_dvd h hx (by omega) (m := z) ⟨n ^ (x - z), by rw [← hc]; ring⟩

/-- Consequently, for `n > 1` every solution is `(2, 2, 2)`, or has `x ≤ z < y`, or has
`y ≤ z < x`. -/
theorem IsSolution.cases_of_one_lt {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 1 < n) (hs : IsSolution a b c n x y z) :
    (x = 2 ∧ y = 2 ∧ z = 2) ∨ (x ≤ z ∧ z < y) ∨ (y ≤ z ∧ z < x) := by
  have h1 := hs.not_z_lt_both h hn
  by_cases hxz : x ≤ z
  · by_cases hyz : y ≤ z
    · exact Or.inl (hs.eq_two_of_le h (by omega) hxz hyz)
    · exact Or.inr (Or.inl ⟨hxz, by omega⟩)
  · by_cases hyz : y ≤ z
    · exact Or.inr (Or.inr ⟨hyz, by omega⟩)
    · exact absurd ⟨by omega, by omega⟩ h1

/-! ### Axiom audit -/

#print axioms lu_core
#print axioms isPrimitivePythagorean_lu
#print axioms jesmanowiczFor_lu
#print axioms jesmanowiczFor_lu_swap
#print axioms jesmanowiczFor_15_8_17_one
#print axioms jesmanowiczFor_8_15_17_one
#print axioms jesmanowicz_7_24_25
#print axioms jesmanowiczFor_7_24_25_one
#print axioms jesmanowiczFor_24_7_25_one
#print axioms no_solution_z_lt_x_lt_y
#print axioms IsSolution.eq_of_z_lt
#print axioms pow_add_pow_not_dvd
#print axioms IsSolution.not_z_lt_both
#print axioms IsSolution.cases_of_one_lt
#print axioms five_pow_dvd_sq_sub
#print axioms four_pow_dvd_sq_sub
#print axioms no_solution_5_12_13_y_le_z_lt_x
#print axioms no_solution_5_12_13_x_le_z_lt_y
#print axioms jesmanowiczFor_5_12_13
#print axioms jesmanowiczFor_12_5_13

end Jesmanowicz
