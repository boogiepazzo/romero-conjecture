/-
# Jeśmanowicz' conjecture for the triple `(3, 4, 5)` and every `n ≥ 1`

STATUS: IN PROGRESS / NOT YET SOLVED

(The status line refers to Jeśmanowicz' conjecture as a whole, which is OPEN and
is NOT proved here; see `RomeroConjecture/Jesmanowicz.lean` for the statement
`Jesmanowicz.JesmanowiczConjecture`.)

## What IS proved in this file (machine-checked, no `sorry`, no extra axioms)

This file is a re-formalization of a KNOWN theorem, not a new result:

**Theorem (M.-J. Deng and G. L. Cohen, "On the conjecture of Jeśmanowicz concerning
Pythagorean triples", Bull. Austral. Math. Soc. 57 (1998), 515–524).**
For every `n ≥ 1` the only solution in positive integers of
`(3 n)^x + (4 n)^y = (5 n)^z` is `x = y = z = 2`.

* `jesmanowiczFor_3_4_5 (n) (hn : 0 < n) : JesmanowiczFor 3 4 5 n` — the theorem above.
* `jesmanowiczFor_4_3_5` — the same for the swapped triple `(4, 3, 5)`.

Auxiliary results (each fully proved):

* `three_pow_dvd_five_pow_sub` : if `c ∈ {1, 4}`, `z > 0` and `3^x ∣ 5^z - c^z` then `x ≤ z`
  (lifting-the-exponent for the prime `3`).
* `four_pow_dvd_five_pow_sub` : if `c ∈ {1, 3}`, `z > 0` and `4^y ∣ 5^z - c^z` then `y ≤ z`
  (lifting-the-exponent for the prime `2`).
* `no_solution_z_lt_both` : no `n > 0`, `z > 0`, `a, b > 0` with
  `3^(z+a) n^a + 4^(z+b) n^b = 5^z` (the case `z < min x y`).
* `no_solution_y_le_z_lt_x` : no `n, y, a > 0`, `b ≥ 0` with
  `3^(y+b+a) n^(b+a) + 4^y = 5^(y+b) n^b` (the case `y ≤ z < x`).
* `no_solution_x_le_z_lt_y` : no `n, x, a > 0`, `b ≥ 0` with
  `3^x + 4^(x+b+a) n^(b+a) = 5^(x+b) n^b` (the case `x ≤ z < y`).

## Proof outline

The proof is elementary and self-contained (we did not transcribe the argument of
Deng–Cohen; the case split by the relative size of `z` against `x, y` is the standard
one in the literature on the non-primitive case). Let `(3n)^x + (4n)^y = (5n)^z`.

* `x ≤ z` and `y ≤ z`: size argument (`IsSolution.eq_two_of_le`) gives `(2,2,2)`.
* `z < x`, `z < y`: cancel `n^z`. Then `n ∣ 5^z`, so `n = 1` (Sierpiński's theorem
  applies and gives `x = z = 2`, absurd) or `5 ∣ n`. If `x ≠ y`, factoring out the
  smaller power of `n` leaves a cofactor which is a power of `5` greater than `1`
  but is not divisible by `5`. If `x = y`, then `3^x + 4^x` is a power of `5`, so
  `x = 2` by Sierpiński, contradicting `2 ≤ z < x`.
* `y ≤ z < x`: cancel `n^y`. If `y = z` then `3^x ∣ 5^z - 4^z` with `x > z`. If
  `y < z` then `n^(z-y) ∣ 4^y`, `n` is `1` (Sierpiński) or even, the cofactor
  `q = 4^y / n^(z-y)` is a power of `2`, and parity forces `q = 1`; then
  `3^x ∣ 5^z - 1` with `x > z`. Both contradict `three_pow_dvd_five_pow_sub`.
* `x ≤ z < y`: symmetric, with `3` in place of `2`, ending in `4^y ∣ 5^z - 3^z` or
  `4^y ∣ 5^z - 1` with `y > z`, contradicting `four_pow_dvd_five_pow_sub`.

## What is NOT proved

* Jeśmanowicz' conjecture itself (OPEN).
* Any triple other than `(3, 4, 5)` / `(4, 3, 5)` for `n > 1`; in particular the
  case `(5, 12, 13)` with general `n` (also covered by Deng–Cohen's paper) is not
  formalized here.
-/
import RomeroConjecture.Jesmanowicz

namespace Jesmanowicz

/-! ### Auxiliary congruences -/

theorem five_pow_mod_eight (z : ℕ) :
    (z % 2 = 0 → 5 ^ z % 8 = 1) ∧ (z % 2 = 1 → 5 ^ z % 8 = 5) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem three_pow_mod_eight' (z : ℕ) :
    (z % 2 = 0 → 3 ^ z % 8 = 1) ∧ (z % 2 = 1 → 3 ^ z % 8 = 3) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- Upper bound for a multiplicity from a non-divisibility. -/
theorem multiplicity_le_of_not_dvd {p n k : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    (h : ¬ p ^ (k + 1) ∣ n) : multiplicity p n ≤ k := by
  by_contra hlt
  exact h ((multiplicity_dvd_iff_le hn).2 (by omega))

/-- `v_p(n) < n` for `n > 0`. -/
theorem multiplicity_lt_self {p n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) :
    multiplicity p n < n := by
  have h1 : p ^ multiplicity p n ≤ n := Nat.le_of_dvd hn (pow_multiplicity_dvd p n)
  have h2 : multiplicity p n < p ^ multiplicity p n := Nat.lt_pow_self hp.out.one_lt
  omega

/-! ### Two lifting-the-exponent bounds -/

/-- If `c ∈ {1, 4}`, `z > 0` and `3^x ∣ 5^z - c^z`, then `x ≤ z`. -/
theorem three_pow_dvd_five_pow_sub {c x z : ℕ} (hc : c = 1 ∨ c = 4) (hz : 0 < z)
    (h : 3 ^ x ∣ 5 ^ z - c ^ z) : x ≤ z := by
  have hc5 : c < 5 := by omega
  have hlt : c ^ z < 5 ^ z := Nat.pow_lt_pow_left hc5 (by omega)
  have hc3 : c ^ z % 3 = 1 := by
    rcases hc with rfl | rfl
    · simp
    · exact four_pow_mod_three z
  rcases Nat.mod_two_eq_zero_or_one z with hze | hzo
  · obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by omega⟩
    have hw : w ≠ 0 := by omega
    have hc2 : c ^ 2 < 25 := by rcases hc with rfl | rfl <;> norm_num
    have hdvd : 3 ∣ 25 - c ^ 2 := by rcases hc with rfl | rfl <;> norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hlte := Nat.multiplicity_pow_sub_pow (p := 3) (by decide) hc2 hdvd (by norm_num) hw
    have e : 5 ^ (2 * w) - c ^ (2 * w) = 25 ^ w - (c ^ 2) ^ w := by
      rw [pow_mul, pow_mul]; norm_num
    rw [e] at h
    have hne : 25 ^ w - (c ^ 2) ^ w ≠ 0 := by
      have := Nat.pow_lt_pow_left hc2 hw
      omega
    have hx := (multiplicity_dvd_iff_le hne).1 h
    have hv : multiplicity 3 (25 - c ^ 2) ≤ 2 := by
      apply multiplicity_le_of_not_dvd
      · rcases hc with rfl | rfl <;> norm_num
      · rcases hc with rfl | rfl <;> norm_num
    have hw' := multiplicity_lt_self (p := 3) (n := w) (by omega)
    omega
  · -- `z` odd: `5^z - c^z ≡ 1 (mod 3)`
    obtain ⟨k, rfl⟩ : ∃ k, z = 2 * k + 1 := ⟨z / 2, by omega⟩
    have h5 := five_pow_mod_three_odd k
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · omega
    · exfalso
      have h3 : 3 ∣ 5 ^ (2 * k + 1) - c ^ (2 * k + 1) :=
        (dvd_pow_self 3 (by omega)).trans h
      omega

/-- If `c ∈ {1, 3}`, `z > 0` and `4^y ∣ 5^z - c^z`, then `y ≤ z`. -/
theorem four_pow_dvd_five_pow_sub {c y z : ℕ} (hc : c = 1 ∨ c = 3) (hz : 0 < z)
    (h : 4 ^ y ∣ 5 ^ z - c ^ z) : y ≤ z := by
  have hc5 : c < 5 := by omega
  have hlt : c ^ z < 5 ^ z := Nat.pow_lt_pow_left hc5 (by omega)
  rcases Nat.mod_two_eq_zero_or_one z with hze | hzo
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : 2 ∣ 5 - c := by rcases hc with rfl | rfl <;> norm_num
    have hlte := Nat.multiplicity_pow_two_sub_pow hc5 hdvd (by norm_num) (n := z) (by omega)
      (Nat.even_iff.2 hze)
    have hne : 5 ^ z - c ^ z ≠ 0 := by omega
    have e : (4 : ℕ) ^ y = 2 ^ (2 * y) := by rw [pow_mul]; norm_num
    rw [e] at h
    have hy := (multiplicity_dvd_iff_le hne).1 h
    have hv : multiplicity 2 (5 + c) + multiplicity 2 (5 - c) ≤ 4 := by
      rcases hc with rfl | rfl
      · have h1 : multiplicity 2 (5 + 1) ≤ 1 :=
          multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
        have h2 : multiplicity 2 (5 - 1) ≤ 2 :=
          multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
        omega
      · have h1 : multiplicity 2 (5 + 3) ≤ 3 :=
          multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
        have h2 : multiplicity 2 (5 - 3) ≤ 1 :=
          multiplicity_le_of_not_dvd (by norm_num) (by norm_num)
        omega
    have hz' := multiplicity_lt_self (p := 2) (n := z) hz
    omega
  · -- `z` odd: `5^z - c^z ≡ 4` or `2 (mod 8)`
    have h5 := (five_pow_mod_eight z).2 hzo
    have hc8 : c ^ z % 8 = 1 ∨ c ^ z % 8 = 3 := by
      rcases hc with rfl | rfl
      · simp
      · exact Or.inr ((three_pow_mod_eight' z).2 hzo)
    by_contra hyz
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
    have h16 : 16 ∣ 5 ^ z - c ^ z :=
      (Dvd.intro (4 ^ y') (by ring)).trans h
    omega

/-! ### The three impossible configurations -/

/-- Case `z < x`, `z < y` (after cancelling `n^z`). -/
theorem no_solution_z_lt_both {n z a b : ℕ} (hn : 0 < n) (hz : 0 < z) (ha : 0 < a)
    (hb : 0 < b) (h : 3 ^ (z + a) * n ^ a + 4 ^ (z + b) * n ^ b = 5 ^ z) : False := by
  have hnd : n ∣ 5 ^ z := by
    rw [← h]
    exact Dvd.dvd.add (Dvd.dvd.mul_left (dvd_pow_self n (by omega)) _)
      (Dvd.dvd.mul_left (dvd_pow_self n (by omega)) _)
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hnd
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `n = 1`
    simp only [pow_zero, one_pow, mul_one] at h
    have := sierpinski_3_4_5 (by omega) (by omega) hz h
    omega
  have h5n : 5 ∣ 5 ^ k := dvd_pow_self 5 (by omega)
  have hpos : ∀ m : ℕ, 0 < (5 ^ k) ^ m := fun m => by positivity
  have h3 : ¬ 5 ∣ 3 ^ (z + a) := fun hd => by
    have := Nat.prime_five.dvd_of_dvd_pow hd
    omega
  have h4 : ¬ 5 ∣ 4 ^ (z + b) := fun hd => by
    have := Nat.prime_five.dvd_of_dvd_pow hd
    omega
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
    have hd : 0 < d := by omega
    have hfac : (5 ^ k) ^ a * (3 ^ (z + a) + 4 ^ (z + (a + d)) * (5 ^ k) ^ d) = 5 ^ z := by
      rw [← h]; ring
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (Dvd.intro_left _ hfac)
    have h3pos : 0 < 3 ^ (z + a) := by positivity
    have h4pos : 0 < 4 ^ (z + (a + d)) * (5 ^ k) ^ d := by positivity
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp at hj; omega
    · have hd5 : 5 ∣ 3 ^ (z + a) + 4 ^ (z + (a + d)) * (5 ^ k) ^ d := by
        rw [hj]; exact dvd_pow_self 5 (by omega)
      have hd5' : 5 ∣ 4 ^ (z + (a + d)) * (5 ^ k) ^ d :=
        Dvd.dvd.mul_left (h5n.trans (dvd_pow_self _ (by omega))) _
      exact h3 ((Nat.dvd_add_left hd5').1 hd5)
  · -- `a = b`: `3^x + 4^x` is a power of `5`
    have hfac : (5 ^ k) ^ a * (3 ^ (z + a) + 4 ^ (z + a)) = 5 ^ z := by
      rw [← h]; ring
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (Dvd.intro_left _ hfac)
    have h3pos : 0 < 3 ^ (z + a) := by positivity
    have h4pos : 0 < 4 ^ (z + a) := by positivity
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp at hj; omega
    · have hs := sierpinski_3_4_5 (by omega) (by omega) hjpos hj
      -- `z + a = 2`, so `z = a = 1`
      obtain ⟨rfl, rfl⟩ : z = 1 ∧ a = 1 := by omega
      rw [hs.2.2] at hj
      norm_num at hj hfac
      have : 1 ≤ 5 ^ k := Nat.one_le_pow _ _ (by norm_num)
      omega
  · obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
    have hd : 0 < d := by omega
    have hfac : (5 ^ k) ^ b * (3 ^ (z + (b + d)) * (5 ^ k) ^ d + 4 ^ (z + b)) = 5 ^ z := by
      rw [← h]; ring
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (Dvd.intro_left _ hfac)
    have h4pos : 0 < 4 ^ (z + b) := by positivity
    have h3pos : 0 < 3 ^ (z + (b + d)) * (5 ^ k) ^ d := by positivity
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp at hj; omega
    · have hd5 : 5 ∣ 3 ^ (z + (b + d)) * (5 ^ k) ^ d + 4 ^ (z + b) := by
        rw [hj]; exact dvd_pow_self 5 (by omega)
      have hd5' : 5 ∣ 3 ^ (z + (b + d)) * (5 ^ k) ^ d :=
        Dvd.dvd.mul_left (h5n.trans (dvd_pow_self _ (by omega))) _
      exact h4 ((Nat.dvd_add_right hd5').1 hd5)

/-- Case `y ≤ z < x` (after cancelling `n^y`); here `z = y + b`, `x = z + a`. -/
theorem no_solution_y_le_z_lt_x {n y a b : ℕ} (hn : 0 < n) (hy : 0 < y) (ha : 0 < a)
    (h : 3 ^ (y + b + a) * n ^ (b + a) + 4 ^ y = 5 ^ (y + b) * n ^ b) : False := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- `y = z`
    simp only [add_zero, pow_zero, mul_one, zero_add] at h
    have hd : 3 ^ (y + a) ∣ 5 ^ y - 4 ^ y := ⟨n ^ a, by omega⟩
    have := three_pow_dvd_five_pow_sub (Or.inr rfl) hy hd
    omega
  have hnb : n ^ b ∣ 4 ^ y := by
    have h1 : n ^ b ∣ 3 ^ (y + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 3 ^ (y + b + a) * n ^ (b + a) + 4 ^ y := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_right h1).1 h2
  have e4 : (4 : ℕ) ^ y = 2 ^ (2 * y) := by rw [pow_mul]; norm_num
  have hn2 : n ∣ 2 ^ (2 * y) := by
    rw [← e4]; exact (dvd_pow_self n (by omega)).trans hnb
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_pow, mul_one] at h
    have := sierpinski_3_4_5 (by omega) hy (by omega) h
    omega
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < (2 ^ k) ^ b := by positivity
  have h' : 3 ^ (y + b + a) * (2 ^ k) ^ a + q = 5 ^ (y + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (5 ^ (y + b)), ← h]; ring
  have hq2 : q ∣ 2 ^ (2 * y) := by rw [← e4, hq]; exact Dvd.intro_left _ rfl
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hq2
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `q = 1`
    have hd : 3 ^ (y + b + a) ∣ 5 ^ (y + b) - 1 ^ (y + b) :=
      ⟨(2 ^ k) ^ a, by rw [one_pow, ← h']; simp⟩
    have := three_pow_dvd_five_pow_sub (Or.inl rfl) (by omega) hd
    omega
  · -- parity
    have h2a : 2 ∣ 3 ^ (y + b + a) * (2 ^ k) ^ a :=
      Dvd.dvd.mul_left ((dvd_pow_self 2 (by omega)).trans (dvd_pow_self _ (by omega))) _
    have h2j : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    have h5 : 2 ∣ 5 ^ (y + b) := by rw [← h']; exact Dvd.dvd.add h2a h2j
    have := Nat.prime_two.dvd_of_dvd_pow h5
    omega

/-- Case `x ≤ z < y` (after cancelling `n^x`); here `z = x + b`, `y = z + a`. -/
theorem no_solution_x_le_z_lt_y {n x a b : ℕ} (hn : 0 < n) (hx : 0 < x) (ha : 0 < a)
    (h : 3 ^ x + 4 ^ (x + b + a) * n ^ (b + a) = 5 ^ (x + b) * n ^ b) : False := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- `x = z`
    simp only [add_zero, pow_zero, mul_one, zero_add] at h
    have hd : 4 ^ (x + a) ∣ 5 ^ x - 3 ^ x := ⟨n ^ a, by omega⟩
    have := four_pow_dvd_five_pow_sub (Or.inr rfl) hx hd
    omega
  have hnb : n ^ b ∣ 3 ^ x := by
    have h1 : n ^ b ∣ 4 ^ (x + b + a) * n ^ (b + a) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ b ∣ 3 ^ x + 4 ^ (x + b + a) * n ^ (b + a) := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_left h1).1 h2
  have hn3 : n ∣ 3 ^ x := (dvd_pow_self n (by omega)).trans hnb
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hn3
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_pow, mul_one] at h
    have := sierpinski_3_4_5 hx (by omega) (by omega) h
    omega
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < (3 ^ k) ^ b := by positivity
  have h' : q + 4 ^ (x + b + a) * (3 ^ k) ^ a = 5 ^ (x + b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (5 ^ (x + b)), ← h]; ring
  have hq3 : q ∣ 3 ^ x := by rw [hq]; exact Dvd.intro_left _ rfl
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hq3
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `q = 1`
    have hd : 4 ^ (x + b + a) ∣ 5 ^ (x + b) - 1 ^ (x + b) :=
      ⟨(3 ^ k) ^ a, by rw [one_pow, ← h']; simp⟩
    have := four_pow_dvd_five_pow_sub (Or.inl rfl) (by omega) hd
    omega
  · have h3a : 3 ∣ 4 ^ (x + b + a) * (3 ^ k) ^ a :=
      Dvd.dvd.mul_left ((dvd_pow_self 3 (by omega)).trans (dvd_pow_self _ (by omega))) _
    have h3j : 3 ∣ 3 ^ j := dvd_pow_self 3 (by omega)
    have h5 : 3 ∣ 5 ^ (x + b) := by rw [← h']; exact Dvd.dvd.add h3j h3a
    have := Nat.prime_three.dvd_of_dvd_pow h5
    omega

/-! ### The main theorem -/

/-- **Deng–Cohen (1998), re-formalized.** Jeśmanowicz' conjecture holds for the triple
`(3, 4, 5)` and every `n ≥ 1`: the only positive solution of
`(3 n)^x + (4 n)^y = (5 n)^z` is `x = y = z = 2`. -/
theorem jesmanowiczFor_3_4_5 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 3 4 5 n := by
  intro x y z hs
  by_cases hxz : x ≤ z
  · by_cases hyz : y ≤ z
    · exact hs.eq_two_of_le isPrimitivePythagorean_3_4_5 hn hxz hyz
    · -- `x ≤ z < y`
      exfalso
      obtain ⟨hx, hy, hz, heq⟩ := hs
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hxz
      obtain ⟨a, rfl⟩ : ∃ a, y = x + b + a := ⟨y - (x + b), by omega⟩
      refine no_solution_x_le_z_lt_y (n := n) (x := x) (a := a) (b := b) hn hx (by omega) ?_
      apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ x by positivity)
      calc n ^ x * (3 ^ x + 4 ^ (x + b + a) * n ^ (b + a))
          = (3 * n) ^ x + (4 * n) ^ (x + b + a) := by ring
        _ = (5 * n) ^ (x + b) := heq
        _ = n ^ x * (5 ^ (x + b) * n ^ b) := by ring
  · exfalso
    by_cases hyz : y ≤ z
    · -- `y ≤ z < x`
      obtain ⟨hx, hy, hz, heq⟩ := hs
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hyz
      obtain ⟨a, rfl⟩ : ∃ a, x = y + b + a := ⟨x - (y + b), by omega⟩
      refine no_solution_y_le_z_lt_x (n := n) (y := y) (a := a) (b := b) hn hy (by omega) ?_
      apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ y by positivity)
      calc n ^ y * (3 ^ (y + b + a) * n ^ (b + a) + 4 ^ y)
          = (3 * n) ^ (y + b + a) + (4 * n) ^ y := by ring
        _ = (5 * n) ^ (y + b) := heq
        _ = n ^ y * (5 ^ (y + b) * n ^ b) := by ring
    · -- `z < x`, `z < y`
      have hc := hs.cancel hn (by omega) (by omega)
      obtain ⟨hx, hy, hz, -⟩ := hs
      obtain ⟨a, rfl⟩ : ∃ a, x = z + a := ⟨x - z, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = z + b := ⟨y - z, by omega⟩
      simp only [Nat.add_sub_cancel_left] at hc
      exact no_solution_z_lt_both hn hz (by omega) (by omega) hc

/-- The same for the swapped triple `(4, 3, 5)`. -/
theorem jesmanowiczFor_4_3_5 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 4 3 5 n :=
  jesmanowiczFor_swap.1 (jesmanowiczFor_3_4_5 n hn)

/-! ### Axiom audit -/

#print axioms three_pow_dvd_five_pow_sub
#print axioms four_pow_dvd_five_pow_sub
#print axioms no_solution_z_lt_both
#print axioms no_solution_y_le_z_lt_x
#print axioms no_solution_x_le_z_lt_y
#print axioms jesmanowiczFor_3_4_5
#print axioms jesmanowiczFor_4_3_5

end Jesmanowicz
