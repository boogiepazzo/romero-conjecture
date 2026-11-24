import Mathlib

namespace Jesmanowicz

/-- `(a, b, c)` is a primitive Pythagorean triple of positive integers. -/
def IsPrimitivePythagorean (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ Nat.Coprime a b ∧ a ^ 2 + b ^ 2 = c ^ 2

/-- `(x, y, z)` is a positive integer solution of `(a n)^x + (b n)^y = (c n)^z`. -/
def IsSolution (a b c n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ (a * n) ^ x + (b * n) ^ y = (c * n) ^ z

/-- Jeśmanowicz' statement for one fixed triple `(a, b, c)` and one fixed `n`:
the only positive solution of `(a n)^x + (b n)^y = (c n)^z` is `x = y = z = 2`. -/
def JesmanowiczFor (a b c n : ℕ) : Prop :=
  ∀ x y z : ℕ, IsSolution a b c n x y z → x = 2 ∧ y = 2 ∧ z = 2

/-- **Jeśmanowicz' conjecture** (OPEN; stated, not proved). -/
def JesmanowiczConjecture : Prop :=
  ∀ a b c n : ℕ, IsPrimitivePythagorean a b c → 0 < n → JesmanowiczFor a b c n

/-! ### Basic facts -/

theorem isSolution_two_two_two {a b c : ℕ} (h : IsPrimitivePythagorean a b c) (n : ℕ) :
    IsSolution a b c n 2 2 2 := by
  obtain ⟨-, -, -, -, h⟩ := h
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [mul_pow, mul_pow, mul_pow, ← add_mul, h]

theorem isPrimitivePythagorean_swap {a b c : ℕ} :
    IsPrimitivePythagorean a b c ↔ IsPrimitivePythagorean b a c := by
  constructor <;> rintro ⟨h1, h2, h3, h4, h5⟩ <;>
    exact ⟨h2, h1, h3, h4.symm, by rw [add_comm]; exact h5⟩

theorem isSolution_swap {a b c n x y z : ℕ} :
    IsSolution a b c n x y z ↔ IsSolution b a c n y x z := by
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    exact ⟨h2, h1, h3, by rw [add_comm]; exact h4⟩

theorem jesmanowiczFor_swap {a b c n : ℕ} :
    JesmanowiczFor a b c n ↔ JesmanowiczFor b a c n := by
  constructor <;> intro h x y z hs <;>
    · obtain ⟨h1, h2, h3⟩ := h y x z (isSolution_swap.1 hs)
      exact ⟨h2, h1, h3⟩

/-! ### Parity of primitive triples -/

theorem sq_mod_four_of_even {a : ℕ} (h : a % 2 = 0) : a ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  have : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
  omega

theorem sq_mod_four_of_odd {a : ℕ} (h : a % 2 = 1) : a ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
  omega

/-- In a primitive Pythagorean triple the hypotenuse is odd. -/
theorem IsPrimitivePythagorean.c_odd {a b c : ℕ} (h : IsPrimitivePythagorean a b c) :
    c % 2 = 1 := by
  obtain ⟨-, -, -, hcop, h⟩ := h
  by_contra hc
  have hc4 := sq_mod_four_of_even (a := c) (by omega)
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb)
    rw [hcop] at this
    omega
  · have := sq_mod_four_of_even ha; have := sq_mod_four_of_odd hb; omega
  · have := sq_mod_four_of_odd ha; have := sq_mod_four_of_even hb; omega
  · have := sq_mod_four_of_odd ha; have := sq_mod_four_of_odd hb; omega

/-- In a primitive Pythagorean triple exactly one leg is even. -/
theorem IsPrimitivePythagorean.legs_parity {a b c : ℕ} (h : IsPrimitivePythagorean a b c) :
    (a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0) := by
  have hc := h.c_odd
  have hc4 := sq_mod_four_of_odd hc
  obtain ⟨-, -, -, hcop, h⟩ := h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have := sq_mod_four_of_even ha; have := sq_mod_four_of_even hb; omega
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · have := sq_mod_four_of_odd ha; have := sq_mod_four_of_odd hb; omega

/-- The even leg of a primitive Pythagorean triple is divisible by `4`. -/
theorem IsPrimitivePythagorean.four_dvd_of_even {a b c : ℕ}
    (h : IsPrimitivePythagorean a b c) (hb : b % 2 = 0) : 4 ∣ b := by
  have hc := h.c_odd
  have ha : a % 2 = 1 := by have := h.legs_parity; omega
  obtain ⟨-, -, -, -, h⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, b = 2 * l := ⟨b / 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, c = 2 * m + 1 := ⟨c / 2, by omega⟩
  have h1 : l ^ 2 + k * (k + 1) = m * (m + 1) := by nlinarith
  have hk : k * (k + 1) % 2 = 0 := (Nat.even_mul_succ_self k).two_dvd |> Nat.mod_eq_zero_of_dvd
  have hm : m * (m + 1) % 2 = 0 := (Nat.even_mul_succ_self m).two_dvd |> Nat.mod_eq_zero_of_dvd
  have hl : l % 2 = 0 := by
    by_contra hl
    have := sq_mod_four_of_odd (a := l) (by omega)
    omega
  omega

theorem IsPrimitivePythagorean.two_le_left {a b c : ℕ} (h : IsPrimitivePythagorean a b c) :
    2 ≤ a := by
  obtain ⟨ha, hb, hc, -, h⟩ := h
  by_contra hlt
  obtain rfl : a = 1 := by omega
  have hbc : b < c := by nlinarith
  nlinarith

theorem IsPrimitivePythagorean.two_le_right {a b c : ℕ} (h : IsPrimitivePythagorean a b c) :
    2 ≤ b :=
  (isPrimitivePythagorean_swap.1 h).two_le_left

/-! ### Size constraints on the exponents (valid for every `n ≥ 1`) -/

/-- Pure size lemma: if `A² + B² = C²` with `A, B ≥ 2` and `A^x + B^y = C^z`
with `x, y ≤ z`, then `x = y = z = 2`. -/
theorem exponents_of_le {A B C x y z : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B)
    (h : A ^ 2 + B ^ 2 = C ^ 2) (hx : 0 < x) (hy : 0 < y)
    (hxz : x ≤ z) (hyz : y ≤ z) (heq : A ^ x + B ^ y = C ^ z) :
    x = 2 ∧ y = 2 ∧ z = 2 := by
  have hAC : A < C := by nlinarith
  have hBC : B < C := by nlinarith
  rcases lt_trichotomy z 2 with hz | rfl | hz
  · obtain rfl : z = 1 := by omega
    obtain rfl : x = 1 := by omega
    obtain rfl : y = 1 := by omega
    simp only [pow_one] at heq
    nlinarith
  · have hx' : x = 1 ∨ x = 2 := by omega
    have hy' : y = 1 ∨ y = 2 := by omega
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · simp only [pow_one] at heq; nlinarith
    · simp only [pow_one] at heq; nlinarith
    · simp only [pow_one] at heq; nlinarith
    · exact ⟨rfl, rfl, rfl⟩
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, z = k + 1 + 2 := ⟨z - 3, by omega⟩
    have hA1 : A ^ x ≤ A ^ (k + 1 + 2) := Nat.pow_le_pow_right (by omega) hxz
    have hB1 : B ^ y ≤ B ^ (k + 1 + 2) := Nat.pow_le_pow_right (by omega) hyz
    have hA2 : A ^ (k + 1) < C ^ (k + 1) := Nat.pow_lt_pow_left hAC (by omega)
    have hB2 : B ^ (k + 1) < C ^ (k + 1) := Nat.pow_lt_pow_left hBC (by omega)
    have hA3 : A ^ (k + 1 + 2) < C ^ (k + 1) * A ^ 2 := by
      rw [pow_add]; exact Nat.mul_lt_mul_of_pos_right hA2 (by positivity)
    have hB3 : B ^ (k + 1 + 2) < C ^ (k + 1) * B ^ 2 := by
      rw [pow_add]; exact Nat.mul_lt_mul_of_pos_right hB2 (by positivity)
    have hC : C ^ (k + 1 + 2) = C ^ (k + 1) * A ^ 2 + C ^ (k + 1) * B ^ 2 := by
      rw [pow_add, ← h, mul_add]
    omega

/-- If `z ≥ max x y` in a solution, then the solution is `(2, 2, 2)`. -/
theorem IsSolution.eq_two_of_le {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 0 < n) (hs : IsSolution a b c n x y z) (hxz : x ≤ z) (hyz : y ≤ z) :
    x = 2 ∧ y = 2 ∧ z = 2 := by
  obtain ⟨hx, hy, -, heq⟩ := hs
  have ha := h.two_le_left
  have hb := h.two_le_right
  obtain ⟨-, -, -, -, hp⟩ := h
  refine exponents_of_le (A := a * n) (B := b * n) (C := c * n) ?_ ?_ ?_ hx hy hxz hyz heq
  · nlinarith
  · nlinarith
  · rw [mul_pow, mul_pow, mul_pow, ← add_mul, hp]

/-- In any solution other than `(2, 2, 2)` we have `z < max x y`. -/
theorem IsSolution.z_lt_max {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 0 < n) (hs : IsSolution a b c n x y z) (hne : ¬(x = 2 ∧ y = 2 ∧ z = 2)) :
    z < max x y := by
  by_contra hlt
  rw [not_lt, max_le_iff] at hlt
  exact hne (hs.eq_two_of_le h hn hlt.1 hlt.2)

/-- A solution with all three exponents equal has them equal to `2`
(the Fermat-type case is trivial here). -/
theorem IsSolution.eq_two_of_eq {a b c n x : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 0 < n) (hs : IsSolution a b c n x x x) : x = 2 :=
  (hs.eq_two_of_le h hn le_rfl le_rfl).1

/-- In every solution `z ≥ 2`. -/
theorem IsSolution.two_le_z {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 0 < n) (hs : IsSolution a b c n x y z) : 2 ≤ z := by
  obtain ⟨hx, hy, hz, heq⟩ := hs
  by_contra hlt
  obtain rfl : z = 1 := by omega
  have ha := h.two_le_left
  have hb := h.two_le_right
  obtain ⟨-, -, -, -, hp⟩ := h
  have hA : a * n ≤ (a * n) ^ x := Nat.le_self_pow (by omega) _
  have hB : b * n ≤ (b * n) ^ y := Nat.le_self_pow (by omega) _
  have hle : a * n + b * n ≤ c * n := by rw [pow_one] at heq; omega
  have : a + b ≤ c := by
    rw [← add_mul] at hle; exact Nat.le_of_mul_le_mul_right hle hn
  nlinarith

/-- Cancelling `n^z` when `z ≤ min x y`. -/
theorem IsSolution.cancel {a b c n x y z : ℕ} (hn : 0 < n)
    (hs : IsSolution a b c n x y z) (hzx : z ≤ x) (hzy : z ≤ y) :
    a ^ x * n ^ (x - z) + b ^ y * n ^ (y - z) = c ^ z := by
  obtain ⟨-, -, -, heq⟩ := hs
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hzx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hzy
  have hnz : 0 < n ^ z := by positivity
  apply Nat.eq_of_mul_eq_mul_right hnz
  rw [← mul_pow, ← heq, mul_pow, mul_pow]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- If `z < min x y` in a solution, then `n` divides `c ^ z`
(so every prime factor of `n` divides `c`). -/
theorem IsSolution.n_dvd_of_lt {a b c n x y z : ℕ} (hn : 0 < n)
    (hs : IsSolution a b c n x y z) (hzx : z < x) (hzy : z < y) : n ∣ c ^ z := by
  rw [← hs.cancel hn hzx.le hzy.le]
  exact Dvd.dvd.add (Dvd.dvd.mul_left (dvd_pow_self n (by omega)) _)
    (Dvd.dvd.mul_left (dvd_pow_self n (by omega)) _)

/-- For `n = 1`, the equation is `a^x + b^y = c^z`. -/
theorem isSolution_one {a b c x y z : ℕ} :
    IsSolution a b c 1 x y z ↔ 0 < x ∧ 0 < y ∧ 0 < z ∧ a ^ x + b ^ y = c ^ z := by
  simp [IsSolution]

/-! ### The classical case `(3, 4, 5)`, `n = 1` (Sierpiński 1956) -/

theorem isPrimitivePythagorean_3_4_5 : IsPrimitivePythagorean 3 4 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by norm_num⟩

theorem three_pow_mod_eight (u : ℕ) : 3 ^ u % 8 = 1 ∨ 3 ^ u % 8 = 3 := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem three_pow_mod_four_odd (k : ℕ) : 3 ^ (2 * k + 1) % 4 = 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : 3 ^ (2 * (k + 1) + 1) = 3 ^ (2 * k + 1) * 9 := by ring
    omega

theorem five_pow_mod_three_odd (k : ℕ) : 5 ^ (2 * k + 1) % 3 = 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : 5 ^ (2 * (k + 1) + 1) = 5 ^ (2 * k + 1) * 25 := by ring
    omega

theorem five_pow_mod_four (z : ℕ) : 5 ^ z % 4 = 1 := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem four_pow_mod_three (y : ℕ) : 4 ^ y % 3 = 1 := by
  induction y with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- Parity reduction (mod 3): in `3^x + 4^y = 5^z` with `x > 0`, `z` is even. -/
theorem z_even_3_4_5 {x y z : ℕ} (hx : 0 < x) (h : 3 ^ x + 4 ^ y = 5 ^ z) : z % 2 = 0 := by
  by_contra hz
  obtain ⟨k, rfl⟩ : ∃ k, z = 2 * k + 1 := ⟨z / 2, by omega⟩
  obtain ⟨x, rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  have h1 := five_pow_mod_three_odd k
  have h2 := four_pow_mod_three y
  have h3 : 3 ^ (x + 1) = 3 * 3 ^ x := by ring
  omega

/-- Parity reduction (mod 4): in `3^x + 4^y = 5^z` with `y > 0`, `x` is even. -/
theorem x_even_3_4_5 {x y z : ℕ} (hy : 0 < y) (h : 3 ^ x + 4 ^ y = 5 ^ z) : x % 2 = 0 := by
  by_contra hx
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have h1 := three_pow_mod_four_odd k
  have h2 := five_pow_mod_four z
  have h3 : 4 ^ (y + 1) = 4 * 4 ^ y := by ring
  omega

/-- **Sierpiński (1956).** The only positive integer solution of
`3^x + 4^y = 5^z` is `x = y = z = 2`. -/
theorem sierpinski_3_4_5 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 3 ^ x + 4 ^ y = 5 ^ z) : x = 2 ∧ y = 2 ∧ z = 2 := by
  have hze := z_even_3_4_5 hx h
  have hxe := x_even_3_4_5 hy h
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, x = 2 * u := ⟨x / 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  rw [pow_mul' 3, pow_mul' 5] at h
  -- parities of `A = 5^w` and `B = 3^u`
  have hAodd : 5 ^ w % 2 = 1 := by have := five_pow_mod_four w; omega
  have hB8 := three_pow_mod_eight u
  have h4pos : 0 < 4 ^ (y + 1) := by positivity
  have hBA : 3 ^ u < 5 ^ w := by
    by_contra hle
    have : (5 ^ w) ^ 2 ≤ (3 ^ u) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨d, hd⟩ : ∃ d, 5 ^ w = 3 ^ u + d := ⟨5 ^ w - 3 ^ u, by omega⟩
  have hdpos : 0 < d := by omega
  have hfac : d * (2 * 3 ^ u + d) = 2 ^ (2 * (y + 1)) := by
    rw [pow_mul]; norm_num; rw [hd] at h; nlinarith
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hfac)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hfac)
  have hij : i + j = 2 * (y + 1) := by
    rw [hj, hi, ← pow_add] at hfac
    exact Nat.pow_right_injective (le_refl 2) hfac
  have hltij : i < j := by
    have : 2 ^ i < 2 ^ j := by rw [← hi, ← hj]; omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  -- `i = 1`
  have hi1 : i = 1 := by
    rcases Nat.lt_or_ge i 2 with hlt | hge
    · interval_cases i
      · simp at hi; omega
      · rfl
    · exfalso
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have e1 : 2 ^ (i' + 2) = 4 * 2 ^ i' := by ring
      have e2 : 2 ^ (j' + 2) = 4 * 2 ^ j' := by ring
      omega
  subst hi1
  have hd2 : d = 2 := by simpa using hi
  subst hd2
  have hj' : j = 2 * y + 1 := by omega
  subst hj'
  have hB1 : 3 ^ u + 1 = 4 ^ y := by
    have : 2 ^ (2 * y + 1) = 2 * 4 ^ y := by rw [pow_succ, pow_mul]; norm_num; ring
    omega
  -- now `3^u + 1 = 4^y` and `5^w = 3^u + 2`
  have hy1 : y = 1 := by
    rcases Nat.lt_or_ge y 2 with hlt | hge
    · interval_cases y
      · simp at hB1
      · rfl
    · exfalso
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
      have : 4 ^ (y' + 2) = 16 * 4 ^ y' := by ring
      omega
  subst hy1
  have hu : u = 1 := by
    have : 3 ^ u = 3 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num)) this
  subst hu
  have hw : w = 1 := by
    have : 5 ^ w = 5 ^ 1 := by omega
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) this
  subst hw
  exact ⟨rfl, rfl, rfl⟩

/-- Jeśmanowicz' conjecture holds for the triple `(3, 4, 5)` with `n = 1`. -/
theorem jesmanowiczFor_3_4_5_one : JesmanowiczFor 3 4 5 1 := by
  intro x y z hs
  obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
  exact sierpinski_3_4_5 hx hy hz h

/-- The same for the swapped triple `(4, 3, 5)`. -/
theorem jesmanowiczFor_4_3_5_one : JesmanowiczFor 4 3 5 1 :=
  jesmanowiczFor_swap.1 jesmanowiczFor_3_4_5_one

/-! ### The case `(5, 12, 13)`, `n = 1` (Jeśmanowicz 1956) -/

theorem isPrimitivePythagorean_5_12_13 : IsPrimitivePythagorean 5 12 13 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by norm_num⟩

/-- If `d * s = P * Q` with `P ∣ d` and `Q ∣ s` then `d = P` and `s = Q`. -/
theorem eq_of_mul_eq_of_dvd {P Q d s : ℕ} (hP : 0 < P) (hQ : 0 < Q) (h : d * s = P * Q)
    (h1 : P ∣ d) (h2 : Q ∣ s) : d = P ∧ s = Q := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨k, rfl⟩ := h2
  have hmk : m * k = 1 := by
    have : P * Q * (m * k) = P * Q * 1 := by
      calc P * Q * (m * k) = P * m * (Q * k) := by ring
        _ = P * Q * 1 := by rw [h, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  obtain ⟨rfl, rfl⟩ : m = 1 ∧ k = 1 := by simpa using hmk
  simp

/-- A prime power dividing `d * s`, where the prime does not divide both factors,
divides one of the factors. -/
theorem prime_pow_dvd_or {p e d s : ℕ} (hp : p.Prime) (h : p ^ e ∣ d * s)
    (hnot : ¬(p ∣ d ∧ p ∣ s)) : p ^ e ∣ d ∨ p ^ e ∣ s := by
  by_cases hd : p ∣ d
  · have hs : ¬ p ∣ s := fun hs => hnot ⟨hd, hs⟩
    exact Or.inl ((Nat.Coprime.pow_left e
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hs)).dvd_of_dvd_mul_right h)
  · exact Or.inr ((Nat.Coprime.pow_left e
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hd)).dvd_of_dvd_mul_left h)

theorem thirteen_pow_mod_three (z : ℕ) : 13 ^ z % 3 = 1 := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem thirteen_pow_mod_four (z : ℕ) : 13 ^ z % 4 = 1 := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem five_pow_mod_three (u : ℕ) : 5 ^ u % 3 = 1 ∨ 5 ^ u % 3 = 2 := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem five_pow_eq_one_or (u : ℕ) : 5 ^ u = 1 ∨ 5 ^ u % 5 = 0 := by
  cases u with
  | zero => simp
  | succ k => right; rw [pow_succ]; omega

theorem thirteen_pow_mod_eight (z : ℕ) :
    (z % 2 = 0 → 13 ^ z % 8 = 1) ∧ (z % 2 = 1 → 13 ^ z % 8 = 5) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem thirteen_pow_mod_five (z : ℕ) :
    (z % 4 = 0 → 13 ^ z % 5 = 1) ∧ (z % 4 = 1 → 13 ^ z % 5 = 3) ∧
    (z % 4 = 2 → 13 ^ z % 5 = 4) ∧ (z % 4 = 3 → 13 ^ z % 5 = 2) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem thirteen_pow_mod_sixteen (z : ℕ) :
    (z % 4 = 0 → 13 ^ z % 16 = 1) ∧ (z % 4 = 1 → 13 ^ z % 16 = 13) ∧
    (z % 4 = 2 → 13 ^ z % 16 = 9) ∧ (z % 4 = 3 → 13 ^ z % 16 = 5) := by
  induction z with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem twentyfive_pow_mod_thirteen (u : ℕ) :
    (u % 2 = 0 → 25 ^ u % 13 = 1) ∧ (u % 2 = 1 → 25 ^ u % 13 = 12) := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem twentyfive_pow_mod_sixteen (u : ℕ) :
    (u % 2 = 0 → 25 ^ u % 16 = 1) ∧ (u % 2 = 1 → 25 ^ u % 16 = 9) := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem twentyfive_pow_mod_eight (u : ℕ) : 25 ^ u % 8 = 1 := by
  induction u with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem three_pow_lt_four_pow (k : ℕ) : 3 ^ (k + 5) < 4 ^ (k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 3 ^ (k + 1 + 5) = 3 * 3 ^ (k + 5) := by ring
    have e2 : 4 ^ (k + 1 + 4) = 4 * 4 ^ (k + 4) := by ring
    omega

/-- Parity reduction (mod 3): in `5^x + 12^y = 13^z` with `y > 0`, `x` is even. -/
theorem x_even_5_12_13 {x y z : ℕ} (hy : 0 < y) (h : 5 ^ x + 12 ^ y = 13 ^ z) :
    x % 2 = 0 := by
  by_contra hx
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have h1 := five_pow_mod_three_odd k
  have h2 := thirteen_pow_mod_three z
  have h3 : 12 ^ (y + 1) = 12 * 12 ^ y := by ring
  omega

/-- `25^u + 12 = 13^z` has no solution with `u, z > 0` (mod 13, 5 and 16). -/
theorem twentyfive_pow_add_twelve_ne {u z : ℕ} (hu : 0 < u) (hz : 0 < z) :
    25 ^ u + 12 ≠ 13 ^ z := by
  intro h
  obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
  have e1 : 25 ^ (u' + 1) = 25 * 25 ^ u' := by ring
  have e2 : 13 ^ (z' + 1) = 13 * 13 ^ z' := by ring
  have a1 := twentyfive_pow_mod_thirteen (u' + 1)
  have a2 := twentyfive_pow_mod_sixteen (u' + 1)
  have a3 := thirteen_pow_mod_five (z' + 1)
  have a4 := thirteen_pow_mod_sixteen (z' + 1)
  have hue : (u' + 1) % 2 = 0 := by omega
  have hz4 : (z' + 1) % 4 = 3 := by omega
  omega

/-- **Jeśmanowicz (1956).** The only positive integer solution of
`5^x + 12^y = 13^z` is `x = y = z = 2`. -/
theorem jesmanowicz_5_12_13 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 5 ^ x + 12 ^ y = 13 ^ z) : x = 2 ∧ y = 2 ∧ z = 2 := by
  have hxe := x_even_5_12_13 hy h
  obtain ⟨u, rfl⟩ : ∃ u, x = 2 * u := ⟨x / 2, by omega⟩
  have h25 : 5 ^ (2 * u) = 25 ^ u := by rw [pow_mul]; norm_num
  -- `y ≥ 2`
  have hy2 : 2 ≤ y := by
    by_contra hlt
    obtain rfl : y = 1 := by omega
    rw [h25, pow_one] at h
    exact twentyfive_pow_add_twelve_ne (by omega) hz h
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
  -- `z` even (mod 8)
  have hze : z % 2 = 0 := by
    by_contra hzo
    have e : 12 ^ (y + 2) = 144 * 12 ^ y := by ring
    have a1 := twentyfive_pow_mod_eight u
    have a2 := thirteen_pow_mod_eight z
    rw [h25] at h
    omega
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by omega⟩
  rw [pow_mul' 5, pow_mul' 13] at h
  have hA4 := thirteen_pow_mod_four w
  have hB4 := five_pow_mod_four u
  have hB3 := five_pow_mod_three u
  have h12pos : 0 < 12 ^ (y + 2) := by positivity
  have hBA : 5 ^ u < 13 ^ w := by
    by_contra hle
    have : (13 ^ w) ^ 2 ≤ (5 ^ u) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨d, hd⟩ : ∃ d, 13 ^ w = 5 ^ u + 2 * d := ⟨(13 ^ w - 5 ^ u) / 2, by omega⟩
  have hdpos : 0 < d := by omega
  have e2 : 2 ^ (2 * y + 2) = 4 ^ (y + 1) := by
    rw [show 2 * y + 2 = 2 * (y + 1) by ring, pow_mul]; norm_num
  have hfac : d * (5 ^ u + d) = 2 ^ (2 * y + 2) * 3 ^ (y + 2) := by
    have e : 12 ^ (y + 2) = 4 * (4 ^ (y + 1) * 3 ^ (y + 2)) := by
      rw [show (12 : ℕ) = 4 * 3 by norm_num, mul_pow]; ring
    rw [e2]; rw [hd, e] at h; nlinarith
  have hPpos : 0 < 2 ^ (2 * y + 2) := by positivity
  have hQpos : 0 < 3 ^ (y + 2) := by positivity
  have h2 : 2 ^ (2 * y + 2) ∣ d ∨ 2 ^ (2 * y + 2) ∣ 5 ^ u + d :=
    prime_pow_dvd_or Nat.prime_two (Dvd.intro _ hfac.symm)
      (by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; omega)
  have h3 : 3 ^ (y + 2) ∣ d ∨ 3 ^ (y + 2) ∣ 5 ^ u + d :=
    prime_pow_dvd_or Nat.prime_three (Dvd.intro_left _ hfac.symm)
      (by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; omega)
  have hcop : Nat.Coprime (2 ^ (2 * y + 2)) (3 ^ (y + 2)) :=
    Nat.Coprime.pow _ _ (by norm_num)
  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · -- both divide `d`: impossible by size
    exfalso
    have hdvd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 h3
    obtain ⟨-, hs⟩ := eq_of_mul_eq_of_dvd (P := 2 ^ (2 * y + 2) * 3 ^ (y + 2))
      (Q := 1) (d := d) (s := 5 ^ u + d) (by positivity) (by norm_num)
      (by rw [mul_one]; exact hfac) hdvd (one_dvd _)
    clear * - hs hdpos
    omega
  · -- `d = 4^(y+1)`, `5^u + d = 3^(y+2)`: the genuine case
    obtain ⟨hd', hs⟩ := eq_of_mul_eq_of_dvd hPpos hQpos hfac h2 h3
    rw [e2] at hd'
    rcases Nat.lt_or_ge y 3 with hlt | hge
    · have h5 := five_pow_eq_one_or u
      interval_cases y
      · norm_num at hd' hs
        have hu : u = 1 := by
          have : 5 ^ u = 5 ^ 1 := by omega
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) this
        subst hu
        have hw : w = 1 := by
          have : 13 ^ w = 13 ^ 1 := by omega
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 13) this
        subst hw
        exact ⟨rfl, rfl, rfl⟩
      · norm_num at hd' hs; omega
      · norm_num at hd' hs; omega
    · exfalso
      obtain ⟨k, rfl⟩ : ∃ k, y = k + 3 := ⟨y - 3, by omega⟩
      have := three_pow_lt_four_pow k
      rw [show k + 3 + 1 = k + 4 by ring] at hd'
      rw [show k + 3 + 2 = k + 5 by ring] at hs
      clear * - hs hd' this
      omega
  · -- `d = 3^(y+2)`, `5^u + d = 4^(y+1)`: impossible mod 4
    exfalso
    obtain ⟨hs, hd'⟩ := eq_of_mul_eq_of_dvd hPpos hQpos
      (by rw [mul_comm]; exact hfac) h2 h3
    rw [e2] at hs
    have : 4 ^ (y + 1) = 4 * 4 ^ y := by ring
    omega
  · -- both divide `5^u + d`: then `d = 1`, impossible mod 4
    exfalso
    have hdvd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 h3
    obtain ⟨hd', -⟩ := eq_of_mul_eq_of_dvd (P := 1)
      (Q := 2 ^ (2 * y + 2) * 3 ^ (y + 2)) (d := d) (s := 5 ^ u + d) (by norm_num)
      (by positivity) (by rw [one_mul]; exact hfac) (one_dvd _) hdvd
    omega

/-- Jeśmanowicz' conjecture holds for the triple `(5, 12, 13)` with `n = 1`. -/
theorem jesmanowiczFor_5_12_13_one : JesmanowiczFor 5 12 13 1 := by
  intro x y z hs
  obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
  exact jesmanowicz_5_12_13 hx hy hz h

end Jesmanowicz
