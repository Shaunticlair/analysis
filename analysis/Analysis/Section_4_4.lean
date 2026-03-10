import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

theorem toNat_of_nonneg {z:ℤ} (hz: z ≥ 0) : ∃ m : ℕ, z = (m:ℤ) := by
  use z.toNat; simp [hz]

theorem toNat_of_neg {z:ℤ} (hz: z < 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega

theorem toNat_of_nonpos {z:ℤ} (hz: z ≤ 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega

lemma cast_sub (a b:ℕ) (h: b ≤ a): (a - b: ℕ) = (a: ℤ) - (b: ℤ) := by exact Int.ofNat_sub h

-- We were suggested to use Proposition 2.3.9
theorem euclid_algorithm (n q : ℕ) (hq : q > 0) :
∃ (m r : ℕ), (0 ≤ r ∧ r < q ∧ n = m * q + r):= by
  use n / q, n % q
  simp_all
  constructor
  · apply Nat.mod_lt n hq
  · have := Nat.div_add_mod n q
    rw [mul_comm, this]

-- But we need to generalize this to integers
theorem euclid_algorithm' (z : ℤ) (q : ℕ) (hq : q > 0) :
∃ (m : ℤ )(r : ℕ), (r < q ∧ z = m * q + r):= by
  rcases le_total z 0 with (hz | hz)
  · choose z' hz' using toNat_of_nonpos hz
    choose a b hab using (euclid_algorithm z' q hq)
    by_cases hb : b = 0
    · use -a, 0; simp [hq, hz', hab.2, hb]
    · use -(a+1), q - b; observe : 0 < b
      simp [hq, this, hz', hab.2.2]
      simp [cast_sub q b (by omega)]; ring
  · choose z' hz' using toNat_of_nonneg hz
    choose a b hab using (euclid_algorithm z' q hq)
    use a, b; simp [hab.2.1, hz', hab.2.2];


/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  choose m r hr hmr using euclid_algorithm' x.num x.den (by positivity)
  apply existsUnique_of_exists_of_unique
  · use m
    constructor
    · rw [←Rat.num_div_den x, hmr, le_iff_exists_nonneg_add];
      use r/x.den; field_simp;
      apply div_nonneg (by positivity) (by positivity)

    · rw [←Rat.num_div_den x, hmr, ]; simp; simp [add_div];
      have: (r : ℚ ) < (x.den : ℚ) := by field_simp; exact hr
      rw [div_lt_one (by positivity)]; exact this


  · intro z1 z2 ⟨hz11, hz12⟩ ⟨hx21, hx22⟩
    rcases lt_trichotomy z1 z2 with (h | h | h)
    · exfalso; have : ((z1 + 1) : ℚ) ≤ z2 := by exact_mod_cast (by linarith);
      linarith
    · exact h
    · exfalso; have : ((z2 + 1) : ℚ) ≤ z1 := by exact_mod_cast (by linarith);
      linarith

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  choose n hn1 _ using Rat.between_int x; obtain ⟨hn11, hn12⟩ := hn1
  choose m hm using Int.eq_nat_or_neg n
  rcases hm with rfl | rfl
  · simp at hn12; use m + 1; simp [hn12]
  · use 1; simp at hn12; simp;
    linarith [show (m + 1 : ℚ) > 0 by positivity]

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  intro h; choose f hf using h
  have : ∀ k n, f n > k:= by
    intro k
    induction' k with k ih
    · intro n; by_contra h; have : f n = 0 := by omega;
      specialize hf n; rw [this] at hf; contradiction
    · intro n; specialize ih (n+1)
      specialize hf n; linarith
  specialize this (f 0) 0; omega

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue; use fun n ↦ -n; intro n; simp

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue; use fun n ↦ ⟨1/(n+1), by positivity⟩; intro n; simp
  field_simp; apply div_lt_div_of_pos_left; positivity; positivity; linarith

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  induction' n with n ih
  · left; use 0
  · rcases ih with (ihe | iho)
    · right; choose k hk using ihe; use k; rw [hk]; ring
    · left; choose k hk using iho; use k + 1; rw [hk]; ring

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  intro ⟨he,ho⟩; choose k hk using he; choose m hm using ho
  rw [hk] at hm; have : 2*(k - m) = 1 := by ring; omega
  by_cases h: k - m ≤ 0
  · observe hkm: k-m = 0
    rw [hkm] at this; simp at this
  · push_neg at h; observe h2 : 2*(k - m) ≥ 2
    rw [this] at h2; simp at h2

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  · push_neg at hpos; observe hx0 : -x ≥ 0 ; observe h0 : -x ≠ 0
    exact this (-x) (by simp [hx]) h0 (lt_of_le_of_ne hx0 h0.symm)
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←Rat.num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx --norm_cast can close goals
  -- P p := p^2 can be split in half to get another number q^2
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  -- If p^2 can be split, then there's some smaller q^2 that can be split
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd
    · -- p is even
      obtain ⟨ k, rfl ⟩ := hp --Because p was even, we can break it into 2*k
      rw [show k+k = 2*k by ring] at *
      choose q hpos hq using hPp.2 -- Split p^2 to get q^2
      -- q^2 and k^2 both come from p^2, but q^2 is smaller
      have : q^2 = 2 * k^2 := by linarith -- We can split q^2 to get k^2
      use q; constructor
      · rcases lt_trichotomy q (2*k) with hlt | heq | hgt
        · exact hlt
        · rw [heq] at hq; ring_nf at hq; have : k > 0 := by linarith
          have : k^2 > 0 := by apply pow_pos; exact this
          have : 4 = 8 := by linarith
          contradiction
        · exfalso;
          have:= pow_lt_pow_left₀ (n := 2) hgt (by linarith) (by norm_num)
          have : (2*k)^2 < 2 * q^2 := by omega
          omega
      · unfold P; exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    · -- p can't be odd because p^2 = 2*q^2 is even
      have h1 : Odd (p^2) := by
        choose k hk using hp; rw [hk]; use 2*k + 2*k^2; ring
      have h2 : Even (p^2) := by
        choose q hpos hq using hPp.2
        use q^2; rw [hq]; ring
      observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
      tauto
  classical
  -- Function f produces the smaller number q from p
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  -- f always produces a smaller number q (= f p) from p that can be split (again)
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  -- Grab some p that can be split
  choose p hP using hP
  -- Recursively apply f to produce an infinite descending chain of natural numbers
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  -- Prove that all a n have the desired properties (smaller, splittable)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP -- Original p known to be splittable
    | succ n ih => exact (hf (a n) ih).2 -- f p is splittable if p is
  -- Prove that all a n are strictly descending
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    rw [this]; specialize hf (a n) (ha n); exact hf.1
    --grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
