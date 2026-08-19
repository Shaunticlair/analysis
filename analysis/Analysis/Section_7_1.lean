import Mathlib.Tactic

/-!
# Analysis I, Section 7.1: Finite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Technical note: it is convenient in Lean to extend finite sequences (usually by zero) to be
functions on the entire integers.

Main constructions and results of this section:
-/

-- This makes available the convenient notation `∑ n ∈ A, f n` to denote summation of `f n` for
-- `n` ranging over a finite set `A`.
open BigOperators

/-!
- API for summation over finite sets (encoded using Mathlib's `Finset` type), using the
  `Finset.sum` method and the `∑ n ∈ A, f n` notation.
- Fubini's theorem for finite series

We do not attempt to replicate the full API for `Finset.sum` here, but in subsequent sections we
shall make liberal use of this API.

-/

-- This is a technical device to avoid Mathlib's insistence on decidable equality for finite sets.
open Classical

namespace Finset

-- We use `Finset.Icc` to describe finite intervals in the integers. `Finset.mem_Icc` is the
-- standard Mathlib tool for checking membership in such intervals.
#check mem_Icc

/-- Definition 7.1.1 -/
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

/--
  Definition 7.1.1. This is similar to Mathlib's `Finset.sum_Icc_succ_top` except that the
  latter involves summation over the natural numbers rather than integers.
-/
theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by
  apply sum_of_empty; linarith

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := sum_of_empty (by linarith) _



lemma sum_of_single (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by
  have := sum_of_nonempty (m:=m) (n:=m-1) (by linarith)
  rw [show m-1+1 = m by omega] at this
  rw [this]; rw [sum_of_empty] <;> linarith

lemma sum_of_pair (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  rw [sum_of_nonempty, sum_of_single]; linarith

lemma sum_of_trio (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have := sum_of_nonempty (m:=m) (n:=m+1) (by linarith)
  rw [show m+1+1 = m+2 by omega] at this
  rw [this]; simp; exact sum_of_pair a m

/-- Remark 7.1.3 -/
example (a: ℤ → ℝ) (m n:ℤ) : ∑ i ∈ Icc m n, a i = ∑ j ∈ Icc m n, a j := rfl

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  obtain ⟨k, rfl⟩ : ∃ k:ℕ, p = n + k := ⟨(p-n).toNat, by grind⟩
  induction' k with k hk
  · nth_rw 2 [sum_of_empty (by omega)]; simp
  simp; rw [← add_assoc]
  rw [sum_of_nonempty (by linarith), sum_of_nonempty (by linarith)]
  rw [← add_assoc, hk (by linarith)]

/-- Lemma 7.1.4(b) / Exercise 7.1.1 -/
theorem shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  by_cases h: n < m
  · rw [sum_of_empty, sum_of_empty] <;> linarith
  obtain ⟨r, rfl⟩ : ∃ r:ℕ, n = m + r := ⟨(n-m).toNat, by aesop⟩
  induction' r with r hr
  · simp only [CharP.cast_eq_zero, add_zero]
    rw [sum_of_single, sum_of_single]; congr; linarith
  simp; rw [← add_assoc, show m + ↑r + 1 + k = m +r + k + 1 by linarith]
  rw [sum_of_nonempty, sum_of_nonempty]
  rw [hr (by linarith)]; simp; congr 1; all_goals linarith

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_add {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
  by_cases h: n < m
  · rw [sum_of_empty, sum_of_empty, sum_of_empty] <;> linarith
  obtain ⟨r, rfl⟩ : ∃ r:ℕ, n = m + r := ⟨(n-m).toNat, by aesop⟩
  induction' r with r hr
  · simp -- Identical to the last one
  simp; rw [← add_assoc]; repeat rw [sum_of_nonempty]
  rw [hr (by linarith)]; ring
  all_goals linarith

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_const_mul {m n:ℤ}  (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  by_cases h: n < m
  · rw [sum_of_empty, sum_of_empty] <;> linarith
  obtain ⟨r, rfl⟩ : ∃ r:ℕ, n = m + r := ⟨(n-m).toNat, by aesop⟩
  induction' r with r hr
  · simp only [CharP.cast_eq_zero, add_zero, sum_of_single]
  simp; rw[← add_assoc]; repeat rw [sum_of_nonempty]
  rw [hr (by linarith)]; ring
  all_goals linarith

/-- Lemma 7.1.4(e) / Exercise 7.1.1 -/
theorem abs_finite_series_le {m n:ℤ}   (a: ℤ → ℝ) (c:ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
  by_cases h: n < m
  · rw [sum_of_empty, sum_of_empty]; norm_num; all_goals linarith
  obtain ⟨r, rfl⟩ : ∃ r:ℕ, n = m + r := ⟨(n-m).toNat, by aesop⟩
  induction' r with r hr
  · simp only [CharP.cast_eq_zero, add_zero, sum_of_single]; rfl
  simp; rw [← add_assoc]; repeat rw [sum_of_nonempty]
  -- get the triangle inequality
  apply le_trans (abs_add _ _)
  simp; apply hr (by linarith)
  all_goals linarith

/-- Lemma 7.1.4(f) / Exercise 7.1.1 -/
theorem finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
  by_cases hnot_sdiff_comm: n < m
  · rw [sum_of_empty, sum_of_empty]; all_goals linarith
  obtain ⟨r, rfl⟩ : ∃ r:ℕ, n = m + r := ⟨(n-m).toNat, by aesop⟩
  induction' r with r hr
  · simp only [CharP.cast_eq_zero, add_zero, sum_of_single];
    apply h m; all_goals linarith
  specialize hr (by peel h with i hm h; intro hmr; apply h (by omega)) (by linarith)
  simp; rw [← add_assoc]; repeat rw [sum_of_nonempty]
  apply add_le_add hr (by apply h; all_goals omega)
  all_goals linarith

#check sum_congr



-- Originally got a line-by-line annotation from Claude, but rewrote it myself for comprehension

set_option maxHeartbeats 220000 in
/--
  Proposition 7.1.8: the value of a finite sum `∑ x ∈ X, f x`, when computed via an enumeration
  of `X` by a bijection `g : Icc 1 n → X` (i.e. `∑ i ∈ Icc 1 n, f (g i)`), does not depend on
  the choice of bijection used to enumerate `X`. This is proved by induction on `n = |X|`: given
  two bijections `g`, `h`, we peel off the last term `g (n+1) = x`, relocate the corresponding
  term of `h` (at whatever index `j` maps to `x`) to the end via `h'`, delete `x` from `X`, and
  apply the induction hypothesis to the two induced bijections `Icc 1 n → X.erase x`.
-/
theorem finite_series_of_rearrange' {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :

    ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- This proof is written to broadly follow the structure of the original text.
  revert X n; intro n  -- generalize X (and hcard, g, h, hg, hh) so we can induct on n
  induction' n with n hn  -- induct on n = X.card
  · simp  -- base case n = 0: empty, trivially zero
  intro X hX g h hg hh  -- reintroduce everything
  -- Use function π to replace our awkward workaround for type conversion in the series def
  set π : ℤ → Icc (1:ℤ) (n+1) :=
    fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1:ℤ) (n+1) → X) :
      ∑ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∑ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
    apply sum_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]  -- check functions termwise
  simp [-mem_Icc, hπ]
  rw [sum_of_nonempty (by linarith) _]  -- peel off last term in g series
  set x := g (π (n+1))  -- name g(n+1)
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x  -- get corresponding index in h series
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  -- h' := Shift indices of h, when above j
  set h' : ℤ → X := fun i ↦ if (i:ℤ) < j then h (π i) else h (π (i+1))
  have : ∑ i ∈ Icc (1:ℤ) (n + 1), f (h (π i)) = ∑ i ∈ Icc (1:ℤ) n, f (h' i) + f x := by calc
    _ = ∑ i ∈ Icc (1:ℤ) j, f (h (π i)) + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      symm; apply concat_finite_series <;> linarith  -- [1,j]+[j+1,n+1]
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f ( h (π j) )
        + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      congr; convert sum_of_nonempty _ _ <;> simp [hj1]  -- [1,j-1]+[j]+[j+1,n+1]
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f x + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]  -- Replace middle term: f x = f(g(j))
      symm; convert shift_finite_series _; simp  -- reindex [j+1,n+1] to [j,n]
    -- Move f x to end (so we can congr later)
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) + f x := by abel
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h' i) + ∑ i ∈ Icc (j:ℤ) n, f (h' i) + f x := by -- h → h'
      congr 2
      all_goals apply sum_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by linarith]  -- on [1,j-1], i < j so h' i = h (π i)
      simp [show ¬ i < j by linarith]  -- on [j,n], i ≥ j so h' i = h (π (i+1))
    _ = _ := by congr; convert concat_finite_series _ _ _ <;> linarith  -- recombine indices
  rw [this]
  congr 1
  have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g (π i) ≠ x := by -- For g', restrict X to X\{x}
    simp at hi -- g is injective, so if we don't have g(n+1), we don't have x
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x := by -- For h', restrict X to X\{x}
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt: i < j <;> by_contra! heq  -- i<j or i>j give different behavior for h'
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq  -- h injective: w/o h(j), we can't have x
    . linarith  -- i<j: h(i) ≠ h(j) = x
    contrapose! hlt; linarith  -- index shifts, and i+1>j: h'(i) = h(i+1) ≠ h(j) = x
  set gtil : Icc (1:ℤ) n → X.erase x := -- create g_ restricted to X\{x}
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, Subtype.val_inj, g_ne_x] ⟩
  set htil : Icc (1:ℤ) n → X.erase x := -- create h_ restricted to X\{x}
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, Subtype.val_inj, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val  -- create f_ restricted to X\{x}

  -- If card is equal, then inj is sufficient
  have hcard : Nat.card { x // x ∈ Icc 1 (n:ℤ) } = Nat.card { y // y ∈ X.erase x } := by
    rw [Nat.card_eq_finsetCard, Int.card_Icc] -- Left side: |Icc 1 n| = n
    rw [Nat.card_eq_finsetCard, Finset.card_erase_of_mem (x.prop)] -- Right side: |X\{x}| = |X|-1 = n
    simp [hX] -- Use |X| = n+1 to equate them

  -- Pseudo-inj of π makes it easier to get injectivity of gtil (composition includes π)
  have hπ_pseudoinj {a b : ℤ} {m : ℕ} (hm : m ≤ n+1) (ha : a ∈ Icc (1:ℤ) (m)) (hb : b ∈ Icc (1:ℤ) (m))
    (hab: π a = π b) : a = b := by
    unfold π at hab; simp at ha hb; repeat rw [dif_pos (by simp; constructor <;> linarith)] at hab
    simpa using hab

  have why : Function.Bijective gtil := by
    rw [Nat.bijective_iff_injective_and_card ] -- Stolen from rkirov on github, ty rkirov
    refine ⟨?_, hcard⟩;
    intro a b hab; simp [gtil] at hab; rw [Subtype.eq_iff]; -- Setting up
    apply hπ_pseudoinj (?_: n ≤ n+1) (?_) (?_) (hg.injective (Subtype.val_inj.1 hab)) <;> simp-- Repeated injectivity

  have hh'_inj {a b : ℤ} (ha : a ∈ Icc (1:ℤ) n) (hb : b ∈ Icc (1:ℤ) n)
    (hab: h' a = h' b) : a = b := by
    unfold h' at *; obtain ⟨ha1, ha2⟩ := (by simpa using ha); obtain ⟨hb1, hb2⟩ := (by simpa using hb)
    by_cases haj : a < j <;> by_cases hbj : b < j <;> simp [haj, hbj] at hab <;>
    apply hh.injective at hab  <;> apply hπ_pseudoinj (by simp: n+1 ≤ n+1) (by simp; omega) (by simp; omega) at hab
    <;> linarith

  have why2 : Function.Bijective htil := by
    rw [Nat.bijective_iff_injective_and_card ]
    refine ⟨?_, hcard⟩;
    intro a b hab; simp [htil] at hab; rw [Subtype.eq_iff]; -- Setting up
    apply hh'_inj a.2 b.2 (Subtype.val_inj.1 hab) -- Repeated injectivity
  calc
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply sum_congr rfl; grind  -- f(g(i)) = f_(g_(i))
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2  -- f_(g_(i)) = f_(h_(i)) by induction
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply sum_congr rfl; grind  -- f_(h_(i)) = f(h(i))





/--
  This fact ensures that Definition 7.1.6 would be well-defined even if we did not appeal to the
  existing {name}`Finset.sum` method.

  Specifically, we could always convert it into the sum defined by Tao using the guaranteed bijection.
-/
theorem exist_bijection {n:ℕ} {Y:Type*} (X: Finset Y) (hcard: X.card = n) :
    ∃ g: Icc (1:ℤ) n → X, Function.Bijective g := by
  have := Finset.equivOfCardEq (show (Icc (1:ℤ) n).card = X.card by simp [hcard])
  exact ⟨ this, this.bijective ⟩

/-- Definition 7.1.6 -/
theorem finite_series_eq {n:ℕ} {Y:Type*} (X: Finset Y) (f: Y → ℝ) (g: Icc (1:ℤ) n → X)
  (hg: Function.Bijective g) :
    ∑ i ∈ X, f i = ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert sum_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all

/-- Proposition 7.1.11(a) / Exercise 7.1.2 -/
theorem finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by
  rw [finite_series_eq (n:=0)];
  rw [sum_of_empty (by norm_num)];
  have : Icc 1 ((0:ℕ):ℤ) = ∅ := by ext i; simp only [notMem_empty, iff_false, mem_Icc]; aesop
  use fun i ↦ absurd i.prop (by simp only [this]; apply notMem_empty)

  sorry

/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  sorry

/--
  A technical lemma relating a sum over a finset with a sum over a fintype. Combines well with
  tools such as `map_finite_series` below.
-/
theorem finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, f x = ∑ x:X, f x.val := (sum_coe_sort X f).symm

/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by sorry

-- Proposition 7.1.11(d) is `rfl` in our formalism and is therefore omitted.

/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by sorry

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by sorry

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by sorry

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by sorry

/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by sorry

/-- Lemma 7.1.13 -/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . sorry
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . sorry
      sorry

/-- Corollary 7.1.14 (Fubini's theorem for finite series). -/
theorem finite_series_refl {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

theorem finite_series_comm {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]


-- Exercise 7.1.3 : develop as many analogues as you can of the above theory for finite products
-- instead of finite sums.

#check Nat.factorial_zero
#check Nat.factorial_succ

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics {tactic}`zify`, {tactic}`norm_cast`, and {tactic}`omega`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  sorry

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  sorry

/-- Exercise 7.1.6 -/
theorem sum_union_disjoint {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) :
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  sorry

/-- {given}`aᵢ` Exercise 7.1.7. Uses {lean}`Fin m` (so {lean}`aᵢ < m`) instead of the book's {lean}`aᵢ ≤ m`;
  the bound is baked into the type, and {kw (of := «term_<_»)}`<` replaces {kw (of := «term_≤_»)}`≤` to match the 0-indexed shift. -/
theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  sorry

end Finset
