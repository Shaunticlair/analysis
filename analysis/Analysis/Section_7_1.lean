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
theorem abs_finite_series_le {m n:ℤ}   (a: ℤ → ℝ)  :
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
  by_cases hnm: n < m
  · rw [sum_of_empty, sum_of_empty]; all_goals linarith
  obtain ⟨r, rfl⟩ : ∃ r:ℕ, n = m + r := ⟨(n-m).toNat, by aesop⟩
  induction' r with r hr
  · simp only [CharP.cast_eq_zero, add_zero, sum_of_single];
    apply h; all_goals linarith
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
theorem finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
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
    rw [Nat.bijective_iff_injective_and_card ] -- If card is equal, then inj is sufficient
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
  rw [finite_series_eq (n:=0), sum_of_empty (by norm_num)];
  have : Icc 1 ((0:ℕ):ℤ) = ∅ := by ext i; simp only [notMem_empty, iff_false, mem_Icc]; aesop
  use fun i ↦ absurd i.prop (by simp only [this]; apply notMem_empty)
  constructor
  · intro i j hij; simp_all; have := i.prop; simp [-coe_mem, notMem_empty] at this
  · intro x; absurd x.prop; simp [-coe_mem]

/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  choose g hg using exist_bijection (n:=1) {x₀} (by simp only [card_singleton]) -- We proved in ch3 that {x₀} has cardinality 1
  -- ... Well, we proved it for Set, but proving it for Finset feels redundant
  --let g : Icc (1:ℤ) (1:ℕ) → ({x₀} : Finset X') := fun i ↦ ⟨x₀, by simp⟩
  rw [finite_series_eq (n:=1) (g:=g) (hg:=hg)];
  · simp only [Nat.cast_one]; rw [sum_of_single]; simp; congr; rw [Subtype.coe_eq_iff]; use (by simp); grind

/--
  A technical lemma relating a sum over a finset with a sum over a fintype. Combines well with
  tools such as `map_finite_series` below.
-/
theorem finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, f x = ∑ x:X, f x.val := (sum_coe_sort X f).symm

#check finite_series_eq






#check Finset.sum
#check Finset.univ
/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X Y:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
  show ∑ x ∈ (Finset.univ : Finset X), f x = ∑ y ∈ (Finset.univ : Finset Y), f (g y) -- For my understanding
  let n:= Finset.card (Finset.univ : Finset Y)
  have hcard : Finset.card (Finset.univ : Finset X) = n := (Fintype.card_of_bijective hg).symm
  choose s hs using exist_bijection (n:=n) (Finset.univ : Finset Y) rfl
  rw [finite_series_eq (Finset.univ : Finset Y) (n:=n) (g:=s) (hg:=hs)]
  let s': Icc 1 (n:ℤ) → Y := fun i ↦ s i
  let g' : Y → (Finset.univ : Finset X) := fun y ↦ ⟨g y, mem_univ _⟩
  rw [finite_series_eq (Finset.univ : Finset X) (n:=n) (g:=g' ∘ s') ]; rfl
  rw [Fintype.bijective_iff_injective_and_card]; refine ⟨?_, by simp [Fintype.card, hcard]⟩
  · intro i j hij; simp [g'] at hij; apply hg.injective at hij; simp [s'] at hij; apply hs.injective
    exact Subtype.eq hij


-- Proposition 7.1.11(d) is `rfl` in our formalism and is therefore omitted.

abbrev Icc_castSucc {m n:ℤ} (i: Icc m n): Icc m (n+1) :=
  ⟨i + 1, by have := i.prop;
             simp_all [-coe_mem]; linarith⟩

abbrev Icc_castPred {m n:ℤ} (i : Icc m (n+1)) (hi : i.val < n+1): Icc m n :=
  ⟨i, by have := i.prop;
             simp_all [-coe_mem]; linarith⟩

lemma sum_congr' {m n:ℤ} (f g: ℤ → ℝ) (h: ∀ i, m ≤ i → i ≤ n → f i = g i) :
    ∑ i ∈ Icc m n, f i = ∑ i ∈ Icc m n, g i := by
  by_cases hnm: n < m
  · rw [sum_of_empty, sum_of_empty]; all_goals linarith
  obtain ⟨r, rfl⟩ : ∃ r:ℕ, n = m + r := ⟨(n-m).toNat, by aesop⟩
  induction' r with r hr
  · simp [h]
  simp; rw [← add_assoc]; repeat rw [sum_of_nonempty (by linarith)]
  rw [hr (by intro i hmi hmr; apply h _ hmi; omega) (by simp_all)];
  rw [h _ (by linarith) (by omega)];


theorem finite_series_of_insert {Z:Type*} {X: Finset Z} (y : Z) (hy : y ∉ X) (f: Z → ℝ) :
    ∑ z ∈ X ∪ {y}, f z = ∑ z ∈ X, f z + f y := by
  choose s hs using exist_bijection X rfl
  rw [finite_series_eq X f s hs]
  let s' : Icc 1 ((#X :ℤ)+1) → (X ∪ {y} : Finset Z) :=
    fun i ↦ if hi : i.val ∈ Icc 1 (#X :ℤ) then
    ⟨((s (Icc_castPred i (by simp_all; linarith)))), by simp_all⟩  else ⟨y, by simp⟩
  let s'' : Icc 1 ((#X :ℤ)+1) → (X ∪ {y} : Finset Z) :=
    fun i ↦ if hi : i.val ≤ (#X :ℤ) then
    ⟨((s (Icc_castPred i (by linarith)))), by simp_all⟩  else ⟨y, by simp⟩
  have hs'': Function.Bijective s'' := by -- I feel like it's reasonable to reuse card_insert_of_notMem (equiv in ch3)
    rw [Fintype.bijective_iff_injective_and_card]; refine ⟨?_, by simp [Fintype.card,card_insert_of_notMem hy] ⟩
    · intro i j hij;
      by_cases hi : i.val ≤ #X <;> by_cases hj : j.val ≤ #X <;> have hi' := i.prop <;> have hj' := j.prop <;>
      simp [s'', hi, hj, -coe_mem, Icc_castPred] at hij hi' hj' <;> try grind -- Either linarith or contradiction
      · rw [Subtype.val_inj] at hij; apply hs.injective at hij; grind
  rw [finite_series_eq (X ∪ {y}) f s'' hs'' (n:= #X + 1)]; simp only [Nat.cast_add, Nat.cast_one,]
  rw [sum_of_nonempty (by simp)]; unfold s''
  congr 1; swap; simp
  simp; apply sum_congr'; intro i hi1 hi2; repeat rw [dif_pos (by constructor<;>linarith)]
  simp [hi2]; intro h; linarith


/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
    generalize h: Y.card = n; revert Y
    induction' n with n ih
    · intro Y hdisj h; rw [card_eq_zero] at h; subst h; simp only [union_empty, finite_series_of_empty, add_zero]
    intro Y hdisj h;
    choose y hy using (by rw [← Finset.card_ne_zero]; linarith : Y.Nonempty)
    let Y' := Y.erase y
    have hsep : Y = Y' ∪ {y} := by grind
    have hsep' : (X ∪ Y) = (X ∪ Y') ∪ {y} := by grind
    rw [Finset.disjoint_left] at hdisj
    rw [hsep', hsep]
    rw [finite_series_of_insert y (by grind), finite_series_of_insert y (by grind)];
    rw [← add_assoc]; simp
    apply ih
    · rw [disjoint_left]; grind
    unfold Y'; rw [Finset.card_erase_of_mem hy]; omega; -- Once again, assuming I can use theorems from ch3 (or those related)


#check finite_series_eq
#check exist_bijection
/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
    choose s hs using exist_bijection X rfl
    rw [finite_series_eq X (f+g) s hs, finite_series_eq X f s hs, finite_series_eq X g s hs];
    rw [← finite_series_add]; congr; ext i; split_ifs with h <;> simp

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
    choose s hs using exist_bijection X rfl
    rw [finite_series_eq X f s hs, finite_series_eq X (fun i ↦ c * f i) s hs];
    rw [← finite_series_const_mul]; simp;

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
    choose s hs using exist_bijection X rfl
    rw [finite_series_eq X f s hs, finite_series_eq X g s hs]
    apply finite_series_of_le; intro i h1i hin; split_ifs with h'
    apply h; exact (s ⟨i, h'⟩).prop; rfl



/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by
    choose s hs using exist_bijection X rfl
    rw [finite_series_eq X f s hs, finite_series_eq X (fun i ↦ |f i|) s hs]
    nth_rw 2 [show (0:ℝ) = |(0:ℝ)| by simp]; -- Extract || from our dite construction
    conv=> arg 2; arg 2; intro i; rw [ ← apply_dite abs _ _]
    let g: ℤ → ℝ := fun i ↦ if hi : i ∈ Icc 1 (#X :ℤ) then f ↑(s ⟨i, hi⟩) else 0
    have := abs_finite_series_le g (m:= 1) (n:=#X);
    apply this

/-- Lemma 7.1.13 -/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  · intro X hX; rw [card_eq_zero] at hX; subst hX;
    simp only [product_eq_sprod, empty_product]; -- Previously proven that ∅ ×ˢ Y = ∅
    rw [finite_series_of_empty, finite_series_of_empty];
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
      · rw [show X = X' ∪ {x₀} by grind];
        simp only [Finset.product_eq_sprod]; rw [union_product];
        ext i; simp [mem_product]
      rw [disjoint_left]; intro z hz hz'; simp at hz hz'; grind

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

-- Skipping this section for time.




#check finite_series_const_mul
#check concat_finite_series

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics {tactic}`zify`, {tactic}`norm_cast`, and {tactic}`omega`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  induction' n with n hn
  · simp  -- base case n = 0: (x+y)^0 = 1 = 0!/(0!*0!) * x^0 * y^0
  let F (n:ℕ) :ℝ  := n.factorial
  have hF_succ : ∀ n, F (n+1) = (n+1) * F n := by intro n; simp [F, Nat.factorial_succ]
  let C : ℕ → ℤ → ℝ := fun m j ↦ (F m) / (F j.toNat * F (m-j).toNat)
  let D : ℕ → ℤ → ℝ := fun m j ↦ x^j * y^(m - j) * (C m j)
  convert_to _ = ∑ j ∈ Icc (0:ℤ) (n+1), D (n+1) j; congr; ext i; unfold D; unfold C; ring
  replace hn : (x + y)^n = ∑ j ∈ Icc (0:ℤ) n, D n j := by convert hn using 1; congr; ext i; unfold D C; ring

  rw [show (x + y)^(n+1) = (x+y)^n * (x+y) by ring]
  rw [hn, mul_add, ];
  nth_rw 1 [shift_finite_series (k:= 1)]; simp -- Left side
  rw [sum_of_nonempty];
  rw [← concat_finite_series (m:=0) (n:=0) (p:=n)]; any_goals try linarith
  rw [sum_of_nonempty]; -- Right side
  rw [← concat_finite_series (m:=0) (n:=0) (p:=n)]; any_goals try linarith
  rw [add_mul, add_mul]; simp

  convert_to D n 0 * y + ((∑ i ∈ Icc 1 ↑n, D n (i - 1)) * x + (∑ x ∈ Icc 1 ↑n, D n x) * y) + D n ↑n * x = _
  ring; congr 1; congr 1
  · unfold D C F; field_simp; norm_cast
  swap
  · unfold D C F; field_simp; norm_cast
  rw [mul_comm,← finite_series_const_mul]
  rw [mul_comm _ y, ← finite_series_const_mul]
  rw [← finite_series_of_add];
  apply sum_congr'; intro i hi1 hi2; simp;
  obtain ⟨k, rfl⟩ : ∃ k:ℕ, i = k+1 := ⟨(i-1).toNat, by omega⟩
  simp;

  have hnk: (n:ℤ) - k = ((n - k : ℕ) : ℤ) := by omega
  have hnk1: (n:ℤ) - (k+1) = ((n - k - 1 : ℕ) : ℤ) := by omega

  have hx:= by calc
    x * D n k = (x^k*x)*(y ^ (n - k)) * C n k := by unfold D; rw [hnk]; simp [zpow_natCast]; ring
    _ = (x ^ (k+1))*(y ^ (n - k)) * C n k := by rw [pow_succ]
  have hy:= by calc
    y * D n (k + 1) = (x ^ (k+1))*(y ^ (n - k - 1)*y) * C n (k+1) := by unfold D; rw [hnk1]; norm_cast; ring
    _ = (x ^ (k+1))*(y ^ (n - k)) * C n (k+1) := by rw [← pow_succ]; congr; omega -- omega seems good for type issues
  rw [hx, hy]; unfold D
  rw [← mul_add]; congr 1
  · simp; rw [hnk]; norm_cast
  unfold C; rw [hnk1]; simp
  try polyrith
  have : F (n - k) = F (n - k - 1) * ((n - k:ℕ) :ℝ) := by
    unfold F; rw [← Nat.mul_factorial_pred (by linarith)]; simp; ring
  repeat rw [hF_succ]
  repeat rw [this]
  have hnk0 : (n - k : ℕ) ≠ 0 := by omega
  field_simp
  have hnk': (n:ℝ) - k = ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk
  rw [← hnk']
  ring



theorem binomial_theorem' (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  induction' n with n hn
  · simp  -- base case n = 0: (x+y)^0 = 1 = 0!/(0!*0!) * x^0 * y^0
  let F (n:ℕ) :ℝ  := n.factorial
  have hF_succ : ∀ n, F (n+1) = (n+1) * F n := by intro n; simp [F, Nat.factorial_succ]
  let C : ℕ → ℤ → ℝ := fun m j ↦ (F m) / (F j.toNat * F (m-j).toNat)
  let D : ℕ → ℤ → ℝ := fun m j ↦ x^j * y^(m - j) * (C m j)
  convert_to _ = ∑ j ∈ Icc (0:ℤ) (n+1), D (n+1) j; congr; ext i; unfold D; unfold C; ring
  replace hn : (x + y)^n = ∑ j ∈ Icc (0:ℤ) n, D n j := by convert hn using 1; congr; ext i; unfold D C; ring

  rw [show (x + y)^(n+1) = (x+y)^n * (x+y) by ring]
  rw [hn, mul_add, ];
  nth_rw 1 [shift_finite_series (k:= 1)]; simp -- Left side
  rw [sum_of_nonempty];
  rw [← concat_finite_series (m:=0) (n:=0) (p:=n)]; any_goals try linarith
  rw [sum_of_nonempty]; -- Right side
  rw [← concat_finite_series (m:=0) (n:=0) (p:=n)]; any_goals try linarith
  rw [add_mul, add_mul]; simp

  convert_to D n 0 * y + ((∑ i ∈ Icc 1 ↑n, D n (i - 1)) * x + (∑ x ∈ Icc 1 ↑n, D n x) * y) + D n ↑n * x = _
  ring; congr 1; congr 1
  · unfold D C F; field_simp; norm_cast
  swap
  · unfold D C F; field_simp; norm_cast
  rw [mul_comm,← finite_series_const_mul]
  rw [mul_comm _ y, ← finite_series_const_mul]
  rw [← finite_series_of_add];
  apply sum_congr'; intro i hi1 hi2; simp;
  obtain ⟨k, rfl⟩ : ∃ k:ℕ, i = k+1 := ⟨(i-1).toNat, by omega⟩
  simp;

  have hnk: (n:ℤ) - k = ((n - k : ℕ) : ℤ) := by omega
  have hnk1: (n:ℤ) - (k+1) = ((n - k - 1 : ℕ) : ℤ) := by omega

  have hx:= by calc
    x * D n k = (x^k*x)*(y ^ (n - k)) * C n k := by unfold D; rw [hnk]; simp [zpow_natCast]; ring
    _ = (x ^ (k+1))*(y ^ (n - k)) * C n k := by rw [pow_succ]
  have hy:= by calc
    y * D n (k + 1) = (x ^ (k+1))*(y ^ (n - k - 1)*y) * C n (k+1) := by unfold D; rw [hnk1]; norm_cast; ring
    _ = (x ^ (k+1))*(y ^ (n - k)) * C n (k+1) := by rw [← pow_succ]; congr; omega -- omega seems good for type issues
  rw [hx, hy]; unfold D
  rw [← mul_add]; congr 1
  · simp; rw [hnk]; norm_cast
  unfold C; rw [hnk1]; simp
  try polyrith
  have : F (n - k) = F (n - k - 1) * ((n - k:ℕ) :ℝ) := by
    unfold F; rw [← Nat.mul_factorial_pred (by linarith)]; simp; ring
  repeat rw [hF_succ]
  repeat rw [this]
  have hnk0 : (n - k : ℕ) ≠ 0 := by omega
  field_simp
  have hnk': (n:ℝ) - k = ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk
  rw [← hnk']
  ring


-- For this problem,You can't really induct over the type itself... because
-- the inductive hypothesis would be over the index for a different type.
-- Sum is being taken over a type, which under the hood is Finset.univ
-- So, we'll induct over finsets instead: that way, we can use any set in the
-- IH, not just univ.

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  generalize (Finset.univ : Finset X) = S
  induction' S using Finset.induction_on with x S hx ih
  · rw [Metric.tendsto_atTop]; intro e he; use 0; intro n hn
    repeat rw [finite_series_of_empty];
    simp only [dist_self, he]
  rw [Finset.sum_insert hx] -- Justified use by finite_series_of_insert
  conv => arg 1; intro n; rw [Finset.sum_insert hx]
  exact (h x).add ih -- tendsTo_add equivalent from last chapter

#check Finset.univ
-- Explicit argument
abbrev univ' (X:Type*) [Fintype X] : Finset X := Finset.univ


-- Interesting note: by using `generalize`, I'm induction over the length
-- of the index set, without actually going in order necessarily
-- (i=0,1,2,3...n).
-- I *could* induct on like, some m, while indexing Icc 1 m.
-- But in Lean, that would be 'going against the grain' of the
-- built-in machinery, which encourages you to generically induct
-- over cardinality, rather than a precise ordering.
/-- Exercise 7.1.6 -/
theorem sum_union_disjoint {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) :
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  -- ∑ i is actually ∑ i ∈ (Finset.univ : Finset (Fin n))
  -- ∑ s is actually ∑ s ∈ (Finset.univ : Finset S)
  -- Informally, S = ⋃ i, E i
  have : (Finset.univ : Finset S) = (Finset.univ : Finset (Fin n)).biUnion E := by
    ext i; refine ⟨?_, by intro hi; exact mem_univ i⟩
    intro _; rw [mem_biUnion]; choose k hk using cover i
    use k; simp [hk]
  revert this
  generalize (Finset.univ : Finset S) = Z
  generalize (Finset.univ : Finset (Fin n)) = I
  induction' I using Finset.induction_on with i I hi ih generalizing Z
  · rintro rfl; simp -- empty set on both sides
  simp; rintro rfl
  rw [finite_series_of_disjoint_union]
  · rw [sum_insert hi] -- Allowing myself to use sum_insert. I've could just rearranged to use finite_series_of_insert
    simp [ih _ rfl]
  rw [disjoint_right]; intro x hx
  simp at hx; choose j hj1 hj2 using hx;
  specialize disj i j (by grind)
  exact Disjoint.notMem_of_mem_left_finset ((Disjoint.symm disj)) hj2


#check Finset.sum_boole
#check exist_bijection




theorem finite_series_comm' {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℕ) :
  ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  exact_mod_cast finite_series_comm X Y (fun z ↦ (f z :ℝ )) -- Coercion

theorem finite_series_of_disjoint_union' {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℕ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
    exact_mod_cast finite_series_of_disjoint_union hdisj (fun z ↦ (f z :ℝ )) -- Coercion

/-
Finset.sum_congr.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [AddCommMonoid M] {f g : ι → M}
  (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g
-/
lemma sum_const' {ι : Type u_1} {M : Type u_4} {s : Finset ι} [AddCommMonoid M] (b : M) :
  ∑ _x ∈ s, b = #s • b := by
  induction' s using Finset.induction_on with a s has ih
  · simp
  rw [sum_insert has]; rw [ih]; rw [card_insert_of_notMem has];
  symm; apply succ_nsmul'

lemma sum_boole' {ι : Type u_1} (p : ι → Prop) [DecidablePred p]
  (s : Finset ι) : (∑ x ∈ s, if p x then 1 else 0) = (#({x ∈ s | p x})) := by
  have : s = {x ∈ s | p x} ∪ s.filter (fun x ↦ ¬ p x) := by
    ext i; simp [Finset.mem_filter]; tauto

  nth_rw 1 [this];
  rw [finite_series_of_disjoint_union' (by rw [disjoint_left]; simp; grind)] -- sum_union is just type-generic finite_series_of_disjoint_union
  rw [← add_zero #({x ∈ s | p x})]
  congr 1
  · rw [Finset.sum_congr rfl (g:= fun i ↦ 1)] -- We've already made sum_congr'. This would just be over sets instead of Icc. Who cares
    rw [sum_const']; simp
    · intro x hx; simp at hx; simp [hx]
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_filter] at hx
  simp [hx.2]


lemma nat_eq_sum_lt (m n:ℕ) (h: n ≤ m) :
    n = ∑ j : Fin m, if n > j then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if n > j then 1 else 0),
      Finset.sum_boole']
  simp; rw [← Finset.card_range n]
  congr; ext i; simp [Finset.mem_filter]; grind


/-- {given}`aᵢ` Exercise 7.1.7. Uses {lean}`Fin m` (so {lean}`aᵢ < m`) instead of the book's {lean}`aᵢ ≤ m`;
  the bound is baked into the type, and {kw (of := «term_<_»)}`<` replaces {kw (of := «term_≤_»)}`≤` to match the 0-indexed shift. -/
theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  simp [Set.toFinset_setOf]
  conv => lhs; arg 2; intro i; rw [nat_eq_sum_lt (n := a i ) (m:=m) (by grind)]
  rw [finite_series_comm' Finset.univ Finset.univ
      (fun p ↦ if (a p.1 : ℕ) > ((p.2:Fin m) : ℕ) then 1 else 0)]
  congr; ext j; simp only [Fin.val_fin_lt]
  simp only [sum_boole']

end Finset
