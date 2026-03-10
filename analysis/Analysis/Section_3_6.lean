import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/
set_option linter.unusedVariables false

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  use fun x ↦ let w := nat_equiv ((x:ℕ) * 2); ⟨w, by unfold w; simp; apply w.property⟩
  constructor
  · intro a b h; simp at h;
    rw [coe_inj] at h; simpa using h
  intro ⟨y, hy⟩; simp at hy; choose hy hey using hy
  choose z hz using hey
  use z; simp [show z*2 = z + z by ring]
  rw [← hz]; simp

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  use id; exact Function.bijective_id -- I feel like this is known enough that I don't need to justify

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  choose f hf using h -- Borrowed from rkirov because I was trying to do exactly this but I couldn't
  let e := Equiv.ofBijective f hf -- Find the theorems
  use e.symm
  exact Equiv.bijective e.symm

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  choose f1 hf1 using h1; choose f2 hf2 using h2
  let e1 := Equiv.ofBijective f1 hf1; let e2 := Equiv.ofBijective f2 hf2
  use e2 ∘ e1
  apply Function.Bijective.comp (Equiv.bijective e2) (Equiv.bijective e1)


/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩
-- Setoid means "set with an equivalence relation"

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) : -- Borderline definitional
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

lemma SetTheory.Set.nat_to_fin (n:ℕ) (i j: ℕ) (hi: i < n) (hj: j < n) :
    Fin_mk _ i hi = Fin_mk _ j hj ↔ i = j := by
  refine ⟨?_, by intro h; subst h; rfl⟩
  intro h; simpa using h

lemma SetTheory.Set.nat_to_fin_to_nat (n:ℕ) (i: ℕ) (hi: i < n) :
(Fin_mk _ i hi : ℕ) = i := by
  simp


/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by
  refine ⟨?_, by rintro rfl; rfl⟩
  intro h; unfold castSucc at h; simp at h; rw [← SetTheory.Set.coe_inj]; exact h

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by
  have := Fin.toNat_lt (x); unfold castSucc; simp at *; linarith


/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

theorem SetTheory.Set.Fin.castPred_inj {n} {x y : Fin (n + 1)} (hx : (x : ℕ) ≠ n) (hy : (y : ℕ) ≠ n) :
    castPred x hx = castPred y hy ↔ x = y := by
  refine ⟨?_, by rintro rfl; rfl⟩
  intro h; unfold castPred at h; simp at h; rw [← SetTheory.Set.coe_inj]; exact h

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by
  unfold castSucc castPred; simp

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by
  unfold castSucc castPred; simp

/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

#check SetTheory.Set.Fin.coe_inj

lemma SetTheory.Set.Fin.coe_inj' {n: ℕ } (a b : Fin n) : (a:ℕ) ≠ (b:ℕ) ↔ a ≠ b := by
  rw [not_iff_not, coe_inj]

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by have := Fin.toNat_lt i; linarith)
  else
    Fin_mk _ ((x:ℕ) - 1) (by have := Fin.toNat_lt x; rw [← coe_inj'] at h; omega)

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by simp) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  unfold succAbove; split_ifs with h <;> (simp; omega)

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
    simp [predAbove, succAbove]; rw [← coe_inj'] at h
    split_ifs with h1 h2 <;> simp at * <;> try omega

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
  simp [predAbove, succAbove];
  split_ifs with h1 h2 <;> simp at * <;> simp at * <;> try omega


/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
(nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  rw [has_card]; symm -- Easier to add than subtract
  use fun i ↦ ⟨((i+1:ℕ):nat), by simp; refine ⟨subtype_property _ _, ?_⟩; linarith [Fin.toNat_lt i]⟩
  constructor
  · intro a b h; simp at h; rwa [Fin.coe_inj]
  intro ⟨j, hj⟩; simp at hj; choose hjnat hj1 hjn using hj
  set j' := nat_equiv.symm ⟨j, hjnat⟩ -- Avoid subtraction
  choose k hk using Nat.exists_eq_add_one_of_ne_zero (n := j') (by linarith)
  use ⟨(k:nat), by simp; refine ⟨subtype_property _ _, ?_⟩; linarith⟩
  simp; rw [nat_to_fin_to_nat];
  rw [← hk];
  simp [j']; linarith

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX; subst this
  choose x hx using nonempty_def hnon
  choose error _ using hf.2 ⟨x,hx⟩
  have := error.prop; simp at this
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  constructor <;> intro h
  · choose f hf using h
    by_contra hc; push_neg at hc; choose x hx using nonempty_def hc
    have := (f ⟨x, hx⟩).prop
    simp at this
  subst X; use fun x ↦ absurd x.prop (by simp)
  constructor <;> intro x <;> have := x.prop <;> simp at this




-- I tried using Fin.castPred here, but I started having issues like
-- (x : Fin n) and (x : Fin n - 1 + 1) being different objects

-- Once I fixed that, I had to unravel a ▸
-- every time I wanted to work with that object.

-- Soooo I'm just not doing that. This can be left in its original form.


abbrev SetTheory.Set.lift_erase (X: Set) (x: X) :
(X \ {x.val}: Set) → X := fun ⟨z, hz⟩ ↦ ⟨ z, by aesop ⟩

lemma SetTheory.Set.lift_erase_objinj (X: Set) (x : X):
  ∀ z, ((lift_erase X x) z).val = z.val := by simp

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  have hι := lift_erase_objinj X x; set ι := lift_erase X x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property -- x maps to index m₀
  rw [← Fin.coe_toNat] at hm₀f; simp at hm₀f
  have hne x': (f (ι x'):ℕ) ≠ m₀ := by -- Injective: other numbers can't map to m₀
      have := by simpa using x'.prop;
      contrapose! this; intro _;
      rw [← this, ← Fin.coe_inj, hf.1.eq_iff] at hm₀f;
      symm; rwa [← coe_inj, hι] at hm₀f
  have h z (hz : z = x ) := hz ▸ hm₀f; have h z := mt (h z)

  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x')) -- Original map f x < n
    let := hne x'
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by
    constructor
    · intro a b h;rw [← coe_inj]; rw [← hι, ← hι b]; congr 1; apply hf.1; rw [Fin.coe_inj]
      have ha := hg_def a;have hb := hg_def b
      have : (f (ι a):ℕ) < m₀ ↔ (f (ι b):ℕ) < m₀ := by

        by_contra hc; rw [not_iff] at hc; split_ifs at ha with ha' <;>
        simp only [ha', not_true_eq_false, false_iff, not_false_eq_true, true_iff] at hc
        <;> simp [hc] at hb <;> rw [← h, ha] at hb <;> try simp at hc
        · apply hne b; omega
        · apply hne a; omega
      split_ifs at ha with h1 <;> simp only [h1, false_iff, true_iff] at this <;>
      simp [this] at hb <;> rw [h] at ha <;> rw [ha] at hb
      · exact hb
      · have := hne b; have := hne a; omega

    intro y;

    by_cases hy: y < m₀
    · have hex := hf.2 (Fin_embed _ _ (by simp) y)
      have hex : ∃ a, (f a) = (y:ℕ) := by use hex.choose; rw [hex.choose_spec]; simp
      choose a ha using hex;
      let a' : X':= ⟨a, by simp [X', a.prop]; rw [coe_inj]; apply h; linarith⟩
      use a'; rw [← ha] at hy;
      have := hg_def a'; simp [a', hy] at this;
      rw [Fin.coe_inj, ← ha]; convert this
    · let yp1 := Fin_mk n (y+1) (by have := Fin.toNat_lt y; omega)
      have hex := hf.2 yp1
      have hex : ∃ a, (f a) = (y+1:ℕ) := by use hex.choose; rw [hex.choose_spec]; simp
      choose a ha using hex
      let a' : X' := ⟨a, by simp [X', a.prop]; rw [coe_inj]; apply h; linarith⟩
      use a'; have := hg_def a';
      rw [Fin.coe_inj]; rw [if_neg] at this; convert this;
      rw [ha]; omega
      · linarith
  use g




/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro X m h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X





/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction' n with n ih
  · use 0; intro i; have := i.prop; simp at this
  choose M ih using ih (fun i ↦ f (Fin.castSucc i))
  use max M (f (Fin.last n))
  intro i;
  by_cases hi : i = n
  · convert le_max_right _ _; simp [hi]
  apply le_trans ?_ (le_max_left _ _)
  specialize ih (Fin.castPred i hi)
  convert ih using 1; congr; simp

-- Note: this is a different proof from the one I saw in the original text??
-- It's fine tho, both make sense
-- Maybe based on "One can also use similar arguments to show that any unbounded
-- set..." in Remark 3.6.13

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  · choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  constructor <;> intro h
  · suffices X.has_card 0 from ⟨⟨0, this⟩, has_card_to_card this⟩
    rwa [has_card_zero]
  rw [← has_card_zero]
  convert has_card_card h.1; rw [h.2]

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl


/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
(X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  choose n hX using hX; have hX' := has_card_to_card hX
  suffices (X ∪ {x}).has_card (n+1) from ⟨⟨n+1, this⟩, has_card_to_card (hX' ▸ this)⟩
  unfold has_card at *; symm at ⊢ hX
  choose f hf using hX
  use fun i ↦ if hi: i = n then
    ⟨x, by simp⟩
  else
    let w := f (Fin.castPred i hi)
    ⟨w, by simp [w.prop]⟩
  constructor
  · intro a b h; simp at h
    split_ifs at h with ha hb hc <;> simp at h
    · simp [ha, hb]
    · apply absurd ?_ hx; rw [h]; apply subtype_property
    · apply absurd ?_ hx; rw [← h]; apply subtype_property
    · rw [coe_inj] at h; apply hf.1 at h; rwa [Fin.castPred_inj] at h
  intro y; have :=by simpa using y.prop
  rcases this with hy | hy
  · choose i hi using hf.2 ⟨y, hy⟩
    use Fin.castSucc i; simp;
    conv => lhs; arg 1; rw [hi]
  · use Fin.last n; simp
    conv => lhs; arg 1; rw [← hy]

noncomputable abbrev SetTheory.Set.np1_card_term {X:Set} {n:ℕ} (h: X.has_card (n + 1)) : X:=
Classical.choice ( let ⟨x, hx⟩ := nonempty_def (pos_card_nonempty (by omega) h); ⟨⟨x, hx⟩⟩)



/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
(X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  choose NX hX using hX; choose NY hY using hY
  induction' NY with n ih generalizing Y
  · rw [has_card_zero] at hY; subst Y; simp; use NX
  have y := np1_card_term hY
  have herase := card_erase (by simp) hY y; simp at herase
  have ⟨h1, h2⟩:= ih herase
  apply has_card_to_card at herase; apply has_card_to_card at hY
  by_cases h: y.val ∈ X ∪ Y \ {↑y}
  · suffices h : X ∪ Y \ {↑y} = X ∪ Y from ?_
    · rw [h] at h1 h2; refine ⟨h ▸ h1, by omega⟩
    ext i; by_cases hi : i = y.val
    · subst hi; simp [h]; simp at h; tauto
    simp_all
  have ⟨h3, h4⟩:= card_insert h1 h
  suffices h : (X ∪ Y \ {↑y}) ∪ {↑y}  = X ∪ Y from ?_
  · rw [h] at h3 h4; rw [h4]
    refine ⟨h3, by rw [hY]; omega⟩
  ext i; simp; grind


lemma SetTheory.Set.Disjoint.notMem_of_mem_left {X Y : Set} {x : Object}
 (hx : x ∈ X) (hd : Disjoint X Y) : x ∉ Y := by
  rw [disjoint_iff] at hd;
  contrapose! hd; apply nonempty_of_inhabited (x := x)
  simp; exact ⟨hx,hd⟩

lemma SetTheory.Set.Disjoint.notMem_of_mem_right {X Y : Set} {x : Object}
 (hy : x ∈ Y) (hd : Disjoint X Y) : x ∉ X := by
  rw [disjoint_iff] at hd;
  contrapose! hd; apply nonempty_of_inhabited
  simp; exact ⟨hd,hy⟩



theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
(hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  choose NX hX using hX; choose NY hY using hY
  induction' NY with n ih generalizing Y
  · rw [has_card_zero] at hY; subst Y; simp
  have y := np1_card_term hY
  have he1 := card_erase (by simp) hY y; simp at he1
  have h1 := ih ?_ he1
  have ⟨h2, _⟩ := card_union ⟨_, hX⟩ ⟨_, he1⟩
  have ⟨_, h3⟩ := card_insert h2 (x := y) (by simp [Disjoint.notMem_of_mem_right y.prop hdisj])
  rw [h1, has_card_to_card he1] at h3; rw [has_card_to_card hY]
  convert h3 using 1;
  congr 1; ext i; simp; grind
  · rw [disjoint_iff]; ext i; simp; intro hx hy;
    contrapose! hy; apply Disjoint.notMem_of_mem_left hx hdisj

theorem SetTheory.Set.card_union_disjoint' {X Y:Set} (hX: X.finite) (hY: Y.finite)
(hdisj: Disjoint X Y) : (X ∪ Y).finite ∧ (X ∪ Y).card = X.card + Y.card  := by
  exact ⟨(card_union hX hY).1, card_union_disjoint hX hY hdisj⟩

lemma SetTheory.Set.subset_empty {X:Set} : X ⊆ ∅ → X = ∅ := by
  intro h; rw [subset_def] at h; simp at h
  rwa [eq_empty_iff_forall_notMem]


lemma SetTheory.Set.erase_subset {X Y :Set} {x : Object} (hs : Y ⊆ X)
(hx : x ∉ Y): Y ⊆ X \ {x} := by
  intro y hy; simp [hs _ hy]; contrapose! hx; rwa [← hx]

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  choose n hX using hX
  induction' n with n ih generalizing X
  · rw [has_card_zero] at hX; subst X;
    apply subset_empty at hY; subst Y; simp
  by_cases h: X = Y
  · subst h; simp; use n+1
  have hY' : Y ⊂ X := by
    rw [ssubset_def]; refine ⟨hY, by symm; exact h⟩
  choose x hx using ssubset_exists _ _ hY'
  lift x to X using hx.1
  have := card_erase (by simp) hX x
  specialize ih (erase_subset hY hx.2) this
  simp [ih]; apply le_trans ih.2;
  simp [has_card_to_card this, has_card_to_card hX]

#check SetTheory.Set.nonempty_of_inhabited'




theorem SetTheory.Set.card_erase' {n:ℕ} {X:Set} (hX: X.has_card n) (x:X) :
    n ≥ 1 ∧ (X \ {x.val}).has_card (n-1) := by
  have hn : n ≥ 1 := by
    by_contra! h; simp at h; subst h; rw [has_card_zero] at hX;
    contrapose! hX; apply nonempty_of_inhabited' x
  refine ⟨hn, card_erase hn hX x⟩



/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  choose n hX using hX
  choose x hx using ssubset_exists _ _ hY
  lift x to X using hx.1
  have ⟨hn, hm1⟩:= card_erase' hX x
  have hm1' := has_card_to_card hm1; have hX' := has_card_to_card hX
  apply lt_of_le_of_lt (b := (X \{x.val}).card) ?_ ?_
  · apply (card_subset ⟨_,hm1⟩ (erase_subset hY.1 hx.2)).2
  · rw[hm1', hX']; omega

lemma SetTheory.Set.image_zero {X Y : Set} (f: X → Y) : image f ∅ = ∅ := by
  ext y; simp [image]


abbrev SetTheory.Set.singleton_has_card_one:= Example_3_6_7a

theorem SetTheory.Set.singleton_finite (x:Object) : ({x}:Set).finite := ⟨1, singleton_has_card_one x⟩

theorem SetTheory.Set.singleton_card_one (x:Object) : ({x}:Set).card = 1 := has_card_to_card (singleton_has_card_one x)

theorem SetTheory.Set.eq_singleton_card_one (X : Set) (h : ∃ x, X = {x}) : X.card = 1 := by
  choose x hx using h; rw [hx]; simp [singleton_card_one]

theorem SetTheory.Set.card_one_eq_singleton (X : Set) (h : X.card = 1) : ∃ x, X = {x} := by
  apply card_to_has_card (by simp) at h
  rw [has_card] at h; symm at h; choose f hf using h
  use (f (Fin_mk _ 0 (by simp))); ext x; simp
  refine ⟨?_, by rintro rfl; apply subtype_property⟩
  intro hx; choose i hi using hf.2 ⟨x, hx⟩
  simp [← coe_inj] at hi; subst hi; congr;
  have := Fin.toNat_lt i; simp at this; aesop



/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  choose n hX using hX
  induction' n with n ih generalizing X
  · rw [has_card_zero] at hX; subst X; simp [image_zero]
  have x := np1_card_term hX
  have he := card_erase (by simp) hX x; simp at he
  have hi := lift_erase_objinj X x; set i := lift_erase X x
  have ⟨hfin,hineq⟩ := ih (fun z ↦ f (i z)) he
  apply has_card_to_card at he; apply has_card_to_card at hX
  rw [hX]; rw [he] at hineq
  suffices (image (fun z ↦ f (i z)) (X \ {↑x})) ∪ {↑(f x)} = image f X from ?_
  · rw [← this]
    have := card_union hfin (singleton_finite (f x))
    rw [singleton_card_one] at this
    refine ⟨this.1, le_trans this.2 (by simp [hineq])⟩
  ext j; simp only [mem_union, mem_singleton];
  repeat rw [mem_image]
  constructor
  · intro h
    rcases h with h | h
    · choose k hk using h; use i k; simp at hk; simp [hi, hk]
    · use x; simp [x.prop, h]
  rintro ⟨z, h1, h2⟩
  by_cases h : z = x
  · subst h; right; rw [h2]
  let z' : (X \ {↑x}:Set):= ⟨z, by simp [h1]; rwa [← coe_inj] at h⟩
  left; use z'; refine ⟨z'.prop,  by convert h2⟩


/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
    apply EquivCard_to_card_eq ; symm
    use fun x ↦ ⟨f x, by aesop⟩
    constructor
    · intro _ _ h; simpa [coe_inj, hf.eq_iff] using h;
    intro y; have := y.prop; rw [mem_image] at this
    choose x hx1 hx2 using this
    use x; simp; congr;

lemma SetTheory.Set.single_prod (X : Set) (x : Object) :
({x}:Set) ×ˢ X ≈ X := by
  use fun z ↦ right z
  constructor
  · intro a b h; simp at h; ext; repeat rw [pair_eq_left_right]
    rw [h]; have := (left a).prop; have := (left b).prop
    simp_all
  intro y; use mk_cartesian ⟨x, by simp⟩ y
  simp



/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  choose n hX using hX; choose m hY using hY
  induction' n with n ih generalizing X
  · rw [has_card_zero] at hX; subst X; simp
  let x := np1_card_term hX
  have := card_erase (by simp) hX x; simp at this
  have ⟨ih1, ih2⟩ := ih this
  set A := (X \ {↑x}) ×ˢ Y; set B := ({↑x}:Set) ×ˢ Y
  suffices h :X ×ˢ Y = A ∪ B from ?_
  · rw [h]; have hsing:= single_prod Y x
    have hsing := (EquivCard_to_has_card_eq hsing).mpr hY
    have ⟨h1, h2⟩ := card_union_disjoint' ih1 ⟨_, hsing⟩ ?_
    refine ⟨h1, ?_⟩; rw [h2, ih2]
    let hctc := @has_card_to_card
    rw [hctc hY, hctc hX,hctc hsing, hctc this]; ring
    · rw [disjoint_iff]; ext i; simp; aesop
  unfold A B; ext i; simp only [mem_union];
  repeat rw [mem_cartesian]
  constructor <;> intro h
  · choose a b h using h
    by_cases hl : a = x
    · right; use ⟨a, by simp [hl]⟩; use b;
    left; use ⟨a, by aesop⟩; use b
  rcases h with h | h
  · choose a b h using h; use ⟨a, by have := (a).prop; aesop⟩;  use b
  choose a b h using h
  use ⟨a, by have := a.prop; have := x.prop; aesop ⟩; use b


noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := fun F ↦ ((powerset_axiom F).mp F.prop).choose
  invFun := fun f ↦ ⟨f, by rw [powerset_axiom]; use f⟩
  left_inv := by
    intro f; simp; generalize_proofs h1 h2
    ext; simp; apply h1.choose_spec
  right_inv := by intro f; simp

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [pow_fun_equiv.apply_eq_iff_eq]


lemma SetTheory.Set.EquivCard_to_finite {X Y : Set} (hXY : X ≈ Y) : X.finite ↔ Y.finite := by
  constructor <;> intro h <;> choose n h using h <;> use n
  · rwa [← EquivCard_to_has_card_eq hXY]
  · rwa [EquivCard_to_has_card_eq hXY]


theorem SetTheory.Set.pow_eq_pow_fin (A:Set) {B : Set} (hB: B.finite): A ^ B ≈ A ^ (Fin B.card) := by
  have: B ≈ Fin B.card := has_card_card hB; symm at this
  choose f hf using this
  use fun F ↦ pow_fun_equiv.symm (fun i ↦ (pow_fun_equiv F) (f i))
  constructor
  · intro F G h; simp at h; apply pow_fun_equiv.injective; ext i;
    choose j hj using hf.2 i; have h := congr_fun h j; rwa [hj, ← coe_inj] at h

  let finv : B → Fin (B.card):= fun b ↦ (hf.2 b).choose
  intro F; use pow_fun_equiv.symm (fun i ↦ (pow_fun_equiv F) (finv i))
  simp; rw [pow_fun_equiv.symm_apply_eq]; ext i
  congr; apply congr_arg; unfold finv
  generalize_proofs h1;
  apply hf.1; simp [h1.choose_spec]

theorem SetTheory.Set.pow_fin_eqv_pow_fin {A : Set} (n : ℕ): A ^ Fin (n+1) ≈ A ×ˢ (A ^ (Fin (n))) := by
  use fun F ↦
    let f := pow_fun_equiv F
    mk_cartesian (f (Fin.last n))
    (pow_fun_equiv.symm (fun x ↦ f (Fin_embed _ _ (by simp) x)))
  simp [mk_cartesian]
  constructor
  · intro F G h; simp at h
    have ⟨h1, h2⟩ := h
    apply pow_fun_equiv.injective; ext i;
    by_cases hi : i = n
    · (have : i = Fin.last n := by simp [hi]); rw [this]; exact h.1
    rw [coe_inj] at h2; apply pow_fun_equiv.symm.injective at h2
    have := congr_fun h2 ⟨i.val, ?_⟩
    congr;
    · rw [mem_Fin]; use i; have := Fin.toNat_lt i; refine ⟨ by omega, by simp⟩
  intro y;
  let f : Fin (n+1) → A := fun x ↦
    if h: x = n then
      left y
    else
      pow_fun_equiv (right y) (Fin.castPred x h)
  use pow_fun_equiv.symm f
  simp; congr; rw [pair_eq_left_right]; simp
  unfold f; simp; congr; rw [pow_fun_equiv.symm_apply_eq];
  ext i; simp [ne_of_lt (Fin.toNat_lt i)]
  congr; apply congr_arg; unfold Fin.castPred; simp



theorem SetTheory.Set.card_pow_fin {Y:Set} (hY: Y.finite) (m : ℕ) :
    (Y ^ (Fin m)).finite ∧ (Y ^ (Fin m)).card = Y.card ^ m := by
  choose n hY using hY;
  induction' m with m ih -- Y ^ ∅
  · simp; suffices h : (Y ^ ∅).has_card 1 from ⟨⟨1, h⟩, has_card_to_card h⟩
    let f:(∅:Set) → Y := fun x ↦  absurd (x.prop) (by simp)
    suffices h : (Y ^ (∅ : Set)) = ({(pow_fun_equiv.symm f).val}:Set) from ?_
    · rw [h]; apply singleton_has_card_one
    ext F; simp; constructor
    · rintro ⟨f, rfl⟩; congr; ext i; have := i.prop; simp at this
    rintro rfl; use f; congr
  rcases n with _ | n; -- ∅ ^ F : vacuous
  · rw [has_card_zero] at hY; subst Y;
    suffices h : ((∅:Set) ^ Fin (m + 1)) = ∅ by rw [h]; simp
    ext F; simp; intro f
    have := (f (Fin.last _)).prop; simp at this
  let Z := (Y ^ (Fin m)) -- Extract last element to make prod
  have h : (Y ^ Fin (m+1)) ≈ Y ×ˢ Z  := by unfold Z; convert pow_fin_eqv_pow_fin _
  have ⟨hfin, hcard⟩:= card_prod ⟨_, hY⟩ ih.1
  rw [← EquivCard_to_card_eq h] at hcard
  rw [← EquivCard_to_finite h] at hfin
  refine ⟨hfin, ?_⟩
  rw [hcard, ih.2];
  ring


theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  have h := pow_eq_pow_fin Y hX; rw [EquivCard_to_card_eq h, EquivCard_to_finite h ]
  apply card_pow_fin hY


/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) :=
  ⟨prod_commutator _ _,(prod_commutator _ _).bijective⟩

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

noncomputable abbrev SetTheory.Set.curry_equiv' (A B C : Set) : (A → (B → C)) ≃ (A ×ˢ B → C) :=
  curry_equiv (X:=A) (Y:=B) (Z:=C)


/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  let e1 := pow_fun_equiv' (A ^ B) C
  let e2 := Equiv.arrowCongr (Equiv.refl C) (pow_fun_equiv' A B)
  let e3 := curry_equiv' C B A
  let e4 := Equiv.arrowCongr (prod_commutator C B) (Equiv.refl A)
  let e5 := pow_fun_equiv' A (B ×ˢ C)
  use (e5.symm ∘ e4 ∘ e3 ∘ e2 ∘ e1)
  simp [e2.bijective]

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by
  rw [← Fin_card a, ← Fin_card b, ← Fin_card c]
  have h := card_pow (Fin_finite a) (Fin_finite b); rw [← h.2]
  have h := card_pow h.1 (Fin_finite c); rw [← h.2]
  have h := card_prod (Fin_finite b) (Fin_finite c); rw [← h.2]
  have h := card_pow (Fin_finite a) h.1 ; rw [← h.2]
  apply EquivCard_to_card_eq
  apply (pow_pow_EqualCard_pow_prod _ _ _)

lemma SetTheory.Set.union_mem_of_notMem_left {X Y : Set} {x : (X ∪ Y:Set)}
 (hx : ↑x  ∉ X): ↑x ∈ Y := by simpa [hx] using x.prop

lemma SetTheory.Set.union_mem_of_notMem_right {X Y : Set} {x : (X ∪ Y:Set)}
 (hy : ↑x  ∉ Y): ↑x ∈ X := by simpa [hy] using x.prop


#check SetTheory.Set.EquivCard_to_card_eq

lemma SetTheory.Set.eq_card_to_EquivCard {A B : Set} (hA: A.finite) (hB: B.finite) (h:A.card = B.card):
 A ≈ B := by
  choose n hA using hA; choose m hB using hB;
  rw [has_card_to_card hA, has_card_to_card hB] at h; subst h
  choose f hf using hA;unfold has_card at hB; symm at hB; choose g hg using hB
  use g ∘ f
  exact Function.Bijective.comp hg hf





-- I seem to totally need Classical
open Classical in
theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  use fun z ↦
    pow_fun_equiv.symm fun w ↦ if h: w.val ∈ B then
      pow_fun_equiv (left z) ⟨w, h⟩
    else
      pow_fun_equiv (right z) ⟨w, union_mem_of_notMem_left h⟩
  constructor
  · intro a b h; simp at h; ext; repeat rw [pair_eq_left_right]
    simp; constructor <;> rw [coe_inj] <;> apply pow_fun_equiv.injective <;> ext i
    <;> have := congr_fun h ⟨i, by aesop⟩ <;>
    [simp [i.prop] at this; simp [Disjoint.notMem_of_mem_right i.prop hd] at this]
    <;> rw [this]
  intro y;
  let hba : B → A := fun i ↦ (pow_fun_equiv y) ⟨i, by aesop⟩
  let hca : C → A := fun i ↦ (pow_fun_equiv y) ⟨i, by aesop⟩
  use (mk_cartesian (pow_fun_equiv.symm hba) (pow_fun_equiv.symm hca))
  simp; rw [pow_fun_equiv.symm_apply_eq]; ext i;
  by_cases hi : i.val ∈ B; simp [hi, hba]; simp [hi, hca];

abbrev SetTheory.Set.interval (a b : ℕ) := Fin b \ Fin a

lemma SetTheory.Set.disjoint_sdiff_right (A B : Set) : Disjoint (A) (B \ A) := by
  rw [disjoint_iff]; ext; simp; aesop


#check Nat.sub_lt_sub_right
lemma SetTheory.Set.interval_card (a b : ℕ) (h: a ≤ b) : (interval a b).finite ∧ (interval a b).card = b - a := by
  rw [← Fin_card (b-a)];
  suffices h : interval a b ≈ Fin (b - a) from ?_
  · have: has_card _ _:= h
    refine ⟨⟨_, this⟩, has_card_to_card ((Fin_card (b-a)).symm ▸ this)⟩
  symm
  use fun i ↦ ⟨((i:ℕ ) + a:nat), by
    have h1:= Fin.toNat_lt i; unfold interval; simp; have h3 := ((i:ℕ ) + a:nat).prop
    simp at h3; simp [h3];omega⟩
  constructor
  · intro i j h; simp at h; rwa [← Fin.coe_inj] at h
  intro ⟨k,hk⟩; simp [interval] at hk
  obtain ⟨ ⟨hk1, hkb⟩, hk2⟩  := hk; specialize hk2 hk1
  let K : nat := ⟨k, hk1⟩
  use ⟨((K:ℕ)-a:nat),
  by simp; have := ((K:ℕ)-a:nat).prop; simp at this; simp [this];
     apply Nat.sub_lt_sub_right (by convert hk2); convert hkb⟩
  simp;
  conv => rhs; rw [show k = ((K:nat):ℕ) by simp [K]]
  congr; refine Eq.symm (Nat.eq_add_of_sub_eq hk2 ?_)
  rw [Fin.toNat]; generalize_proofs h1 h2
  have := h2.choose_spec.choose_spec; simp at this
  conv => lhs; rw [this]
  simp

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by
  have :=interval_card b (b+c); simp at this
  rw [← Fin_card a, ← Fin_card b, ← this.2]
  have hab := card_pow (Fin_finite a) (Fin_finite b); rw [← hab.2]
  have hac := card_pow (Fin_finite a) (this.1); rw [← hac.2]
  have hbc := card_union_disjoint' (Fin_finite b) (this.1) (disjoint_sdiff_right _ _); rw [← hbc.2]
  have habc := card_pow (Fin_finite a) (hbc.1); rw [← habc.2]
  have habac := card_prod hab.1 hac.1; rw [← habac.2]
  apply EquivCard_to_card_eq
  apply (pow_prod_pow_EqualCard_pow_union _ _ _ (disjoint_sdiff_right _ _))


/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor <;> intro h
  · choose f hf using h
    rw [← card_image_inj hA hf]
    apply (card_subset hB (image_in_codomain f A)).2
  choose n hA using hA; choose m hB using hB
  rw [has_card_to_card hA, has_card_to_card hB] at h
  unfold has_card at hA hB; symm at hB
  choose fa hfa using hA; choose fb hfb using hB
  let g : Fin n → Fin m := fun i ↦ Fin_embed _ _ h i
  use (fb ∘ g ∘ fa)
  · intro x y h; apply hfb.injective at h; apply hfa.injective;
    simp only [Function.comp_apply] at h;
    unfold g at h; simp at h; rwa [←coe_inj]

open Classical in
/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  choose a ha using nonempty_def hA
  use fun b ↦ if h: ∃ x : A, f x = b then
    h.choose
  else
    ⟨a, ha⟩
  intro a; use f a; simp;
  generalize_proofs h1; apply hf; apply h1.choose_spec -- hf makes choice unique


#check SetTheory.Set.union_eq_partition

lemma SetTheory.Set.inter_union_sdiff_right (A B: Set) : A ∩ B ∪ A \ B = A := by
  ext i; simp; grind

lemma SetTheory.Set.inter_union_sdiff_left (A B: Set) : A ∩ B ∪ B \ A = B := by
  ext i; simp; grind

lemma SetTheory.Set.sdiff_finite {A B : Set} (hA: A.finite) (hB: B.finite) : (A \ B).finite := by
  apply (card_subset hA (by intro x; simp; tauto)).1

lemma SetTheory.Set.inter_finite {A B : Set} (hA: A.finite) (hB: B.finite) : (A ∩ B).finite := by
  apply (card_subset hA (by intro x; simp; tauto)).1


/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
    rw [SetTheory.Set.union_eq_partition]
    nth_rw 2 [union_comm]; rw [inter_union_sdiff_right]
    have := card_union_disjoint' hA (sdiff_finite hB hA) (by simp [disjoint_iff]; ext i; simp; grind)
    rw [this.2]
    have := card_union_disjoint' (sdiff_finite hB hA) (inter_finite hA hB)  (by simp [disjoint_iff]; ext i; simp; grind)
    rw [add_assoc, ← this.2]
    rw [union_comm, inter_union_sdiff_left A B]

lemma SetTheory.Set.card_iUnion_remove_elem {n: ℕ}{A: Fin (n+1) → Set} (hA: ∀ i, (A i).finite):
(iUnion _ A) = A (Fin.last n) ∪ (iUnion _ (fun i ↦ A (Fin.castSucc i))):= by
  ext i; rw [mem_iUnion, mem_union, mem_iUnion]
  constructor
  · rintro ⟨a, ha⟩; by_cases h : a = Fin.last n
    · left; rwa [← h]
    · simp at h; right; use Fin.castPred a h; convert ha; simp
  intro h; rcases h with h | h
  · use (Fin.last n)
  choose a ha using h; use (Fin.castSucc a)

lemma SetTheory.Set.iUnion_of_finite_is_finite {n : ℕ } (I: Fin n → Set)
(hI: ∀ i, (I i).finite):
  (iUnion _ I).finite := by
  induction' n with n ih
  · use 0; rw [has_card_zero]; ext i; simp [mem_iUnion]
  rw [card_iUnion_remove_elem hI]
  apply (card_union (hI (Fin.last n)) ?_).1
  apply ih _ ; intro i; apply hI (Fin.castSucc i)

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  contrapose! hAcard
  induction' n with n ih
  · simp; apply card_eq_zero_of_empty; ext i; simp [mem_iUnion]
  let A' i:= A (Fin.castSucc i); let hA' := fun i ↦ hA (Fin.castSucc i)
  rw [card_iUnion_remove_elem hA]
  have := card_union (hA (Fin.last n)) (iUnion_of_finite_is_finite A' hA')
  apply le_trans this.2
  rw [add_comm]; gcongr
  · apply ih hA'
    intro i; apply hAcard (Fin.castSucc i)
  convert hAcard (Fin.last n) using 0; constructor <;> omega





/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  · intro hf; intro S hS hScard; apply card_to_has_card (by simp) at hScard
    apply has_card_to_card; rw [has_card] at *; symm at *
    choose g hg using hScard
    use fun i ↦ ⟨f ⟨g i, hS _ (g i).prop⟩, by apply mem_image_of_eval; simp [(g i).prop]⟩
    constructor
    · intro i j h; simp [coe_inj] at h; apply hf at h; simp at h; simp [coe_inj] at h; rwa [hg.1.eq_iff] at h
    intro y; choose x hx1 hx2 using (mem_image _ _ _).mp y.prop; choose i hi using hg.2 ⟨x, hx1⟩
    use i; simp [hi, hx2]
  intro h;
  intro a b hf; by_contra hab; let Z : Set := {↑a, ↑b}; specialize h Z (by intro i hi; aesop)
  have := card_union_disjoint (singleton_finite a) (singleton_finite b) (by simp [disjoint_iff]; ext i; simp; grind)
  simp [← pair_eq, singleton_card_one, singleton_card_one] at this
  rw [this] at h; simp at h; suffices 1 = 2 by simp at this;
  rw [← h]; unfold Z at *; symm
  apply eq_singleton_card_one; use f a; ext i; rw [mem_image]; simp [a.prop, b.prop]
  refine ⟨?_, by rintro rfl; simp⟩; intro h; rcases h with rfl | rfl; rfl; rw [hf]


/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite :=
(card_subset (card_pow (Fin_finite n) (Fin_finite n)).1 (specify_subset _)).1

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

theorem SetTheory.Set.specification_axiom''' {A: Set} {P: A → Prop}
(x : A.specify P): ∃ (h : ↑x ∈ A), P ⟨x, h⟩ := by
  have := x.prop; rwa [specification_axiom''] at this


noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) :
(Fin n) → (Fin n) := by
  have := specification_axiom''' p; simp only [powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.perm_mem_pow {n : ℕ} (p: Permutations n) :
↑p ∈ (Fin n) ^ (Fin n) := by
  have hp:= p.prop; unfold Permutations at hp;
  rw [specification_axiom''] at hp; exact hp.choose

-- perm and equiv both choose a function, whose object equals p's object
-- Thus, perm and equiv have the same object.
-- Same object → same underlying function
theorem SetTheory.Set.perm_toFun_eq_pow_fun_equiv {n : ℕ } (p: Permutations n) (h : ↑p ∈ ((Fin n) ^ (Fin n) : Set)):
Permutations_toFun p = pow_fun_equiv ⟨p, h⟩ := by simp [Permutations_toFun, pow_fun_equiv];

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
Function.Bijective (Permutations_toFun p) := (specification_axiom''' p).choose_spec

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
  simp [Permutations_toFun]; generalize_proofs h1 h2; rw [← coe_inj];
  conv => rhs; rw [← h1.choose_spec, ← h2.choose_spec]
  aesop

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun p :=  Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun e := ⟨pow_fun_equiv.symm e, by
    unfold Permutations; rw [specification_axiom'']; use (subtype_property _ _);
    simp; exact Equiv.bijective e⟩
  left_inv p:= by
    simp [Equiv.ofBijective]; ext; simp;
    unfold pow_fun_equiv Permutations_toFun; simp; generalize_proofs h; exact h.choose_spec
  right_inv e:= by
    simp [Equiv.ofBijective, Permutations_toFun]; ext i; simp; generalize_proofs h
    have := h.choose_spec; conv at this => rhs; unfold pow_fun_equiv; simp
    rw [coe_of_fun_inj] at this; rw [this]
}





/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
(hSc : ∀ i, (S i).has_card m)
(hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
  induction' n with n ih
  · suffices h : ((Fin 0).iUnion S).has_card 0 from ⟨⟨0, h⟩, by simp; apply has_card_to_card h⟩
    rw [has_card_zero]; ext i; simp [mem_iUnion]
  specialize ih (fun i ↦ hSc (Fin.castSucc i)) (fun i j h ↦ hSd ((Fin.castSucc_inj).mp.mt h))
  have hlast := hSc (Fin.last n)
  have ⟨hfin, hcard⟩:= card_union_disjoint' ⟨_, hlast⟩ ih.1 ?_
  rw [ih.2, (has_card_to_card hlast)] at hcard;
  rw [SetTheory.Set.card_iUnion_remove_elem (by intro i; exact ⟨_, (hSc i)⟩)]
  convert And.intro hfin hcard using 2; ring
  · rw [disjoint_comm,disjoint_iff]; ext i; rw [mem_inter, mem_iUnion]; simp
    intro x hx hxn hi; apply Disjoint.notMem_of_mem_left hi ?_
    apply hSd; simp



#check SetTheory.Set.perm_equiv_equiv (n:=4)


abbrev SetTheory.Set.specify_coe {A: Set} {P: A → Prop} (x : A.specify P): A :=
  subtype_mk A (specification_axiom x.prop)


theorem SetTheory.Set.Fin.predAbove_inj {n: ℕ} (i x y: Fin (n+1)) (hx : x ≠ i) (hy : y ≠ i):
    x = y ↔ Fin.predAbove i x hx = Fin.predAbove i y hy := by
  refine ⟨by rintro rfl; rfl, ?_⟩; intro h; have := congr_arg (Fin.succAbove i) h
  simp [Fin.succAbove_predAbove] at this; rwa [← Fin.coe_inj] at this

theorem SetTheory.Set.Fin.succAbove_inj {n: ℕ} (i: Fin (n+1)) (x y: Fin n):
    x = y ↔ Fin.succAbove i x = Fin.succAbove i y := by
  refine ⟨by rintro rfl; rfl, ?_⟩; unfold succAbove; intro h
  split_ifs at h with hx h hy ; simp_all; aesop; (simp_all; omega);
  (simp at h; rw [← coe_toNat] at h; rw [SetTheory.Object.natCast_inj] at h; omega); simp_all


/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSlast i: ∀(s: S i), (perm_equiv_equiv (specify_coe s)) (Fin.last n) = i := by
    intro s; unfold specify_coe; convert (specification_axiom''' s).choose_spec

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    have equiv : S i ≃ Permutations n := Equiv.ofBijective
      (fun s ↦ perm_equiv_equiv.symm (Equiv.ofBijective -- (S i) ≃ (perm n)
          (fun x ↦ Fin.predAbove i
                                ((perm_equiv_equiv (specify_coe s)) (Fin.castSucc x) ) -- - (Fin n) ≃ (Fin n)
                                (by (conv => rhs; rw [← hSlast i s]); simp [specify_coe, subtype_mk]))
                    ?fin_to_fin_is_bijective)) ?si_to_perm_is_bijective
    use equiv, equiv.injective, equiv.surjective
    · constructor -- Prove (Fin n) → (Fin n) is bijective (thus makes a valid perm n)
      · intro a b h; simp only [← Fin.predAbove_inj] at h; simp at h; rwa [← Fin.coe_inj] at h
      · intro y; simp only
        use Fin.castPred ((perm_equiv_equiv (specify_coe s)).symm (Fin.succAbove i y)) ?ne_n; rotate_left;
        · conv => rhs; rw [show n = Fin.last n by simp]
          rw [ne_eq,← Fin.coe_inj, Equiv.symm_apply_eq, hSlast i s]; apply Fin.succAbove_ne
        generalize_proofs h1; simp [Fin.castSucc_castPred _ h1]
    · constructor-- Prove (S i) →  (perm n) is injective
      · intro a b h; have hab (j : S i) : (j:Object) = (specify_coe j) := by simp
        ext; rw [hab, hab]; congr 1;
        rw [← (perm_equiv_equiv).injective.eq_iff]; ext k; congr 1
        by_cases hk : k = Fin.last n
        · subst hk; rw[hSlast i a, hSlast i b]
        · simp [Equiv.ofBijective] at h;
          replace h := congr_fun h.1;
          specialize h (Fin.castPred k (by contrapose! hk; simp [Fin.coe_inj,hk]))
          simp only [Fin.castSucc_castPred, ← Fin.predAbove_inj] at h; exact h
      · intro p; simp only -- Prove (S i) → (perm n) is surjective (construct (perm n) → (S i))
        let f : Fin (n+1) → Fin (n+1) := fun x ↦ -- (Fin n) ≃ (Fin n) used within (perm n) → (S i)
          if hx : x = n then i
          else Fin.succAbove i ((perm_equiv_equiv p) (Fin.castPred x hx))
        use ⟨ perm_equiv_equiv.symm (Equiv.ofBijective f ?f_is_bijective),
          by unfold S f; rw [specification_axiom'']; use (subtype_property _ _); simp [Equiv.ofBijective]⟩
        unfold f; simp [perm_equiv_equiv.symm_apply_eq] -- Prove that this is the correct input
        ext j; simp [specify_coe, Equiv.ofBijective]; unfold subtype_mk; simp
        · constructor -- Prove that f was bijective (and thus could form a perm n element)
          · intro x y h; unfold f at h; simp at h; split_ifs at h with hx h2 hy; simp_all
            all_goals rw [← Fin.coe_inj] at h
            · contrapose! h; symm; apply Fin.succAbove_ne
            · contrapose! h; apply Fin.succAbove_ne
            · simp [← Fin.succAbove_inj] at h; rwa [← Fin.coe_inj, Fin.castPred_inj] at h
          · intro y; by_cases hy : y = i
            · use Fin.last n; simp [f, hy]
            · use Fin.castSucc ((perm_equiv_equiv p).symm (Fin.predAbove i y hy)); unfold f; simp
  -- P (n+1) = union S i; and S i ≈ P n. So, we decompose P (n+1) into n+1 terms of P n
  choose m hm using Permutations_finite n; rw [has_card_to_card hm] -- Use union of S i to get desired card
  have := card_iUnion_card_disjoint (fun i ↦ (EquivCard_to_has_card_eq (hSe i).symm).mp hm) ?disjoint
  rw [← this.2]; congr; ext F; rw [mem_iUnion]; unfold S;
  constructor -- Prove that P(n+1) is union of S i
  · intro h; unfold Permutations at h; use (perm_equiv_equiv ⟨F,h⟩ ) (Fin.last n); simp; convert h
  · choose j hj; rw [specification_axiom''] at hj; use hj.choose

  intro i j hij; rw [disjoint_iff]; ext k; unfold S; simp; -- Prove that S i and S j are disjoint
  intro hk1 hk2 t; (have : t = hk1 := by simp); subst this -- (can add their cardinalities)
  rwa [hk2, ← Fin.coe_inj]




/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ): -- I picked such an awful way to do this
    (Permutations n).card = n.factorial := by
  induction' n with n ih
  · simp
    rw [EquivCard_to_card_eq (Y := (∅ : Set) ^ (∅ : Set)) ?_]
    · apply eq_singleton_card_one
      use ↑(fun i ↦ absurd i.prop (by simp) : (∅:Set) → (∅:Set))
      ext i; simp; constructor
      · rintro ⟨f, rfl⟩; rw [coe_of_fun_inj]; ext i; absurd i.prop; simp
      rintro rfl; aesop

    use (fun _ ↦ (pow_fun_equiv.symm (absurd ·.prop (by simp) ))  )
    rw [Function.bijective_iff_has_inverse]
    use (fun _ ↦ (perm_equiv_equiv (n:=0)).symm
      (Equiv.ofBijective
        (absurd ·.prop (by simp))
        (by apply Function.Involutive.bijective; intro i; absurd i.prop; simp)))
    constructor <;> intro i <;> simp <;>
    [rw [perm_equiv_equiv.symm_apply_eq];rw [pow_fun_equiv.symm_apply_eq]]
    <;> ext j <;> absurd j.prop<;> simp
  rw [Permutations_ih, ih]; aesop


theorem SetTheory.Set.Permutations_card' (n: ℕ): -- I did it so it wasn't stupid this time
    (Permutations n).card = n.factorial := by
    induction' n with n ih
    · simp; suffices Permutations 0 = empty ^ empty from ?_
      · rw [this]; apply has_card_to_card; use fun _ ↦ Fin_mk _ 0 (by simp)
        constructor
        · intro f g; simp; apply pow_fun_equiv.injective; ext i; absurd i.prop; simp
        · intro i; use pow_fun_equiv.symm (absurd ·.prop (by simp));
          have := Fin.toNat_lt i; simp; omega
      ext i; unfold Permutations; rw [specification_axiom'']
      rw [fin_0_empty]; constructor; tauto
      · intro h; use h; apply Function.Involutive.bijective; intro i; absurd i.prop; simp
    rw [Permutations_ih, ih]; aesop

-- I was gonna clean up the first version but it didn't work out but I made these cool lemmas
lemma SetTheory.Set.empty_pow_empty_singleton: ∃ x, (empty^empty)= {↑x} := by
  use ↑(fun i ↦ absurd i.prop (by simp) : empty → empty)
  ext i; simp; constructor
  · rintro ⟨f, rfl⟩; rw [coe_of_fun_inj]; ext i; absurd i.prop; simp
  rintro rfl; aesop

lemma SetTheory.Set.empty_pow_empty_uniq: ∃ x, ∀ i, i ∈ (empty^empty) → i = x := by
  choose x hx using empty_pow_empty_singleton
  use x; intro i hi; rw [SetTheory.Set.ext_iff] at hx;
  replace hx := (hx i).mp hi; simpa using hx



/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
