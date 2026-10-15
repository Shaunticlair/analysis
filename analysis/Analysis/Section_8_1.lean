import Mathlib.Tactic

/-!
# Analysis I, Section 8.1: Countability

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
`Countable` typeclass corresponds to what we call "at most countable" in this text.
- Countability of the integers and rationals.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/

namespace Chapter8

/-- The definition of equal cardinality. For simplicity we restrict attention to the Type 0 universe.
This is analogous to `Chapter3.SetTheory.Set.EqualCard`, but we are not using the latter since
the Chapter 3 set theory is deprecated. -/
abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Relation with Mathlib's `Equiv` concept -/
theorem EqualCard.iff {X Y : Type} : EqualCard X Y ↔ Nonempty (X ≃ Y) := by
  simp [EqualCard]; constructor
  . intro ⟨ f, hf ⟩; exact ⟨ .ofBijective f hf ⟩
  intro ⟨ e ⟩; exact ⟨ e.toFun, e.bijective ⟩

/-- Equivalence with Mathlib's `Cardinal.mk` concept -/
theorem EqualCard.iff' {X Y : Type} : EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y := by
  simp [Cardinal.eq, iff]

theorem EqualCard.refl (X : Type) : EqualCard X X :=  ⟨ id, Function.bijective_id ⟩

theorem EqualCard.symm {X Y : Type} (hXY : EqualCard X Y) : EqualCard Y X := by
  rw [EqualCard.iff] at *
  obtain ⟨ e ⟩ := hXY;
  use e.symm; use e; have := e.bijective
  refine Function.leftInverse_iff_comp.mpr ?_; simp
  refine Function.LeftInverse.rightInverse ?_; exact Equiv.leftInverse_symm e
  -- Playing with apply

theorem EqualCard.trans {X Y Z : Type} (hXY : EqualCard X Y) (hYZ : EqualCard Y Z) :
  EqualCard X Z := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYZ
  use g ∘ f
  exact Function.Bijective.comp hg hf

instance EqualCard.instSetoid : Setoid Type := ⟨ EqualCard, ⟨ refl, symm, trans ⟩ ⟩

theorem EqualCard.univ (X : Type) : EqualCard (.univ : Set X) X :=
  ⟨ Subtype.val, Subtype.val_injective, by intro _; aesop ⟩

/--
Defined as EqualCard X ℕ.

(Meaning, ∃ f : X → ℕ, Function.Bijective f)-/
abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

theorem CountablyInfinite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  CountablyInfinite X ↔ CountablyInfinite Y := ⟨ hXY.symm.trans, hXY.trans ⟩

theorem Finite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Finite X ↔ Finite Y := by obtain ⟨ f, hf ⟩ := hXY; exact (Equiv.ofBijective f hf).finite_iff

theorem AtMostCountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  AtMostCountable X ↔ AtMostCountable Y := by
  simp [AtMostCountable, CountablyInfinite.equiv hXY, Finite.equiv hXY]

/-- Equivalence with Mathlib's `Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]; constructor
  . intro ⟨ e ⟩; exact ⟨ Denumerable.mk' e ⟩
  intro ⟨ h ⟩; exact ⟨ h.eqv X ⟩

/-- Equivalence with Mathlib's `Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem CountablyInfinite.toCountable {X : Type} (hX: CountablyInfinite X) : Countable X := by
  simp_all [iff']

theorem CountablyInfinite.toInfinite {X : Type} (hX: CountablyInfinite X) : Infinite X := by
  simp_all [iff']

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  observe h1 : CountablyInfinite X ↔ Countable X ∧ Infinite X
  observe h2 : Finite X ∨ Infinite X
  observe h3 : Finite X → Countable X
  tauto

/-- Annotations added by GPT-6 Sol (from OpenAI); original proof preserved. -/
theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ := by
  constructor
  /- Invert the bijection X → ℕ, then forget membership proofs to obtain ℕ → A. -/
  . intro ⟨ g, hg ⟩
    choose f hleft hright using Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    /- The inverse is injective, and its image is exactly X. -/
    . intro x y hxy; apply hright.injective; simp_all [Subtype.val_inj]
    ext; simp; constructor
    . intro hx; use g ⟨ _, hx ⟩; simp [hleft _]
    rintro ⟨ _, rfl ⟩; aesop
  /- Restrict invFun f to X. Since X is the image of the injective f,
     this gives a bijection X → ℕ. -/
  intro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  use (Function.invFun f) ∘ Subtype.val; split_ands
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h; grind
  intro n; use ⟨ f n, by aesop ⟩; grind

/-- Examples 8.1.3 -/
example : CountablyInfinite ℕ := by
  use id; exact Function.bijective_id

example : CountablyInfinite (.univ \ {0}: Set ℕ) := by
  use (fun n ↦ n-1); refine Function.bijective_iff_has_inverse.mpr ?_
  use (fun n ↦ ⟨n+1, by aesop⟩);
  constructor
  · unfold Function.LeftInverse; intro n; simp; congr; have := n.prop; simp [-Subtype.coe_prop] at this
    omega
  exact congrFun rfl -- n+1-1 is too easy to simplify

example : CountablyInfinite ((fun n:ℕ ↦ 2*n) '' .univ) := by
  -- To go in either direction bijectively, we'd need natural division for inversion (evil)
  -- Whether explicitly for the function in one way, or implicitly for surjectivity in the other
  -- Easier to just do injective, since 2*n is already injective.
  rw [CountablyInfinite.iff_image_inj]
  use (⟨ fun n ↦ 2*n, by intro a b hab; grind⟩)
  simp




/-- Proposition 8.1.4 (Well ordering principle / Exercise 8.1.2 -/
theorem Nat.exists_unique_min {X : Set ℕ} (hX : X.Nonempty) :
  ∃! m ∈ X, ∀ n ∈ X, m ≤ n := by
  choose x hx using hX
  refine existsUnique_of_exists_of_unique ?_ ?_
  · by_contra! h
    suffices ∀ k, ∀ x ∈ X, x > k by
      contrapose! this; use x+1; use x, hx;  grind
    intro k x hx
    induction' k with k ih generalizing x
    · grind -- If x=0, then there's some n < 0
    grind -- x > z > k (z ∈ X exists because of infinite descent)
  intros; grind

def Int.exists_unique_min : Decidable (∀ (X : Set ℤ) (_hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg; use .univ; simp; unfold ExistsUnique; push_neg
  intro z h; contrapose! h; use z-1; omega

def NNRat.exists_unique_min : Decidable (∀ (X : Set NNRat) (_hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg; use .univ\{0}; simp; unfold ExistsUnique;
  use ⟨1, by simp⟩; push_neg
  intro q h; contrapose! h; intro hq; use q/2; have := q.prop; constructor; positivity;
  have : 0 < q := by positivity
  bound


open Classical in
noncomputable abbrev Nat.min (X : Set ℕ) : ℕ := if hX : X.Nonempty then (exists_unique_min hX).exists.choose else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) : min X ∈ X ∧ ∀ n ∈ X, min X ≤ n := by
  simp [hX, min]; exact (exists_unique_min hX).exists.choose_spec

theorem Nat.min_eq {X : Set ℕ} (hX : X.Nonempty) {a:ℕ} (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) : min X = a :=
  (exists_unique_min hX).unique (min_spec hX) ha

@[simp]
theorem Nat.min_empty : min ∅ = 0 := by simp [Nat.min]

example : Nat.min ((fun n ↦ 2*n) '' (.Ici 1)) = 2 := by
  apply Nat.min_eq;
  · use 2; simp
  simp

theorem Nat.min_eq_sInf {X : Set ℕ} (hX : X.Nonempty) : min X = sInf X := by
  apply Nat.min_eq hX; constructor
  · exact Nat.sInf_mem hX -- Nat set contains its inf
  intro n hn; apply Nat.sInf_le hn

open Classical in
/-- Equivalence with Mathlib's `Nat.find` method -/
theorem Nat.min_eq_find {X : Set ℕ} (hX : X.Nonempty) : min X = Nat.find hX := by
  symm; rw [Nat.find_eq_iff]; have := min_spec hX; grind

/-
If X and Y were both finite, that would make the union finite.
So, we can flip that around to prove something is infinite.
-/
lemma infinite_of_union_with_finite {U : Type} {X Y : Set U}
    (h : (X ∪ Y).Infinite) (hy : Y.Finite): X.Infinite  := by
  contrapose! h; simp_all

theorem Nat.min_eq' {X : Set ℕ} {a:ℕ} (hX : X.Nonempty) (ha : a= min X) : a ∈ X ∧ ∀ n ∈ X, a ≤ n := by
  have hn_min:= Nat.min_spec hX
  grind


/-- Proposition 8.1.5 -/
theorem Nat.monotone_enum_of_infinite (X : Set ℕ) [Infinite X] : ∃! f : ℕ → X, Function.Bijective f ∧ StrictMono f := by
  -- This proof is written to follow the structure of the original text.
  let a : ℕ → ℕ := Nat.strongRec (fun n a ↦ min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m h })
  have ha : ∀ n, a n = min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := Nat.strongRec.eq_def _
  have ha_infinite (n:ℕ) : Infinite { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
    apply Set.Infinite.to_subtype -- Infinite types vs Infinite sets
    apply infinite_of_union_with_finite (Y := a '' (Finset.range n) ∩ X) -- If X is infinite and we remove finite, the remainder is infinite
    · have hX: X.Infinite := Set.infinite_coe_iff.mp (inferInstance) -- Types and sets again
      convert hX
      ext x; simp; constructor <;> intro h; grind; simp [h]; grind -- Logically equivalent sets
    exact Set.toFinite (a '' ↑(Finset.range n) ∩ X)
  have ha_nonempty (n:ℕ) : { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m }.Nonempty := Set.Nonempty.of_subtype
  have ha_mono : StrictMono a := by -- min means ≤, condition of set means ≠
    intro n m hnm
    have hn_min:= min_eq' (ha_nonempty n) ((ha n))
    have hm_min:= min_eq' (ha_nonempty m) ((ha m))
    simp at hm_min hn_min
    refine Nat.lt_of_le_of_ne ?_ ?_
    · apply hn_min.2; apply hm_min.1.1
      intro x hx;
      apply hm_min.1.2; omega
    apply Ne.symm ; apply hm_min.1.2; apply hnm

  have ha_injective : Function.Injective a := by -- Strictmono is always injective
    exact StrictMono.injective ha_mono
  have haX (n:ℕ) : a n ∈ X := by -- Part of def
    specialize ha n; have hn_min:= Nat.min_spec (ha_nonempty n)
    rw [← ha ] at hn_min
    simp at hn_min; bound
  set f : ℕ → X := fun n ↦ ⟨ a n, haX n ⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy; simp [f] at hxy; solve_by_elim
  have hf_surjective : Function.Surjective f := by
    intro ⟨ x, hx ⟩; simp [f]; by_contra -- Suppose x ∈ X had no counterpart in n ∈ ℕ
    have h1 (n:ℕ) : x ∈ { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by -- That qualifies it for the minset
      simp; grind-- Then it would be in the set we pull from to get a n terms
    have h2 (n:ℕ) : x ≥ a n := by -- It's always in the minset, so it's going to be ≥ the min
      rw [ha n]; exact ge_iff_le.mpr ((min_spec (ha_nonempty n)).2 _ (h1 n))
    have h3 (n:ℕ) : a n ≥ n := by -- increasing sequence, so it has to be at least as fast as linear
      induction' n with n ih
      · simp
      suffices a (n + 1) > n by tauto
      apply lt_of_le_of_lt ih; apply ha_mono; simp
    have h4 (n:ℕ) : x ≥ n := (h3 n).trans (h2 n)
    linarith [h4 (x+1)] -- In short, if x is never the min, it gets escalated to infinity
  apply ExistsUnique.intro _ ⟨ ⟨ hf_injective, hf_surjective ⟩, ha_mono ⟩
  intro g ⟨ hg_bijective, hg_mono ⟩; by_contra! -- Suppose different
  replace : { n | g n ≠ f n }.Nonempty := by -- Then there must be some distinct elems
    contrapose! this
    apply funext; simpa [Set.eq_empty_iff_forall_notMem] using this
  set m := min { n | g n ≠ f n } -- Which means there is a smallest distinct elem
  have hm : g m ≠ f m := (min_spec this).1
  have hm' {n:ℕ} (hn: n < m) : g n = f n := by  -- Earlier terms all agree
    by_contra hgfn; linarith [(min_spec this).2 n (by simp [hgfn])]
  have hgm : g m = min { x ∈ X | ∀ (n:ℕ) (h:n < m), x ≠ a n } := by -- By construction, g m is the min of this set
    symm; apply Nat.min_eq (ha_nonempty _); simp; constructor
    · intro r hr; apply ne_of_gt; suffices a r = g r by rw [this]; simp; apply hg_mono hr
      rw [hm' hr]

    intro x hx h
    choose k hk using hg_bijective.2 ⟨x, hx⟩ -- Any other term in this set should be ≥
    have := by simpa using congrArg Subtype.val hk;
    rw [← this]; simp
    apply StrictMono.monotone hg_mono -- Which means their input index should be ≥
    contrapose! h; use k; grind -- This is true because if it were an earlier index, it would equal its counterpart (not in the set)
  rw [←ha m] at hgm; contrapose! hm; exact Subtype.val_injective hgm

theorem Nat.countable_of_infinite (X : Set ℕ) [Infinite X] : CountablyInfinite X := by
  have := (monotone_enum_of_infinite X).exists
  exact EqualCard.symm ⟨ this.choose, this.choose_spec.1 ⟩

/-- Corollary 8.1.6 -/
theorem Nat.atMostCountable_subset (X: Set ℕ) : AtMostCountable X := by
  obtain _ | _ := finite_or_infinite X
  . tauto
  simp [AtMostCountable, countable_of_infinite]

/-- Corollary 8.1.7 -/
theorem AtMostCountable.subset {X: Type} (hX : AtMostCountable X) (Y: Set X) : AtMostCountable Y := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ f, hf ⟩ | hX := hX
  . let f' : Y → f '' Y := fun y ↦ ⟨ f y, by aesop ⟩
    have hf' : Function.Bijective f' := by
      constructor
      · unfold f'; intro a b hab; simp at hab; apply hf.1 at hab; bound -- injective preserved
      intro y; have := y.prop; simp [-Subtype.coe_prop] at this
      choose x hx using this; use ⟨x, hx.1⟩; unfold f'; simp; congr; tauto -- f '' Y is defined by having corresponding elem in Y
    rw [equiv ⟨ _, hf' ⟩ ]; apply Nat.atMostCountable_subset
  simp [AtMostCountable, show Finite Y by infer_instance]

theorem AtMostCountable.subset' {A: Type} {X Y: Set A} (hX: AtMostCountable X) (hY: Y ⊆ X) : AtMostCountable Y := by
  refine' (equiv ⟨ fun y ↦ ⟨ ↑↑y, y.property ⟩, _, _ ⟩).mp (subset hX { x : X | ↑x ∈ Y })
  . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _; simp_all
  intro ⟨ y, hy ⟩; use ⟨ ⟨ y, hY hy ⟩, by aesop ⟩

/-- Proposition 8.1.8 / Exercise 8.1.4 -/
theorem AtMostCountable.image_nat (Y: Type) (f: ℕ → Y) : AtMostCountable (f '' .univ) := by
  set B := f '' .univ
  let A : Set ℕ := {n : ℕ | f n ∈ B}
  let A : Set ℕ := {n : ℕ | n = Nat.min {i : ℕ | f i = f n}}
  have : AtMostCountable A := by exact Nat.atMostCountable_subset A
  suffices EqualCard A B by rwa [← AtMostCountable.equiv this]
  use fun n ↦ ⟨f n, by aesop⟩
  constructor
  · intro a b hab; simp at hab
    have ha := a.prop; have hb := b.prop; simp [A, -Subtype.coe_prop] at ha hb
    have hmina := Nat.min_eq' ⟨a, by simp⟩ (ha)
    have hminb := Nat.min_eq' ⟨b, by simp⟩ (hb)
    suffices (a:ℕ) = (b:ℕ) by bound
    apply le_antisymm
    apply hmina.2; grind
    apply hminb.2; grind
  intro y; have := y.prop; simp [B] at this;
  choose x hx' using this
  let A' := {i : ℕ | f i = f x}
  set z := (Nat.min {i : ℕ | f i = f x}) with hx
  have hminz := Nat.min_spec ( X:= A') (by use x; simp [A'])
  simp [A'] at hminz
  have : f z = f x := by unfold z; grind
  simp; use z; use (by unfold A; simp; rw [this])
  grind

/-- Corollary 8.1.9 / Exercise 8.1.5 -/
theorem AtMostCountable.image {X:Type} (hX: CountablyInfinite X) {Y: Type} (f: X → Y) : AtMostCountable (f '' .univ) := by
  obtain ⟨g, hg⟩ := hX.symm
  suffices (f '' Set.univ) = (f ∘ g) '' Set.univ by
    rw [this]; apply image_nat
  suffices  (f ∘ g) '' Set.univ =  (f '' (g '' Set.univ)) by
    rw [this]; congr; exact (Set.preimage_eq_iff_eq_image hg).mp rfl
  exact Set.image_comp f g Set.univ

#check CountablyInfinite.iff_image_inj




-- let q : ℕ → A := fun n ↦ if h : Even n then f (h.choose) else g (odd_of_not_even h).choose

theorem CountablyInfinite.union {A:Type} {X Y: Set A} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X ∪ Y: Set A) := by
  rw [CountablyInfinite.iff']

  choose f hf using hX.symm
  choose g hg using hY.symm
  constructor
  · rw [← AtMostCountable.iff]
    let q : ℕ → A := fun n ↦ if Even n then f (n/2) else g (n/2)
    suffices (X ∪ Y : Set A) = q '' Set.univ by rw [this]; apply AtMostCountable.image_nat
    ext i; simp; constructor <;> intro h
    · rcases h with hi | hi
      · choose y hy using hf.2 ⟨i, hi⟩
        use 2*y; unfold q; simp; grind
      · choose y hy using hg.2 ⟨i, hi⟩
        use 2*y + 1; unfold q; simp; grind
    choose y hy using h; unfold q at hy; by_cases h: Even y <;> simp [h] at hy <;> grind
  rw [CountablyInfinite.iff'] at hX hY
  rw [Set.infinite_coe_iff] at *
  apply Set.Infinite.mono (s:=X); simp; grind



/-- Corollary 8.1.11 --/
theorem Int.countablyInfinite : CountablyInfinite ℤ := by
  -- This proof is written to follow the structure of the original text.
  have h1 : CountablyInfinite {n:ℤ | n ≥ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    . intro h; use n.toNat; simp [h]
  have h2 : CountablyInfinite {n:ℤ | n ≤ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (-↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    intro h; use (-n).toNat; simp [h]
  have : CountablyInfinite (.univ : Set ℤ) := by
    convert h1.union h2; ext; simp; omega
  rwa [←CountablyInfinite.equiv (.univ _)]

/-- Lemma 8.1.12 -/
theorem CountablyInfinite.lower_diag : CountablyInfinite { n : ℕ × ℕ | n.2 ≤ n.1 } := by
  -- This proof is written to follow the structure of the original text.
  let A := { n : ℕ × ℕ | n.2 ≤ n.1 }
  let a : ℕ → ℕ := fun n ↦ ∑ m ∈ .range (n+1), m
  have ha : StrictMono a := by
    refine strictMono_nat_of_lt_succ ?_; intro n
    unfold a; nth_rw 2 [Finset.sum_range_succ]; linarith
  let f : A → ℕ := fun ⟨ (n, m), _ ⟩ ↦ a n + m
  have hf : Function.Injective f := by
    rintro ⟨ ⟨ n, m ⟩, hnm ⟩ ⟨ ⟨ n',m'⟩, hnm' ⟩ h
    simp [A,f] at hnm hnm' ⊢ h
    obtain hnn' | rfl | hnn' := lt_trichotomy n n'
    . have : a n' + m' > a n + m := by calc
        _ ≥ a n' := by linarith
        _ ≥ a (n+1) := ha.monotone (by linarith)
        _ = a n + (n + 1) := Finset.sum_range_succ id _
        _ > a n + m := by linarith
      linarith
    . simpa using h
    have : a n + m > a n' + m' := by calc
        _ ≥ a n := by linarith
        _ ≥ a (n'+1) := ha.monotone (by linarith)
        _ = a n' + (n' + 1) := Finset.sum_range_succ id _
        _ > a n' + m' := by linarith
    linarith
  let f' : A → f '' .univ := fun p ↦ ⟨ f p, by aesop ⟩
  have hf' : Function.Bijective f' := by
    constructor
    . intro p q hpq; simp [f'] at hpq; solve_by_elim
    intro ⟨ l, hl ⟩; simp at hl
    obtain ⟨ n, m, q, rfl ⟩ := hl; use ⟨ (n, m), q ⟩
  have : AtMostCountable A := by rw [AtMostCountable.equiv ⟨ _, hf' ⟩]; apply Nat.atMostCountable_subset
  have hfin : ¬ Finite A := by
    intro hA; apply Finite.Set.subset at hA; swap; apply { n : ℕ × ℕ | n.2 ≤ n.1 ∧ n.2=0 }
    specialize hA (by unfold A; simp; intros; tauto)
    contrapose! hA; simp; refine toInfinite ?_;
    use fun ⟨n, hn⟩ ↦ n.1
    refine Function.bijective_iff_has_inverse.mpr ?_; use fun n ↦ ⟨ ⟨n,0⟩, by simp⟩
    simp [Function.LeftInverse, Function.RightInverse]; intros; tauto
  simp [AtMostCountable] at this; tauto

/-- Corollary 8.1.13 -/
theorem CountablyInfinite.prod_nat : CountablyInfinite (ℕ × ℕ) := by
  have upper_diag : CountablyInfinite { n : ℕ × ℕ | n.1 ≤ n.2 } := by
    refine (equiv ⟨ fun ⟨ (n, m), _ ⟩ ↦ ⟨ (m, n), by aesop ⟩, ?_, ?_ ⟩).mp lower_diag
    . intro ⟨ (_, _), _ ⟩ ⟨ (_, _), _ ⟩ _; aesop
    intro ⟨ (n, m), _ ⟩; use ⟨ (m, n), by aesop ⟩
  have : CountablyInfinite (.univ : Set (ℕ × ℕ)) := by
    convert union lower_diag upper_diag; ext ⟨ n, m ⟩; simp; omega
  exact (equiv (.univ _)).mp this

/-- Corollary 8.1.14 / Exercise 8.1.8 -/
theorem CountablyInfinite.prod {X Y:Type} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X × Y) := by
  choose f hf using hX
  choose g hg using hY
  let q : X × Y → ℕ × ℕ := fun ⟨x, y⟩ ↦ ⟨f x, g y⟩
  have hq: Function.Bijective q := by
    constructor
    · intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h; simp [q] at *; constructor; apply hf.1 h.1; apply hg.1 h.2
    intro ⟨z₁, z₂⟩; choose x hx using hf.2 z₁; choose y hy using hg.2 z₂; use ⟨x, y⟩; simp [q] at *; tauto
  choose nn hnn using prod_nat
  rw [equiv ⟨q, hq⟩]; exact prod_nat

/-- Corollary 8.1.15 -/
theorem Rat.countablyInfinite : CountablyInfinite ℚ := by
  -- This proof is written to follow the structure of the original text.
  have : CountablyInfinite { n:ℤ | n ≠ 0 } := by
    rw [CountablyInfinite.iff']; constructor
    · rw [← AtMostCountable.iff]
      refine AtMostCountable.subset ?_ {n | n ≠ 0}
      unfold AtMostCountable; left;
      apply Int.countablyInfinite
    have huniv: { n:ℤ | n ≠ 0 } ∪ {0} = Set.univ := by ext i; simp; tauto
    rw [Set.infinite_coe_iff] at *
    have := CountablyInfinite.toInfinite Int.countablyInfinite
    have:= Set.infinite_univ (h:=this)
    apply infinite_of_union_with_finite (by rwa [huniv]) (by simp)
  apply Int.countablyInfinite.prod at this
  let f : ℤ × { n:ℤ | n ≠ 0 } → ℚ := fun (a,b) ↦ (a/b:ℚ)
  replace := AtMostCountable.image this f
  have h : f '' .univ = .univ := by
    ext q; unfold f; simp; use q.num; use q.den; simp; exact Rat.num_div_den q
  simp [h, AtMostCountable.equiv (EqualCard.univ _), AtMostCountable] at this
  have hfin : ¬ Finite ℚ := by
    by_contra!
    replace : Finite (.univ : Set ℕ) := by
      apply @Finite.Set.finite_of_finite_image ℕ ℚ _ (↑·); intro _ _ _ _; simp
    rw [Set.finite_coe_iff, Set.finite_univ_iff,←not_infinite_iff_finite] at this
    apply this; infer_instance
  tauto







/-
Presumably don't need to prove that an Infinite type is nonempty:
if it were empty, it would have finite card 0.
-/
lemma infinite_elem (X : Type) [h: Infinite X] : ∃ _x : X, True := by
  exact (exists_const X).mpr trivial


#check infinite_of_union_with_finite

lemma infinite_of_infinite_diff_finite {X : Type} {A B : Set X}
(hA : A.Infinite) (hB : B.Finite) :
  (A \ B).Infinite  := by
  contrapose! hA; simp_all; -- Statement about finites
  apply Set.Finite.subset (s := (A \ B) ∪ B) -- Union is a superset
  apply Set.Finite.union hA hB -- Union of finites is finite
  field_simp -- Logically simple to prove


/-
I could've just used the built-in, but I thought it was more in the spirit
to do it myself.
-/
open Classical in
lemma infinite_to_nat (X : Type) [h: Infinite X] : ∃ f : ℕ → X, Function.Injective f := by
  -- Better to give this an external name
  have h_nonempty (n : ℕ ) (f : (m : ℕ) → m < n → X):
    ∃ x : X, ∀ (m : ℕ) (hm : m < n), x ≠ f m hm := by
      suffices ∃ x, x ∈ (.univ \ {f m hm | (m : ℕ) (hm : m < n) }) by
        choose x hx using this; use x; simp_all; grind
      suffices ({f m hm | (m : ℕ) (hm : m < n) }).Finite by
        apply (infinite_of_infinite_diff_finite
          (by exact Set.infinite_univ_iff.mpr h) this).nonempty
      have := Set.finite_range (fun i : Fin n ↦ f i.val i.isLt) -- `Set.finite_range`: f '' ( Fin n ) is finite.
      convert this
      ext i; simp; constructor
      · rintro ⟨m, hm, hf⟩; use ⟨m, hm⟩
      rintro ⟨i, rfl⟩; use i; simp
  let f : ℕ → X := Nat.strongRec (fun n f ↦ Classical.choose (h_nonempty n f))
  use f
  intro n m hnm; contrapose! hnm;
  wlog hnm' : n < m
  · symm; apply this; grind; grind
  symm; unfold f
  -- `Nat.strongRec.eq_def` recommended by GPT-6: applies strong induction function to m,
  -- so we can access f m, which uses the choose statement we want.
  rw [Nat.strongRec.eq_def]
  -- Since we can't directly access the recursive strongRec function easily, make it a function so we can pre-handle other args.
  have h f := (h_nonempty m f).choose_spec n hnm'
  apply h

open Classical in
example (X: Type) : Infinite X ↔ ∃ Y : Set X, Y ≠ .univ ∧ EqualCard Y X := by
  constructor
  · intro hX; choose f hf using infinite_to_nat X
    let B := f '' .univ
    let Y := Set.univ \ {f 0}; use Y
    constructor
    · unfold Y; rw [Set.ne_univ_iff_exists_notMem]; use f 0; simp
    apply EqualCard.symm
    have hB : ∀ x ∈ B, ∃ n, f n = x := by rintro x ⟨n, _, hn⟩; use n
    let g : X → Y := fun x ↦ if hx: x ∈ B then
      ⟨f ((hB x hx).choose + 1),
        by unfold Y; simp; rw [← ne_eq]; intro h; apply hf at h; linarith⟩ else
      ⟨x, by simp [Y]; contrapose! hx; unfold B; simp_all⟩
    use g
    have hfn (n : ℕ) : f n ∈ B := by use n; simp
    have hgfn n : (g (f n)).val = f (n+1) := by
      unfold g; rw [dif_pos (hfn n)]; simp; congr;
      apply hf; generalize_proofs h1; apply h1.choose_spec
    constructor
    · intro x y hxy
      have : x ∈ B ↔ y ∈ B := by
        constructor <;> intro h <;> by_contra h' <;> simp [g, h, h'] at hxy
        simp [B] at h h'; grind; grind
      by_cases h : x ∈ B
      · have hx:= this.1 h
        obtain ⟨n, hn, rfl⟩ := h
        obtain ⟨m, hm, rfl⟩ := hx
        rw [Subtype.ext_iff, hgfn, hgfn] at hxy
        apply hf at hxy; simp_all
      have hy := h; simp [this] at hy
      simpa [h, hy, g] using hxy
    intro y; by_cases hy: y.val ∈ B
    · choose n hn using hy; have : n ≠ 0 := by grind
      use f (n-1);
      apply Subtype.ext; rw [hgfn, ← hn.2];
      congr; omega
    use y; simp [g, hy]
  rintro ⟨Y, hY, hY2⟩
  contrapose! hY2; simp at hY2
  observe hssub: Y ⊂ .univ
  rw [EqualCard.iff'] -- Use finiteness: ssubset has smaller cardinality
  apply ne_of_lt
  -- Nat cards, for comparison
  rw [← Nat.cast_card, ← Nat.cast_card, Nat.cast_lt]
  -- Turn type cards into set cards
  rw [Nat.card_coe_set_eq, ← Set.ncard_univ]
  apply Set.ncard_lt_ncard hssub





/-- Exercise 8.1.6 -/
lemma AMC_injective (A: Type) : AtMostCountable A ↔ ∃ f : A → ℕ, Function.Injective f := by
  constructor <;> intro h
  · rcases h with h | h
    · choose f hf using h; use f; exact Function.Bijective.injective hf
    let e := Finite.equivFin A -- A is finite, bijective with some fintype
    -- This fintype elems are a subset of ℕ, so we can use it for an injection
    use fun n ↦ e n
    intro a b hab; simp_all; apply e.injective; bound
  choose f hf using h
  -- Get a surjective function from the existence of the injective function
  by_cases hA: Finite A
  · grind
  simp at hA
  -- We're mapping from ℕ to cover all of A: so, A must be AMC
  have him:= AtMostCountable.image_nat A (Function.invFun f)
  apply (AtMostCountable.equiv ?_).mpr him
  -- Of course, we have to prove that mapping from ℕ *will* cover all of A
  -- Proven by the surjectivity of `Function.invFun f`
  have hsurj:= Function.invFun_surjective hf
  use fun a ↦ ⟨a, by simp; apply hsurj⟩
  constructor
  · intro a b hab; simp_all
  intro c; use c


/-Requires choice?-/

/-- Exercise 8.1.9 -/
lemma ex_8_1_9 {I X:Type} (hI: AtMostCountable I) (A: I → Set X) (hA: ∀ i, AtMostCountable (A i)) :
  AtMostCountable (⋃ i, A i) := by
  rw [AMC_injective]
  suffices ∃ g : (⋃ i, A i) → ℕ × ℕ, Function.Injective g by
    choose g hg using this
    choose s hs1 hs2 using CountablyInfinite.prod_nat
    use s ∘ g, Function.Injective.comp hs1 hg
  rw [AMC_injective] at hI
  choose f hf using hI
  have gA i:= (AMC_injective _).mp (hA i)
  have gA i: ↑(A i) ↪ ℕ:= ⟨(gA i).choose, (gA i).choose_spec⟩
  -- Each a comes from some A i
  have ha (a : ↑(⋃ i, A i)) : ∃ i, a.val ∈ A i := by simpa [-Subtype.coe_prop] using a.prop
  -- So, you can create a function giving you i for each of them
  choose idx hidx using ha -- Cool trick I learned from GPT-6 for unpacking

  -- idx gets me get the first index
  -- gA idx gives me the second index

  let s : (⋃ i, A i) → ℕ × ℕ :=
    fun a ↦ (f (idx a), gA (idx a) ⟨a, hidx a⟩)
    -- Encode the chosen set and the element's code within it.

  clear hA
  use s; intro a b hab
  simp [s] at hab
  have hfab := hf hab.1
  have hgab := hab.2
  /-
  IMPORTANT: currently, idx a and idx b are creating two different types
  The problem: rewrites don't work well inside of types
  Solution: generalize the indices first, then substitute them
  -/
  clear hab
  generalize_proofs h1 h2 at hgab
  generalize idx a = i at *
  generalize idx b = j at *
  subst hfab
  apply (gA i).injective at hgab; grind -- Now we're safe to finish

/-
Alternate solution instead of `generalize`: just use `rw!` instead of `rw`-/
example {I X:Type} (hI: AtMostCountable I) (A: I → Set X) (hA: ∀ i, AtMostCountable (A i)) :
  AtMostCountable (⋃ i, A i) := by
  rw [AMC_injective]
  suffices ∃ g : (⋃ i, A i) → ℕ × ℕ, Function.Injective g by
    choose g hg using this
    choose s hs1 hs2 using CountablyInfinite.prod_nat
    use s ∘ g, Function.Injective.comp hs1 hg
  rw [AMC_injective] at hI
  choose f hf using hI
  have gA i:= (AMC_injective _).mp (hA i)
  have gA i: ↑(A i) ↪ ℕ:= ⟨(gA i).choose, (gA i).choose_spec⟩
  -- Each a comes from some A i
  have ha (a : ↑(⋃ i, A i)) : ∃ i, a.val ∈ A i := by simpa [-Subtype.coe_prop] using a.prop
  -- So, you can create a function giving you i for each of them
  choose idx hidx using ha -- Cool trick I learned from GPT-6 for unpacking

  -- idx gets me get the first index
  -- gA idx gives me the second index

  let s : (⋃ i, A i) → ℕ × ℕ :=
    fun a ↦ (f (idx a), gA (idx a) ⟨a, hidx a⟩)
    -- Encode the chosen set and the element's code within it.

  clear hA
  use s; intro a b hab
  simp [s] at hab
  have hfab := hf hab.1
  have hgab := hab.2
  clear hab
  rw! [hfab] at hgab
  apply (gA (idx b)).injective at hgab; grind

/-
This seems to mostly be a matter of googling and then implementing.

The various methods for defining/proving these bijections uses methods we don't focus on in
this class (primes, towers of fractions...)

Overall it doesn't seem particularly worth it so I'm gonna skip.
-/

/-- Exercise 8.1.10.  Note the lack of the `noncomputable` keyword in the `abbrev`. -/
abbrev explicit_bijection : ℕ → ℚ := sorry

theorem explicit_bijection_spec : Function.Bijective explicit_bijection := by sorry

end Chapter8
