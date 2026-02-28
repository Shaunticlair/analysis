import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as `Set.pi` and `Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  _1: Object -- More readable to me
  _2: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

lemma SetTheory.Set.singleton_inj {a b : Object} : ({a}:Set) = {b} ↔ a = b := by
  refine ⟨?_, by rintro rfl; rfl⟩
  intro h; rw [SetTheory.Set.ext_iff] at h
  simpa using h

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  constructor
  · intro h; rw [SetTheory.Set.ext_iff] at h; simp at h
    rw [(h a).mp, (h b).mp]; repeat tauto
  rintro ⟨rfl, rfl⟩; ext; simp

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
toFun p := ({ (({p.1}:Set):Object), (({p.1, p.2}:Set):Object) }:Set)
inj' := by
  intro a b hx; simp at hx;
  rw [SetTheory.Set.ext_iff] at hx
  have : a.1 = b.1 := by
    specialize hx ({a.1}:Set); simp at hx
    rcases hx with hx | hx -- a.1 equals singleton or pair: same outcome
    · rwa [← singleton_inj]
    · symm at hx; rw [pair_eq_singleton_iff] at hx; tauto
  ext; exact this
  by_cases h: a.1 = a.2 -- If the terms are equal...
  · specialize hx ({a.1, b.2}:Set)
    simp [← this, h] at hx; -- {{a.2}, {a.2,a.2}} collapses
    rw [pair_eq_singleton_iff] at hx; rw [hx.2]
  · specialize hx ({a.1,a.2}:Set) -- If terms are unequal...
    simp [← this] at hx;
    -- We can't have {a.1,a.2}={a.1} if a.1 ≠ a.2
    have h' : ¬ a.2 = a.1 := by contrapose! h; simp_all
    rw [pair_eq_singleton_iff] at hx; simp [h'] at hx
    rw [SetTheory.Set.ext_iff] at hx -- a.2 must be a.1 or b.2
    specialize hx a.2; simp [h'] at hx; exact hx -- Former is false

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _ -- .replace function was simple enough

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by grind))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom];
  constructor
  · intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS;
    obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.left {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.prop).choose

noncomputable abbrev SetTheory.Set.right {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.prop)).choose

theorem SetTheory.Set.pair_eq_left_right {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ left z, right z ⟩:OrderedPair) := by
  -- Need to grab statement to use for choose_spec
  have := (mem_cartesian _ _ _).mp z.prop
  -- New notation to me!
  -- choose_spec would normally use this.choose
  -- So we instead clarify that we want to use the fact that
  -- this.choose = left z
  obtain ⟨ y, hy: z.val = (⟨ left z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, right z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  -- "EmbeddingLike" means it's injective:
  -- apply_eq_iff_eq allows us to turn toObject(a)=toObject(b) into a=b
  -- (an instance of injectivity)
  simp_all [EmbeddingLike.apply_eq_iff_eq]


--have := this.choose_spec.choose_spec

/-- This equips an `OrderedPair` with proofs that `x ∈ X` and `y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp] -- Using the above theorem instead of reusing its proof contents
theorem SetTheory.Set.left_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    left (mk_cartesian x y) = x := by
  -- Any cartesian z can be broken into ⟨x', y'⟩
  let z := mk_cartesian x y;
  -- Or, equivalently, ⟨left z, right z⟩
  have hz := pair_eq_left_right z
  -- But mk_cartesian x ,y has already been constructed as ⟨x, y⟩
  unfold z at hz; unfold mk_cartesian at hz
  -- Since ⟨left z, y'⟩ = ⟨x, y⟩, we know left z = x
  simp [Subtype.val_inj] at hz
  -- Which is our goal!
  convert hz.1.symm

-- Concise ver
theorem SetTheory.Set.left_of_mk_cartesian' {X Y:Set} (x:X) (y:Y) :
    left (mk_cartesian x y) = x := by
  have hz := pair_eq_left_right (mk_cartesian x y)
  simp [mk_cartesian] at *

@[simp]
theorem SetTheory.Set.right_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    right (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.prop
  obtain ⟨ x', hx: z.val = (⟨ x', right z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_left_right_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (left z) (right z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_left_right]

/--
  Connections with the Mathlib set product, which consists of Lean pairs like `(x, y)`
  equipped with a proof that `x` is in the left set, and `y` is in the right set.
  Lean pairs like `(x, y)` are similar to our `OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(left z, right z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where -- Noting that putting z on the left is equivalent to
-- it being a function
  toFun z := mk_cartesian (right z) (left z)
  invFun := fun z ↦ mk_cartesian (right z) (left z)
  left_inv z := by simp only -- Adding variable skips intro z
                   convert mk_cartesian_left_right_eq z
                   convert right_of_mk_cartesian _ _
                   convert left_of_mk_cartesian _ _
  right_inv := by intro z; simp

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun  f := fun z   ↦ f (left z) (right z)
  invFun f := fun x y ↦ f ⟨ (⟨ x, y ⟩:OrderedPair), by simp ⟩
  left_inv _ := by simp
  right_inv _ := by simp [←pair_eq_left_right]

/-- Definition 3.5.6.  The indexing set `I` plays the role of `{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).prop ⟩)
  :I → iUnion I X) -- This is a function; we cast it to an object afterwards
  -- We're basically taking the function x : (i : I) → X i
  -- And replacing its output type with iUnion I X
  -- So, instead of having a dependent type function, we can use the same type for all outputs (by creating a set/type that definitely contains all of our elements)
  -- But otherwise, the function (ft : I → iUnion I X) behaves exactly the same as x, mapping the same indices to the same objects
  -- Of course, we then turn ft into an Object

lemma SetTheory.Set.tuple_fun_union {I:Set} {X: I → Set} (x: ∀ i, X i):
∃ (f : I → iUnion I X), tuple x = f := by simp

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  -- Takes all the functions I → iUnion I X
  -- And only keeps the functions x where (x i : X i)
  -- In other words, each x i must be contained within its corresponding set X i
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)
  -- We don't have to cast t to a tuple because it's already an object
  -- While x is still in function form


/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  · intro ⟨ _, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  -- tuple is defined as some I → iUnion I X cast to Object
  -- So tuple x exactly fulfills powerset_axiom
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x


-- Extensionality between tuples
-- If each index has the same map, the tuples are the same
@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
tuple x = tuple y ↔ x = y := by
  refine ⟨?_, by rintro rfl; rfl⟩
  intro h; simp at h -- Object casting is injective
  ext i;
  apply congr_fun (a := i) at h
  simpa using h

/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (left (left p)) (mk_cartesian (right (left p)) (right p))
  invFun p := mk_cartesian (mk_cartesian (left p) (left (right p))) (right (right p))
  left_inv _ := by simp
  right_inv _ := by simp

-- Helper theorems I made

theorem SetTheory.Set.mem_iProd' {I: Set} {X: I → Set} {t: Object} (h : t ∈ iProd X) : ∃ x: ∀ i, X i, t = tuple x := (mem_iProd t).mp h

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

lemma SetTheory.Set.constr_object {A : Set} {x : Object} {h : x ∈ A}: (⟨x,h⟩:A) = x := by simp

/-- Each tuple in iProd X corresponds to one mapping function -/
noncomputable abbrev SetTheory.Set.iProd_fun_equiv (I:Set) (X: I → Set) :iProd X ≃ (∀ i, X i) where
  toFun z := (mem_iProd' z.prop).choose
  invFun f := ⟨tuple f, tuple_mem_iProd _⟩
  left_inv z  := by
    ext; generalize_proofs h1 h2 at *
    conv => lhs; simp
    symm; exact (h2 z).choose_spec
  right_inv f := by
    ext; simp; generalize_proofs h1 h2 h3
    congr; apply congrFun
    rw [← tuple_inj]
    symm; exact h1.choose_spec

noncomputable instance SetTheory.Set.iProd.inst_coefn {I:Set} {X: I → Set} : CoeFun (iProd X) (fun _ ↦ ∀ i, X i) where
  coe := (iProd_fun_equiv I X)

noncomputable instance SetTheory.Set.iProd.inst_coe_fn_to_iProd {I:Set} {X: I → Set}: Coe (∀ i, X i) (iProd X) where
  coe := (iProd_fun_equiv I X).symm


/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) : iProd (fun _:I ↦ X) ≃ (I → X) :=
  iProd_fun_equiv I (fun _ ↦ X)



/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun t := t ⟨i, by aesop⟩
  invFun x := (fun _:({i}:Set) ↦ x)
  left_inv t := by -- with one input, func t is eq to const func (t i)
    simp only; rw [Equiv.symm_apply_eq];
    ext ⟨j, hj⟩; simp at hj; subst hj; congr
  right_inv x := by -- Cast f(x)=x func → iProd → func, cancels out
    simp only [Equiv.apply_symm_apply] -- We just get f(i)=x

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨tuple (absurd ·.prop (by simp)), tuple_mem_iProd _⟩
  left_inv x  := by ext; rw [(mem_iProd' x.prop).choose_spec]
                    rw [tuple_inj]; ext i;
                    absurd i.prop; simp
  right_inv x := by simp

noncomputable abbrev SetTheory.Set.empty_iProd_equiv' (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun _ := ()
  invFun _ := (absurd ·.prop (by simp) : ∀ i, X i)
  left_inv x  := by
    simp only [Equiv.symm_apply_eq]
    ext i; absurd i.prop; simp
  right_inv x := by simp

-- These instances allow me to use 0 and 1 in {0,1} without explicitly, tediously having to clarify their presence.

--instance set01_0_inst: OfNat ({0,1} : Set) 0 where
--  ofNat := ⟨0, by aesop⟩

--instance set01_1_inst: OfNat ({0,1} : Set) 1 where
--  ofNat := ⟨1, by aesop⟩
/-
noncomputable instance (i: ({0,1}:Set)): Decidable (i = ⟨0, by aesop⟩) := by
  if h : i.val = 0 then
    apply isTrue; ext; simp [h]
  else
    apply isFalse; contrapose! h; simp [h]

noncomputable instance (i: ({0,1}:Set)): Decidable (i = ⟨1, by aesop⟩) := by
  if h : i.val = 1 then
    apply isTrue; ext; simp [h]
  else
    apply isFalse; contrapose! h; simp [h]


-/

noncomputable instance : DecidableEq ({(0:Object), (1:Object)} : Set).toSubtype := by
  intro x y
  if hx : x = ⟨0, by aesop⟩  then
  · if hy: y = ⟨0, by aesop⟩ then
      apply isTrue; simp_all
    else
      apply isFalse; rw [hx]; contrapose! hy; simp [hy]
  else
  · if hy : y = ⟨0, by aesop⟩ then
    · apply isFalse; rw [hy]; exact hx
    else
      apply isTrue
      have hx' := x.prop; have hy' := y.prop; simp at hx' hy'
      rw [← coe_inj ] at *;
      simp_all

noncomputable instance : Fintype ({0, 1} : Set).toSubtype where
  elems := {⟨0, by aesop⟩ , ⟨1, by aesop⟩ }
  complete := by
    intro ⟨x, hx⟩; simp at *
    rwa [SetTheory.Set.mem_pair] at hx

-- In inv_fun below, We want to prove f i ∈ X i
  -- f 1 has a built-in proof of f 1 ∈ X 1, so we just need to substitute i
  -- ▸ can shorthand this subtitution

abbrev SetTheory.Set.zero' : ({0,1}:Set) := ⟨0, by aesop⟩
abbrev SetTheory.Set.one' : ({0,1}:Set) := ⟨1, by aesop⟩

lemma SetTheory.Set.eq0' (i : Object) :
i = 0 ↔ i = (⟨0, by aesop⟩: ({0,1}:Set)) := by simp
lemma SetTheory.Set.eq1' (i : Object) :
i = 1 ↔ i = (⟨1, by aesop⟩: ({0,1}:Set)) := by simp

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X zero') ×ˢ (X one') where
  toFun t := mk_cartesian (t zero') (t one')
  invFun z := (
  fun i : ({0,1}:Set) =>
    if h0 : i = zero' then h0 ▸ left z
    else if h1 : i = one' then h1 ▸ right z
    else absurd i.prop (by rw [← coe_inj ] at *; simp_all)
  : ∀ i, X i)
  left_inv t := by -- f⁻¹ f t splits and then re-creates t
    simp only [Equiv.symm_apply_eq]; ext i; have hi := i.prop
    simp [eq0', eq1'] at hi; rw [coe_inj, coe_inj] at hi -- Get cases
    rcases hi with rfl | rfl <;> simp

  right_inv z:= by
    ext; rw [pair_eq_left_right, pair_eq_left_right]; congr 1;
    rw [left_of_mk_cartesian, right_of_mk_cartesian]
    ext <;> simp only [Equiv.apply_symm_apply] <;> congr; simp

abbrev SetTheory.Set.zero'' : ({0,1,2}:Set) := ⟨0, by aesop⟩
abbrev SetTheory.Set.one'' : ({0,1,2}:Set) := ⟨1, by aesop⟩
abbrev SetTheory.Set.two'' : ({0,1,2}:Set) := ⟨2, by aesop⟩

lemma SetTheory.Set.eq0 (i : Object) :
i = 0 ↔ i = (⟨0, by aesop⟩: ({0,1,2}:Set)) := by simp
lemma SetTheory.Set.eq1 (i : Object) :
i = 1 ↔ i = (⟨1, by aesop⟩: ({0,1,2}:Set)) := by simp
lemma SetTheory.Set.eq2 (i : Object) :
i = 2 ↔ i = (⟨2, by aesop⟩: ({0,1,2}:Set)) := by simp

open Classical in
/-- Example 3.5.10: similar to previous instance -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X zero'') ×ˢ (X one'') ×ˢ (X two'') where
  toFun t := mk_cartesian (t zero'') (mk_cartesian (t one'') (t two''))
  invFun z := (
  fun i : ({0,1,2}:Set) =>
    if h0 : i = zero'' then h0 ▸ left z
    else if h1 : i = one'' then h1 ▸ left (right z)
    else if h2 : i = two'' then h2 ▸ right (right z)
    else absurd i.prop (by rw [← coe_inj ] at *; simp_all)
  : ∀ i, X i)
  left_inv t := by -- f⁻¹ f t splits and then re-creates t
    simp only [Equiv.symm_apply_eq]; ext i; have hi := i.prop
    simp [eq0, eq1, eq2] at hi; repeat rw [coe_inj] at hi -- Get cases
    rcases hi with rfl | rfl | rfl <;> simp
  right_inv z := by
    ext; repeat rw [pair_eq_left_right];
    congr 1;
    repeat rw [left_of_mk_cartesian, right_of_mk_cartesian]
    ext <;> simp only [Equiv.apply_symm_apply] <;> congr <;> simp

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.prop).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.prop i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.prop).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  · intro ⟨ h1, h2 ⟩; use (⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).prop)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.prop; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

-- Fin n → ℕ → Fin n can be canceled out to Fin n
-- Since (i:ℕ) is literally defined as "the number that can be used to generate i with Fin_mk"
theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h', Fin_mk, constr_object]

-- (i : Fin n) contains itself cast to (i : ℕ)
-- The outer layer of Fin n is just a proof, which the object cast
-- destroys anyway
-- So we're just left with (i:ℕ) inside
theorem SetTheory.Set.Fin.coe_toNat' {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  obtain ⟨ h, h'⟩ := toNat_spec i;
  rw [← coe_inj, Fin_mk] at h'; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  refine ⟨by rintro rfl; rfl, ?_⟩
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind -- If they contain the same natural number, they construct the same Fin n term

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  rintro rfl
  simp_all only [coe_toNat]

-- Shifting (i : Fin n) to (i : Fin m) doesn't change the underlying natural number
@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

-- ℕ → Fin n → ℕ can be canceled out to ℕ
@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

-- Lift (i : Fin n) to some larger (i : Fin N)
abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.prop; rw [mem_Fin] at *; grind
⟩



/-- Connections with Mathlib's `Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  -- Pretty simple, because toFun and invFun both cast their counterparts to ℕ
  -- (Note that the following indicates the types that some input passed through, rather than the actual function type signature)
  -- So, Fintype 1 → Fintype 2 → Fintype 1 becomes
  -- Fintype 1 → ℕ → Fintype 2 → ℕ → Fintype 1
  -- Fintype 1 → (ℕ → Fintype 2 → ℕ ) → Fintype 1
  -- Fintype 1 → ℕ → Fintype 1
  -- Fintype 1

  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

theorem SetTheory.Set.nonempty_of_inhabited' {X:Set} (x : X): X ≠ ∅ := nonempty_of_inhabited x.prop

theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  · have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom''] -- (m : ℕ) < 0 is impossible
    let f i : X i := absurd i.property (by simp)
    apply nonempty_of_inhabited' f -- Use empty function
  -- Set up to invoke inductive case
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x' hx' using nonempty_def (hn hX') -- Induction gives func
  lift x' to iProd X' using hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose z hz using nonempty_def (h last)

  have x : ∀ i, X i := fun i ↦
    if h : i = n then
      ⟨z, by convert hz; unfold last; ext; simp [h]⟩
    else
      let z := x' (Fin_mk n i (by have := Fin.toNat_lt i; omega ))
      ⟨z, by convert z.prop using 1; simp [X']; congr; ext; simp⟩
  exact nonempty_of_inhabited (x : iProd X).prop


#check SetTheory.Set.axiom_of_regularity
#check SetTheory.Set.not_mem_self
#check SetTheory.Set.not_mem_mem

lemma SetTheory.Set.mem_pair_eq_pair
(h : {a,b} = ({a,c}:Set)): b = c := by
  by_contra h'
  have h1 := congr_arg (b ∈ ·) h
  have h2 := congr_arg (c ∈ ·) h
  simp at h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | h <;> simp_all

abbrev sto := SetTheory.set_to_object
/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p  := ({ p.1, (({p.1, p.2}:Set):Object) }:Set)
  inj' a b hab := by
    simp at hab
    have : a.1 = b.1 := by
      by_contra h -- Single elems not equal each other, must equal pair
      have ha := congr_arg (a._1 ∈ ·) hab
      have hb := congr_arg (b._1 ∈ ·) hab
      simp [h] at ha;
      have h' := Ne.symm h; simp [h'] at hb
      convert SetTheory.Set.not_mem_mem; simp
      refine ⟨{b._1, b._2}, {a._1, a._2}, ?_⟩
      simp [← ha, ← hb]
    ext; exact this
    rw [← this] at hab
    apply mem_pair_eq_pair at hab
    simp at hab
    apply mem_pair_eq_pair at hab
    exact hab


/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
  refine ⟨by rintro rfl; simp, ?_⟩
  intro h; ext x
  · constructor <;> intro hX
    · choose i hi using t.surj ⟨x, hX⟩
      convert ((t'.x i)).property
      rw [← h i, hi]
    · choose i hi using t'.surj ⟨x, hX⟩
      convert ((t.x i)).property
      rw [h i, hi]
  apply h

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { s:Tuple n // ∀ i, (s.x i:Object) ∈ X i } where
  toFun := fun t ↦
    let Z := (Fin n).replace
      (P := fun i fi ↦ fi = t i) (by aesop)
    let f : Fin n → Z := fun i ↦
      ⟨t i, by rw [replacement_axiom]; use i⟩
    let fsurj : Function.Surjective f := by
      intro y; have := y.prop; rw [replacement_axiom] at this;
      choose i hi using this; use i; rw [← coe_inj, hi]
    ⟨Tuple.mk Z f fsurj, by intro i; simp; convert (t i).prop⟩
  invFun s := ( fun i ↦ ⟨s.val.x i, s.prop i⟩ : ∀ i, X i)
  left_inv t := by -- iProd → Tuple → iProd
    simp; generalize_proofs h1 _ -- iProd elems are fully defined by their function
    ext; simp;
    conv => rhs; rw [h1.choose_spec] -- The function passes through toFun and invFun basically unaffected
  right_inv s:= by -- Tuple → iProd → Tuple
    simp; rw [← Subtype.coe_inj];
    generalize_proofs h1 h2 h3 h4 h5 h6
    have := h2.choose_spec; rw [tuple_inj] at this
    simp_rw [← this]
    ext x -- Need to check set AND function
    · simp only; rw [replacement_axiom]; -- Set elems are the outputs of the function s.x: s.x was preserved through toFun and invFun
      rw [← this]
      constructor <;> intro h
      · choose i hi using h; convert (s.val.x i).prop -- s.x can only generate elements of s.X
      choose i hi using s.val.surj ⟨x, h⟩; rw [← coe_inj] at hi; simp at hi
      rw [← hi]; use i -- s.X is surjective: every element will be generated by some s.x i
    simp -- Function passed through unaffected

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  rw [OrderedPair.eq]; simp

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  repeat rw [OrderedPair.eq];
  constructor <;> intro h <;> exact ⟨h.1.symm, h.2.symm⟩


theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  rw [OrderedPair.eq] at *;
  rw [hpq.1, hpq.2, hqr.1, hqr.2]; simp -- Did rws, but not of the original p,q,r


theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
  tuple a = tuple a := by
  apply (tuple_inj _ _).mpr
  ext; rfl

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
  tuple a = tuple b ↔ tuple b = tuple a := by
  repeat rw [tuple_inj]
  constructor <;> intro h <;> ext i <;> simp [h]

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
tuple a = tuple c := by
  rw [tuple_inj] at *;
  ext i; apply congr_fun at hab; apply congr_fun at hbc;
  rw [hab, hbc]

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  ext i; simp_rw [mem_union, mem_cartesian]
  constructor
  · rintro ⟨x, y, _⟩; subst i; have := y.prop; simp at this;
    rcases this with h | h <;> simp [h]
  intro h ; rcases h with ⟨x, y, _⟩ | ⟨x, y, _⟩ <;> subst i <;>
    use x <;> use ⟨y, by aesop⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext i; simp_rw [mem_inter, mem_cartesian]
  constructor
  · rintro ⟨x, y, _⟩; subst i; have := y.prop; simp at this;
    constructor <;> refine ⟨x, ⟨y, by aesop⟩, rfl⟩
  rintro ⟨⟨x1, y1, h1⟩, ⟨x2, y2, h2⟩⟩; subst i; simp at h2;
  have := y2.prop; rw [h2.2.symm] at *
  use x1; use ⟨y1, by simp [y1.prop, this]⟩

#check mk_cartesian_left_right_eq


/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  ext i; simp_rw [mem_sdiff, mem_cartesian]
  constructor -- Use contradiction: if it's in one set but not the other, y is in and not in C
  · rintro ⟨x, y, _⟩; subst i;
    refine ⟨?hxy, ?_⟩ -- Refine lets me keep the first goal while proving the second
    · use x; use ⟨y, by aesop⟩
    choose a b h using ?hxy; simp at h;
    by_contra hc; choose c d hc using hc; simp at hc
    aesop -- y ∈ C and y ∉ C
  rintro ⟨⟨x,y,h1⟩, h2⟩; subst h1
  suffices y.val ∉ C by use x; use ⟨y, by aesop⟩
  contrapose! h2; use x; use ⟨y, by aesop⟩;



/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  ext i; simp_rw [mem_union, mem_cartesian]
  constructor
  · rintro ⟨x, y, _⟩; subst i; simp; convert x.prop; simp
  intro h ; rcases h with ⟨x, y, _⟩ | ⟨x, y, _⟩ <;> subst i <;>
  use ⟨x, by aesop⟩ <;> use y

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  ext i; simp_rw [mem_inter, mem_cartesian]
  constructor
  · rintro ⟨x, y, _⟩; subst i; simp; convert x.prop; simp
  rintro ⟨⟨x1, y1, h1⟩, ⟨x2, y2, h2⟩⟩; subst i; simp at *;
  aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by
  ext i; simp_rw [mem_sdiff, mem_cartesian];
  constructor
  · rintro ⟨x, y, _⟩; subst i; simp; convert x.prop; simp
  rintro ⟨⟨x,y,h1⟩, h2⟩; subst i; simp at *; aesop

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  ext i; simp_rw [mem_inter, mem_cartesian]; symm
  constructor
  · intro ⟨x, y, _⟩; subst i; simp; aesop
  rintro ⟨⟨x1, y1, h1⟩, ⟨x2, y2, h2⟩⟩; subst i; simp at *;
  nth_rw 2 [h2.1, h2.2]; aesop

@[simp]
lemma SetTheory.Set.empty_prod (A : Set) : (∅:Set) ×ˢ A = (∅:Set) := by ext i; simp

@[simp]
lemma SetTheory.Set.prod_empty (A : Set) : A ×ˢ (∅:Set) = (∅:Set) := by ext i; rw [mem_cartesian]; simp


/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg;
  refine ⟨{1}, ∅, ∅, {1}, ?_ ⟩; simp
  rw [SetTheory.Set.ext_iff]
  push_neg; use OrderedPair.mk 1 1; simp

@[simp]
lemma SetTheory.Set.sdiff_self (A : Set) : A \ A = ∅ := by ext i; simp

@[simp]
lemma SetTheory.Set.sdiff_empty (A : Set) : A \ ∅ = A := by ext i; simp

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg
  refine ⟨{1}, {1}, {1}, ∅, ?_⟩; simp
  rw [SetTheory.Set.ext_iff]; simp

/--
  Exercise 3.5.6.
-/
lemma SetTheory.Set.nonempty_def' {X:Set} : X ≠ ∅ ↔ ∃ x, x ∈ X := by
  refine ⟨nonempty_def, ?_⟩; intro h; apply nonempty_of_inhabited; apply h.choose_spec


theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
(hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
  rw [nonempty_def'] at *
  choose a ha using hA; choose b hb using hB; choose c hc using hC; choose d hd using hD
  constructor <;> intro h
  · constructor <;> intro x hx
    · have : (OrderedPair.mk x b: Object) ∈ A ×ˢ B := by rw [mem_cartesian]; simp [hx, hb]
      apply h at this; simp at this; exact this.1
    · have : (OrderedPair.mk a x: Object) ∈ A ×ˢ B := by rw [mem_cartesian]; simp [ha, hx]
      apply h at this; simp at this; exact this.2
  intro z hz; rw [mem_cartesian] at *; choose x y hz using hz; subst z
  use ⟨x, h.1 _ x.prop⟩; use ⟨y, h.2 _ y.prop⟩

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg -- Cartesians are empty, but that only requires one of the two sets that make it up to be
  refine ⟨∅,{1},∅,∅, ?_⟩; left; simp -- Instantly satisfies left side by making cartesians empty
  simp [subset_def] -- But right side is not: B can be nonempty without making A × B nonempty


/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
∃! h: Z → X ×ˢ Y, left ∘ h = f ∧ right ∘ h = g := by
  apply existsUnique_of_exists_of_unique
  · use fun z ↦ mk_cartesian (f z) (g z)
    constructor <;> ext i <;> simp
  intro f1 f2 hf1 hf2
  ext z; repeat rw [pair_eq_left_right]
  simp;
  rw [← hf2.1, ← hf2.2] at hf1
  constructor <;> congr 1
  apply congr_fun hf1.1; apply congr_fun hf1.2

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
iProd X = ∅ ↔ ∃ i, X i = ∅ := by
  constructor <;> intro h
  · contrapose! h; simp_rw [nonempty_def'] at *
    let w := ((fun i ↦ ⟨(h i).choose, (h i).choose_spec⟩ : ∀ i, X i): iProd X)
    refine ⟨w, w.prop⟩
  by_contra! ht; rw [nonempty_def'] at ht;
  choose t ht using ht; lift t to iProd X using ht
  choose i hi using h
  suffices (t i).val ∈ (∅:Set) by simp_all
  rw [← hi]; apply (t i).prop

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
(iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (left p)) ∩ (B (right p))) := by
  ext a; simp_rw [mem_inter, mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; use mk_cartesian i j; simp; exact ⟨hi, hj⟩
  rintro ⟨z, hz⟩; simp at hz
  refine ⟨⟨left z, hz.1⟩, ⟨right z, hz.2⟩⟩

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (left p) = right p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
graph f = graph f' ↔ f = f' := by
  refine ⟨?_, by rintro rfl; rfl ⟩
  intro h; ext x
  replace h := congr_arg ( (mk_cartesian x (f x)).val ∈ · ) h;
  simp only at h; simp_rw [specification_axiom'] at h
  simp at h; rw [h]


theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
(hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
∃! f: X → Y, G = graph f := by
  apply existsUnique_of_exists_of_unique
  · use (fun x ↦ (hvert x).choose)
    ext z
    constructor <;> intro h
    · specialize hG _ h
      lift z to (X ×ˢ Y) using hG -- We can generate (left z, (hvert x).choose) ∈ G
      rw [specification_axiom']; simp only
      set hvert := hvert (left z)
      apply hvert.unique hvert.choose_spec.1
      convert h; rw [pair_eq_left_right]
    · rw [specification_axiom''] at h
      choose hz h using h; simp at h
      set w : X ×ˢ Y := ⟨ z, hz⟩
      change w.val ∈ G
      specialize hvert (left w)
      convert hvert.choose_spec.1;
      rw [pair_eq_left_right]; simp
      congr; convert h.symm
  intro f1 f2 h1 h2; symm at *;

  rw [← graph_inj, h1, h2]

#check SetTheory.Set.exists_powerset
#check SetTheory.Set.mem_powerset



/-
let graphset := powset.specify (fun S ↦
      ∃ f: Y → X, graph f = PSet S)
    let funset := graphset.replace (P := fun G F ↦
      G = graph F) ?_
      -/

/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
  apply existsUnique_of_exists_of_unique
  · let powset := powerset (Y ×ˢ X)
    let funset := powset.replace (P := fun S F ↦
      ∃ f: Y → X, f = F ∧ PSet S = graph f) ?_
    use funset; intro F; rw [replacement_axiom]
    refine ⟨by intro ⟨_, h⟩; peel h with g h; exact h.1, ?_⟩
    intro ⟨f, hf⟩
    use ⟨graph f, by rw [mem_powerset]; use graph f; simp; apply specify_subset⟩
    use f; simp [hf]; symm; apply PSet_prop'
    · simp only; intro x F1 F2 ⟨⟨_,h1, h2⟩, ⟨_,h3, h4⟩⟩;
      rw [← h1, ← h3]; simp; rw [← graph_inj, ← h2, ← h4]
  rintro S1 S2 h1 h2; ext F; rw [h1, h2]




theorem SetTheory.Set.recursion_finite (X: Set) (f: ℕ → X → X) (c:X) :
∀ (n : ℕ), ∃ g : Fin (n+1) → X,
g (Fin_mk _ 0 (by simp)) = c ∧
∀ i (h: i < n), g (Fin_mk _ (i+1) (by omega)) = f i (g (Fin_mk _ i (by omega))) := by
  intro n
  induction' n with n ih
  · simp; use fun i ↦ c
  choose g hg0 hgih using ih;
  let Q: Fin (n+2) → X := fun i ↦
    if h2 : i < n+1 then
      g (Fin_mk _ i h2)
    else if h1 : i = n+1 then
      f n (g (Fin_mk _ (n) (by linarith)))
    else
      absurd (by omega: ¬ (i < n+2)) (by push_neg; convert Fin.toNat_lt i)
  use Q;
  refine ⟨by rw [← hg0]; simp [Q], ?_⟩
  intro i hi
  by_cases h : i < n
  · have hp1:i+1 < n+1 := by omega
    simp [Q, h, hi]
    exact hgih i h
  simp [show i = n by omega,Q]

-- recursion_finite with two different bounds are equal
-- up to the min of those bounds
theorem SetTheory.Set.recursion_eq (X: Set) (f: ℕ → X → X) (c:X)
(n m i: ℕ) (hn: i < n+1) (hm: i < m+1):
(recursion_finite X f c n).choose (Fin_mk _ i hn) =
(recursion_finite X f c m).choose (Fin_mk _ i hm) := by
  have hnr:= (recursion_finite X f c n).choose_spec
  have hmr:= (recursion_finite X f c m).choose_spec
  induction' i with i ih
  · rw [hnr.1, hmr.1]
  rw [hnr.2, hmr.2, ih]
  linarith; linarith

theorem SetTheory.Set.recursion' (X: Set) (f: ℕ → X → X) (c:X) :
∃ a: ℕ → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
  have hfin := recursion_finite X f c
  let hg n:= (hfin n).choose_spec
  let g n:= (hfin n).choose
  use fun n ↦ g n (Fin_mk _ n (by simp))
  refine ⟨by convert (hg 0).1, ?_⟩
  intro n; simp
  specialize hg (n+1); unfold g
  rw [hg.2 _ (by linarith)]
  congr 1
  rw [recursion_eq X f c n (n+1) n (by simp) (by linarith) ]


lemma SetTheory.Set.natcast_eq_nat_equiv (n:ℕ) : (n: nat) = nat_equiv n := rfl

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
  apply existsUnique_of_exists_of_unique
  · let ha := (recursion' X (fun n ↦ f (nat_equiv.symm n )) c)
    use fun n ↦ ha.choose (nat_equiv n)
    simp [ha.choose_spec]
  intro f1 f2 h1 h2; ext n
  rw [show n = nat_equiv (nat_equiv.symm n) by simp]
  set m := nat_equiv.symm n
  induction' m with m ih
  · rw [show nat_equiv 0 = 0 by rfl]
    rw [h1.1, h2.1]
  rw [coe_inj] at ih;
  unfold instNatCast at h1 h2
  simp_rw [natcast_eq_nat_equiv] at h1 h2
  rw [h1.2, h2.2, ih]


/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  have succ_inj n m: n = m ↔ succ n = succ m :=
    ⟨by rintro rfl; rfl, by convert (succ_of_ne n m).mt; simp; simp⟩
  obtain ⟨f, ⟨hf0, hfp⟩, hfu⟩ := recursion nat' (fun n m ↦ succ m) zero
  simp at hfu
  apply existsUnique_of_exists_of_unique
  · use f
    have hne0 (x:nat): x ≠ 0 → ∃ k, x = (k + 1:ℕ) := by
      intro h; rw [ne_eq, ← nat_equiv_coe_of_coe' x, ] at h
      rw [← SetTheory.Set.nat_coe_eq (n := 0), nat_equiv_inj] at h;
      choose k hk using Nat.exists_eq_add_one_of_ne_zero h
      use k; rw [← hk]; simp
    constructor -- Bijective
    · constructor
      · intro x1 x2 heq -- Injectivity
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · rw [nat_coe_eq_zero hx1] at heq ⊢
          symm; by_contra! h; choose k hk using hne0 x2 h
          subst x2; rw [hf0, hfp] at heq
          apply succ_ne _ heq.symm
        apply nat_coe_eq at hx1; rw [hx1, hfp] at heq
        have : x2 ≠ 0 := by rintro rfl; rw [hf0] at heq; apply succ_ne _ heq
        choose k hk using hne0 x2 this; subst hk
        rw [hfp, ← succ_inj] at heq;
        rw [hx1]; congr; rw [← nat_equiv_inj];
        apply ih heq (by simp)
      apply ind; use 0 -- Surjectivity
      intro y ih; choose x hx using ih
      use ((x+1 : ℕ):nat)
      rw [hfp]; simp [hx]
    refine ⟨hf0, ?_⟩ -- Function behaves as intended
    intro n m; simp[hfp]
    refine ⟨by rintro rfl; rfl, (succ_inj _ _).2⟩
  intro f1 f2 ⟨h1b, h10, h1i⟩ ⟨h2b, h20, h2i⟩; ext n
  congr;
  induction' hx1: (n:ℕ) with i ih generalizing n
  · rw [nat_equiv.symm_apply_eq] at hx1; have hx1 : n = (0:nat) := by simp [hx1]; rfl
    subst hx1; rw [h10, h20]
  let r := nat_equiv i;
  have hx1 : n = (nat_equiv.symm r + 1 : ℕ ) := by unfold r; simp [← hx1]
  subst hx1 -- n = r + 1
  rw [(h1i _ _).mp rfl,  (h2i _ _).mp rfl ] -- move +1 outside operation
  rw [← succ_inj]; apply ih; unfold r; simp -- cancel +1 both sides



end Chapter3
