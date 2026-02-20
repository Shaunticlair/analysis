import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]




/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
    image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
  ext y; rw [mem_image, specification_axiom'']
  constructor <;> intro h
  · obtain ⟨x, h1, h2⟩ := h
    use (h2 ▸ (f x).property) -- ▸ allows for inline substitution
    refine ⟨x, h1 ,by simp [← h2]⟩
  · choose h x h1 h2 using h
    refine ⟨x, h1, by simp [h2]⟩


/--
  Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by -- '' is used to generate function images in Mathlib
  -- Left side is image in SetTheory.Set, right side is Mathlib image
  ext;
  simp only [replacement_axiom, Subtype.exists, exists_and_right, Set.mem_setOf_eq, _root_.Set.mem_image, exists_and_left, exists_eq_right]; grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _);
  map_tacs [use 1; use 2; use 3]; all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
  intro h; rw [mem_image]; use x

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
  refine ⟨{1,2},{1}, fun x ↦ ⟨1, by aesop⟩, {1}, ⟨2, by aesop⟩, ?_⟩
  simp -- f (2) = 1 ∈ image f {1}, but 2 ∉ {1}

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that U be a subset of Y.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of mem_preimage that does not require x to be of type X.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h; by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩; have := mem_preimage f U ⟨ _, hx ⟩; simp_all
    . grind [specification_axiom]
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop -- specification_axiom''

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.preimage_f_3_4_2' : preimage f_3_4_2 {1,2,3} = {1} := by
ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
· rintro ⟨x, rfl, _⟩ ; simp_all; omega
intro h; simp at h; subst h; use 1; simp

theorem SetTheory.Set.image_preimage_f_3_4_2'': image f_3_4_2 {1} = {2} := by
  ext; rw [mem_image]; constructor
  · rintro ⟨_, h, rfl⟩; unfold f_3_4_2; simp_all
  intro h; simp at h; subst h; use 1; simp


theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
  simp; rw [SetTheory.Set.ext_iff]; push_neg
  use 1; right; refine ⟨?_, by simp⟩;
  rw [preimage_f_3_4_2', image_preimage_f_3_4_2''];
  simp

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  -- x^2=4=2^2 → x = ± 2
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  -- Lean can infer about x^2=1 and x^2=0 automatically
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  simp; rw [_root_.Set.ext_iff]; push_neg
  use -2; left; refine ⟨ ?_, by simp ⟩
  rw [_root_.Set.mem_preimage, _root_.Set.mem_image]; use 2; simp

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a `CoeOut` rather than a
`Coe` because the input type `X → Y` contains
parameters not present in the output type `Output` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun] -- function_to_object was defined as an injective embedding

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

noncomputable abbrev SetTheory.Set.powfun {X Y:Set} (F : (Y ^ X : Set) ): X → Y :=
  ((SetTheory.Set.powerset_axiom _).mp F.property).choose

lemma SetTheory.Set.powfun_prop {X Y:Set} (F : (Y ^ X : Set) ): powfun F = F.val :=
  ((SetTheory.Set.powerset_axiom _).mp F.property).choose_spec

lemma SetTheory.Set.powfun_obj_fun {X Y:Set} (f : X → Y ) :
(powfun ⟨f, by aesop⟩) = f := by rw [powfun]; aesop

#check SetTheory.Set.powfun_prop
/-- The set of subsets of X (powerset of X)-/
def SetTheory.Set.powerset (X:Set) : Set :=
(({0,1} ^ X): Set).replace
  (P := fun F S ↦ S = preimage (powfun F) {1})
  (by aesop)

open Classical in
/- Exercise 3.4.6 (i) -/
/-- Membership for the set of subsets of X (powerset of X)-/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  rw [powerset, replacement_axiom]
  constructor
  · rintro ⟨F, rfl⟩ -- powerset elem is preimage: naturally a subset of X
    refine ⟨ preimage (powfun F) {1},
      by simp, by apply preimage_in_domain ⟩
  rintro ⟨S, rfl, h⟩ -- Function outputs 1 if in S, 0 else: recreates S
  let f : X → ({0, 1}: Set) :=
    fun x ↦ if x.val ∈ S then ⟨1, by simp⟩  else ⟨0, by simp⟩
  use ⟨f, by aesop⟩
  simp [powfun_obj_fun]
  ext; simp [f]; aesop

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x
-- Notably, Tao's construction allows for taking the union over sets that contain non-sets
-- Funny enough, this means ⋃₀ ∅ = ⋃₀ A if A contains only non-sets

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  ext; rw [union_axiom]; simp
  refine ⟨?_, by aesop⟩
  rintro ⟨S, hS, rfl | rfl | rfl⟩
  all_goals aesop

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by grind))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  · simp_all [replacement_axiom]; grind
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  ext; rw [mem_iUnion]; simp -- x would need to be indexed by an element of the empty set

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I := -- Decompose ∃ into a choice function
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

-- We don't need to pick β if I is nonempty: we'll just use choice
noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  rw [specification_axiom''];
  simp -- (∀ i:I, x ∈ A i) on both sides of equality
  intro h; apply h -- Specialize to (nonempty_choose hI)

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV: V ⊆ Y) :
    image f_inv V = preimage f V := by
  ext x; rw [mem_image, mem_preimage'];
  simp -- Both expressions ask, "does x have a counterpart in V under f"
  constructor
  · rintro ⟨y, hV', hY, rfl⟩ -- x is linked to y ∈ V by f_inv
    refine ⟨(f_inv ⟨y, hY⟩).property, ?_⟩ -- x ∈ X b/c it's output of f_inv
    convert hV'; rw [hf.2] -- Cancel inverse: shows f x = y ↔ f_inv y = x
  · rintro ⟨hX, hV'⟩
    refine ⟨_, hV', hV _ hV', ?_⟩
    rw [hf.1] -- Cancel inverse: shows f_inv (f x) = x

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : S ⊆ preimage f (image f S) := by
  intro x hx; simp
  refine ⟨hS _ hx, x, ?_, hx⟩
  refine ⟨hS _ hx, rfl⟩

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : image f (preimage f U) ⊆ U := by
  rintro y; rw [mem_image];
  rintro ⟨x, h1, h2⟩; simp at h1;
  exact h2 ▸ h1.2

lemma SetTheory.Set.preimage_subset {X Y:Set} (f:X → Y) (A B : Set)
  (hAB : A ⊆ B) : preimage f A ⊆ preimage f B := by
  intro x hx; rw [mem_preimage'] at *; peel hx with x' hx'x hA
  exact hAB _ hA

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : preimage f (image f (preimage f U)) = preimage f U := by
apply subset_antisymm
· apply preimage_subset; apply image_of_preimage
· apply preimage_of_image; apply preimage_in_domain

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
intro y hy; rw [mem_image] at hy; choose y hy using hy
simp at hy;
rw [mem_inter, mem_image, mem_image]
refine ⟨⟨y, hy.1.1, hy.2⟩, ⟨y, hy.1.2, hy.2⟩⟩

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
  intro y; rw [mem_sdiff]; repeat rw [mem_image];
  rintro ⟨⟨x, hxA, hxf⟩, h2⟩;
  push_neg at h2; replace h2 := (h2 x).mt (by simp_all)
  refine ⟨x, by simp [hxA, h2], hxf⟩


theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
  ext y; rw [mem_image, mem_union, mem_image, mem_image];
  conv => lhs; arg 1; intro; simp;
  grind -- Comparing (a ∨ b) ∧ c with (a ∧ c) ∨ (b ∧ c)
  -- Just needs a little extra work because one side has 2 ∃ terms and the other has 1

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse; push_neg;
  refine ⟨{1,2},{1}, fun _ ↦ ⟨1, by aesop⟩, {1}, {2}, ?_⟩
  simp; rw [SetTheory.Set.ext_iff]; push_neg
  use 1; right; simp

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse; push_neg
  refine ⟨{1,2},{1}, fun _ ↦ ⟨1, by aesop⟩, {1,2},{1},?_⟩
  simp; rw [SetTheory.Set.ext_iff]; push_neg
  use 1; left; simp

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
ext x; rw [mem_preimage', mem_inter, mem_preimage', mem_preimage'];
simp; tauto -- Both sides are nearly identical

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
ext x; rw [mem_preimage', mem_union, mem_preimage', mem_preimage'];
conv => lhs; arg 1; intro; simp;
simp; grind -- Comparing two (a ∨ b) statements: ∃ is the only problem

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
ext x; rw [mem_preimage', mem_sdiff, mem_preimage', mem_preimage'];
conv => lhs; arg 1; intro; simp;
simp; tauto -- Similar to inter, except we have x ∉ B instead of x ∈ B
-- diff caused problems in the image case, but in preimage, we're always
-- referring to the same x: ∀ x, x = x' ∧ P x can be redundantly reduced to P x'

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
  constructor <;> intro h
  · intro y; -- If f f⁻¹ S = S, that means no elements are lost when we preimage and image
    -- We'll only use {y} to focus on the element of interest
    specialize h ({y.val}:Set) (by intro y; aesop)
    rw [SetTheory.Set.ext_iff] at h; specialize h y;
    (conv at h => rhs; simp); simp only [iff_true] at h
    -- If y is in an image, it map to some corresponding input element x
    rw [mem_image] at h
    obtain ⟨x, hX, h⟩ := h; rw [coe_inj] at h; use x
  intro U hUY; apply subset_antisymm; apply image_of_preimage
  intro y hy; rw [mem_image]; -- To be in the image, y must have an input x ∈ f⁻¹ U
  choose x h using (h ⟨y, hUY _ hy⟩); -- Grab x
  use x; simp -- Prove x ∈ f⁻¹ U: we know because y ∈ U
  refine ⟨ ⟨x.property, by simp [h,hy]⟩, by simp [h]⟩

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
  (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
  constructor <;> intro h
  · intro x z hf
    specialize h ({x.val}:Set) (by intro; aesop)
    rw [SetTheory.Set.ext_iff] at h; specialize h z
    simp at h; rw [coe_inj, coe_inj] at h
    symm; rw [← h]
    refine ⟨x.property, z.property, hf⟩
  intro S hSX; apply subset_antisymm;
  · intro x hx; -- To be in preimage, f x ∈ image f S
    rw [mem_preimage'] at hx; simp at hx -- Find z ∈ S with f z = f x
    obtain ⟨hxX, z, ⟨hzX, hf⟩, hzS⟩ := hx
    lift x to X using hxX with x' hx' -- f takes type X as input
    lift z to X using hzX with z' hz'
    convert hzS -- By injectivity, x = z. So if z ∈ S, x ∈ S
    apply h; rw [coe_inj] at hf; apply hf.symm
  apply preimage_of_image _ _ hSX

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

#check SetTheory.Set.mem_powerset

noncomputable abbrev SetTheory.Set.PSet {X: Set} (x : powerset X): Set := ((mem_powerset x).mp (x.property)).choose

lemma SetTheory.Set.PSet_prop {X: Set} (x : powerset X): x = set_to_object (PSet x) ∧ PSet x ⊆ X :=
  ((mem_powerset _).mp (x.property)).choose_spec

lemma SetTheory.Set.PSet_prop' (A X : Set) (h :  (A:Object) ∈ powerset X ) :
  A = PSet ⟨A, h⟩ := by
  have := (PSet_prop ⟨A, h⟩).1  -- PSet is the set specifically constructed to correspond to (A : Object)
  simpa using this -- (A : Object) = (Pset ⟨A, h⟩ : Object) + object embedding is injective

abbrev SetTheory.Set.set_partial_functions (X Y:Set) : Set := by
  let PX := powerset X
  let PY := powerset Y

  let fX : PX → Set := fun X' ↦
  union (
    PY.replace (P := fun Y' Y'X' ↦ Y'X' = set_to_object ((PSet Y')^(PSet X')) ) (by aesop)
  )

  exact union (
    PX.replace (P := fun X' YX' ↦ YX' = fX (X')  ) (by aesop)
  )

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
  use set_partial_functions X Y; intro F
  rw [mem_union_powerset_replace_iff];
  constructor
  · rintro ⟨X', YX', h, hF⟩; -- F ∈ fX (X')
    simp at h; subst h; rw [mem_union_powerset_replace_iff] at hF;
    obtain ⟨Y', Y'X', hF1, hF⟩ := hF -- F ∈ Y' ^ X'
    simp at hF1; subst hF1
    refine ⟨ PSet X', PSet Y', (PSet_prop X').2, (PSet_prop Y').2, ?_⟩
    rw [powerset_axiom] at hF; peel hF with f hF; rw [hF] -- Thus, F corresponds to f : X' → Y'
  rintro ⟨X', Y', hX, hY, ⟨f, hf⟩ ⟩ -- Access the corresponding elem within Z step-by-step
  use ⟨X', by simp [hX]⟩; simp;
  rw [mem_union_powerset_replace_iff]
  use ⟨Y', by simp [hY]⟩; simp
  rw [← mem_powerset'] at hX hY
  rw [← PSet_prop', ← PSet_prop'] -- Fix type of function
  refine ⟨f, hf.symm⟩

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  use union {set_to_object X, set_to_object Y}
  intro x; rw [union_axiom]; simp
  aesop -- (S = X ∨ S = Y) is contextually equivalent to (x ∈ X ∨ x ∈ Y)

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by
  ext x; repeat rw [specification_axiom''];
  -- They only differ on the statement that x ∈ A β, but ∀ i, x ∈ A i implies this anyway
  constructor <;> intro ⟨_, h⟩ <;> refine ⟨h _, h⟩

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
= iUnion (I ∪ J) A := by
  ext x; simp [mem_iUnion]; rw [← exists_or]
  peel with i
  constructor <;> intro h
  · rcases h with h | h <;> choose h1 h2 using h <;> refine ⟨by tauto, h2⟩
  tauto

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by
  apply nonempty_def at hI; apply nonempty_of_inhabited
  simp; left; apply hI.choose_spec

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
= iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
  have hIJ := union_of_nonempty hI hJ
  ext x; rw [mem_inter]; repeat rw [mem_iInter]
  simp; rw [← forall_and]
  peel with i
  constructor <;> intro h
  · intro hi
    rcases hi with hi | hi
    apply h.1 hi ; apply h.2 hi
  · constructor <;> intro hi <;> apply h <;> tauto

lemma SetTheory.Set.not_mem {A : Set} (x : Object): x ∉ A ↔ ¬ (x ∈ A) := by simp

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
  ext x; rw [mem_iInter, mem_sdiff, mem_iUnion]; push_neg
  choose i hI using nonempty_def hI
  constructor <;> intro h
  · intro i; rw [mem_sdiff]; simp [h]
  constructor <;> [specialize h ⟨i, hI⟩; peel h with i h] -- Req. nonempty to get x ∈ X
  <;> simp at h <;> tauto -- x ∈ X \ A i contains the desired info for both goals


/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
  ext x; rw [mem_sdiff, mem_iInter, mem_iUnion]; push_neg
  rw [← exists_and_left]; simp -- For x ∈ X \ A i, choice of i doesn't affect x ∈ X

end Chapter3
