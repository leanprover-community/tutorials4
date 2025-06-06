import Mathlib.Data.Real.Basic

/-
In the previous file, we saw how to rewrite using equalities.
The analogue operation with mathematical statements is rewriting using
equivalences. This is also done using the `rw` tactic.
Lean uses `↔` to denote equivalence instead of `⇔` (increase font size if you don't see a difference).

In the following exercises we will use the lemma:

  `sub_nonneg {x y : ℝ} : 0 ≤ y - x ↔ x ≤ y`

The curly braces around x and y instead of parentheses mean Lean will always try to figure out what
x and y are from context, unless we really insist on telling it (we'll see how to insist much later).
Let's not worry about that for now.

In order to announce an intermediate statement we use:

  `have my_name : my statement := by`

This triggers the apparition of a new goal: proving the statement. After this is done,
the statement becomes available under the name `my_name`.
-/

example {a b c : ℝ} (hab : a ≤ b) : c + a ≤ c + b := by
  rw [← sub_nonneg]
  have key : c + b - (c + a) = b - a :=  by-- Here we introduce an intermediate statement named key
    -- and prove it in an idented code block (or on the same line if the proof is very short)
    ring
  -- we can now use the key statement
  rw [key]
  rw [sub_nonneg]
  exact hab

/-
Of course the previous lemma is already in the core library, named `add_le_add_left`, so we can use it below.

Let's prove a variation (without invoking commutativity of addition to reduce to the previous statement
since this would spoil our fun).
-/
-- 0009
example {a b : ℝ} (hab : a ≤ b) (c : ℝ) : a + c ≤ b + c := by
  -- sorry
  have key : b + c - (a + c) = b - a := by ring
  rw [← sub_nonneg]
  rw [key]
  rw [sub_nonneg]
  exact hab
  -- sorry

/-
Let's see how we could use this lemma. It is already in the core library, under the name `add_le_add_right`:

  `add_le_add_right {a b : ℝ} (hab : a ≤ b) (c : ℝ) : a + c ≤ b + c`

This can be read as: "add_le_add_right is a function that will take as input real numbers a and b, an
assumption `hab` claiming a ≤ b and a real number c, and will output a proof of a + c ≤ b + c".

In addition, recall that curly braces around `a b` mean Lean will figure out those arguments unless we
insist to help. This is because they can be deduced from the next argument `hab`.
So it will be sufficient to feed `hab` and `c` to this function.
-/
example {a b : ℝ} (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact add_le_add_right ha b


/-
In the second line of the above proof, we need to prove `0 + b ≤ a + b`.
The proof after the colon says: this is exactly lemma `add_le_add_right` applied to ha and b.
Actually the `calc` block expects proof terms, and the `by` keyword is used to tell Lean we will use tactics
to build such a proof term. But since the only tactic used in this block is `exact`, we can skip
tactics entirely, and write:
-/
example (a b : ℝ) (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := add_le_add_right ha b


-- Let's do a variant.
-- 0010
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  -- sorry
  calc
    a = a + 0 := by ring
    _ ≤ a + b := add_le_add_left hb a
  -- sorry

/-
The two preceding examples are in the core library :

  `le_add_of_nonneg_left  {a b : ℝ} (ha : 0 ≤ a) : b ≤ a + b`
  `le_add_of_nonneg_right {a b : ℝ} (hb : 0 ≤ b) : a ≤ a + b`

Again, there won't be any need to memorize those names, we will
soon see how to get rid of such goals automatically.
But we can already try to understand how their names are built:
"le_add" describe the conclusion "less or equal than some addition"
It comes first because we are focussed on proving stuff, and
auto-completion works by looking at the beginning of words.
"of" introduces assumptions. "nonneg" is Lean's abbreviation for non-negative.
"left" or "right" disambiguates between the two variations.

Let's use those lemmas by hand for now.

Note that you can have several inequalities steps in a `calc` block,
transitivity of inequalities will be used automatically to assemble
the pieces.
-/
-- 0011
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  -- sorry
  calc
    0 ≤ a := ha
    _ ≤ a + b := le_add_of_nonneg_right hb
  -- sorry

-- And let's combine with our earlier lemmas.
-- 0012
example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  -- sorry
  calc
    a + c ≤ b + c := add_le_add_right hab c
    _ ≤ b + d := add_le_add_left hcd b
  -- sorry

/-
In the above examples, we prepared proofs of assumptions of our lemmas beforehand, so
that we could feed them to the lemmas. This is called forward reasoning.
The `calc` proofs also belong to this category.

We can also announce the use of a lemma, and provide proofs after the fact, using
the `apply` tactic. This is called backward reasoning because we get the conclusion
first, and provide proofs later. Using `rw` on the goal (rather than on an assumption
from the local context) is also backward reasoning.

Let's do that using the lemma

  `mul_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y`
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  rw [← sub_nonneg]
  have key : b * c - a * c = (b - a) * c := by ring
  rw [key]
  apply mul_nonneg
  -- Here we don't provide proofs for the lemma's assumptions
  -- Now we need to provide the proofs.
  -- There are now two things to prove. We use the center dot (typed using `\.`) to
  -- focus on the current first goal.
  · rw [sub_nonneg]
    exact hab
  · exact hc

/-
Let's prove the same statement using only forward reasoning: announcing stuff,
proving it by working with known facts, moving forward.
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  have hab' : 0 ≤ b - a := by
    rw [← sub_nonneg] at hab
    exact hab
  have h₁ : 0 ≤ (b - a) * c := mul_nonneg hab' hc
  have h₂ : (b - a) * c = b * c - a * c := by ring
  have h₃ : 0 ≤ b * c - a * c := by
    rw [h₂] at h₁
    exact h₁
  rw [sub_nonneg] at h₃
  exact h₃

/-
One reason why the backward reasoning proof is shorter is because Lean can
infer of lot of things by comparing the goal and the lemma statement. Indeed
in the `apply mul_nonneg` line, we didn't need to tell Lean that `x = b - a`
and `y = c` in the lemma. It was infered by "unification" between the lemma
statement and the goal.

To be fair to the forward reasoning version, we should introduce a convenient
variation on `rw`. The `rwa` tactic performs rewrite and then looks for an
assumption matching the goal. We can use it to rewrite our latest proof as:
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  have hab' : 0 ≤ b - a := by rwa [← sub_nonneg] at hab
  have h₁ : 0 ≤ (b - a) * c := mul_nonneg hab' hc
  have h₂ : (b - a) * c = b * c - a * c := by ring
  have h₃ : 0 ≤ b * c - a * c := by rwa [h₂] at h₁
  rwa [sub_nonneg] at h₃

/-
Let's now combine forward and backward reasoning, to get our most
efficient proof of this statement. Note in particular how unification is used
to know what to prove inside the parentheses in the `mul_nonneg` arguments.
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  rw [← sub_nonneg]
  calc
    0 ≤ (b - a) * c := mul_nonneg (by rwa [sub_nonneg]) hc
    _ = b * c - a * c := by ring


/-
Let's now practice all three styles using:

  `mul_nonneg_of_nonpos_of_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b`

  `sub_nonpos {a b : α} : a - b ≤ 0 ↔ a ≤ b`
-/
-- First using mostly backward reasoning
-- 0013
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  -- sorry
  rw [← sub_nonneg]
  have fact : a * c - b * c = (a - b) * c
  ring
  rw [fact]
  apply mul_nonneg_of_nonpos_of_nonpos
  · rwa [sub_nonpos]
  · exact hc
  -- sorry

-- Using forward reasoning
-- 0014
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  -- sorry
  have hab' : a - b ≤ 0 := by rwa [← sub_nonpos] at hab
  have h₁ : 0 ≤ (a - b) * c := mul_nonneg_of_nonpos_of_nonpos hab' hc
  have h₂ : (a - b) * c = a * c - b * c := by ring
  have h₃ : 0 ≤ a * c - b * c := by rwa [h₂] at h₁
  rwa [sub_nonneg] at h₃
  -- sorry

-- 0015
/-- Using a combination of both, with a `calc` block -/
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  -- sorry
  have hab' : a - b ≤ 0 := by rwa [sub_nonpos]
  rw [← sub_nonneg]
  calc
    0 ≤ (a - b) * c := mul_nonneg_of_nonpos_of_nonpos hab' hc
    _ = a * c - b * c := by ring
  -- sorry

/-
Let's now move to proving implications. Lean denotes implications using
a simple arrow `→`, the same it uses for functions (say denoting the type of functions
from `ℕ` to `ℕ` by `ℕ → ℕ`). This is because it sees a proof of `P ⇒ Q` as a function turning
a proof of `P` into a proof `Q`.

Many of the examples that we already met are implications under the hood. For instance we proved

  `le_add_of_nonneg_left (a b : ℝ) (ha : 0 ≤ a) : b ≤ a + b`

But this can be rephrased as

  `le_add_of_nonneg_left (a b : ℝ) : 0 ≤ a → b ≤ a + b`

In order to prove `P → Q`, we use the tactic `intro`, followed by an assumption name.
This creates an assumption with that name asserting that `P` holds, and turns the goal into `Q`.

Let's check we can go from our old version of `le_add_of_nonneg_left` to the new one.

-/
example (a b : ℝ) : 0 ≤ a → b ≤ a + b := by
  intro ha
  exact le_add_of_nonneg_left ha

/-
Actually Lean doesn't make any difference between those two versions. It is also happy with
-/
example (a b : ℝ) : 0 ≤ a → b ≤ a + b :=
  le_add_of_nonneg_left

/- No tactic state is shown in the above line because we don't even need to enter
tactic mode using `by`.

Let's practise using `intro`. -/
-- 0016
example (a b : ℝ) : 0 ≤ b → a ≤ a + b := by
  -- sorry
  intro hb
  calc
    a = a + 0 := by ring
    _ ≤ a + b := add_le_add_left hb a
  -- sorry

/-
What about lemmas having more than one assumption? For instance:

  `add_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b`

A natural idea is to use the conjunction operator (logical AND), which Lean denotes
by ∧. Assumptions built using this operator can be decomposed using the `rcases` tactic,
which is a very general assumption-decomposing tactic.
-/
example {a b : ℝ} : 0 ≤ a ∧ 0 ≤ b → 0 ≤ a + b := by
  intro hyp
  rcases hyp with ⟨ha, hb⟩
  exact add_nonneg ha hb

/-
Needing that intermediate line invoking `rcases` shows this formulation is not what is used by
Lean. It rather sees `add_nonneg` as two nested implications:
if a is non-negative then if b is non-negative then a+b is non-negative.
It reads funny, but it is much more convenient to use in practice.
-/
example {a b : ℝ} : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
  add_nonneg

/-
The above pattern is so common that implications are defined as right-associative operators,
hence parentheses are not needed above.

Let's prove that the naive conjunction version implies the funny Lean version. For this we need
to know how to prove a conjunction. The `constructor` tactic creates two goals from a conjunction goal.
It can also be used to create two implication goals from an equivalence goal.
-/
example {a b : ℝ} (H : 0 ≤ a ∧ 0 ≤ b → 0 ≤ a + b) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  intro ha
  intro hb
  apply H
  constructor
  exact ha
  exact hb

/-
Let's practice `rcases` and `constructor`. In the next exercise, `P`, `Q` and `R` denote
unspecified mathematical statements.
-/
-- 0017
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- sorry
  intro hyp
  rcases hyp with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP
  -- sorry

/-
Of course using `constructor` only to be able to use `exact` twice in a row feels silly. One can
also use the anonymous constructor syntax: ⟨ ⟩
Beware those are not parentheses but angle brackets. This is a generic way of providing
compound objects to Lean when Lean already has a very clear idea of what it is waiting for.

So we could have replaced the last three lines by:
  exact ⟨hQ, hP⟩

We can also combine the `intros` steps. We can now compress our earlier proof to:
-/
example {a b : ℝ} (H : 0 ≤ a ∧ 0 ≤ b → 0 ≤ a + b) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  intro ha hb
  exact H ⟨ha, hb⟩

/-
The anonymous contructor trick actually also works in `intro`. So we can replace
  intro h,
  rcases h with ⟨h₁, h₂⟩
by
  intro ⟨h₁, h₂⟩,
Now redo the previous exercise using all those compressing techniques, in exactly two lines. -/
-- 0018
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- sorry
  intro ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩
  -- sorry

/-
We are ready to come back to the equivalence between the different formulations of
lemmas having two assumptions. Remember the `constructor` tactic can be used to split
an equivalence into two implications.
-/
-- 0019
example (P Q R : Prop) : P ∧ Q → R ↔ P → Q → R := by
  -- sorry
  constructor
  · intro hyp hP hQ
    exact hyp ⟨hP, hQ⟩
  · rintro hyp ⟨hP, hQ⟩
    exact hyp hP hQ
  -- sorry

/-
If you used more than five lines in the above exercise then try to compress things
(without simply removing line ends).

One last compression technique: given a proof `h` of a conjunction `P ∧ Q`, one can get
a proof of `P` using `h.left` and a proof of `Q` using `h.right`, without using `rcases`.
One can also use the more generic (but less legible) names `h.1` and `h.2`.

Similarly, given a proof `h` of `P ↔ Q`, one can get a proof of `P → Q` using `h.mp`
and a proof of `Q → P` using `h.mpr` (or the generic `h.1` and `h.2` that are even less legible
in this case).

Before the final exercise in this file, let's make sure we'll be able to leave
without learning 10 lemma names. The `linarith` tactic will prove any equality or
inequality or contradiction that follows by linear combinations of assumptions from the
context (with constant coefficients).
-/
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Now let's enjoy this for a while.
-/
-- 0020
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  -- sorry
  linarith
  -- sorry

-- And let's combine with our earlier lemmas.
-- 0021
example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  -- sorry
  linarith
  -- sorry

/-
Final exercise

In the last exercise of this file, we will use the divisibility relation on ℕ,
denoted by `∣` (beware this is a unicode divisibility bar, not the ASCII pipe character),
and the `gcd` function.

The definitions are the usual ones, but our goal is to avoid using these definitions and
only use the following three lemmas:

  `dvd_refl (a : ℕ) : a ∣ a`

  `dvd_antisymm {a b : ℕ} : a ∣ b → b ∣ a → a = b :=`

  `dvd_gcd_iff {a b c : ℕ} : c ∣ gcd a b ↔ c ∣ a ∧ c ∣ b`
-/
-- All functions and lemmas below are about natural numbers.
open Nat

-- 0022
example (a b : ℕ) : a ∣ b ↔ gcd a b = a := by
  -- sorry
  have fact : gcd a b ∣ a ∧ gcd a b ∣ b := by rw [← dvd_gcd_iff]
  constructor
  · intro h
    apply dvd_antisymm fact.left
    rw [dvd_gcd_iff]
    exact ⟨dvd_refl a, h⟩
  · intro h
    rw [← h]
    exact fact.right
  -- sorry
