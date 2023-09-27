import Tutorials.TutoLib

/-
Negations, proof by contradiction and contraposition.

This file introduces the logical rules and tactics related to negation:
exfalso, by_contra, contrapose, by_cases and push_neg.

There is a special statement denoted by `False` which, by definition,
has no proof.

So `False` implies everything. Indeed `False → P` means any proof of
`False` could be turned into a proof of P.
This fact is known by its latin name
"ex falso quod libet" (from False follows whatever you want).
Hence Lean's tactic to invoke this is called `exfalso`.
-/
example : False → 0 = 1 := by
  intro h
  exfalso
  exact h

/-
The preceding example suggests that this definition of `False` isn't very useful.
But actually it allows us to define the negation of a statement P as
"P implies False" that we can read as "if P were true, we would get
a contradiction". Lean denotes this by `¬ P`.

One can prove that (¬ P) ↔ (P ↔ False). But in practice we directly
use the definition of `¬ P`.
-/
example {x : ℝ} : ¬x < x := by
  intro hyp
  rw [lt_iff_le_and_ne] at hyp
  rcases hyp with ⟨hyp_inf, hyp_non⟩
  clear hyp_inf -- we won't use that one, so let's discard it
  change x = x → False at hyp_non -- Lean doesn't need this psychological line
  apply hyp_non
  rfl

open Int

-- 0045
example (n : ℤ) (h_even : Even n) (h_not_even : ¬Even n) : 0 = 1 := by
  -- sorry
  exfalso
  exact h_not_even h_even
  -- sorry

-- 0046
example (P Q : Prop) (h₁ : P ∨ Q) (h₂ : ¬(P ∧ Q)) : ¬P ↔ Q := by
  -- sorry
  constructor
  · intro hnP
    rcases h₁ with hP | hQ
    · exfalso
      exact hnP hP
    · exact hQ
  · intro hQ hP
    exact h₂ ⟨hP, hQ⟩
  -- sorry

/-
The definition of negation easily implies that, for every statement P,
`P → ¬ ¬ P`.

The excluded middle axiom, which asserts `P ∨ ¬ P` allows us to
prove the converse implication.

Together those two implications form the principle of double negation elimination.
  `not_not {P : Prop} : (¬ ¬ P) ↔ P`

The implication `¬ ¬ P → P` is the basis for proofs by contradiction:
in order to prove `P`, it suffices to prove `¬ ¬ P`, ie `¬ P → False`.

Of course there is no need to keep explaining all this. The tactic
`by_contra Hyp` will transform any goal `P` into `False` and
add `Hyp : ¬ P` to the local context.

Let's return to a proof from the 5th file: uniqueness of limits for a sequence.
This cannot be proved without using some version of the excluded middle
axiom. We used it secretely in

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

(we'll prove a variation on this lemma below).

In the proof below, we also take the opportunity to introduce the `let` tactic
which creates a local definition. If needed, it can be unfolded using `unfold_let`.
For instance after using `let N₀ := max N N'`, you could write
`unfold_let N₀ at h` to replace `N₀` by its definition in some local assumption `h`.
-/
example (u : ℕ → ℝ) (l l' : ℝ) : SeqLimit u l → SeqLimit u l' → l = l' := by
  intro hl hl'
  by_contra H
  change l ≠ l' at H -- Lean does not need this line, but it makes H easier to read
  have ineg : |l - l'| > 0 := abs_pos.mpr (sub_ne_zero_of_ne H) -- details about that line are not important
  rcases hl (|l - l'| / 4) (by linarith) with ⟨N, hN⟩
  rcases hl' (|l - l'| / 4) (by linarith) with ⟨N', hN'⟩
  let N₀ := max N N'
  specialize hN N₀ (le_max_left _ _)
  specialize hN' N₀ (le_max_right _ _)
  have clef : |l - l'| < |l - l'|
  calc
    |l - l'| = |l - u N₀ + (u N₀ - l')| := by ring_nf
    _ ≤ |l - u N₀| + |u N₀ - l'| := by apply abs_add
    _ = |u N₀ - l| + |u N₀ - l'| := by rw [abs_sub_comm]
    _ < |l - l'| := by linarith

  linarith -- linarith can also find simple numerical contradictions

/-
Another incarnation of the excluded middle axiom is the principle of
contraposition: in order to prove P ⇒ Q, it suffices to prove
not Q ⇒ not P.
-/

-- Using a proof by contradiction, let's prove the contraposition principle
-- 0047
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  -- sorry
  intro hP
  by_contra hnQ
  exact h hnQ hP
  -- sorry

/-
Again Lean doesn't need this principle explained to it. We can use the
`contrapose` tactic.
-/
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  contrapose
  exact h

/-
In the next exercise, we'll use
 Odd n : ∃ k, n = 2*k + 1
 Int.odd_iff_not_even {n : ℤ} : odd n ↔ ¬ even n
-/
-- 0048
example (n : ℤ) : Even (n ^ 2) ↔ Even n := by
  -- sorry
  constructor
  · contrapose
    rw [← Int.odd_iff_not_even, ← Int.odd_iff_not_even]
    rintro ⟨k, rfl⟩
    use 2 * k * (k + 1)
    ring
  · rintro ⟨k, rfl⟩
    use 2 * k ^ 2
    ring
  -- sorry

/-
As a last step on our law of the excluded middle tour, let's notice that, especially
in pure logic exercises, it can sometimes be useful to use the
excluded middle axiom in its original form:
  `Classical.em : ∀ P, P ∨ ¬ P`

Instead of applying this lemma and then using the `rcases` tactic, we
have the shortcut
 `by_cases h : P`

combining both steps to create two proof branches: one assuming
`h : P`, and the other assuming `h : ¬ P`.

For instance, let's prove a reformulation of this implication relation,
which is sometimes used as a definition in other logical foundations,
especially those based on truth tables (hence very strongly using
excluded middle from the very beginning).
-/
variable (P Q : Prop)

example : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      exact h hP
    · left
      exact hP
  · intro h hP
    rcases h with hnP | hQ
    · exfalso
      exact hnP hP
    · exact hQ

-- 0049
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  -- sorry
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      exact h ⟨hP, hQ⟩
    · left
      exact hP
  · rintro h ⟨hP, hQ⟩
    rcases h with hnP | hnQ
    · exact hnP hP
    · exact hnQ hQ
  -- sorry

/-
It is crucial to understand negation of quantifiers.
Let's do it by hand for a little while.
In the first exercise, only the definition of negation is needed.
-/
-- 0050
example (n : ℤ) : (¬∃ k, n = 2 * k) ↔ ∀ k, n ≠ 2 * k := by
  -- sorry
  constructor
  · intro hyp k hk
    exact hyp ⟨k, hk⟩
  · rintro hyp ⟨k, rfl⟩
    exact hyp k rfl
  -- sorry

/-
Contrary to negation of the existential quantifier, negation of the
universal quantifier requires excluded middle for the first implication.
In order to prove this, we can use either
* a double proof by contradiction
* a contraposition, `not_not : (¬ ¬ P) ↔ P` and a proof by contradiction.

Recall we have
`EvenFun (f : ℝ → ℝ) := ∀ x, f (-x) = f x`

-/

-- 0051
example (f : ℝ → ℝ) : ¬EvenFun f ↔ ∃ x, f (-x) ≠ f x := by
  -- sorry
  constructor
  · contrapose
    intro h
    rw [not_not]
    intro x
    by_contra H
    apply h
    use x
  /- Alternative version
      intro h
      by_contra H
      apply h
      intro x
      by_contra H'
      apply H
      use x -/
  · intro ⟨x, hx⟩ h'
    exact hx (h' x)
  -- sorry

/-
Of course we can't keep repeating the above proofs, especially the second one.
So we use the `push_neg` tactic.
-/
example : ¬EvenFun fun x => 2 * x := by
  unfold EvenFun
  -- Here unfolding is important because push_neg won't do it.
  push_neg
  use 42
  linarith

-- 0052
example (f : ℝ → ℝ) : ¬EvenFun f ↔ ∃ x, f (-x) ≠ f x := by
  -- sorry
  unfold EvenFun
  push_neg
  rfl
  -- sorry

def BoundedAbove (f : ℝ → ℝ) :=
  ∃ M, ∀ x, f x ≤ M

example : ¬BoundedAbove fun x => x := by
  unfold BoundedAbove
  push_neg
  intro M
  use M + 1
  linarith

-- Let's contrapose
-- 0053
example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  -- sorry
  contrapose
  push_neg
  intro h
  use x / 2
  constructor <;> linarith
  -- sorry

/-
The "contrapose, push_neg" combo is so common that we can abreviate it to
`contrapose!`

Let's use this trick, together with:
  `eq_or_lt_of_le : a ≤ b → a = b ∨ a < b`
-/
-- 0054
example (f : ℝ → ℝ) : (∀ x y, x < y → f x < f y) ↔ ∀ x y, x ≤ y ↔ f x ≤ f y := by
  -- sorry
  constructor
  · intro hf x y
    constructor
    · intro hxy
      rcases eq_or_lt_of_le hxy with hxy | hxy
      · rw [hxy]
      · linarith [hf x y hxy]
    · contrapose!
      apply hf
  · intro hf x y
    contrapose!
    intro h
    rwa [hf]
  -- sorry
