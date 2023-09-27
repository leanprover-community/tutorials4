import Tutorials.TutoLib


section

/-
The first part of this file makes sure you can negate quantified statements
in your head without the help of `push_neg`.

You need to complete the statement and then use the `check_me` tactic
to check your answer. This tactic exists only for those exercises,
it mostly calls `push_neg` and then cleans up a bit.

`def SeqLimit (u : ℕ → ℝ) (l : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`
-/
-- In this section, u denotes a sequence of real numbers
-- f is a function from ℝ to ℝ
-- x₀ and l are real numbers
variable (u : ℕ → ℝ) (f : ℝ → ℝ) (x₀ l : ℝ)


-- Negation of "u tends to l"
-- 0062
example :
    (¬∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε) ↔-- sorry
      ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| > ε := by
-- sorry
check_me
-- sorry

-- Negation of "f is continuous at x₀"
-- 0063
example :
    (¬∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε) ↔-- sorry
      ∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ |f x - f x₀| > ε := by
-- sorry
check_me
-- sorry

/-
In the next exercise, we need to keep in mind that
`∀ x x', ...` is the abbreviation of
`∀ x, ∀ x', ... `.

Also, `∃ x x', ...` is the abbreviation of `∃ x, ∃ x', ...`.
-/
-- Negation of "f is uniformly continuous on ℝ"
-- 0064
example :
    (¬∀ ε > 0, ∃ δ > 0, ∀ x x', |x' - x| ≤ δ → |f x' - f x| ≤ ε) ↔-- sorry
      ∃ ε > 0, ∀ δ > 0, ∃ x x', |x' - x| ≤ δ ∧ |f x' - f x| > ε := by
-- sorry
check_me
-- sorry

-- Negation of "f is sequentially continuous at x₀"
-- 0065
example :
    (¬∀ u : ℕ → ℝ,
          (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ ε) →
            ∀ ε > 0, ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε) ↔-- sorry
      ∃ u : ℕ → ℝ,
        (∀ δ > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ) ∧ ∃ ε > 0, ∀ N, ∃ n ≥ N, |f (u n) - f x₀| > ε := by
-- sorry
check_me
-- sorry

end

/-
We now turn to elementary applications of negations to limits of sequences.
Remember that `linarith` can find easy numerical contradictions.

Also recall the following lemmas:

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

`ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

/-- The sequence `u` tends to `+∞`. -/
`def TendstoInfinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A`
-/

-- 0066
example {u : ℕ → ℝ} : TendstoInfinity u → ∀ l, ¬SeqLimit u l := by
  -- sorry
  intro lim_infinie l lim_l
  rcases lim_l 1 (by linarith) with ⟨N, hN⟩
  rcases lim_infinie (l + 2) with ⟨N', hN'⟩
  let N₀ := max N N'
  specialize hN N₀ (le_max_left _ _)
  specialize hN' N₀ (le_max_right _ _)
  rw [abs_le] at hN
  linarith
  -- sorry

def NondecreasingSeq (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

-- 0067
example (u : ℕ → ℝ) (l : ℝ) (h : SeqLimit u l) (h' : NondecreasingSeq u) : ∀ n, u n ≤ l := by
  -- sorry
  intro n
  by_contra H
  push_neg  at H
  rcases h ((u n - l) / 2) (by linarith) with ⟨N, hN⟩
  specialize hN (max n N) (le_max_right _ _)
  specialize h' n (max n N) (le_max_left _ _)
  rw [abs_le] at hN
  linarith
  -- sorry

/-
In the following exercises, `A : set ℝ` means that A is a set of real numbers.
We can use the usual notation `x ∈ A`.

The notation `∀ x ∈ A, ...` is the abbreviation of `∀ x, x ∈ A → ... `

The notation `∃ x ∈ A, ...` is the abbreviation of `∃ x, x ∈ A ∧ ... `.

We'll work with upper bounds and supremums.
Again we'll introduce specialized definitions for the sake of exercises, but mathlib
has more general versions.

`def UpperBound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x`

`def IsSup (A : set ℝ) (x : ℝ) := UpperBound A x ∧ ∀ y, UpperBound A y → x ≤ y`


Remark: one can easily show that a set of real numbers has at most one sup,
but we won't need this.
-/
-- 0068
example {A : Set ℝ} {x : ℝ} (hx : IsSup A x) : ∀ y, y < x → ∃ a ∈ A, y < a := by
  -- sorry
  intro y
  contrapose!
  exact hx.right y
  -- sorry

/-
Let's do a variation on an example from file 07 that will be useful in the last
exercise below.
-/
-- 0069
theorem le_of_le_add_all' {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) → y ≤ x := by
  -- sorry
  contrapose!
  intro h
  use (y - x) / 2
  constructor <;> linarith
  -- sorry

-- 0070
example {x y : ℝ} {u : ℕ → ℝ} (hu : SeqLimit u x) (ineg : ∀ n, u n ≤ y) : x ≤ y := by
  -- sorry
  apply le_of_le_add_all'
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  specialize hN N (by linarith)
  rw [abs_le] at hN
  linarith [ineg N]
  -- sorry
