import Tutorials.TutoLib

/-
This file continues the elementary study of limits of sequences.
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

and the definition:

`def SeqLimit (u : ℕ → ℝ) (l : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

You can also use a property proved in the previous file:

`unique_limit : SeqLimit u l → SeqLimit u l' → l = l'`

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`
-/
variable {φ : ℕ → ℕ}

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
theorem id_le_extraction' : Extraction φ → ∀ n, n ≤ φ n := by
  intro hyp n
  induction' n with n hn
  · exact Nat.zero_le _
  · exact Nat.succ_le_of_lt (by linarith [hyp n (n + 1) (by linarith)])

-- 0039
/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
theorem extraction_ge : Extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  -- sorry
  intro h N N'
  use max N N'
  constructor
  apply le_max_right
  calc
    N ≤ max N N' := by apply le_max_left
    _ ≤ φ (max N N') := by apply id_le_extraction' h
  -- sorry

variable {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but does not it when displaying the goal.
-/
-- 0040
/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
theorem near_cluster : ClusterPoint u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  -- sorry
  intro hyp ε ε_pos N
  rcases hyp with ⟨φ, φ_extr, hφ⟩
  rcases hφ ε ε_pos with ⟨N', hN'⟩
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩
  exact ⟨φ q, hq', hN' _ hq⟩
  -- sorry

/-
The above exercice can be done in five lines.
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/
-- 0041
/-- If `u` tends to `l` then its subsequences tend to `l`. -/
theorem subseq_tendsto_of_tendsto' (h : SeqLimit u l) (hφ : Extraction φ) : SeqLimit (u ∘ φ) l := by
  -- sorry
  intro ε ε_pos
  rcases h ε ε_pos with ⟨N, hN⟩
  use N
  intro n hn
  apply hN
  calc
    N ≤ n := hn
    _ ≤ φ n := id_le_extraction' hφ n
  -- sorry

-- 0042
/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
theorem cluster_limit (hl : SeqLimit u l) (ha : ClusterPoint u a) : a = l := by
  -- sorry
  rcases ha with ⟨φ, φ_extr, lim_u_φ⟩
  have lim_u_φ' : SeqLimit (u ∘ φ) l := subseq_tendsto_of_tendsto' hl φ_extr
  exact unique_limit lim_u_φ lim_u_φ'
  -- sorry

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, SeqLimit u l) → CauchySequence u := by
  -- sorry
  intro hyp
  rcases hyp with ⟨l, hl⟩
  intro ε ε_pos
  rcases hl (ε / 2) (by linarith) with ⟨N, hN⟩
  use N
  intro p q hp hq
  calc
    |u p - u q| = |u p - l + (l - u q)| := by congr; ring
    _ ≤ |u p - l| + |l - u q| := by apply abs_add
    _ = |u p - l| + |u q - l| := by rw [abs_sub_comm (u q) l]
    _ ≤ ε := by linarith [hN p hp, hN q hq]
  -- sorry

/-
In the next exercise, you can reuse
 `near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε`
-/
-- 0044
example (hu : CauchySequence u) (hl : ClusterPoint u l) : SeqLimit u l := by
  -- sorry
  intro ε ε_pos
  rcases hu (ε / 2) (by linarith) with ⟨N, hN⟩
  use N
  have clef : ∃ N' ≥ N, |u N' - l| ≤ ε / 2
  apply near_cluster hl (ε / 2) (by linarith)
  rcases clef with ⟨N', h⟩
  rcases h with ⟨hNN', hN'⟩
  intro n hn
  calc
    |u n - l| = |u n - u N' + (u N' - l)| := by congr; ring
    _ ≤ |u n - u N'| + |u N' - l| := by apply abs_add
    _ ≤ ε := by linarith [hN n N' (by linarith) hNN']
  -- sorry
