import Tutorials.TutoLib

/-
This is the final file in the series. Here we use everything covered
in previous files to prove a couple of famous theorems from
elementary real analysis. Of course they all have more general versions
in mathlib.

As usual, keep in mind the following:

  `abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

  `ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

  `le_max_left p q : p ≤ max p q`

  `le_max_right p q : q ≤ max p q`

as well as a lemma from the previous file:

  `le_of_le_add_all : (∀ ε > 0, y ≤ x + ε) →  y ≤ x`

Let's start with a variation on a known exercise.
-/
-- 0071
theorem le_lim' {x y : ℝ} {u : ℕ → ℝ} (hu : SeqLimit u x) (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x := by
  sorry

/-
Let's now return to the result proved in the `00_` file of this series,
and prove again the sequential characterization of upper bounds (with a slighly
different proof).

For this, and other exercises below, we'll need many things that we proved in previous files,
and a couple of extras.

From the 5th file:

  `limit_const (x : ℝ) : SeqLimit (λ n, x) x`


  `squeeze (lim_u : SeqLimit u l) (lim_w : SeqLimit w l) (hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : SeqLimit v l`

From the 8th:

  `def UpperBound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x`

  `def IsSup (A : set ℝ) (x : ℝ) := UpperBound A x ∧ ∀ y, UpperBound A y → x ≤ y`

  `lt_sup (hx : is_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a `

You can also use:

  `Nat.one_div_pos_of_nat {n : ℕ} : 0 < 1 / (n + 1 : ℝ)`

  `inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε`

and their easy consequences:

  `limit_of_sub_le_inv_succ (h : ∀ n, |u n - x| ≤ 1/(n+1)) : SeqLimit u x`

  `limit_const_add_inv_succ (x : ℝ) : SeqLimit (λ n, x + 1/(n+1)) x`

  `limit_const_sub_inv_succ (x : ℝ) : SeqLimit (λ n, x - 1/(n+1)) x`

as well as:

  `lim_le (hu : SeqLimit u x) (ineg : ∀ n, u n ≤ y) : x ≤ y`

The structure of the proof is offered. It features a new tactic:
`choose` which invokes the axiom of choice (observing the tactic state before and
after using it should be enough to understand everything).
-/
-- 0072
theorem isSup_iff (A : Set ℝ) (x : ℝ) :
    IsSup A x ↔ UpperBound A x ∧ ∃ u : ℕ → ℝ, SeqLimit u x ∧ ∀ n, u n ∈ A := by
  constructor
  · intro h
    constructor
    sorry
    · have : ∀ n : ℕ, ∃ a ∈ A, x - 1 / (n + 1) < a := by
        intro n
        have : 1 / (n + 1 : ℝ) > 0 := Nat.one_div_pos_of_nat
      sorry
      choose u hu using this
  sorry
  · rintro ⟨maj, u, limu, u_in⟩
  sorry

/-- Continuity of a function at a point  -/
def ContinuousAtPt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

variable {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

-- 0073
theorem seq_continuous_of_continuous (hf : ContinuousAtPt f x₀) (hu : SeqLimit u x₀) :
    SeqLimit (f ∘ u) (f x₀) := by
  sorry

-- 0074
example : (∀ u : ℕ → ℝ, SeqLimit u x₀ → SeqLimit (f ∘ u) (f x₀)) → ContinuousAtPt f x₀ := by
  sorry

/-
Recall from the 6th file:


  `def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

  `def ClusterPoint (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ SeqLimit (u ∘ φ) a`


  `id_le_extraction : extraction φ → ∀ n, n ≤ φ n`

and from the 8th file:

  `def TendstoInfinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A`

  `not_seqLimit_of_tendstoInfinity : TendstoInfinity u → ∀ l, ¬ SeqLimit u l`
-/
variable {φ : ℕ → ℕ}

-- 0075
theorem subseq_tendstoInfinity (h : TendstoInfinity u) (hφ : Extraction φ) :
    TendstoInfinity (u ∘ φ) := by
  sorry

-- 0076
theorem squeeze_infinity {u v : ℕ → ℝ} (hu : TendstoInfinity u) (huv : ∀ n, u n ≤ v n) :
    TendstoInfinity v := by
  sorry

/-
We will use segments: `Icc a b := { x | a ≤ x ∧ x ≤ b }`
The notation stands for Interval-closed-closed. Variations exist with
o or i instead of c, where o stands for open and i for infinity.

We will use the following version of Bolzano-Weierstrass

  `bolzano_weierstrass (h : ∀ n, u n ∈ Icc a b) : ∃ c ∈ Icc a b, ClusterPoint u c`

as well as the obvious

  `seqLimit_id : TendstoInfinity (λ n, n)`
-/
open Set

-- 0077
theorem bdd_above_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, ContinuousAtPt f x) :
    ∃ M, ∀ x ∈ Icc a b, f x ≤ M := by
  sorry

/-
In the next exercise, we can use:

  `abs_neg x : |-x| = |x|`
-/
-- 0078
theorem continuous_opposite {f : ℝ → ℝ} {x₀ : ℝ} (h : ContinuousAtPt f x₀) :
    ContinuousAtPt (fun x => -f x) x₀ := by
  sorry

/-
Now let's combine the two exercises above
-/
-- 0079
theorem bdd_below_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, ContinuousAtPt f x) :
    ∃ m, ∀ x ∈ Icc a b, m ≤ f x := by
  sorry

/-
Remember from the 5th file:

 `unique_limit : SeqLimit u l → SeqLimit u l' → l = l'`

and from the 6th one:

  `subseq_tendsto_of_tendsto (h : SeqLimit u l) (hφ : extraction φ) : SeqLimit (u ∘ φ) l`

We now admit the following version of the least upper bound theorem
(that cannot be proved without discussing the construction of real numbers
or admitting another strong theorem).

`sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :`
  `∃ x ∈ Icc a b, is_sup A x`

In the next exercise, it can be useful to prove inclusions of sets of real number.
By definition, `A ⊆ B` means : `∀ x, x ∈ A → x ∈ B`.
Hence one can start a proof of `A ⊆ B` by `intro x x_in`,
which brings `x : ℝ` and `x_in : x ∈ A` in the local context,
and then prove `x ∈ B`.

Note also the use of
  `{x | P x}`
which denotes the set of `x` satisfying predicate `P`.

Hence `x' ∈ { x | P x} ↔ P x'`, by definition.
-/
-- 0080
example {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, ContinuousAtPt f x) :
    ∃ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f x₀ := by
  sorry

-- The following stupid lemma can be used below.
lemma stupid {a b x : ℝ} (h : x ∈ Icc a b) (h' : x ≠ b) : x < b :=
  lt_of_le_of_ne h.right h'

/-
And now the final boss...
-/
def I := (Icc 0 1 : Set ℝ) -- the type ascription makes sure 0 and 1 are real numbers here

-- 0081
example (f : ℝ → ℝ) (hf : ∀ x, ContinuousAtPt f x) (h₀ : f 0 < 0) (h₁ : f 1 > 0) :
    ∃ x₀ ∈ I, f x₀ = 0 := by
  let A := { x | x ∈ I ∧ f x < 0 }
  have ex_x₀ : ∃ x₀ ∈ I, IsSup A x₀ := by
  sorry
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩
  use x₀, x₀_in
  have : f x₀ ≤ 0 := by
  sorry
  have x₀_1 : x₀ < 1 := by
  sorry
  have : f x₀ ≥ 0 := by
    have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1 / (n + 1) ∈ I := by
      have : ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) ≤ 1 - x₀ := by
      sorry
    sorry
    have not_in : ∀ n : ℕ, x₀ + 1 / (n + 1) ∉ A := by
      -- By definition, x ∉ A means ¬ (x ∈ A).
    sorry
    dsimp at not_in
  sorry
  linarith

