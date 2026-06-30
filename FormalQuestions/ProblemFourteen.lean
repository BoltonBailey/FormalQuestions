import Mathlib

/-!

# Problem 14

[Reference](https://www.gwern.net/Problem-14)

This file includes **Question**s about the problem of calculating
the equity of a game with red and black cards, as described in the reference:

> You have 52 playing cards (26 red, 26 black). You draw cards one by one.
> A red card pays you a dollar. A black one fines you a dollar. You can stop any time you want.
> Cards are not returned to the deck after being drawn.
> What is the optimal stopping rule in terms of maximizing expected payoff?
> Also, what is the expected payoff following this optimal rule?

-/


/--
We define $e(r, b)$ to be the equity with $r$ red cards and $b$ black cards.
We can view this as inductively defined as follows:

$$ e(r, 0) = r $$
$$ e(0, b) = 0 $$
$$ e(r+1, b+1) =
 \max \left(
    0,
    \frac{r+1}{r + b + 2}\left( e(r, b+1) + 1 \right)
    + \frac{b+1}{r + b + 2} \left(e(r+1, b) - 1\right) \right) $$
-/
def e : ℕ → ℕ → ℚ
| 0, _ => 0
| r, 0 => r
| r+1, b+1 => max 0 ((r+1)/(r+b+2) * (e r (b+1) + 1) + (b+1)/(r+b+2) * (e (r+1) b - 1))

-- The first few diagonals of the table of values of `e` are as follows, consistent with the post:

#eval e 1 1 -- 1 / 2
#eval e 2 2 -- 2 / 3
#eval e 3 3 -- 17 / 20


/--
For a deck with n red cards and m black cards, the expected payoff is at least n - m.
-/
theorem sub_le_e (n m : ℕ) : n - m ≤ e n m := by
  induction n generalizing m with
  | zero => simp [e]
  | succ n ih =>
    induction m with
    | zero => simp [e]
    | succ m ihm =>
      simp only [e]
      apply le_trans _ (le_max_right 0 _)
      have hn := ih (m + 1)
      have hm := ihm
      push_cast at *
      have h1 : (0 : ℚ) ≤ (n + 1) / (n + m + 2) := by positivity
      have h2 : (0 : ℚ) ≤ (m + 1) / (n + m + 2) := by positivity
      have key1 : e n (m + 1) + 1 ≥ (n : ℚ) - m := by linarith
      have key2 : e (n + 1) m - 1 ≥ (n : ℚ) - m := by linarith
      have hsum : (n + 1 : ℚ) / (n + m + 2) + (m + 1) / (n + m + 2) = 1 := by
        field_simp; ring
      calc (n : ℚ) + 1 - (m + 1)
          = (n - m) * ((n + 1) / (n + m + 2) + (m + 1) / (n + m + 2)) := by rw [hsum]; ring
        _ = (n + 1) / (n + m + 2) * (n - m) + (m + 1) / (n + m + 2) * (n - m) := by ring
        _ ≤ (n + 1) / (n + m + 2) * (e n (m + 1) + 1) +
            (m + 1) / (n + m + 2) * (e (n + 1) m - 1) := by
            apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ ‹_› <;> linarith

/--
For one deck with n red cards and m black cards, and another deck with m red cards and n black cards,
the total expected payoff is positive.
-/
theorem zero_le_e (n m : ℕ) : 0 ≤ e n m := by
  induction n generalizing m with
  | zero => simp [e]
  | succ n ih =>
    induction m with
    | zero => simp [e]; positivity
    | succ m ihm =>
      simp only [e]
      linarith [le_max_left (α := ℚ) 0
        (((↑n + 1) / (↑n + ↑m + 2)) * (e n (m + 1) + 1) +
         ((↑m + 1) / (↑n + ↑m + 2)) * (e (n + 1) m - 1))]


/--
For a deck with a positive equal amount of cards of each color, the expected payoff is strictly positive.
-/
theorem e_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < e n n := by
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ k =>
    simp only [e]
    apply lt_of_lt_of_le _ (le_max_right 0 _)
    have h1 : (0 : ℚ) ≤ e k (k + 1) := zero_le_e k (k + 1)
    have h2 : (1 : ℚ) ≤ e (k + 1) k := by
      have := sub_le_e (k + 1) k; push_cast at this; linarith
    have hcoeff : (k + 1 : ℚ) / (↑k + ↑k + 2) = 1 / 2 := by field_simp; ring
    rw [hcoeff]; nlinarith

/--
For one deck with n red cards and m black cards, and another deck with m red cards and n black cards,
the total expected payoff is positive.
-/
theorem pos_e_swap_add (n m : ℕ) (hn : 0 < n + m) : 0 < e n m + e m n := by
  rcases lt_trichotomy n m with h | rfl | h
  case inl =>
    have hcast : (n : ℚ) + 1 ≤ m := by exact_mod_cast h
    linarith [sub_le_e m n, zero_le_e n m]
  case inr.inl =>
    linarith [e_pos_of_pos n (by omega)]
  case inr.inr =>
    have hcast : (m : ℚ) + 1 ≤ n := by exact_mod_cast h
    linarith [sub_le_e n m, zero_le_e m n]


/-- Unfolded recursion (blueprint `lem:recursion`): for `r, b ≥ 1` (here in the
`r+1, b+1` form), `e` satisfies the optimality equation with `N = r + b + 2`. -/
theorem e_succ_succ (r b : ℕ) :
    e (r + 1) (b + 1) =
      max 0 ((r + 1) / (r + b + 2) * (e r (b + 1) + 1)
        + (b + 1) / (r + b + 2) * (e (r + 1) b - 1)) := by
  simp only [e]

/-- Reduction (blueprint `lem:reduction`): if the "continue" value is `≤ 0`, the
equity is exactly `0`. -/
theorem e_eq_zero_of_inner_nonpos (r b : ℕ)
    (h : (r + 1) / (r + b + 2) * (e r (b + 1) + 1)
        + (b + 1) / (r + b + 2) * (e (r + 1) b - 1) ≤ 0) :
    e (r + 1) (b + 1) = 0 := by
  rw [e_succ_succ]
  exact max_eq_left h

/-- A supersolution (blueprint `def:super`): a nonnegative real-valued function
dominating the boundary data and satisfying the supersolution inequality, here
written in the equivalent "continue value" form
`φ(r,b) ≥ (r/N)(φ(r-1,b)+1) + (b/N)(φ(r,b-1)-1)`. Real-valued so that barriers built
from `Real.sqrt` are admissible. -/
structure IsSupersolution (φ : ℕ → ℕ → ℝ) : Prop where
  nonneg : ∀ r b, 0 ≤ φ r b
  zero_left : ∀ b, φ 0 b = 0
  base : ∀ r : ℕ, (r : ℝ) ≤ φ r 0
  ss : ∀ r b : ℕ,
    (r + 1) / (r + b + 2) * (φ r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (φ (r + 1) b - 1) ≤ φ (r + 1) (b + 1)

/-- Comparison principle (blueprint `prop:comparison`): any supersolution `φ`
dominates the equity `e` (compared after casting `e` into `ℝ`). -/
theorem e_le_of_supersolution {φ : ℕ → ℕ → ℝ} (hφ : IsSupersolution φ) :
    ∀ r b, (e r b : ℝ) ≤ φ r b := by
  have H : ∀ n r b, r + b = n → (e r b : ℝ) ≤ φ r b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro r b hrb
      cases r with
      | zero => simpa [e] using hφ.nonneg 0 b
      | succ r =>
        cases b with
        | zero => simpa [e] using hφ.base (r + 1)
        | succ b =>
          rw [e_succ_succ, Rat.cast_max, Rat.cast_zero]
          push_cast
          apply max_le (hφ.nonneg _ _)
          have h1 : (e r (b + 1) : ℝ) ≤ φ r (b + 1) :=
            ih (r + (b + 1)) (by omega) r (b + 1) rfl
          have h2 : (e (r + 1) b : ℝ) ≤ φ (r + 1) b :=
            ih ((r + 1) + b) (by omega) (r + 1) b rfl
          have hc1 : (0 : ℝ) ≤ (r + 1) / (r + b + 2) := by positivity
          have hc2 : (0 : ℝ) ≤ (b + 1) / (r + b + 2) := by positivity
          have f1 : (r + 1) / (r + b + 2) * ((e r (b + 1) : ℝ) + 1)
              ≤ (r + 1) / (r + b + 2) * (φ r (b + 1) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hc1
          have f2 : (b + 1) / (r + b + 2) * ((e (r + 1) b : ℝ) - 1)
              ≤ (b + 1) / (r + b + 2) * (φ (r + 1) b - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hc2
          linarith [hφ.ss r b]
  intro r b
  exact H (r + b) r b rfl

/-- The real-`√` quadratic barrier (blueprint, "The barrier"): a width-`c√r` layer
with normalisation `K`, threshold constant `c`, glued to `0` above the strip and to
the deterministic value `(r-b) + (c²/K)√r` below the diagonal. -/
noncomputable def phiBar (K c : ℝ) (r b : ℕ) : ℝ :=
  if (r : ℝ) + c * Real.sqrt r - b ≤ 0 then 0
  else if (r : ℝ) ≤ b then ((r : ℝ) + c * Real.sqrt r - b) ^ 2 / (K * Real.sqrt r)
  else ((r : ℝ) - b) + (c ^ 2 / K) * Real.sqrt r

/-- The real-`√` quadratic barrier with `c = 137`, `K = 91` is a supersolution
(blueprint `prop:comparison` would then give `e r b = 0` on the region).

The structural fields (nonnegativity, boundary data) are proved here. The `ss`
field - the supersolution inequality - reduces to the scalar inequality `P(x) ≥ 0`
with `P(x) = (3/2K) x² - (c/K + 1) x + (c - 2/K)` plus a bounded `O(1) + O(1/√r)`
error; that analytic core is the single remaining gap and is left as `sorry`. -/
theorem phiBar_isSupersolution : IsSupersolution (phiBar 91 137) := by
  refine ⟨?nonneg, ?zero_left, ?base, ?ss⟩
  case nonneg =>
    intro r b
    unfold phiBar
    split_ifs with h1 h2
    · exact le_rfl
    · positivity
    · have hbr : (b : ℝ) ≤ r := le_of_lt (not_le.mp h2)
      have hpos : (0 : ℝ) ≤ (137 ^ 2 / 91) * Real.sqrt r := by positivity
      linarith
  case zero_left =>
    intro b
    have hD : (↑(0 : ℕ) : ℝ) + 137 * Real.sqrt ↑(0 : ℕ) - (b : ℝ) ≤ 0 := by
      simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add, zero_sub,
        Left.neg_nonpos_iff]
      positivity
    unfold phiBar
    rw [if_pos hD]
  case base =>
    intro r
    unfold phiBar
    split_ifs with h1 h2
    · -- threshold reached at b = 0 forces r = 0, so the bound is 0 ≤ 0
      have hs : Real.sqrt r ≥ 0 := Real.sqrt_nonneg _
      have : (r : ℝ) ≤ 0 := by
        have : (r : ℝ) + 137 * Real.sqrt r ≤ 0 := by simpa using h1
        nlinarith
      have hr0 : (r : ℝ) = 0 := le_antisymm this (Nat.cast_nonneg r)
      simp [hr0]
    · -- b = 0 and r ≤ 0 ⇒ r = 0; layer value is 0 ≥ 0 = ↑r
      have hr0 : (r : ℝ) = 0 := le_antisymm (by simpa using h2) (Nat.cast_nonneg r)
      simp [hr0]
    · -- bulk piece: ↑r ≤ (↑r - 0) + (c²/K)√r
      have hpos : (0 : ℝ) ≤ (137 ^ 2 / 91) * Real.sqrt r := by positivity
      simp only [Nat.cast_zero, sub_zero]
      linarith
  case ss =>
    intro r b
    -- Reduces to `P(x) ≥ 0` (blueprint, "The correct scalar inequality") plus a
    -- bounded `O(1) + O(1/√r)` error. Analytic core; not yet formalised.
    sorry

/-- **Question** would like to prove that given r > 137, and b > r + 137 √ r (real
square root), then e(r, b) = 0.
-/
theorem question (r b : ℕ) (hr : r > 137) (hb : (b : ℝ) > r + 137 * Real.sqrt r) :
    e r b = 0 := by
  sorry
