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

/-- Comparison principle (blueprint `prop:comparison`): any supersolution `φ`
dominates the equity `e`. -/
theorem e_le_of_supersolution (φ : ℕ → ℕ → ℚ)
    (hnonneg : ∀ r b, 0 ≤ φ r b)
    (_hzero : ∀ b, φ 0 b = 0)
    (hbase : ∀ r : ℕ, (r : ℚ) ≤ φ r 0)
    (hss : ∀ r b, (r + 1) / (r + b + 2) * (φ r (b + 1) + 1)
        + (b + 1) / (r + b + 2) * (φ (r + 1) b - 1) ≤ φ (r + 1) (b + 1)) :
    ∀ r b, e r b ≤ φ r b := by
  have H : ∀ n r b, r + b = n → e r b ≤ φ r b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro r b hrb
      cases r with
      | zero => simpa [e] using hnonneg 0 b
      | succ r =>
        cases b with
        | zero => simpa [e] using hbase (r + 1)
        | succ b =>
          rw [e_succ_succ]
          apply max_le (hnonneg _ _)
          have h1 : e r (b + 1) ≤ φ r (b + 1) := ih (r + (b + 1)) (by omega) r (b + 1) rfl
          have h2 : e (r + 1) b ≤ φ (r + 1) b := ih ((r + 1) + b) (by omega) (r + 1) b rfl
          have hc1 : (0 : ℚ) ≤ (r + 1) / (r + b + 2) := by positivity
          have hc2 : (0 : ℚ) ≤ (b + 1) / (r + b + 2) := by positivity
          have f1 : (r + 1) / (r + b + 2) * (e r (b + 1) + 1)
              ≤ (r + 1) / (r + b + 2) * (φ r (b + 1) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hc1
          have f2 : (b + 1) / (r + b + 2) * (e (r + 1) b - 1)
              ≤ (b + 1) / (r + b + 2) * (φ (r + 1) b - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hc2
          linarith [hss r b]
  intro r b
  exact H (r + b) r b rfl

/-- **Question** would like to prove that given r > 137, and b > r + 137 √ r, then e(r, b) = 0.
-/
theorem question (r b : ℕ) (hr : r > 137) (hb : b > r + 137 * Nat.sqrt r) : e r b = 0 := by
  sorry
