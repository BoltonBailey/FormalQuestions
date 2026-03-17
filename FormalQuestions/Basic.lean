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
For a deck with n red cards > m black cards, the expected payoff is at least n - m.
Proof by induction.
-/
theorem e_pos_of_diff (n m : ℕ) (hn : n > m) : e n m ≥ n - m := by
  sorry

/--
For one deck with n red cards and m black cards, and another deck with m red cards and n black cards,
the total expected payoff is positive.
-/
theorem pos_e_swap_add (n m : ℕ) (hn : 0 < n + m) : 0 < e n m + e m n := by
  sorry

/--
For a deck with a positive equal amount fo cards of each color, the expected payoff is positive.
-/
theorem e_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < e n n := by
  sorry


/-- **Question** would like to prove that given r > 137, and b > r + 137 √ r, then e(r, b) = 0.
-/
theorem question (r b : ℕ) (hr : r > 137) (hb : b > r + 137 * Nat.sqrt r) : e r b = 0 := by
  sorry
