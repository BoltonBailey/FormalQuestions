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

/-- Evaluation of `phiBar` in the far field (`D ≤ 0`). -/
theorem phiBar_far {K c : ℝ} {r b : ℕ}
    (h : (r : ℝ) + c * Real.sqrt r - b ≤ 0) : phiBar K c r b = 0 := by
  unfold phiBar; rw [if_pos h]

/-- Evaluation of `phiBar` in the bulk (`D > 0`, below the diagonal `b < r`). -/
theorem phiBar_bulk {K c : ℝ} {r b : ℕ}
    (h1 : ¬ (r : ℝ) + c * Real.sqrt r - b ≤ 0) (h2 : ¬ (r : ℝ) ≤ b) :
    phiBar K c r b = ((r : ℝ) - b) + (c ^ 2 / K) * Real.sqrt r := by
  unfold phiBar; rw [if_neg h1, if_neg h2]

/-- Nonnegativity of the barrier. -/
theorem phiBar_nonneg (r b : ℕ) : 0 ≤ phiBar 91 137 r b := by
  unfold phiBar
  split_ifs with h1 h2
  · exact le_rfl
  · positivity
  · have hbr : (b : ℝ) ≤ r := le_of_lt (not_le.mp h2)
    have hpos : (0 : ℝ) ≤ (137 ^ 2 / 91) * Real.sqrt r := by positivity
    linarith

/-- Bulk case of the supersolution inequality (`b + 1 < r`): collapses to
`√r ≤ √(r+1)`. -/
theorem phiBar_ss_bulk (r b : ℕ) (hbulk : (b : ℝ) + 1 < r) :
    (r + 1) / (r + b + 2) * (phiBar 91 137 r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar 91 137 (r + 1) b - 1)
      ≤ phiBar 91 137 (r + 1) (b + 1) := by
  have hs : Real.sqrt (r : ℝ) ≤ Real.sqrt ((r : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hN : (0 : ℝ) < (r : ℝ) + b + 2 := by positivity
  have hQ : (0 : ℝ) ≤ (137 : ℝ) ^ 2 / 91 := by positivity
  have hC : phiBar 91 137 (r + 1) (b + 1)
      = ((↑(r + 1) : ℝ) - ↑(b + 1)) + ((137 : ℝ) ^ 2 / 91) * Real.sqrt ↑(r + 1) := by
    apply phiBar_bulk
    · refine not_le.mpr ?_; push_cast; nlinarith [Real.sqrt_nonneg ((r : ℝ) + 1)]
    · refine not_le.mpr ?_; push_cast; linarith
  have hA : phiBar 91 137 r (b + 1)
      = ((r : ℝ) - ↑(b + 1)) + ((137 : ℝ) ^ 2 / 91) * Real.sqrt r := by
    apply phiBar_bulk
    · refine not_le.mpr ?_; push_cast; nlinarith [Real.sqrt_nonneg (r : ℝ)]
    · refine not_le.mpr ?_; push_cast; linarith
  have hB : phiBar 91 137 (r + 1) b
      = ((↑(r + 1) : ℝ) - b) + ((137 : ℝ) ^ 2 / 91) * Real.sqrt ↑(r + 1) := by
    apply phiBar_bulk
    · refine not_le.mpr ?_; push_cast; nlinarith [Real.sqrt_nonneg ((r : ℝ) + 1)]
    · refine not_le.mpr ?_; push_cast; linarith
  rw [hC, hA, hB]
  simp only [div_mul_eq_mul_div]
  rw [← add_div, div_le_iff₀ hN]
  push_cast
  nlinarith [mul_nonneg (mul_nonneg hQ (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1))
      (by linarith [hs] : (0 : ℝ) ≤ Real.sqrt ((r : ℝ) + 1) - Real.sqrt r),
    Real.sqrt_nonneg (r : ℝ), Real.sqrt_nonneg ((r : ℝ) + 1), hs]

/-- Far-field case of the supersolution inequality (the point lies in the vanishing
region, `D₁ ≤ 0`): the left side is `≤ 0`. -/
theorem phiBar_ss_far (r b : ℕ)
    (hfar : (↑(r + 1) : ℝ) + 137 * Real.sqrt ↑(r + 1) - ↑(b + 1) ≤ 0) :
    (r + 1) / (r + b + 2) * (phiBar 91 137 r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar 91 137 (r + 1) b - 1)
      ≤ phiBar 91 137 (r + 1) (b + 1) := by
  have hN : (0 : ℝ) < (r : ℝ) + b + 2 := by positivity
  have hs01 : Real.sqrt (r : ℝ) ≤ Real.sqrt ((r : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have ht1 : (1 : ℝ) ≤ Real.sqrt ((r : ℝ) + 1) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (r : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) r])
    rwa [Real.sqrt_one] at h
  have htsq : Real.sqrt ((r : ℝ) + 1) ^ 2 = (r : ℝ) + 1 :=
    Real.sq_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) r])
  have hfar' := hfar
  push_cast at hfar'
  have hC : phiBar 91 137 (r + 1) (b + 1) = 0 := phiBar_far hfar
  have hA0 : (↑r : ℝ) + 137 * Real.sqrt ↑r - ↑(b + 1) ≤ 0 := by push_cast; nlinarith [hs01, hfar']
  have hA : phiBar 91 137 r (b + 1) = 0 := phiBar_far hA0
  have hbge : (r : ℝ) ≤ b := by nlinarith [ht1, hfar']
  have hkey : (↑b + 1 : ℝ) * phiBar 91 137 (r + 1) b ≤ ↑b - ↑r := by
    by_cases hBfar : (↑(r + 1) : ℝ) + 137 * Real.sqrt ↑(r + 1) - ↑b ≤ 0
    · rw [phiBar_far hBfar, mul_zero]; linarith [hbge]
    · have hlay : (↑(r + 1) : ℝ) ≤ ↑b := by push_cast; nlinarith [ht1, hfar']
      have hBval : phiBar 91 137 (r + 1) b
          = (↑(r + 1) + 137 * Real.sqrt ↑(r + 1) - ↑b) ^ 2 / (91 * Real.sqrt ↑(r + 1)) := by
        unfold phiBar; rw [if_neg hBfar, if_pos hlay]
      have hD0 : (0 : ℝ) < ↑r + 1 + 137 * Real.sqrt ((r : ℝ) + 1) - ↑b := by
        have := not_le.mp hBfar; push_cast at this; linarith
      rw [hBval]; push_cast
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 91 * Real.sqrt ((r : ℝ) + 1))]
      have hd1 : ↑r + 1 + 137 * Real.sqrt ((r : ℝ) + 1) - ↑b ≤ 1 := by linarith [hfar']
      have hdsq : (↑r + 1 + 137 * Real.sqrt ((r : ℝ) + 1) - ↑b) ^ 2 ≤ 1 := by
        nlinarith [hD0, hd1]
      have hb1 : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
      have hstep1 : ((b : ℝ) + 1) * (↑r + 1 + 137 * Real.sqrt ((r : ℝ) + 1) - ↑b) ^ 2 ≤ (b : ℝ) + 1 := by
        nlinarith [mul_nonneg hb1 (by linarith [hdsq] :
          (0 : ℝ) ≤ 1 - (↑r + 1 + 137 * Real.sqrt ((r : ℝ) + 1) - ↑b) ^ 2)]
      have hbr2 : (137 : ℝ) * Real.sqrt ((r : ℝ) + 1) ≤ ↑b - ↑r := by linarith [hd1]
      have hfin : (b : ℝ) + 1 ≤ (↑b - ↑r) * (91 * Real.sqrt ((r : ℝ) + 1)) := by
        nlinarith [htsq, ht1, hD0, hbr2,
          mul_nonneg (sub_nonneg.mpr hbr2) (by positivity : (0 : ℝ) ≤ 91 * Real.sqrt ((r : ℝ) + 1)),
          mul_nonneg (by linarith [ht1] : (0 : ℝ) ≤ 12466 * Real.sqrt ((r : ℝ) + 1) - 137)
            (le_trans zero_le_one ht1)]
      linarith [hstep1, hfin]
  rw [hC, hA]
  simp only [div_mul_eq_mul_div, zero_add]
  rw [← add_div, div_le_iff₀ hN]
  nlinarith [hkey]

/-- Hard (tight) case of the supersolution inequality: the layer `r ≤ b` together
with the diagonal seam `b = r - 1`, where the margin is `O(√r)` but the bound is
asymptotically tight. This is the remaining analytic core. -/
theorem phiBar_ss_hard (r b : ℕ)
    (hnear : ¬ (↑(r + 1) : ℝ) + 137 * Real.sqrt ↑(r + 1) - ↑(b + 1) ≤ 0)
    (hrb : (r : ℝ) ≤ (b : ℝ) + 1) :
    (r + 1) / (r + b + 2) * (phiBar 91 137 r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar 91 137 (r + 1) b - 1)
      ≤ phiBar 91 137 (r + 1) (b + 1) := by
  sorry

/-- The supersolution inequality (`ss` field) for the real-`√` quadratic barrier with
`c = 137`, `K = 91`. The far-field and bulk cases are proved directly; the tight
layer/seam case is `phiBar_ss_hard`. -/
theorem phiBar_ss (r b : ℕ) :
    (r + 1) / (r + b + 2) * (phiBar 91 137 r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar 91 137 (r + 1) b - 1)
      ≤ phiBar 91 137 (r + 1) (b + 1) := by
  by_cases hfar : (↑(r + 1) : ℝ) + 137 * Real.sqrt ↑(r + 1) - ↑(b + 1) ≤ 0
  · exact phiBar_ss_far r b hfar
  · by_cases hbulk : (b : ℝ) + 1 < r
    · exact phiBar_ss_bulk r b hbulk
    · exact phiBar_ss_hard r b hfar (by linarith [not_lt.mp hbulk])

/-- The real-`√` quadratic barrier with `c = 137`, `K = 91` is a supersolution
(blueprint `prop:comparison` would then give `e r b = 0` on the region).

The structural fields (nonnegativity, boundary data) are proved here; the `ss`
field is `phiBar_ss`. -/
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
  case ss => exact phiBar_ss

/-- **Question** would like to prove that given r > 137, and b > r + 137 √ r (real
square root), then e(r, b) = 0.
-/
theorem question (r b : ℕ) (hr : r > 137) (hb : (b : ℝ) > r + 137 * Real.sqrt r) :
    e r b = 0 := by
  sorry
