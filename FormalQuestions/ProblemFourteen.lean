import Mathlib
import SOS

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
For one deck with n red cards and m black cards,
and another deck with m red cards and n black cards,
the total expected payoff is positive.
-/
theorem zero_le_e (n m : ℕ) : 0 ≤ e n m := by
  induction n generalizing m with
  | zero => simp [e]
  | succ n ih =>
    induction m with
    | zero => simp only [e]; positivity
    | succ m ihm =>
      simp only [e]
      exact le_max_left _ _


/--
For a deck with a positive equal amount of cards of each color,
the expected payoff is strictly positive.
-/
theorem e_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < e n n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [e]
  apply lt_of_lt_of_le _ (le_max_right 0 _)
  have h1 : (0 : ℚ) ≤ e k (k + 1) := zero_le_e k (k + 1)
  have h2 : (1 : ℚ) ≤ e (k + 1) k := by
    have := sub_le_e (k + 1) k; push_cast at this; linarith
  have hcoeff : (k + 1 : ℚ) / (↑k + ↑k + 2) = 1 / 2 := by field_simp; ring
  rw [hcoeff]; nlinarith

/--
For one deck with n red cards and m black cards,
and another deck with m red cards and n black cards,
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
    e (r + 1) (b + 1) = 0 :=
  (e_succ_succ r b).trans (max_eq_left h)

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

/-- Evaluation of `phiBar` in the layer (`D > 0`, above the diagonal `r ≤ b`). -/
theorem phiBar_layer {K c : ℝ} {r b : ℕ}
    (h1 : ¬ (r : ℝ) + c * Real.sqrt r - b ≤ 0) (h2 : (r : ℝ) ≤ b) :
    phiBar K c r b = ((r : ℝ) + c * Real.sqrt r - b) ^ 2 / (K * Real.sqrt r) := by
  unfold phiBar; rw [if_neg h1, if_pos h2]

/-! ## The general supersolution theorem

`phiBar K c` is a supersolution (hence `e r b = 0` on `{b ≥ r + c·√r}`) provided
four explicit polynomial side-conditions on `(K,c)` hold together with the
parameter-dependent layer inequality `hlayer`:

* `0 < K`                                        – positivity of the barrier;
* `K ≤ 2*c`                                      – the bulk ≤ layer-form bound;
* `1 ≤ c*(K-1)`                                  – the far-field bound;
* `K² - 8·K·c + 2·K + 4·c² + 16·c + 13 ≤ 0`      – the `r = 0` base case
  (which already forces `c ≥ 1 + √2`).

The genuinely `(K,c)`-dependent input `hlayer` is the square-root-cleared
supersolution defect in the diffusive layer; everything else is generic. -/

open scoped Real

/-- Generic universal upper bound by the layer formula (blueprint "layer form"),
for any `0 < K ≤ 2*c`. In the bulk `b < R` the cleared difference is
`(R-b)·((R-b)+(2c-K)√R) ≥ 0`. -/
theorem phiBar_le_layerform_of {K c : ℝ} (hK0 : 0 < K) (hK2c : K ≤ 2 * c) (R b : ℕ)
    (hR : 1 ≤ R) :
    phiBar K c R b ≤ ((R : ℝ) + c * Real.sqrt R - b) ^ 2 / (K * Real.sqrt R) := by
  have hsr : 0 < Real.sqrt R :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.lt_of_lt_of_le one_pos hR)
  have hsq : Real.sqrt R ^ 2 = (R : ℝ) := Real.sq_sqrt (by positivity)
  have hKne : K ≠ 0 := ne_of_gt hK0
  have hsrne : Real.sqrt (R:ℝ) ≠ 0 := ne_of_gt hsr
  unfold phiBar
  split_ifs with h1 h2
  · positivity
  · exact le_refl _
  · have hb : (b : ℝ) < R := not_le.mp h2
    rw [← sub_nonneg,
      show ((R:ℝ) + c * Real.sqrt R - b) ^ 2 / (K * Real.sqrt R)
            - ((R:ℝ) - b + c ^ 2 / K * Real.sqrt R)
          = ((R:ℝ) - b) * (((R:ℝ) - b) + (2*c - K) * Real.sqrt R) / (K * Real.sqrt R) from by
        field_simp; ring]
    apply div_nonneg _ (by positivity)
    have h2cK : (0:ℝ) ≤ 2*c - K := by linarith
    nlinarith [mul_nonneg h2cK (Real.sqrt_nonneg (R:ℝ)), sub_pos.mpr hb, Real.sqrt_nonneg (R:ℝ)]

/-- Bulk case of the supersolution inequality (`b + 1 < r`), any `0 < K`. -/
theorem phiBar_ss_bulk_of {K c : ℝ} (hK0 : 0 < K) (hc0 : 0 ≤ c) (r b : ℕ)
    (hbulk : (b : ℝ) + 1 < r) :
    (r + 1) / (r + b + 2) * (phiBar K c r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar K c (r + 1) b - 1)
      ≤ phiBar K c (r + 1) (b + 1) := by
  have hs : Real.sqrt (r : ℝ) ≤ Real.sqrt ((r : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hN : (0 : ℝ) < (r : ℝ) + b + 2 := by positivity
  have hQ : (0 : ℝ) ≤ c ^ 2 / K := by positivity
  have hC : phiBar K c (r + 1) (b + 1)
      = ((↑(r + 1) : ℝ) - ↑(b + 1)) + (c ^ 2 / K) * Real.sqrt ↑(r + 1) := by
    apply phiBar_bulk
    · refine not_le.mpr ?_; push_cast
      nlinarith [mul_nonneg hc0 (Real.sqrt_nonneg ((r : ℝ) + 1))]
    · refine not_le.mpr ?_; push_cast; linarith
  have hA : phiBar K c r (b + 1)
      = ((r : ℝ) - ↑(b + 1)) + (c ^ 2 / K) * Real.sqrt r := by
    apply phiBar_bulk
    · refine not_le.mpr ?_; push_cast; nlinarith [mul_nonneg hc0 (Real.sqrt_nonneg (r : ℝ))]
    · refine not_le.mpr ?_; push_cast; linarith
  have hB : phiBar K c (r + 1) b
      = ((↑(r + 1) : ℝ) - b) + (c ^ 2 / K) * Real.sqrt ↑(r + 1) := by
    apply phiBar_bulk
    · refine not_le.mpr ?_; push_cast
      nlinarith [mul_nonneg hc0 (Real.sqrt_nonneg ((r : ℝ) + 1))]
    · refine not_le.mpr ?_; push_cast; linarith
  rw [hC, hA, hB]
  simp only [div_mul_eq_mul_div]
  rw [← add_div, div_le_iff₀ hN]
  push_cast
  have hKne : K ≠ 0 := ne_of_gt hK0
  have hnn : (0:ℝ) ≤ c ^ 2 * ((r:ℝ) + 1) * (Real.sqrt ((r:ℝ) + 1) - Real.sqrt (r:ℝ)) / K :=
    div_nonneg (mul_nonneg (by positivity) (by linarith [hs])) (le_of_lt hK0)
  have hid : ((r:ℝ) + 1 - ((b:ℝ) + 1) + c ^ 2 * Real.sqrt ((r:ℝ) + 1) / K) * ((r:ℝ) + (b:ℝ) + 2)
      - (((r:ℝ) + 1) * ((r:ℝ) - ((b:ℝ) + 1) + c ^ 2 * Real.sqrt (r:ℝ) / K + 1)
        + ((b:ℝ) + 1) * ((r:ℝ) + 1 - (b:ℝ) + c ^ 2 * Real.sqrt ((r:ℝ) + 1) / K - 1))
      = c ^ 2 * ((r:ℝ) + 1) * (Real.sqrt ((r:ℝ) + 1) - Real.sqrt (r:ℝ)) / K := by
    field_simp
    ring
  nlinarith [hnn, hid]

/-- Far-field case of the supersolution inequality, for `1 ≤ K`, `1 ≤ c`,
`1 ≤ c*(K-1)`. The left side is `≤ 0`. -/
theorem phiBar_ss_far_of {K c : ℝ} (hK1 : 1 ≤ K) (hc1 : 1 ≤ c) (hcK1 : 1 ≤ c * (K - 1))
    (r b : ℕ)
    (hfar : (↑(r + 1) : ℝ) + c * Real.sqrt ↑(r + 1) - ↑(b + 1) ≤ 0) :
    (r + 1) / (r + b + 2) * (phiBar K c r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar K c (r + 1) b - 1)
      ≤ phiBar K c (r + 1) (b + 1) := by
  have hN : (0 : ℝ) < (r : ℝ) + b + 2 := by positivity
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hs01 : Real.sqrt (r : ℝ) ≤ Real.sqrt ((r : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have ht1 : (1 : ℝ) ≤ Real.sqrt ((r : ℝ) + 1) := by
    have h := Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ (r : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) r])
    rwa [Real.sqrt_one] at h
  have htsq : Real.sqrt ((r : ℝ) + 1) ^ 2 = (r : ℝ) + 1 :=
    Real.sq_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) r])
  have hfar' := hfar
  push_cast at hfar'
  have hC : phiBar K c (r + 1) (b + 1) = 0 := phiBar_far hfar
  have hA0 : (↑r : ℝ) + c * Real.sqrt ↑r - ↑(b + 1) ≤ 0 := by
    push_cast
    nlinarith [hfar',
      mul_nonneg hc0 (by linarith [hs01] : (0:ℝ) ≤ Real.sqrt ((r:ℝ)+1) - Real.sqrt r)]
  have hA : phiBar K c r (b + 1) = 0 := phiBar_far hA0
  have hbge : (r : ℝ) ≤ b := by
    nlinarith [hfar', mul_nonneg hc0 (Real.sqrt_nonneg ((r:ℝ)+1))]
  have hkey : (↑b + 1 : ℝ) * phiBar K c (r + 1) b ≤ ↑b - ↑r := by
    by_cases hBfar : (↑(r + 1) : ℝ) + c * Real.sqrt ↑(r + 1) - ↑b ≤ 0
    · rw [phiBar_far hBfar, mul_zero]; linarith [hbge]
    · have hlay : (↑(r + 1) : ℝ) ≤ ↑b := by
        push_cast
        nlinarith [hfar', mul_nonneg hc0 (by linarith [ht1] : (0:ℝ) ≤ Real.sqrt ((r:ℝ)+1) - 1)]
      have hBval : phiBar K c (r + 1) b
          = (↑(r + 1) + c * Real.sqrt ↑(r + 1) - ↑b) ^ 2 / (K * Real.sqrt ↑(r + 1)) := by
        unfold phiBar; rw [if_neg hBfar, if_pos hlay]
      have hD0 : (0 : ℝ) < ↑r + 1 + c * Real.sqrt ((r : ℝ) + 1) - ↑b := by
        have := not_le.mp hBfar; push_cast at this; linarith
      rw [hBval]; push_cast
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < K * Real.sqrt ((r : ℝ) + 1))]
      -- Now purely over the formulas (with `t = √(r+1)`, `htsq : t² = r+1`): the goal
      -- `(b+1)·D² ≤ (b-r)·K·t` follows in one shot from the Positivstellensatz pieces
      -- `(b-r)·K·t - (b+1) = P₁ + P₂ + P₃ ≥ 0` and `(b+1)·(1-D²) ≥ 0`.
      have hd1 : ↑r + 1 + c * Real.sqrt ((r : ℝ) + 1) - ↑b ≤ 1 := by linarith [hfar']
      have hbr2 : c * Real.sqrt ((r : ℝ) + 1) ≤ ↑b - ↑r := by linarith [hd1]
      -- TODO: if I put `sos` here Lean hangs. Investigate.
      nlinarith [htsq, ht1, hc0,
        mul_nonneg (sub_nonneg.mpr hbr2)
          (show (0:ℝ) ≤ K * Real.sqrt ((r:ℝ) + 1) - 1 by nlinarith [ht1, hK1]),
        mul_nonneg (sq_nonneg (Real.sqrt ((r:ℝ) + 1))) (sub_nonneg.mpr hcK1),
        mul_nonneg (mul_nonneg hc0 (Real.sqrt_nonneg ((r:ℝ) + 1)))
          (show (0:ℝ) ≤ Real.sqrt ((r:ℝ) + 1) - 1 by linarith [ht1]),
        mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (b:ℝ) + 1 by positivity)
            (show (0:ℝ) ≤ 1 - (↑r + 1 + c * Real.sqrt ((r:ℝ) + 1) - ↑b) by linarith [hd1]))
          (show (0:ℝ) ≤ 1 + (↑r + 1 + c * Real.sqrt ((r:ℝ) + 1) - ↑b) by linarith [hD0])]
  rw [hC, hA]
  simp only [div_mul_eq_mul_div, zero_add]
  rw [← add_div, div_le_iff₀ hN]
  nlinarith [hkey]

/-- Divided form of the all-layer supersolution inequality, generic in `(K,c)`.
The genuinely parameter-dependent content is the hypothesis `hcore`, namely the
square-root-cleared layer defect `0 ≤ F(s,t,bb-s²)`. -/
theorem layer_div_ineq_of {K c s t rr bb : ℝ} (hK0 : 0 < K) (hs : 1 ≤ s) (ht0 : 0 < t)
    (hrr : rr = s ^ 2) (hN : 0 < rr + bb + 2)
    (hcore : 0 ≤ s * (c * t - (bb - s ^ 2)) ^ 2 * (2 * s ^ 2 + (bb - s ^ 2) + 2)
        - (s ^ 2 + 1) * (t * (c * s - (bb - s ^ 2) - 1) ^ 2 + K * s * t)
        - (s ^ 2 + (bb - s ^ 2) + 1) * (s * (c * t - (bb - s ^ 2) + 1) ^ 2 - K * s * t)) :
    (rr + 1) / (rr + bb + 2) * ((rr + c * s - (bb + 1)) ^ 2 / (K * s) + 1)
      + (bb + 1) / (rr + bb + 2) * (((rr + 1) + c * t - bb) ^ 2 / (K * t) - 1)
      ≤ ((rr + 1) + c * t - (bb + 1)) ^ 2 / (K * t) := by
  have hs0 : 0 < s := by linarith
  have hN' : (0:ℝ) < s ^ 2 + bb + 2 := by rw [hrr] at hN; exact hN
  have hKne : K ≠ 0 := ne_of_gt hK0
  have hsne : s ≠ 0 := ne_of_gt hs0
  have htne : t ≠ 0 := ne_of_gt ht0
  have hNne : s ^ 2 + bb + 2 ≠ 0 := ne_of_gt hN'
  have hden : 0 < K * s * t * (s ^ 2 + bb + 2) :=
    mul_pos (mul_pos (mul_pos hK0 hs0) ht0) hN'
  refine sub_nonneg.mp ?_
  have hFdiv : ((rr + 1) + c * t - (bb + 1)) ^ 2 / (K * t)
      - ((rr + 1) / (rr + bb + 2) * ((rr + c * s - (bb + 1)) ^ 2 / (K * s) + 1)
        + (bb + 1) / (rr + bb + 2) * (((rr + 1) + c * t - bb) ^ 2 / (K * t) - 1))
      = (s * (c * t - (bb - s ^ 2)) ^ 2 * (2 * s ^ 2 + (bb - s ^ 2) + 2)
        - (s ^ 2 + 1) * (t * (c * s - (bb - s ^ 2) - 1) ^ 2 + K * s * t)
        - (s ^ 2 + (bb - s ^ 2) + 1) * (s * (c * t - (bb - s ^ 2) + 1) ^ 2 - K * s * t))
        / (K * s * t * (s ^ 2 + bb + 2)) := by
    rw [hrr]; field_simp; ring
  rw [hFdiv]
  exact div_nonneg hcore (le_of_lt hden)

/-- Hard (tight) case of the supersolution inequality, generic in `(K,c)`: the
layer `r ≤ b` together with the diagonal seam `b = r-1`. Needs the `r=0` base
constraint `hr0` and the layer inequality `hlayer`. -/
theorem phiBar_ss_hard_of {K c : ℝ} (hK1 : 1 ≤ K) (hc1 : 1 ≤ c) (hK2c : K ≤ 2 * c)
    (hr0 : K ^ 2 - 8 * K * c + 2 * K + 4 * c ^ 2 + 16 * c + 13 ≤ 0)
    (hlayer : ∀ s t w : ℝ, 1 ≤ s → 0 ≤ w → 0 ≤ t → t ^ 2 = s ^ 2 + 1 →
        0 ≤ s * (c * t - w) ^ 2 * (2 * s ^ 2 + w + 2)
          - (s ^ 2 + 1) * (t * (c * s - w - 1) ^ 2 + K * s * t)
          - (s ^ 2 + w + 1) * (s * (c * t - w + 1) ^ 2 - K * s * t))
    (r b : ℕ)
    (hnear : ¬ (↑(r + 1) : ℝ) + c * Real.sqrt ↑(r + 1) - ↑(b + 1) ≤ 0)
    (hrb : (r : ℝ) ≤ (b : ℝ) + 1) :
    (r + 1) / (r + b + 2) * (phiBar K c r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar K c (r + 1) b - 1)
      ≤ phiBar K c (r + 1) (b + 1) := by
  have hK0 : (0:ℝ) < K := by linarith
  have hc0 : (0:ℝ) ≤ c := by linarith
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · -- `r = 0` base case
    have hA0 : phiBar K c 0 (b + 1) = 0 := by
      apply phiBar_far
      simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add, zero_sub, neg_nonpos]
      positivity
    have hpB := phiBar_le_layerform_of hK0 hK2c (0 + 1) b (by norm_num)
    have hpC := phiBar_layer (K := K) (c := c) (r := 0 + 1) (b := b + 1) hnear
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le b))
    rw [hA0, hpC]
    have hLD0 : (↑(0:ℕ) + 1) / (↑(0:ℕ) + ↑b + 2) * ((0:ℝ) + 1)
        + (↑b + 1) / (↑(0:ℕ) + ↑b + 2)
          * ((↑(0 + 1:ℕ) + c * Real.sqrt ↑(0 + 1:ℕ) - ↑b) ^ 2 / (K * Real.sqrt ↑(0 + 1:ℕ)) - 1)
        ≤ (↑(0 + 1:ℕ) + c * Real.sqrt ↑(0 + 1:ℕ) - ↑(b + 1)) ^ 2 / (K * Real.sqrt ↑(0 + 1:ℕ)) := by
      have hs1 : Real.sqrt ((0 + 1:ℕ) : ℝ) = 1 := by
        rw [show ((0 + 1:ℕ) : ℝ) = 1 from by norm_num, Real.sqrt_one]
      rw [hs1]
      push_cast
      rw [← sub_nonneg]
      have hbne : ((b:ℝ) + 2) ≠ 0 := by positivity
      have hKne : K ≠ 0 := ne_of_gt hK0
      rw [show (1 + c * 1 - ((b:ℝ) + 1)) ^ 2 / (K * 1)
            - ((0 + 1) / (0 + (b:ℝ) + 2) * (0 + 1)
              + ((b:ℝ) + 1) / (0 + (b:ℝ) + 2) * ((1 + c * 1 - (b:ℝ)) ^ 2 / (K * 1) - 1))
          = (3 * (b:ℝ) ^ 2 + (K - 4 * c + 1) * (b:ℝ) + (c ^ 2 - 2 * c - 1)) / (K * ((b:ℝ) + 2)) from by
        field_simp; ring]
      apply div_nonneg
      · sos
      · positivity
    exact le_trans (by gcongr) hLD0
  · -- `r ≥ 1`
    have hrb_nat : r ≤ b + 1 := by exact_mod_cast hrb
    rcases Nat.lt_or_ge b r with hbltr | hrleb
    · -- seam `r = b + 1`
      have hrb1 : r = b + 1 := by omega
      subst hrb1
      have hppos : 0 < Real.sqrt ((b:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hqpos : 0 < Real.sqrt ((b:ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
      have hpq : Real.sqrt ((b:ℝ) + 1) ≤ Real.sqrt ((b:ℝ) + 2) := Real.sqrt_le_sqrt (by linarith)
      have hA : phiBar K c (b + 1) (b + 1) = c ^ 2 * Real.sqrt ((b:ℝ) + 1) / K := by
        rw [phiBar_layer (K := K) (c := c) (by
          refine not_le.mpr ?_; push_cast
          nlinarith [mul_nonneg hc0 (Real.sqrt_nonneg ((b:ℝ) + 1)),
            Real.sqrt_pos.mpr (show (0:ℝ) < (b:ℝ) + 1 by positivity)]) (le_refl _)]
        push_cast
        rw [show ((b:ℝ) + 1 + c * Real.sqrt ((b:ℝ) + 1) - ((b:ℝ) + 1))
          = c * Real.sqrt ((b:ℝ) + 1) from by ring]
        field_simp
      have hB := phiBar_bulk (K := K) (c := c) (r := b + 1 + 1) (b := b)
        (by refine not_le.mpr ?_; push_cast
            nlinarith [mul_nonneg hc0 (Real.sqrt_nonneg ((b:ℝ) + 1 + 1))])
        (by refine not_le.mpr ?_; push_cast; linarith)
      have hC := phiBar_bulk (K := K) (c := c) (r := b + 1 + 1) (b := b + 1) hnear
        (by refine not_le.mpr ?_; push_cast; linarith)
      rw [hA, hB, hC]
      push_cast
      rw [← sub_nonneg]
      have hpq' : Real.sqrt ((b:ℝ) + 1) ≤ Real.sqrt ((b:ℝ) + 1 + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hne1 : ((b:ℝ) + 1 + (b:ℝ) + 2) ≠ 0 := by positivity
      have hne2 : (2 * (b:ℝ) + 3) ≠ 0 := by positivity
      have hKne : K ≠ 0 := ne_of_gt hK0
      rw [show ((b:ℝ) + 1 + 1 - ((b:ℝ) + 1) + c ^ 2 / K * Real.sqrt ((b:ℝ) + 1 + 1)
            - (((b:ℝ) + 1 + 1) / ((b:ℝ) + 1 + (b:ℝ) + 2) * (c ^ 2 * Real.sqrt ((b:ℝ) + 1) / K + 1)
              + ((b:ℝ) + 1) / ((b:ℝ) + 1 + (b:ℝ) + 2)
                * ((b:ℝ) + 1 + 1 - (b:ℝ) + c ^ 2 / K * Real.sqrt ((b:ℝ) + 1 + 1) - 1)))
          = c ^ 2 * ((b:ℝ) + 1 + 1) * (Real.sqrt ((b:ℝ) + 1 + 1) - Real.sqrt ((b:ℝ) + 1))
            / (K * (2 * (b:ℝ) + 3)) from by field_simp; ring]
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg (sq_nonneg c) (by positivity)) (by linarith [hpq'])
      · positivity
    · -- main case `b ≥ r`
      have hsq : Real.sqrt (r:ℝ) ^ 2 = (r:ℝ) := Real.sq_sqrt (by positivity)
      have htq : Real.sqrt ((r:ℝ) + 1) ^ 2 = (r:ℝ) + 1 := Real.sq_sqrt (by positivity)
      have ht2 : Real.sqrt ((r:ℝ) + 1) ^ 2 = Real.sqrt (r:ℝ) ^ 2 + 1 := by rw [htq, hsq]
      have ht0 : 0 < Real.sqrt ((r:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hs1 : (1:ℝ) ≤ Real.sqrt (r:ℝ) := by
        rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hrpos)
      have hpC := phiBar_layer (K := K) (c := c) hnear
        (show ((r + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_le_succ hrleb)
      have hpA := phiBar_le_layerform_of hK0 hK2c r (b + 1) hrpos
      have hpB := phiBar_le_layerform_of hK0 hK2c (r + 1) b (by omega)
      have hrb' : (r:ℝ) ≤ (b:ℝ) := by exact_mod_cast hrleb
      have hcore := hlayer (Real.sqrt r) (Real.sqrt ((r:ℝ) + 1)) ((b:ℝ) - Real.sqrt (r:ℝ) ^ 2)
        hs1 (by rw [hsq]; linarith) ht0.le ht2
      have hLD := layer_div_ineq_of (K := K) (c := c) (s := Real.sqrt r)
        (t := Real.sqrt ((r:ℝ) + 1)) (rr := (r:ℝ)) (bb := (b:ℝ)) hK0 hs1 ht0 hsq.symm
        (by positivity) hcore
      rw [hpC]
      push_cast at hpA hpB ⊢
      refine le_trans ?_ hLD
      gcongr

/-- The supersolution inequality (`ss` field), generic in `(K,c)`, assembled from
the far-field, bulk, and hard (layer/seam) cases. -/
theorem phiBar_ss_of {K c : ℝ} (hK1 : 1 ≤ K) (hc1 : 1 ≤ c) (hK2c : K ≤ 2 * c)
    (hcK1 : 1 ≤ c * (K - 1))
    (hr0 : K ^ 2 - 8 * K * c + 2 * K + 4 * c ^ 2 + 16 * c + 13 ≤ 0)
    (hlayer : ∀ s t w : ℝ, 1 ≤ s → 0 ≤ w → 0 ≤ t → t ^ 2 = s ^ 2 + 1 →
        0 ≤ s * (c * t - w) ^ 2 * (2 * s ^ 2 + w + 2)
          - (s ^ 2 + 1) * (t * (c * s - w - 1) ^ 2 + K * s * t)
          - (s ^ 2 + w + 1) * (s * (c * t - w + 1) ^ 2 - K * s * t))
    (r b : ℕ) :
    (r + 1) / (r + b + 2) * (phiBar K c r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar K c (r + 1) b - 1)
      ≤ phiBar K c (r + 1) (b + 1) := by
  by_cases hfar : (↑(r + 1) : ℝ) + c * Real.sqrt ↑(r + 1) - ↑(b + 1) ≤ 0
  · exact phiBar_ss_far_of hK1 hc1 hcK1 r b hfar
  · by_cases hbulk : (b : ℝ) + 1 < r
    · exact phiBar_ss_bulk_of (by linarith) (by linarith) r b hbulk
    · exact phiBar_ss_hard_of hK1 hc1 hK2c hr0 hlayer r b hfar (by linarith [not_lt.mp hbulk])

/-- **General supersolution theorem.** The barrier `phiBar K c` is a supersolution
provided the four polynomial side-conditions on `(K,c)` hold together with the
layer inequality `hlayer`. By the comparison principle this gives `e r b = 0`
whenever `b ≥ r + c·√r`. -/
theorem phiBar_isSupersolution_of {K c : ℝ} (hK1 : 1 ≤ K) (hc1 : 1 ≤ c) (hK2c : K ≤ 2 * c)
    (hcK1 : 1 ≤ c * (K - 1))
    (hr0 : K ^ 2 - 8 * K * c + 2 * K + 4 * c ^ 2 + 16 * c + 13 ≤ 0)
    (hlayer : ∀ s t w : ℝ, 1 ≤ s → 0 ≤ w → 0 ≤ t → t ^ 2 = s ^ 2 + 1 →
        0 ≤ s * (c * t - w) ^ 2 * (2 * s ^ 2 + w + 2)
          - (s ^ 2 + 1) * (t * (c * s - w - 1) ^ 2 + K * s * t)
          - (s ^ 2 + w + 1) * (s * (c * t - w + 1) ^ 2 - K * s * t)) :
    IsSupersolution (phiBar K c) := by
  have hK0 : (0:ℝ) < K := by linarith
  have hc0 : (0:ℝ) ≤ c := by linarith
  refine ⟨?nonneg, ?zero_left, ?base, ?ss⟩
  case nonneg =>
    intro r b
    unfold phiBar
    split_ifs with h1 h2
    · exact le_rfl
    · positivity
    · have hpos : (0 : ℝ) ≤ (c ^ 2 / K) * Real.sqrt r := by positivity
      linarith
  case zero_left =>
    intro b
    simp [phiBar]
  case base =>
    intro r
    unfold phiBar
    split_ifs with h1 h2
    · have hs : Real.sqrt r ≥ 0 := Real.sqrt_nonneg _
      have hr_le : (r : ℝ) ≤ 0 := by
        have hh : (r : ℝ) + c * Real.sqrt r ≤ 0 := by simpa using h1
        nlinarith [mul_nonneg hc0 hs]
      have hr0' : (r : ℝ) = 0 := le_antisymm hr_le (Nat.cast_nonneg r)
      simp [hr0']
    · have hr0' : (r : ℝ) = 0 := le_antisymm (by simpa using h2) (Nat.cast_nonneg r)
      simp [hr0']
    · have hpos : (0 : ℝ) ≤ (c ^ 2 / K) * Real.sqrt r := by positivity
      simp only [Nat.cast_zero, sub_zero]
      linarith
  case ss => exact phiBar_ss_of hK1 hc1 hK2c hcK1 hr0 hlayer

/-! ### The concrete instance `(K,c) = (6,4)`

The layer certificate: `G(s,w) = A² − (s²+1)·B²` is a degree-8 bivariate
polynomial (the `w`-degree-10 leading terms of `A²` and `(s²+1)B²` cancel),
non-negative on `s ≥ 1`, discharged in one `sos` call. The Putinar certificate
`G = σ₀ + σ₁·(s−1)` needs the Newton-pruned σ-bases (`w`-degree ≤ 2): the dense
bases carry `w³`/`w⁴` rows whose Grams are structurally rank-deficient, which
CSDP tolerates but exact rational rounding does not. Feeding the resulting
`layer_core_6_4` to the general theorem yields `IsSupersolution (phiBar 6 4)`. -/

set_option maxHeartbeats 2000000 in
-- one degree-8 bivariate `sos` solve (a ~35-equation SDP) overruns the default budget
theorem hard_G_nonneg_6_4 {s w : ℝ} (hs : 1 ≤ s) :
    0 ≤ (16*s^5 + 31*s^3 + 15*s + w^2*(s^3+3*s) + w*(2*s^3+s))^2
      - (s^2+1)*(16*s^4 + 17*s^2 + w^2*(s^2+1) + w*(2*s^2+2*s+2) + 1)^2 := by
  sos

/-- Layer inequality for `(K,c) = (6,4)`: removes the square root from
`hard_G_nonneg_6_4`, exactly as `layer_core` does for `(91,137)`. -/
theorem layer_core_6_4 {s t w : ℝ} (hs : 1 ≤ s) (hw : 0 ≤ w) (ht0 : 0 ≤ t)
    (ht2 : t ^ 2 = s ^ 2 + 1) :
    0 ≤ s * (4*t - w) ^ 2 * (2*s^2 + w + 2)
        - (s^2 + 1) * (t * (4*s - w - 1) ^ 2 + 6*s*t)
        - (s^2 + w + 1) * (s * (4*t - w + 1) ^ 2 - 6*s*t) := by
  -- sos -- sos: search failed to find a certificate
  have h0s : (0:ℝ) ≤ s := by linarith
  have hG := hard_G_nonneg_6_4 (w := w) hs
  have hA : 0 ≤ 16*s^5 + 31*s^3 + 15*s + w^2*(s^3+3*s) + w*(2*s^3+s) := by
    nlinarith [pow_nonneg h0s 5, pow_nonneg h0s 3, h0s,
      mul_nonneg (sq_nonneg w) (pow_nonneg h0s 3), mul_nonneg (sq_nonneg w) h0s,
      mul_nonneg hw (pow_nonneg h0s 3), mul_nonneg hw h0s]
  have hBp : 0 ≤ 16*s^4 + 17*s^2 + w^2*(s^2+1) + w*(2*s^2+2*s+2) + 1 := by
    nlinarith [pow_nonneg h0s 4, pow_nonneg h0s 2, mul_nonneg (sq_nonneg w) (pow_nonneg h0s 2),
      sq_nonneg w, mul_nonneg hw (pow_nonneg h0s 2), mul_nonneg hw h0s, hw]
  have hGt : 0 ≤ (16*s^5 + 31*s^3 + 15*s + w^2*(s^3+3*s) + w*(2*s^3+s))^2
      - t^2*(16*s^4 + 17*s^2 + w^2*(s^2+1) + w*(2*s^2+2*s+2) + 1)^2 := by
    rw [ht2]; exact hG
  have hAtBp : 0 ≤ (16*s^5 + 31*s^3 + 15*s + w^2*(s^3+3*s) + w*(2*s^3+s))
      + t*(16*s^4 + 17*s^2 + w^2*(s^2+1) + w*(2*s^2+2*s+2) + 1) :=
    add_nonneg hA (mul_nonneg ht0 hBp)
  have hcore : 0 ≤ (16*s^5 + 31*s^3 + 15*s + w^2*(s^3+3*s) + w*(2*s^3+s))
      - t*(16*s^4 + 17*s^2 + w^2*(s^2+1) + w*(2*s^2+2*s+2) + 1) := by
    nlinarith [hGt, hAtBp, hA, mul_nonneg ht0 hBp]
  have hFeq : (16*s^5 + 31*s^3 + 15*s + w^2*(s^3+3*s) + w*(2*s^3+s))
      - t*(16*s^4 + 17*s^2 + w^2*(s^2+1) + w*(2*s^2+2*s+2) + 1)
      = s * (4*t - w) ^ 2 * (2*s^2 + w + 2) - (s^2 + 1) * (t * (4*s - w - 1) ^ 2 + 6*s*t)
        - (s^2 + w + 1) * (s * (4*t - w + 1) ^ 2 - 6*s*t) := by
    linear_combination (-16*s^3 - 16*s) * ht2
  rw [← hFeq]; exact hcore

/-- The barrier `phiBar 6 4` is a supersolution: a vastly smaller width constant. -/
theorem phiBar_isSupersolution_6_4 : IsSupersolution (phiBar 6 4) := by
  refine phiBar_isSupersolution_of (K := 6) (c := 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_
  intro s t w hs hw ht ht2
  exact layer_core_6_4 hs hw ht ht2

/-- **Question (zero region).** Since `phiBar 6 4` is a (global) supersolution, the
equity vanishes on `{ b > r + 4·√r }` — for *all* `r, b`, with no lower bound on `r`.
(The width constant `4` comes from the `(K,c) = (6,4)` instance; any sufficiently
large `c` with an admissible `K` works — `137` was an earlier placeholder.) -/
theorem question (r b : ℕ) (hb : (b : ℝ) > r + 4 * Real.sqrt r) : e r b = 0 := by
  have hle : (e r b : ℝ) ≤ phiBar 6 4 r b :=
    e_le_of_supersolution phiBar_isSupersolution_6_4 r b
  have hfar : phiBar 6 4 r b = 0 :=
    phiBar_far (show (r : ℝ) + 4 * Real.sqrt r - b ≤ 0 by linarith)
  have hge : (0 : ℝ) ≤ (e r b : ℝ) := by exact_mod_cast zero_le_e r b
  have : (e r b : ℝ) = 0 := le_antisymm (hfar ▸ hle) hge
  exact_mod_cast this
