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

/-- Evaluation of `phiBar` in the layer (`D > 0`, above the diagonal `r ≤ b`). -/
theorem phiBar_layer {K c : ℝ} {r b : ℕ}
    (h1 : ¬ (r : ℝ) + c * Real.sqrt r - b ≤ 0) (h2 : (r : ℝ) ≤ b) :
    phiBar K c r b = ((r : ℝ) + c * Real.sqrt r - b) ^ 2 / (K * Real.sqrt r) := by
  unfold phiBar; rw [if_neg h1, if_pos h2]

/-- Universal upper bound: for `R ≥ 1` and any `b`, the barrier `phiBar 91 137 R b`
is at most the layer formula `(R + 137√R - b)² / (91√R)`. In the far field the layer
formula is nonnegative; in the layer it is an equality; in the bulk (`b < R`) the
difference is `(R-b)(R-b+183√R) ≥ 0` after clearing `91√R`. -/
theorem phiBar_le_layerform (R b : ℕ) (hR : 1 ≤ R) :
    phiBar 91 137 R b ≤ ((R : ℝ) + 137 * Real.sqrt R - b) ^ 2 / (91 * Real.sqrt R) := by
  have hsr : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by exact_mod_cast Nat.lt_of_lt_of_le one_pos hR)
  have hsq : Real.sqrt R ^ 2 = (R : ℝ) := Real.sq_sqrt (by positivity)
  unfold phiBar
  split_ifs with h1 h2
  · positivity
  · exact le_refl _
  · have hb : (b : ℝ) < R := not_le.mp h2
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 91 * Real.sqrt R)]
    nlinarith [hsq, hsr, hb, mul_pos (sub_pos.mpr hb) hsr,
      mul_nonneg (le_of_lt (sub_pos.mpr hb)) (le_of_lt hsr)]

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

/-! ### Algebraic core of the hard case

The hard case reduces, after clearing the positive denominators `91·√r·√(r+1)·N`
and substituting `s = √r`, `t = √(r+1)` (so `t² = s²+1`), `w = b - r`, to the
polynomial inequality `0 ≤ F(s,t,w)` where `F = A(s,w) + t·B(s,w)` with `B ≤ 0`.
Since `A ≥ 0` and `B ≤ 0`, `A + t·B ≥ 0` is equivalent to `A² ≥ (s²+1)·B²`, a
square-root-free polynomial inequality `G(s,w) ≥ 0`. Viewing `G` as a quartic in
`w`, the matrix of its `[w²,w,1]` quadratic form is PSD for `s ≥ 1`, giving the
closed-form Positivstellensatz certificate below. -/

/-- `3s⁴+6s²-1 > 0` for `s ≥ 1` (the leading `w⁴`-coefficient of `G`).

Closed automatically by the `sos` tactic (a sum-of-squares / Positivstellensatz
search via CSDP). Run `sos?` instead of `sos` to freeze the discovered
certificate into a solver-free `sos_witness` term. The higher-degree
Schur-complement lemmas below (`hard_H2_pos`, `hard_H3_nonneg`) and the bivariate
core `hard_G_nonneg` are beyond what the CSDP search finds at practical settings,
so they keep their explicit certificates. -/
theorem hard_c4_pos {s : ℝ} (hs : 1 ≤ s) : 0 < 3*s^4 + 6*s^2 - 1 := by
  sos

/-- The first Schur-complement polynomial `H₂ = 4c₄c₂ - c₃²` is `> 0` for `s ≥ 1`.
Proved by the shift `s = 1+u`, after which every coefficient is nonnegative and the
constant term is positive. -/
theorem hard_H2_pos {s : ℝ} (hs : 1 ≤ s) :
    0 < 766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7 + 2194152*s^6
      - 51240*s^5 - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8 := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ s = 1 + u := ⟨s - 1, by linarith, by ring⟩
  nlinarith [hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5,
    pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8, pow_nonneg hu 9, pow_nonneg hu 10]

/-- The second Schur-complement polynomial `H₃ = c₀H₂ - c₄c₁²` is `≥ 0` for `s ≥ 1`. -/
theorem hard_H3_nonneg {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ 128537021394432*s^18 - 4125629205504*s^17 + 899709427526640*s^16
      - 29910152289888*s^15 + 2464682177754744*s^14 - 85603206522792*s^13
      + 3326576106479060*s^12 - 125823914765544*s^11 + 2154878268368608*s^10
      - 101069507531040*s^9 + 355638798499312*s^8 - 42283028192112*s^7
      - 271963437228936*s^6 - 7218669537192*s^5 - 105787483879228*s^4
      + 82453944*s^3 + 2818336944*s^2 + 2928*s + 8 := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ s = 1 + u := ⟨s - 1, by linarith, by ring⟩
  nlinarith [hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5,
    pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8, pow_nonneg hu 9, pow_nonneg hu 10,
    pow_nonneg hu 11, pow_nonneg hu 12, pow_nonneg hu 13, pow_nonneg hu 14, pow_nonneg hu 15,
    pow_nonneg hu 16, pow_nonneg hu 17, pow_nonneg hu 18]

/-- The square-root-free polynomial inequality `A² ≥ (s²+1)·Bpos²` (equivalently
`G ≥ 0`) for `s ≥ 1`, `w ≥ 0`, where `A` and `Bpos` are the coefficients of the
reduced supersolution defect `F = A - t·Bpos` (`B = -Bpos`). Proved via the
completing-the-square certificate `4·c₄·H₂·G = H₂·(2c₄w²+c₃w)² + (H₂w+2c₄c₁)² + 4c₄·H₃`,
with `c₄ > 0`, `H₂ > 0`, `H₃ ≥ 0` for `s ≥ 1`. Holds for all real `w`. -/
theorem hard_G_nonneg {s w : ℝ} (hs : 1 ≤ s) :
    0 ≤ (18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s))^2
      - (s^2+1)*(18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1)^2 := by
  have hc4 : 0 < 3*s^4 + 6*s^2 - 1 := hard_c4_pos hs
  have hH2 : 0 < 766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7 + 2194152*s^6
      - 51240*s^5 - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8 := hard_H2_pos hs
  have hH3 : 0 ≤ 128537021394432*s^18 - 4125629205504*s^17 + 899709427526640*s^16
      - 29910152289888*s^15 + 2464682177754744*s^14 - 85603206522792*s^13
      + 3326576106479060*s^12 - 125823914765544*s^11 + 2154878268368608*s^10
      - 101069507531040*s^9 + 355638798499312*s^8 - 42283028192112*s^7
      - 271963437228936*s^6 - 7218669537192*s^5 - 105787483879228*s^4
      + 82453944*s^3 + 2818336944*s^2 + 2928*s + 8 := hard_H3_nonneg hs
  have key : 4*(3*s^4 + 6*s^2 - 1)*(766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7
      + 2194152*s^6 - 51240*s^5 - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8)
      * ((18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s))^2
        - (s^2+1)*(18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1)^2)
      = (766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7 + 2194152*s^6 - 51240*s^5
          - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8)
        * (2*(3*s^4 + 6*s^2 - 1)*w^2
            + (-366*s^5 + 2*s^4 - 732*s^3 - 6*s^2 - 366*s - 4)*w)^2
      + ((766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7 + 2194152*s^6 - 51240*s^5
            - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8)*w
          + 2*(3*s^4 + 6*s^2 - 1)*(-6869454*s^7 - 37546*s^6 - 13739274*s^5 - 75094*s^4
            - 6870186*s^3 - 37552*s^2 - 366*s - 4))^2
      + 4*(3*s^4 + 6*s^2 - 1)*(128537021394432*s^18 - 4125629205504*s^17
          + 899709427526640*s^16 - 29910152289888*s^15 + 2464682177754744*s^14
          - 85603206522792*s^13 + 3326576106479060*s^12 - 125823914765544*s^11
          + 2154878268368608*s^10 - 101069507531040*s^9 + 355638798499312*s^8
          - 42283028192112*s^7 - 271963437228936*s^6 - 7218669537192*s^5
          - 105787483879228*s^4 + 82453944*s^3 + 2818336944*s^2 + 2928*s + 8) := by
    ring
  have hrhs : 0 ≤ (766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7 + 2194152*s^6 - 51240*s^5
          - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8)
        * (2*(3*s^4 + 6*s^2 - 1)*w^2
            + (-366*s^5 + 2*s^4 - 732*s^3 - 6*s^2 - 366*s - 4)*w)^2
      + ((766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7 + 2194152*s^6 - 51240*s^5
            - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8)*w
          + 2*(3*s^4 + 6*s^2 - 1)*(-6869454*s^7 - 37546*s^6 - 13739274*s^5 - 75094*s^4
            - 6870186*s^3 - 37552*s^2 - 366*s - 4))^2
      + 4*(3*s^4 + 6*s^2 - 1)*(128537021394432*s^18 - 4125629205504*s^17
          + 899709427526640*s^16 - 29910152289888*s^15 + 2464682177754744*s^14
          - 85603206522792*s^13 + 3326576106479060*s^12 - 125823914765544*s^11
          + 2154878268368608*s^10 - 101069507531040*s^9 + 355638798499312*s^8
          - 42283028192112*s^7 - 271963437228936*s^6 - 7218669537192*s^5
          - 105787483879228*s^4 + 82453944*s^3 + 2818336944*s^2 + 2928*s + 8) := by
    have a1 := mul_nonneg hH2.le (sq_nonneg (2*(3*s^4 + 6*s^2 - 1)*w^2
      + (-366*s^5 + 2*s^4 - 732*s^3 - 6*s^2 - 366*s - 4)*w))
    have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ 4*(3*s^4 + 6*s^2 - 1)) hH3
    have a2 := sq_nonneg ((766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7 + 2194152*s^6
        - 51240*s^5 - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8)*w
      + 2*(3*s^4 + 6*s^2 - 1)*(-6869454*s^7 - 37546*s^6 - 13739274*s^5 - 75094*s^4
        - 6870186*s^3 - 37552*s^2 - 366*s - 4))
    linarith
  have h4 : 0 < 4*(3*s^4 + 6*s^2 - 1)*(766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7
      + 2194152*s^6 - 51240*s^5 - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8) :=
    mul_pos (by linarith) hH2
  have hprod : 0 ≤ 4*(3*s^4 + 6*s^2 - 1)*(766908*s^10 - 7320*s^9 + 2665592*s^8 - 36600*s^7
      + 2194152*s^6 - 51240*s^5 - 4944*s^4 - 21960*s^3 - 300404*s^2 + 8)
      * ((18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s))^2
        - (s^2+1)*(18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1)^2) := by
    rw [key]; exact hrhs
  exact (mul_nonneg_iff_of_pos_left h4).mp hprod

/-- The cleared, square-root-substituted supersolution defect in the all-layer
sub-case is nonnegative: with `s = √r`, `t = √(r+1)`, `w = b - r`, the inequality
`0 ≤ F(s,t,w)`. This combines `hard_G_nonneg` (the polynomial core `A² ≥ (s²+1)Bpos²`)
with the sign facts `A ≥ 0`, `Bpos ≥ 0`, `t ≥ 0` to remove the square root, then
rewrites `F = A - t·Bpos` via `t² = s²+1`. -/
theorem layer_core {s t w : ℝ} (hs : 1 ≤ s) (hw : 0 ≤ w) (ht0 : 0 ≤ t)
    (ht2 : t^2 = s^2 + 1) :
    0 ≤ s*(137*t - w)^2*(2*s^2 + w + 2)
        - (s^2 + 1)*(t*(137*s - w - 1)^2 + 91*s*t)
        - (s^2 + w + 1)*(s*(137*t - w + 1)^2 - 91*s*t) := by
  have h0s : (0:ℝ) ≤ s := by linarith
  have hG := hard_G_nonneg (w := w) hs
  have hA : 0 ≤ 18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s) := by
    nlinarith [pow_nonneg h0s 5, pow_nonneg h0s 3, h0s,
      mul_nonneg (sq_nonneg w) (pow_nonneg h0s 3), mul_nonneg (sq_nonneg w) h0s,
      mul_nonneg hw (pow_nonneg h0s 3), mul_nonneg hw h0s]
  have hBp : 0 ≤ 18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1 := by
    nlinarith [pow_nonneg h0s 4, pow_nonneg h0s 2, mul_nonneg (sq_nonneg w) (pow_nonneg h0s 2),
      sq_nonneg w, mul_nonneg hw (pow_nonneg h0s 2), mul_nonneg hw h0s, hw]
  have hGt : 0 ≤ (18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s))^2
      - t^2*(18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1)^2 := by
    rw [ht2]; exact hG
  have hAtBp : 0 ≤ (18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s))
      + t*(18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1) :=
    add_nonneg hA (mul_nonneg ht0 hBp)
  have hcore : 0 ≤ (18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s))
      - t*(18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1) := by
    nlinarith [hGt, hAtBp, hA, mul_nonneg ht0 hBp]
  have hFeq : (18769*s^5 + 37537*s^3 + 18768*s + w^2*(s^3+3*s) + w*(2*s^3+s))
      - t*(18769*s^4 + 18770*s^2 + w^2*(s^2+1) + w*(2*s^2+183*s+2) + 1)
      = s*(137*t - w)^2*(2*s^2 + w + 2) - (s^2 + 1)*(t*(137*s - w - 1)^2 + 91*s*t)
        - (s^2 + w + 1)*(s*(137*t - w + 1)^2 - 91*s*t) := by
    linear_combination (-18769*s^3 - 18769*s) * ht2
  rw [← hFeq]; exact hcore

/-- Divided ("`1/N`-weighted") form of the all-layer supersolution inequality,
obtained from `layer_core` by clearing the positive denominators `91·s·t·N`. Here
`rr = s²` stands for `↑r`, `bb` for `↑b`, with `s = √r`, `t = √(r+1)`, and the
membership hypothesis `s² ≤ bb` (i.e. `r ≤ b`). -/
theorem layer_div_ineq {s t rr bb : ℝ} (hs : 1 ≤ s) (ht0 : 0 < t) (ht2 : t^2 = s^2 + 1)
    (hrr : rr = s^2) (hbb : s^2 ≤ bb) (hN : 0 < rr + bb + 2) :
    (rr + 1) / (rr + bb + 2) * ((rr + 137*s - (bb + 1))^2 / (91*s) + 1)
      + (bb + 1) / (rr + bb + 2) * (((rr + 1) + 137*t - bb)^2 / (91*t) - 1)
      ≤ ((rr + 1) + 137*t - (bb + 1))^2 / (91*t) := by
  have hs0 : 0 < s := by linarith
  have hN' : (0:ℝ) < s^2 + bb + 2 := by rw [hrr] at hN; exact hN
  have hcore := layer_core (w := bb - s^2) hs (by linarith) ht0.le ht2
  have hden : 0 < 91*s*t*(s^2 + bb + 2) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hs0) ht0) hN'
  refine sub_nonneg.mp ?_
  have hFdiv : ((rr + 1) + 137*t - (bb + 1))^2 / (91*t)
      - ((rr + 1) / (rr + bb + 2) * ((rr + 137*s - (bb + 1))^2 / (91*s) + 1)
        + (bb + 1) / (rr + bb + 2) * (((rr + 1) + 137*t - bb)^2 / (91*t) - 1))
      = (s*(137*t-(bb-s^2))^2*(2*s^2+(bb-s^2)+2)
        - (s^2 + 1)*(t*(137*s-(bb-s^2)-1)^2+91*s*t)
        - (s^2+(bb-s^2)+1)*(s*(137*t-(bb-s^2)+1)^2-91*s*t))
        / (91*s*t*(s^2 + bb + 2)) := by
    rw [hrr]
    field_simp
    ring
  rw [hFdiv]
  exact div_nonneg hcore (le_of_lt hden)

/-- Hard (tight) case of the supersolution inequality: the layer `r ≤ b` together
with the diagonal seam `b = r - 1`, where the margin is `O(√r)` but the bound is
asymptotically tight. This is the remaining analytic core. -/
theorem phiBar_ss_hard (r b : ℕ)
    (hnear : ¬ (↑(r + 1) : ℝ) + 137 * Real.sqrt ↑(r + 1) - ↑(b + 1) ≤ 0)
    (hrb : (r : ℝ) ≤ (b : ℝ) + 1) :
    (r + 1) / (r + b + 2) * (phiBar 91 137 r (b + 1) + 1)
      + (b + 1) / (r + b + 2) * (phiBar 91 137 (r + 1) b - 1)
      ≤ phiBar 91 137 (r + 1) (b + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · -- `r = 0`: small base case. `phiBar` at `(0, b+1)` vanishes; the `(1,·)` points
    -- use `√1 = 1`, reducing to `3b² - 456b + 18494 ≥ 0`.
    have hA0 : phiBar 91 137 0 (b + 1) = 0 := by
      apply phiBar_far
      simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add, zero_sub, neg_nonpos]
      positivity
    have hpB := phiBar_le_layerform (0 + 1) b (by norm_num)
    have hpC := phiBar_layer (K := 91) (r := 0 + 1) (b := b + 1) hnear
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le b))
    rw [hA0, hpC]
    have hLD0 : (↑(0:ℕ) + 1) / (↑(0:ℕ) + ↑b + 2) * ((0:ℝ) + 1)
        + (↑b + 1) / (↑(0:ℕ) + ↑b + 2)
          * ((↑(0 + 1:ℕ) + 137 * Real.sqrt ↑(0 + 1:ℕ) - ↑b) ^ 2 / (91 * Real.sqrt ↑(0 + 1:ℕ)) - 1)
        ≤ (↑(0 + 1:ℕ) + 137 * Real.sqrt ↑(0 + 1:ℕ) - ↑(b + 1)) ^ 2 / (91 * Real.sqrt ↑(0 + 1:ℕ)) := by
      have hs1 : Real.sqrt ((0 + 1:ℕ) : ℝ) = 1 := by
        rw [show ((0 + 1:ℕ) : ℝ) = 1 from by norm_num, Real.sqrt_one]
      rw [hs1]
      push_cast
      rw [← sub_nonneg]
      rw [show (1 + 137 * 1 - ((b:ℝ) + 1)) ^ 2 / (91 * 1)
            - ((0 + 1) / (0 + (b:ℝ) + 2) * (0 + 1)
              + ((b:ℝ) + 1) / (0 + (b:ℝ) + 2) * ((1 + 137 * 1 - (b:ℝ)) ^ 2 / (91 * 1) - 1))
          = (3 * (b:ℝ) ^ 2 - 456 * (b:ℝ) + 18494) / (91 * ((b:ℝ) + 2)) from by
        field_simp; ring]
      apply div_nonneg
      · nlinarith [sq_nonneg ((b:ℝ) - 76)]
      · positivity
    exact le_trans (by gcongr) hLD0

  · -- `r ≥ 1`
    have hrb_nat : r ≤ b + 1 := by exact_mod_cast hrb
    rcases Nat.lt_or_ge b r with hbltr | hrleb
    · -- `b < r` with `r ≤ b + 1`, so `r = b + 1` (the bulk diagonal seam). Here the
      -- two `r+1`-points are in the bulk; the inequality collapses to `√(b+1) ≤ √(b+2)`.
      have hrb1 : r = b + 1 := by omega
      subst hrb1
      have hppos : 0 < Real.sqrt ((b:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hqpos : 0 < Real.sqrt ((b:ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
      have hpq : Real.sqrt ((b:ℝ) + 1) ≤ Real.sqrt ((b:ℝ) + 2) := Real.sqrt_le_sqrt (by linarith)
      have hA : phiBar 91 137 (b + 1) (b + 1) = 137 ^ 2 * Real.sqrt ((b:ℝ) + 1) / 91 := by
        rw [phiBar_layer (K := 91) (by
          refine not_le.mpr ?_; push_cast
          nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (b:ℝ) + 1 by positivity)]) (le_refl _)]
        push_cast
        rw [show ((b:ℝ) + 1 + 137 * Real.sqrt ((b:ℝ) + 1) - ((b:ℝ) + 1))
          = 137 * Real.sqrt ((b:ℝ) + 1) from by ring]
        field_simp
      have hB := phiBar_bulk (K := 91) (c := 137) (r := b + 1 + 1) (b := b)
        (by refine not_le.mpr ?_; push_cast; nlinarith [Real.sqrt_nonneg ((b:ℝ) + 1 + 1)])
        (by refine not_le.mpr ?_; push_cast; linarith)
      have hC := phiBar_bulk (K := 91) (r := b + 1 + 1) (b := b + 1) hnear
        (by refine not_le.mpr ?_; push_cast; linarith)
      rw [hA, hB, hC]
      push_cast
      rw [← sub_nonneg]
      have hpq' : Real.sqrt ((b:ℝ) + 1) ≤ Real.sqrt ((b:ℝ) + 1 + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hne1 : ((b:ℝ) + 1 + (b:ℝ) + 2) ≠ 0 := by positivity
      have hne2 : (2 * (b:ℝ) + 3) ≠ 0 := by positivity
      rw [show ((b:ℝ) + 1 + 1 - ((b:ℝ) + 1) + 137 ^ 2 / 91 * Real.sqrt ((b:ℝ) + 1 + 1)
            - (((b:ℝ) + 1 + 1) / ((b:ℝ) + 1 + (b:ℝ) + 2) * (137 ^ 2 * Real.sqrt ((b:ℝ) + 1) / 91 + 1)
              + ((b:ℝ) + 1) / ((b:ℝ) + 1 + (b:ℝ) + 2)
                * ((b:ℝ) + 1 + 1 - (b:ℝ) + 137 ^ 2 / 91 * Real.sqrt ((b:ℝ) + 1 + 1) - 1)))
          = 18769 * ((b:ℝ) + 1 + 1) * (Real.sqrt ((b:ℝ) + 1 + 1) - Real.sqrt ((b:ℝ) + 1))
            / (91 * (2 * (b:ℝ) + 3)) from by field_simp; ring]
      apply div_nonneg
      · exact mul_nonneg (by positivity) (by linarith [hpq'])
      · positivity
    · -- main case `b ≥ r`: the three points are in the layer (upper-bounding the two
      -- `LHS` points by their layer formulas), reducing to `layer_div_ineq`.
      have hsq : Real.sqrt (r:ℝ) ^ 2 = (r:ℝ) := Real.sq_sqrt (by positivity)
      have htq : Real.sqrt ((r:ℝ) + 1) ^ 2 = (r:ℝ) + 1 := Real.sq_sqrt (by positivity)
      have ht2 : Real.sqrt ((r:ℝ) + 1) ^ 2 = Real.sqrt (r:ℝ) ^ 2 + 1 := by rw [htq, hsq]
      have ht0 : 0 < Real.sqrt ((r:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hs1 : (1:ℝ) ≤ Real.sqrt (r:ℝ) := by
        rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hrpos)
      have hpC := phiBar_layer (K := 91) hnear
        (show ((r + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_le_succ hrleb)
      have hpA := phiBar_le_layerform r (b + 1) hrpos
      have hpB := phiBar_le_layerform (r + 1) b (by omega)
      have hLD := layer_div_ineq (s := Real.sqrt r) (t := Real.sqrt ((r:ℝ) + 1))
        (rr := (r:ℝ)) (bb := (b:ℝ)) hs1 ht0 ht2 hsq.symm
        (by rw [hsq]; exact_mod_cast hrleb) (by positivity)
      rw [hpC]
      push_cast at hpA hpB ⊢
      refine le_trans ?_ hLD
      gcongr

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
  -- The barrier `phiBar 91 137` is a supersolution, so it dominates `e`; and in the
  -- far field `b > r + 137√r` it vanishes, squeezing `e r b` between `0` and `0`.
  have hle : (e r b : ℝ) ≤ phiBar 91 137 r b :=
    e_le_of_supersolution phiBar_isSupersolution r b
  have hfar : phiBar 91 137 r b = 0 :=
    phiBar_far (K := 91) (show (r : ℝ) + 137 * Real.sqrt r - b ≤ 0 by linarith)
  have hge : (0 : ℝ) ≤ (e r b : ℝ) := by exact_mod_cast zero_le_e r b
  have : (e r b : ℝ) = 0 := le_antisymm (hfar ▸ hle) hge
  exact_mod_cast this

/-
On using the `sos` tactic (sum-of-squares / Positivstellensatz via CSDP), as
suggested by numina fuse. The `sos` project is now a dependency (`import SOS`),
and `hard_c4_pos` above is discharged by `sos`. Findings on the rest:

* The Schur-complement lemmas `hard_H2_pos` (degree 10) and `hard_H3_nonneg`
  (degree 18) and the bivariate quartic core `hard_G_nonneg` are *not* found by
  the CSDP search, even with `sos (config := { maxDepth := 7,
  maxRefutationPower := 2 })` (which runs for minutes before giving up). These
  are the inequalities that genuinely needed the hand-built certificate, so they
  retain the explicit completing-the-square Positivstellensatz identity and the
  shift-`s = 1+u` positivity proofs.

So `sos` automates the low-degree positivity in this file but does not (yet)
replace the explicit certificate that carries the hard case.
-/
