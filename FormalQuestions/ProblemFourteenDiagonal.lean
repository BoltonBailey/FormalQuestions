import Mathlib
import FormalQuestions.ProblemFourteen

/-!
# Diagonal `√r` lower bound for the red/black card game (reflection-free)

This file proves `e(r,r) ≥ (1/8)·√r` and, via the `1`-Lipschitz reduction of
`ProblemFourteen`, the complementary positivity theorem `e(r,b) > 0` for
`b < r + (1/8)·√r`.

The strategy value of "draw until reds-drawn exceed blacks-drawn by `L`, else draw
to the end" has the closed form `W_L(r,b) = (r-b) + L·C(r+b,b-L)/C(r+b,b)`. We verify
this against the game recursion by pure binomial algebra (Pascal's rule and the
multiplicative binomial identities) — no reflection principle is needed — so that
`W_L ≤ e`, giving `e(n,n) ≥ L·C(2n,n-L)/C(2n,n)`. A binomial-ratio estimate
`C(2n,n-L)/C(2n,n) ≥ 1 - L²/n` and the choice `L ≈ √n/2` yield the `√r` growth.
-/

/-- `b · C(r+b, b) = (r+b) · C(r+b-1, b-1)`. -/
theorem HB (r b : ℕ) (hb : 1 ≤ b) :
    b * Nat.choose (r+b) b = (r+b) * Nat.choose (r+b-1) (b-1) := by
  have h := Nat.succ_mul_choose_eq (r+b-1) (b-1)
  have e1 : (r+b-1).succ = r+b := by omega
  have e2 : (b-1).succ = b := by omega
  rw [e1, e2] at h
  rw [mul_comm]; exact h.symm

/-- `r · C(r+b, b) = (r+b) · C(r+b-1, b)`. -/
theorem HA (r b : ℕ) (hr : 1 ≤ r) :
    r * Nat.choose (r+b) b = (r+b) * Nat.choose (r+b-1) b := by
  have hsym1 : Nat.choose (r+b) b = Nat.choose (r+b) r := by
    rw [← Nat.choose_symm (by omega : b ≤ r+b)]; congr 1; omega
  have hsym2 : Nat.choose (r+b-1) b = Nat.choose (r+b-1) (r-1) := by
    rw [← Nat.choose_symm (by omega : b ≤ r+b-1)]; congr 1; omega
  rw [hsym1, hsym2]
  have h := Nat.succ_mul_choose_eq (r+b-1) (r-1)
  have e1 : (r+b-1).succ = r+b := by omega
  have e2 : (r-1).succ = r := by omega
  rw [e1, e2] at h
  rw [mul_comm]; exact h.symm

/-- The reach-probability closed form `P_L(r,b) = C(r+b,b-L)/C(r+b,b)` (as `ℚ`,
`0` when `b < L`). -/
def PL (L r b : ℕ) : ℚ :=
  if L ≤ b then (Nat.choose (r+b) (b-L) : ℚ) / (Nat.choose (r+b) b : ℚ) else 0

/-- `P_L` is a martingale for the draw operator: it satisfies the same weighted
recursion as the deterministic value, proved by Pascal's rule plus the
multiplicative binomial identities. -/
theorem PL_mart (L r b : ℕ) (hr : 1 ≤ r) (hb : 1 ≤ b) :
    PL L r b = (r/(r+b : ℚ)) * PL L (r-1) b + (b/(r+b : ℚ)) * PL L r (b-1) := by
  rcases lt_or_ge b L with hbL | hbL
  · unfold PL
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  · have hcA : (0:ℚ) < (Nat.choose (r+b) b : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : b ≤ r+b)
    have hcB : (0:ℚ) < (Nat.choose (r+b-1) b : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : b ≤ r+b-1)
    have hcC : (0:ℚ) < (Nat.choose (r+b-1) (b-1) : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : b-1 ≤ r+b-1)
    have i1 : (r-1)+b = r+b-1 := by omega
    have i2 : r+(b-1) = r+b-1 := by omega
    rcases eq_or_lt_of_le hbL with hbe | hbg
    · unfold PL
      rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), i1]
      rw [show b - L = 0 by omega]
      have hAq : (r : ℚ) * (Nat.choose (r+b) b) = (r+b) * (Nat.choose (r+b-1) b) := by
        exact_mod_cast HA r b hr
      rw [Nat.choose_zero_right, Nat.choose_zero_right]
      field_simp
      nlinarith [hAq]
    · have hbL1 : L ≤ b - 1 := by omega
      unfold PL
      rw [if_pos hbL, if_pos (by omega : L ≤ b), if_pos hbL1, i1, i2]
      have hAq : (r : ℚ) * (Nat.choose (r+b) b) = (r+b) * (Nat.choose (r+b-1) b) := by
        exact_mod_cast HA r b hr
      have hBq : (b : ℚ) * (Nat.choose (r+b) b) = (r+b) * (Nat.choose (r+b-1) (b-1)) := by
        exact_mod_cast HB r b hb
      have hPq : (Nat.choose (r+b) (b-L) : ℚ)
          = (Nat.choose (r+b-1) (b-1-L) : ℚ) + (Nat.choose (r+b-1) (b-L) : ℚ) := by
        have h := Nat.choose_succ_succ (r+b-1) (b-L-1)
        simp only [Nat.succ_eq_add_one] at h
        rw [show r+b-1+1 = r+b by omega, show b-L-1+1 = b-L by omega] at h
        rw [show b-1-L = b-L-1 by omega]
        exact_mod_cast h
      have nA := ne_of_gt hcA
      have nB := ne_of_gt hcB
      have nC := ne_of_gt hcC
      have nN : ((r:ℚ)+b) ≠ 0 := by positivity
      field_simp
      linear_combination
        (-(↑((r+b-1).choose (b-L)) * ↑((r+b-1).choose (b-1)) : ℚ)) * hAq
        + (-(↑((r+b-1).choose b) * ↑((r+b-1).choose (b-1-L)) : ℚ)) * hBq
        + ((↑r + ↑b) * ↑((r+b-1).choose b) * ↑((r+b-1).choose (b-1)) : ℚ) * hPq

/-- The threshold-strategy value `W_L(r,b) = (r-b) + L·P_L(r,b)`. -/
def wL (L r b : ℕ) : ℚ := ((r : ℚ) - b) + L * PL L r b

/-- `W_L` satisfies the game's "continue-value" recursion. -/
theorem wL_mart (L r b : ℕ) :
    wL L (r+1) (b+1) = ((r:ℚ)+1)/((r:ℚ)+b+2) * (wL L r (b+1) + 1)
      + ((b:ℚ)+1)/((r:ℚ)+b+2) * (wL L (r+1) b - 1) := by
  have hpm := PL_mart L (r+1) (b+1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hpm
  unfold wL
  rw [hpm]
  have hden : ((r:ℚ)+1) + ((b:ℚ)+1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- At surplus exactly `L` (i.e. `b = r + L`) the strategy value vanishes. -/
theorem wL_bdry (L r : ℕ) : wL L r (r+L) = 0 := by
  unfold wL PL
  rw [if_pos (by omega : L ≤ r+L), show (r+L) - L = r by omega]
  have hsym : Nat.choose (r+(r+L)) r = Nat.choose (r+(r+L)) (r+L) := by
    rw [← Nat.choose_symm (by omega : r+L ≤ r+(r+L))]; congr 1; omega
  rw [hsym]
  have hpos : (0:ℚ) < (Nat.choose (r+(r+L)) (r+L) : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [div_self (ne_of_gt hpos)]
  push_cast; ring

theorem wL_zero_le (L b : ℕ) (h : b < L) : wL L 0 b ≤ 0 := by
  unfold wL PL
  rw [if_neg (by omega), mul_zero, add_zero]
  push_cast
  linarith [Nat.cast_nonneg (α := ℚ) b]

theorem wL_r_zero (L r : ℕ) : wL L r 0 = (r:ℚ) := by
  unfold wL PL
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  · rw [if_neg (by omega)]; push_cast; ring

/-- The strategy value is dominated by the equity: `W_L(r,b) ≤ e(r,b)` for
`b ≤ r + L`. Strong induction on `r + b`; in the stop region the bound is
`0 ≤ e`, in the continue region it is the recursion plus monotonicity. -/
theorem wL_le_e (L : ℕ) : ∀ n r b, r + b = n → b ≤ r + L → wL L r b ≤ e r b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r b hrb hbr
    rcases eq_or_lt_of_le hbr with hbe | hblt
    · rw [hbe, wL_bdry]; exact zero_le_e r (r+L)
    · rcases Nat.eq_zero_or_pos r with hr0 | hr1
      · subst hr0
        have he : e 0 b = 0 := by simp [e]
        rw [he]; exact wL_zero_le L b (by omega)
      · rcases Nat.eq_zero_or_pos b with hb0 | hb1
        · subst hb0
          rw [wL_r_zero]; simpa using sub_le_e r 0
        · obtain ⟨rp, rfl⟩ : ∃ rp, r = rp + 1 := ⟨r-1, by omega⟩
          obtain ⟨bp, rfl⟩ : ∃ bp, b = bp + 1 := ⟨b-1, by omega⟩
          rw [wL_mart, e_succ_succ]
          apply le_trans _ (le_max_right 0 _)
          have ih1 : wL L rp (bp+1) ≤ e rp (bp+1) :=
            ih (rp+(bp+1)) (by omega) rp (bp+1) rfl (by omega)
          have ih2 : wL L (rp+1) bp ≤ e (rp+1) bp :=
            ih ((rp+1)+bp) (by omega) (rp+1) bp rfl (by omega)
          have hc1 : (0:ℚ) ≤ ((rp:ℚ)+1)/((rp:ℚ)+bp+2) := by positivity
          have hc2 : (0:ℚ) ≤ ((bp:ℚ)+1)/((rp:ℚ)+bp+2) := by positivity
          have f1 := mul_le_mul_of_nonneg_left
            (show wL L rp (bp+1) + 1 ≤ e rp (bp+1) + 1 by linarith) hc1
          have f2 := mul_le_mul_of_nonneg_left
            (show wL L (rp+1) bp - 1 ≤ e (rp+1) bp - 1 by linarith) hc2
          linarith [f1, f2]

/-- Diagonal corollary: `e(n,n) ≥ L·C(2n,n-L)/C(2n,n)` for any `L ≤ n`. -/
theorem e_diag_ge (L n : ℕ) (hLn : L ≤ n) :
    (L : ℚ) * (Nat.choose (n+n) (n-L) : ℚ) / (Nat.choose (n+n) n : ℚ) ≤ e n n := by
  have h := wL_le_e L (n+n) n n rfl (by omega)
  unfold wL PL at h
  rw [if_pos hLn] at h
  rw [mul_div_assoc]
  linarith [h]

/-- Binomial ratio bound `C(2n,n-L)/C(2n,n) ≥ 1 - L²/n`, by induction on `L`
(each step is the elementary polynomial fact `2L³+3L²+3L+1 ≥ 0`). -/
theorem ratio_lb (n : ℕ) : ∀ L, L ≤ n →
    (1 : ℚ) - (L:ℚ)^2/n ≤ (Nat.choose (n+n) (n-L) : ℚ)/(Nat.choose (n+n) n) := by
  intro L
  induction L with
  | zero =>
    intro _
    have hpos : (0:ℚ) < (Nat.choose (n+n) n : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
    simp [div_self (ne_of_gt hpos)]
  | succ L ih =>
    intro hLn
    have hL : L ≤ n := by omega
    have ihL := ih hL
    have hnpos : (0:ℚ) < (n:ℚ) := by exact_mod_cast (by omega : 0 < n)
    have hRnn : (0:ℚ) < (Nat.choose (n+n) n : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
    have hrelN : Nat.choose (n+n) (n-L) * (n-L) = Nat.choose (n+n) (n-(L+1)) * (n+L+1) := by
      have h := Nat.choose_succ_right_eq (n+n) (n-L-1)
      rw [show n-L-1+1 = n-L by omega, show (n+n)-(n-L-1) = n+L+1 by omega] at h
      rw [show n-(L+1) = n-L-1 by omega]
      linarith [h]
    have hrel : (Nat.choose (n+n) (n-L) : ℚ) * ((n:ℚ)-L)
        = (Nat.choose (n+n) (n-(L+1)) : ℚ) * ((n:ℚ)+L+1) := by
      have hc : (Nat.choose (n+n) (n-L) : ℚ) * ((n-L:ℕ):ℚ)
          = (Nat.choose (n+n) (n-(L+1)) : ℚ) * ((n+L+1:ℕ):ℚ) := by exact_mod_cast hrelN
      rwa [Nat.cast_sub hL, show ((n+L+1:ℕ):ℚ) = (n:ℚ)+L+1 by push_cast; ring] at hc
    have hLn1 : ((n:ℚ)+L+1) > 0 := by positivity
    have key : (Nat.choose (n+n) (n-(L+1)) : ℚ)/(Nat.choose (n+n) n)
        = ((Nat.choose (n+n) (n-L) : ℚ)/(Nat.choose (n+n) n)) * (((n:ℚ)-L)/((n:ℚ)+L+1)) := by
      field_simp
      linarith [hrel]
    rw [key]
    have hfac : (0:ℚ) ≤ ((n:ℚ)-L)/((n:ℚ)+L+1) := by
      apply div_nonneg _ (le_of_lt hLn1)
      have : (L:ℚ) ≤ n := by exact_mod_cast hL
      linarith
    have hstep := mul_le_mul_of_nonneg_right ihL hfac
    refine le_trans ?_ hstep
    rw [← sub_nonneg]
    have hne1 : (n:ℚ) ≠ 0 := ne_of_gt hnpos
    have hne2 : (n:ℚ)+L+1 ≠ 0 := ne_of_gt hLn1
    have key2 : (1 - (L:ℚ)^2/n)*(((n:ℚ)-L)/((n:ℚ)+L+1)) - (1 - ((L:ℚ)+1)^2/n)
              = (2*(L:ℚ)^3 + 3*(L:ℚ)^2 + 3*(L:ℚ) + 1)/((n:ℚ)*((n:ℚ)+L+1)) := by
      field_simp
      ring
    rw [show ((L+1:ℕ):ℚ) = (L:ℚ)+1 by push_cast; ring, key2]
    positivity

/-- Polynomial diagonal bound: `e(n,n) ≥ L·(1 - L²/n)`. -/
theorem e_diag_poly (L n : ℕ) (hLn : L ≤ n) : (L:ℚ) * (1 - (L:ℚ)^2/n) ≤ e n n := by
  have h1 := e_diag_ge L n hLn
  have h2 := ratio_lb n L hLn
  have hL0 : (0:ℚ) ≤ (L:ℚ) := by positivity
  calc (L:ℚ) * (1 - (L:ℚ)^2/n)
      ≤ (L:ℚ) * ((Nat.choose (n+n) (n-L):ℚ)/(Nat.choose (n+n) n)) :=
        mul_le_mul_of_nonneg_left h2 hL0
    _ = (L:ℚ) * (Nat.choose (n+n) (n-L):ℚ) / (Nat.choose (n+n) n) := by rw [mul_div_assoc]
    _ ≤ e n n := h1

/-- Squared diagonal bound `e(r,r)² ≥ r/64` for `r ≥ 4` (take `L = ⌊√r⌋/2`). -/
theorem e_diag_sq (r : ℕ) (hr : 4 ≤ r) : (r:ℚ)/64 ≤ (e r r)^2 := by
  set a := Nat.sqrt r with ha
  set L := a/2 with hLdef
  have ha2 : a ^ 2 ≤ r := Nat.sqrt_le' r
  have ha2' : r < (a+1) ^ 2 := Nat.lt_succ_sqrt' r
  have haval : 2 ≤ a := by rw [ha]; exact Nat.le_sqrt.mpr (by omega)
  have h2L : 2*L ≤ a := by omega
  have haL : a ≤ 2*L+1 := by omega
  have hLge1 : 1 ≤ L := by omega
  have h4 : 4 * L^2 ≤ r := by nlinarith [ha2, Nat.mul_le_mul h2L h2L]
  have h36 : r ≤ 36 * L^2 := by nlinarith [ha2', haL, hLge1]
  have hLn : L ≤ r := by nlinarith [h4, hLge1]
  have hpoly := e_diag_poly L r hLn
  have hrq : (0:ℚ) < r := by exact_mod_cast (by omega : 0 < r)
  have h4q : 4 * (L:ℚ)^2 ≤ r := by exact_mod_cast h4
  have h36q : (r:ℚ) ≤ 36 * (L:ℚ)^2 := by exact_mod_cast h36
  have hfrac : (L:ℚ)^2/r ≤ 1/4 := by rw [div_le_iff₀ hrq]; linarith [h4q]
  have hL0 : (0:ℚ) ≤ (L:ℚ) := by positivity
  have hlow : (3:ℚ)/4 * L ≤ e r r := by
    calc (3:ℚ)/4 * L ≤ (1 - (L:ℚ)^2/r) * L := by nlinarith [hfrac, hL0]
      _ = (L:ℚ)*(1 - (L:ℚ)^2/r) := by ring
      _ ≤ e r r := hpoly
  have hnn : (0:ℚ) ≤ e r r := by exact_mod_cast zero_le_e r r
  nlinarith [hlow, hnn, h36q,
    mul_nonneg (by linarith [hlow] : (0:ℚ) ≤ e r r - 3/4*(L:ℚ))
               (by linarith [hnn, hL0] : (0:ℚ) ≤ e r r + 3/4*(L:ℚ))]

/-- Diagonal `√r` lower bound: `e(r,r) ≥ (1/8)·√r`. -/
theorem e_diag_sqrt (r : ℕ) : (1/8 : ℝ) * Real.sqrt r ≤ (e r r : ℝ) := by
  have hsle : ∀ x : ℝ, x ≤ 4 → Real.sqrt x ≤ 2 := by
    intro x hx
    have h := Real.sqrt_le_sqrt hx
    rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  rcases Nat.lt_or_ge r 4 with hr | hr
  · interval_cases r
    · simpa using zero_le_e 0 0
    · rw [show ((1:ℕ):ℝ) = 1 by norm_num, Real.sqrt_one]
      have hp : (1:ℚ)/2 ≤ e 1 1 := by
        have h := e_diag_ge 1 1 (by norm_num)
        norm_num [Nat.choose] at h; linarith [h]
      have hpℝ : (1:ℝ)/2 ≤ (e 1 1 : ℝ) := by
        have := Rat.cast_le (K := ℝ) |>.mpr hp; push_cast at this; exact this
      linarith [hpℝ]
    · have hp : (1:ℚ)/2 ≤ e 2 2 := by have := e_diag_poly 1 2 (by norm_num); linarith [this]
      have hpℝ : (1:ℝ)/2 ≤ (e 2 2 : ℝ) := by
        have := Rat.cast_le (K := ℝ) |>.mpr hp; push_cast at this; exact this
      push_cast
      nlinarith [hsle 2 (by norm_num), hpℝ, Real.sqrt_nonneg (2:ℝ)]
    · have hp : (2:ℚ)/3 ≤ e 3 3 := by have := e_diag_poly 1 3 (by norm_num); linarith [this]
      have hpℝ : (2:ℝ)/3 ≤ (e 3 3 : ℝ) := by
        have := Rat.cast_le (K := ℝ) |>.mpr hp; push_cast at this; exact this
      push_cast
      nlinarith [hsle 3 (by norm_num), hpℝ, Real.sqrt_nonneg (3:ℝ)]
  · have hsq : (r:ℝ)/64 ≤ (e r r : ℝ)^2 := by
      calc (r:ℝ)/64 = (((r:ℚ)/64 : ℚ) : ℝ) := by push_cast; ring
        _ ≤ (((e r r)^2 : ℚ) : ℝ) := by exact_mod_cast e_diag_sq r hr
        _ = (e r r:ℝ)^2 := by push_cast; ring
    have hnn : (0:ℝ) ≤ (e r r : ℝ) := by exact_mod_cast zero_le_e r r
    have h8 : (0:ℝ) ≤ (1/8 : ℝ) * Real.sqrt r := by positivity
    have hpow : ((1/8:ℝ)*Real.sqrt r)^2 ≤ (e r r:ℝ)^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (r:ℝ))]; linarith [hsq]
    calc (1/8:ℝ)*Real.sqrt r = Real.sqrt (((1/8:ℝ)*Real.sqrt r)^2) := (Real.sqrt_sq h8).symm
      _ ≤ Real.sqrt ((e r r:ℝ)^2) := Real.sqrt_le_sqrt hpow
      _ = e r r := Real.sqrt_sq hnn

/-- Below-threshold positivity: `e(r,b) > 0` whenever `b < r + (1/8)·√r`.
Complementary to the zero region `b > r + 4·√r` of `question`. -/
theorem e_pos_below (r b : ℕ) (hb : (b : ℝ) < r + (1 / 8) * Real.sqrt r) : 0 < e r b :=
  e_pos_below_threshold_of_diag (e_diag_sqrt r) hb
