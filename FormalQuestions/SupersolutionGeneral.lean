import FormalQuestions.ProblemFourteen

/-!
# A general supersolution theorem for the barrier `phiBar K c`

`ProblemFourteen` proves `IsSupersolution (phiBar 91 137)` with a bespoke
certificate, giving the zero region `{ b ≥ r + 137·√r }`. Here we abstract that
argument: we isolate the polynomial constraints on the two parameters `K` (the
normalisation) and `c` (the width constant) under which `phiBar K c` is a
supersolution, and prove the resulting **general theorem** `phiBar_isSupersolution_of`.

The genuinely `(K,c)`-dependent input is the *layer inequality* `hlayer` (the
square-root-cleared supersolution defect in the diffusive layer). Everything else
reduces to four explicit polynomial side-conditions:

* `0 < K`                                  – positivity of the barrier;
* `K ≤ 2*c`                                – the bulk ≤ layer-form bound;
* `1 ≤ c*(K-1)`                            – the far-field bound;
* `K^2 - 8*K*c + 2*K + 4*c^2 + 16*c + 13 ≤ 0` – the `r = 0` base case
  (which already forces `c ≥ 1 + √2`).

Instantiating with `(K,c) = (91,137)` recovers `ProblemFourteen`'s result; with
`(K,c) = (6,4)` we obtain the far stronger zero region `{ b ≥ r + 4·√r }`.
-/

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
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg c) (by positivity)) (by linarith [hs])) (le_of_lt hK0)
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
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (r : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) r])
    rwa [Real.sqrt_one] at h
  have htsq : Real.sqrt ((r : ℝ) + 1) ^ 2 = (r : ℝ) + 1 :=
    Real.sq_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) r])
  have hfar' := hfar
  push_cast at hfar'
  have hC : phiBar K c (r + 1) (b + 1) = 0 := phiBar_far hfar
  have hA0 : (↑r : ℝ) + c * Real.sqrt ↑r - ↑(b + 1) ≤ 0 := by
    push_cast
    nlinarith [hfar', mul_nonneg hc0 (by linarith [hs01] : (0:ℝ) ≤ Real.sqrt ((r:ℝ)+1) - Real.sqrt r)]
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
      have hd1 : ↑r + 1 + c * Real.sqrt ((r : ℝ) + 1) - ↑b ≤ 1 := by linarith [hfar']
      have hdsq : (↑r + 1 + c * Real.sqrt ((r : ℝ) + 1) - ↑b) ^ 2 ≤ 1 := by
        nlinarith [hD0, hd1]
      have hb1 : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
      have hstep1 : ((b : ℝ) + 1) * (↑r + 1 + c * Real.sqrt ((r : ℝ) + 1) - ↑b) ^ 2 ≤ (b : ℝ) + 1 := by
        nlinarith [mul_nonneg hb1 (by linarith [hdsq] :
          (0 : ℝ) ≤ 1 - (↑r + 1 + c * Real.sqrt ((r : ℝ) + 1) - ↑b) ^ 2)]
      have hbr2 : c * Real.sqrt ((r : ℝ) + 1) ≤ ↑b - ↑r := by linarith [hd1]
      have hfin : (b : ℝ) + 1 ≤ (↑b - ↑r) * (K * Real.sqrt ((r : ℝ) + 1)) := by
        nlinarith [htsq, ht1, hbr2, hc0,
          mul_nonneg (sub_nonneg.mpr hbr2)
            (by nlinarith [ht1, hK1] : (0:ℝ) ≤ K * Real.sqrt ((r:ℝ) + 1) - 1),
          mul_nonneg (sq_nonneg (Real.sqrt ((r:ℝ) + 1))) (sub_nonneg.mpr hcK1),
          mul_nonneg (mul_nonneg hc0 (Real.sqrt_nonneg ((r:ℝ) + 1)))
            (by linarith [ht1] : (0:ℝ) ≤ Real.sqrt ((r:ℝ) + 1) - 1)]
      linarith [hstep1, hfin]
  rw [hC, hA]
  simp only [div_mul_eq_mul_div, zero_add]
  rw [← add_div, div_le_iff₀ hN]
  nlinarith [hkey]

/-- Divided form of the all-layer supersolution inequality, generic in `(K,c)`.
The genuinely parameter-dependent content is the hypothesis `hcore`, namely the
square-root-cleared layer defect `0 ≤ F(s,t,bb-s²)`. -/
theorem layer_div_ineq_of {K c s t rr bb : ℝ} (hK0 : 0 < K) (hs : 1 ≤ s) (ht0 : 0 < t)
    (ht2 : t ^ 2 = s ^ 2 + 1) (hrr : rr = s ^ 2) (hN : 0 < rr + bb + 2)
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
      · nlinarith [sq_nonneg (6 * (b:ℝ) + (K - 4 * c + 1)), hr0]
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
        (t := Real.sqrt ((r:ℝ) + 1)) (rr := (r:ℝ)) (bb := (b:ℝ)) hK0 hs1 ht0 ht2 hsq.symm
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
      have hbr : (b : ℝ) ≤ r := le_of_lt (not_le.mp h2)
      linarith
  case zero_left =>
    intro b
    have hD : (↑(0 : ℕ) : ℝ) + c * Real.sqrt ↑(0 : ℕ) - (b : ℝ) ≤ 0 := by
      simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add, zero_sub, Left.neg_nonpos_iff]
      positivity
    unfold phiBar
    rw [if_pos hD]
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

/-! ### Instance 1: the original `(K,c) = (91,137)` -/

/-- `ProblemFourteen`'s result, re-derived from the general theorem: the layer
inequality is exactly the bespoke `layer_core`. -/
theorem phiBar_isSupersolution_91_137 : IsSupersolution (phiBar 91 137) := by
  refine phiBar_isSupersolution_of (K := 91) (c := 137) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_
  intro s t w hs hw ht ht2
  exact layer_core hs hw ht ht2

/-! ### Instance 2: the much smaller `(K,c) = (6,4)`

The certificate is regenerated for `(4,6)`: `c₄ = 3s⁴+6s²-1` is parameter-free
(reused), and the two Schur complements `H₂`, `H₃` are new degree-10 / degree-18
polynomials, both with nonnegative coefficients after the shift `s = 1+u`. -/

theorem hard_H2_pos_6_4 {s : ℝ} (hs : 1 ≤ s) :
    0 < 704*s^10 - 80*s^9 + 2596*s^8 - 400*s^7 + 2580*s^6 - 560*s^5 + 324*s^4
      - 240*s^3 - 356*s^2 + 8 := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ s = 1 + u := ⟨s - 1, by linarith, by ring⟩
  nlinarith [hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5,
    pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8, pow_nonneg hu 9, pow_nonneg hu 10]

theorem hard_H3_nonneg_6_4 {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ 122880*s^18 - 30720*s^17 + 823872*s^16 - 216768*s^15 + 2188976*s^14
      - 605024*s^13 + 2904272*s^12 - 866912*s^11 + 1905652*s^10 - 676576*s^9
      + 405640*s^8 - 272064*s^7 - 148248*s^6 - 42464*s^5 - 62368*s^4 + 992*s^3
      + 2164*s^2 + 32*s + 8 := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ s = 1 + u := ⟨s - 1, by linarith, by ring⟩
  nlinarith [hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5,
    pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8, pow_nonneg hu 9, pow_nonneg hu 10,
    pow_nonneg hu 11, pow_nonneg hu 12, pow_nonneg hu 13, pow_nonneg hu 14, pow_nonneg hu 15,
    pow_nonneg hu 16, pow_nonneg hu 17, pow_nonneg hu 18]

theorem hard_G_nonneg_6_4 {s w : ℝ} (hs : 1 ≤ s) :
    0 ≤ (16*s^5 + 31*s^3 + 15*s + w^2*(s^3+3*s) + w*(2*s^3+s))^2
      - (s^2+1)*(16*s^4 + 17*s^2 + w^2*(s^2+1) + w*(2*s^2+2*s+2) + 1)^2 := by
  have hc4 : 0 < 3*s^4 + 6*s^2 - 1 := hard_c4_pos hs
  have hH2 : 0 < 704*s^10 - 80*s^9 + 2596*s^8 - 400*s^7 + 2580*s^6 - 560*s^5 + 324*s^4
      - 240*s^3 - 356*s^2 + 8 := hard_H2_pos_6_4 hs
  have hH3 : 0 ≤ 122880*s^18 - 30720*s^17 + 823872*s^16 - 216768*s^15 + 2188976*s^14
      - 605024*s^13 + 2904272*s^12 - 866912*s^11 + 1905652*s^10 - 676576*s^9
      + 405640*s^8 - 272064*s^7 - 148248*s^6 - 42464*s^5 - 62368*s^4 + 992*s^3
      + 2164*s^2 + 32*s + 8 := hard_H3_nonneg_6_4 hs
  nlinarith [mul_nonneg hH2.le (sq_nonneg (2*(3*s^4+6*s^2-1)*w^2
      + (-4*s^5 + 2*s^4 - 8*s^3 - 6*s^2 - 4*s - 4)*w)),
    sq_nonneg ((704*s^10 - 80*s^9 + 2596*s^8 - 400*s^7 + 2580*s^6 - 560*s^5 + 324*s^4
        - 240*s^3 - 356*s^2 + 8)*w
      + 2*(3*s^4+6*s^2-1)*(-64*s^7 - 40*s^6 - 132*s^5 - 82*s^4 - 72*s^3 - 46*s^2 - 4*s - 4)),
    mul_nonneg (by linarith : (0:ℝ) ≤ 4*(3*s^4+6*s^2-1)) hH3,
    mul_pos (by linarith : (0:ℝ) < 4*(3*s^4+6*s^2-1)) hH2]

/-- Layer inequality for `(K,c) = (6,4)`: removes the square root from
`hard_G_nonneg_6_4`, exactly as `layer_core` does for `(91,137)`. -/
theorem layer_core_6_4 {s t w : ℝ} (hs : 1 ≤ s) (hw : 0 ≤ w) (ht0 : 0 ≤ t)
    (ht2 : t ^ 2 = s ^ 2 + 1) :
    0 ≤ s * (4*t - w) ^ 2 * (2*s^2 + w + 2)
        - (s^2 + 1) * (t * (4*s - w - 1) ^ 2 + 6*s*t)
        - (s^2 + w + 1) * (s * (4*t - w + 1) ^ 2 - 6*s*t) := by
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

/-- **Improved zero region.** Since `phiBar 6 4` is a (global) supersolution, the
equity vanishes already on `{ b > r + 4·√r }` — for *all* `r, b`, with no lower
bound on `r`. This is far stronger than `question`'s `b > r + 137·√r`. -/
theorem question_4 (r b : ℕ) (hb : (b : ℝ) > r + 4 * Real.sqrt r) : e r b = 0 := by
  have hle : (e r b : ℝ) ≤ phiBar 6 4 r b :=
    e_le_of_supersolution phiBar_isSupersolution_6_4 r b
  have hfar : phiBar 6 4 r b = 0 :=
    phiBar_far (show (r : ℝ) + 4 * Real.sqrt r - b ≤ 0 by linarith)
  have hge : (0 : ℝ) ≤ (e r b : ℝ) := by exact_mod_cast zero_le_e r b
  have : (e r b : ℝ) = 0 := le_antisymm (hfar ▸ hle) hge
  exact_mod_cast this
