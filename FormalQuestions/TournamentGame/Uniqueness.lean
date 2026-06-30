import FormalQuestions.TournamentGame.Basic

/-!

This file contains an autoformalization of
(the uniqueness half of)
the proof provded by Will Sawin in this mathoverflow answer:

<https://mathoverflow.net/a/506379/113060>.

The proof is licensed under CC-BY-SA 4.0,

<https://creativecommons.org/licenses/by-sa/4.0/>

-/

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option backward.isDefEq.respectTransparency false in
/-- The identity matrix with one row replaced by all ones has determinant `1`. -/
theorem det_one_updateRow_ones (i0 : V) :
    ((1 : Matrix V V (ZMod 2)).updateRow i0 (fun _ => 1)).det = 1 := by
  have h : (1 : Matrix V V (ZMod 2)).updateRow i0 (fun _ => 1)
      = 1 + Matrix.replicateCol (Fin 1) (Pi.single i0 (1 : ZMod 2)) *
          Matrix.replicateRow (Fin 1) (fun b => if b = i0 then (0 : ZMod 2) else 1) := by
    ext a b
    rcases eq_or_ne a i0 with rfl | ha <;> rcases eq_or_ne a b with rfl | hab <;>
      simp_all [Matrix.updateRow, Function.update, Matrix.one_apply, Matrix.mul_apply,
        Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.single_apply] <;> tauto
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]

/-- Adding row `i0` to each row in a finset `s` not containing `i0` preserves the determinant. -/
theorem det_addRow {R : Type*} [CommRing R] (A : Matrix V V R) (i0 : V) (s : Finset V)
    (hi0 : i0 ∉ s) :
    (Matrix.of (fun a => if a ∈ s then A a + A i0 else A a)).det = A.det := by
  induction s using Finset.induction with
  | empty => rfl
  | insert x s hx ih =>
    rw [Finset.mem_insert, not_or] at hi0
    obtain ⟨hxne, hs⟩ := hi0
    set B := Matrix.of (fun a => if a ∈ s then A a + A i0 else A a) with hB
    have key : (Matrix.of (fun a => if a ∈ insert x s then A a + A i0 else A a))
        = B.updateRow x (B x + B i0) := by
      ext a b
      rcases eq_or_ne a x with rfl | hax
      · simp [hB, Matrix.updateRow, Function.update, hx, hs, hxne]
      · simp only [Matrix.of_apply, Finset.mem_insert, Matrix.updateRow, Function.update,
          hax, hB]
        simp [hax, (by tauto : (a = x ∨ a ∈ s) ↔ a ∈ s)]
    rw [key, Matrix.det_updateRow_add_self B (fun h => hxne h.symm), ih hs]

/-- The mod-2 reduction of a tournament payoff matrix with its `i0`-th row replaced by all ones
has determinant `1`. -/
theorem det_C_eq_one (i0 : V) :
    (Matrix.of (fun a b : V => if a = i0 then (1 : ZMod 2) else if a = b then 0 else 1)).det = 1 := by
  set C := Matrix.of (fun a b : V => if a = i0 then (1 : ZMod 2) else if a = b then 0 else 1)
    with hC
  have hreduce : (Matrix.of (fun a => if a ∈ univ.erase i0 then C a + C i0 else C a)).det
      = C.det := det_addRow C i0 (univ.erase i0) (by simp)
  have heq : (Matrix.of (fun a => if a ∈ univ.erase i0 then C a + C i0 else C a))
      = (1 : Matrix V V (ZMod 2)).updateRow i0 (fun _ => 1) := by
    ext a b
    rcases eq_or_ne a i0 with rfl | ha
    · simp [hC, Matrix.updateRow, Function.update]
    · rcases eq_or_ne a b with rfl | hab <;>
        simp_all [hC, Matrix.updateRow, Function.update, Matrix.one_apply, mem_erase] <;>
        decide
  rw [heq] at hreduce
  rw [← hreduce, det_one_updateRow_ones]

/-- **Crux.** For a tournament payoff matrix `M` (zero diagonal, `±1` off-diagonal), replacing
its `i0`-th row by all ones yields a nonsingular matrix. Proved by reducing mod 2. -/
theorem tournament_updateRow_det_ne_zero (M : Matrix V V ℝ) (i0 : V)
    (hdiag : ∀ a, M a a = 0) (hoff : ∀ a b, a ≠ b → M a b = 1 ∨ M a b = -1) :
    (M.updateRow i0 (fun _ => 1)).det ≠ 0 := by
  set Bz : Matrix V V ℤ := Matrix.of
    (fun a b => if a = i0 then 1 else if a = b then 0 else (if M a b = 1 then 1 else -1))
    with hBz
  have hcast : M.updateRow i0 (fun _ => 1) = Bz.map (fun x => (x : ℝ)) := by
    ext a b
    rcases eq_or_ne a i0 with rfl | ha
    · simp [hBz, Matrix.updateRow, Function.update]
    · rcases eq_or_ne a b with rfl | hab
      · simp [hBz, Matrix.updateRow, Function.update, ha, hdiag]
      · rcases hoff a b hab with h1 | h1 <;>
          simp [hBz, Matrix.updateRow, Function.update, ha, hab, h1]
  rw [hcast, ← Int.cast_det]
  have hint : Bz.det ≠ 0 := by
    intro h
    have h2 : (Bz.det : ZMod 2) = 0 := by rw [h]; simp
    rw [Int.cast_det] at h2
    have hCeq : (Bz.map (fun x => (x : ZMod 2)))
        = Matrix.of (fun a b : V => if a = i0 then (1 : ZMod 2) else if a = b then 0 else 1) := by
      ext a b
      rcases eq_or_ne a i0 with rfl | ha
      · simp [hBz]
      · rcases eq_or_ne a b with rfl | hab
        · simp [hBz, ha]
        · rcases hoff a b hab with h1 | h1 <;> simp [hBz, ha, hab, h1] <;> decide
    rw [hCeq, det_C_eq_one] at h2
    exact one_ne_zero h2
  exact_mod_cast hint

/-- For a tournament payoff matrix `M`, the only vector `w` with `M.mulVec w = 0` and zero
coordinate sum is `w = 0`. -/
theorem tournament_kernel_trivial [Nonempty V] (M : Matrix V V ℝ)
    (hdiag : ∀ a, M a a = 0) (hoff : ∀ a b, a ≠ b → M a b = 1 ∨ M a b = -1)
    (w : V → ℝ) (hMw : M.mulVec w = 0) (hsum : ∑ a, w a = 0) : w = 0 := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty V›
  set B := M.updateRow i0 (fun _ => 1) with hB
  have hBw : B.mulVec w = 0 := by
    funext a
    rcases eq_or_ne a i0 with rfl | ha
    · simp only [hB, Matrix.mulVec, dotProduct, Matrix.updateRow_self, Pi.zero_apply]
      simpa [one_mul] using hsum
    · have : B.mulVec w a = M.mulVec w a := by
        simp [hB, Matrix.mulVec, dotProduct, Matrix.updateRow_ne ha]
      rw [this, hMw]
  have hdet : B.det ≠ 0 := tournament_updateRow_det_ne_zero M i0 hdiag hoff
  by_contra hw
  exact (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, hBw⟩ ▸ hdet) rfl

/-- Support version: if `M.mulVec w` vanishes wherever `w` does not, and the coordinates of `w`
sum to zero, then `w = 0`. Proved by restricting to the (finite) support of `w`. -/
theorem tournament_kernel_support (M : Matrix V V ℝ)
    (hdiag : ∀ a, M a a = 0) (hoff : ∀ a b, a ≠ b → M a b = 1 ∨ M a b = -1)
    (w : V → ℝ) (hsum : ∑ a, w a = 0)
    (hzero : ∀ a, w a ≠ 0 → M.mulVec w a = 0) : w = 0 := by
  classical
  set S : Finset V := univ.filter (fun a => w a ≠ 0) with hS
  have hoffS : ∀ a, a ∉ S → w a = 0 := by
    intro a ha; by_contra h; exact ha (by simp [hS, h])
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · funext a; exact hoffS a (by rw [hSe]; exact Finset.notMem_empty a)
  · haveI : Nonempty {a // a ∈ S} := hSne.to_subtype
    set cv : {a // a ∈ S} → V := Subtype.val with hcv
    set M' : Matrix {a // a ∈ S} {a // a ∈ S} ℝ := M.submatrix cv cv with hM'
    set w' : {a // a ∈ S} → ℝ := fun a => w a.1 with hw'
    have hmulvec : M'.mulVec w' = 0 := by
      funext a
      obtain ⟨a, ha⟩ := a
      have haw : w a ≠ 0 := by simpa [hS] using ha
      have e1 : M'.mulVec w' ⟨a, ha⟩ = ∑ b ∈ S, M a b * w b := by
        simp only [hM', hcv, Matrix.mulVec, Matrix.submatrix_apply, dotProduct, hw']
        exact Finset.sum_coe_sort S (fun b => M a b * w b)
      have e2 : M.mulVec w a = ∑ b ∈ S, M a b * w b := by
        simp only [Matrix.mulVec, dotProduct]
        refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intro b _ hb
        rw [hoffS b hb, mul_zero]
      have : M'.mulVec w' ⟨a, ha⟩ = 0 := by
        rw [e1, ← e2]; exact hzero a haw
      simpa using this
    have hsum' : ∑ a, w' a = 0 := by
      rw [hw']
      rw [Finset.sum_coe_sort S (fun a => w a)]
      rw [Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => hoffS b hb)]
      exact hsum
    have hker := tournament_kernel_trivial M'
      (fun a => hdiag _) (fun a b hab => hoff _ _ (fun h => hab (Subtype.ext h))) w' hmulvec hsum'
    funext a
    by_cases ha : a ∈ S
    · have := congrFun hker ⟨a, ha⟩; simpa [hw'] using this
    · exact hoffS a ha

/-- The bilinear form of an antisymmetric matrix is antisymmetric. -/
theorem dotProduct_mulVec_antisymm (M : Matrix V V ℝ) (hanti : ∀ a b, M a b = - M b a)
    (u v : V → ℝ) : u ⬝ᵥ M.mulVec v = - (v ⬝ᵥ M.mulVec u) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have h := hanti b a
  rw [h]; ring

/-- **Step C.** For a tournament payoff matrix, there is at most one probability vector `x`
with `M.mulVec x ≤ 0`. (Such `x` are exactly the optimal/equilibrium strategies.) -/
theorem tournament_optimal_unique (M : Matrix V V ℝ)
    (hanti : ∀ a b, M a b = -M b a) (hoff : ∀ a b, a ≠ b → M a b = 1 ∨ M a b = -1)
    (x y : V → ℝ) (hx0 : ∀ a, 0 ≤ x a) (hy0 : ∀ a, 0 ≤ y a)
    (hxsum : ∑ a, x a = 1) (hysum : ∑ a, y a = 1)
    (hMx : ∀ a, M.mulVec x a ≤ 0) (hMy : ∀ a, M.mulVec y a ≤ 0) :
    x = y := by
  have hdiag : ∀ a, M a a = 0 := by intro a; have := hanti a a; linarith
  -- A nonneg vector against a nonpositive image has nonpositive bilinear value.
  have hle : ∀ (u v : V → ℝ), (∀ a, 0 ≤ u a) → (∀ a, M.mulVec v a ≤ 0) →
      u ⬝ᵥ M.mulVec v ≤ 0 := by
    intro u v hu hv
    rw [dotProduct]
    exact Finset.sum_nonpos (fun a _ => mul_nonpos_of_nonneg_of_nonpos (hu a) (hv a))
  -- The bilinear value of each pairing is zero.
  have key : ∀ (u v : V → ℝ), (∀ a, 0 ≤ u a) → (∀ a, M.mulVec v a ≤ 0) →
      u ⬝ᵥ M.mulVec v = 0 → ∀ a, u a ≠ 0 → M.mulVec v a = 0 := by
    intro u v hu hv hzero a hua
    have hnn : ∀ b ∈ (univ : Finset V), 0 ≤ -(u b * M.mulVec v b) := fun b _ =>
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hu b) (hv b))
    have hs0 : ∑ b, -(u b * M.mulVec v b) = 0 := by
      rw [Finset.sum_neg_distrib]
      rw [show ∑ b, u b * M.mulVec v b = u ⬝ᵥ M.mulVec v from rfl, hzero, neg_zero]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs0 a (mem_univ a)
    have h2 : u a * M.mulVec v a = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hua
    · exact h
  -- the four vanishing facts
  have hxMy : x ⬝ᵥ M.mulVec y = 0 := by
    have h1 := hle x y hx0 hMy
    have h2 := dotProduct_mulVec_antisymm M hanti x y
    have h3 := hle y x hy0 hMx
    linarith [h2, h1, h3]
  have hyMx : y ⬝ᵥ M.mulVec x = 0 := by
    have h2 := dotProduct_mulVec_antisymm M hanti x y
    linarith [hxMy]
  have hxMx : x ⬝ᵥ M.mulVec x = 0 := by
    have h2 := dotProduct_mulVec_antisymm M hanti x x
    linarith
  have hyMy : y ⬝ᵥ M.mulVec y = 0 := by
    have h2 := dotProduct_mulVec_antisymm M hanti y y
    linarith
  -- assemble w = x - y in the kernel on its support
  set w : V → ℝ := x - y with hw
  have hsumw : ∑ a, w a = 0 := by
    simp only [hw, Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hxsum, hysum, sub_self]
  have hzero : ∀ a, w a ≠ 0 → M.mulVec w a = 0 := by
    intro a hwa
    have hor : x a ≠ 0 ∨ y a ≠ 0 := by
      by_contra h; push_neg at h
      apply hwa; simp [hw, h.1, h.2]
    have hMxa : M.mulVec x a = 0 := by
      rcases hor with hx | hy
      · exact key x x hx0 hMx hxMx a hx
      · exact key y x hy0 hMx hyMx a hy
    have hMya : M.mulVec y a = 0 := by
      rcases hor with hx | hy
      · exact key x y hx0 hMy hxMy a hx
      · exact key y y hy0 hMy hyMy a hy
    have : M.mulVec w a = M.mulVec x a - M.mulVec y a := by
      simp [hw, Matrix.mulVec_sub, Pi.sub_apply]
    rw [this, hMxa, hMya, sub_zero]
  have : w = 0 := tournament_kernel_support M hdiag hoff w hsumw hzero
  rw [hw] at this
  exact sub_eq_zero.mp (by rw [← this])

section Game
variable {A : Type} [Fintype A] [DecidableEq A] (G : UniformActionNormalFormGame (Fin 2) A)

/-- The payoff matrix of the game (player 0's payoff). -/
def Mtg : Matrix A A ℝ := fun a b => G.payoff 0 ![a, b]

set_option backward.isDefEq.respectTransparency false in
/-- Player 0's mixed payoff is the bilinear form of the payoff matrix. -/
theorem payoff0_eq (profile : Fin 2 → PMF A) :
    G.toMixedGame.payoff 0 profile
      = (fun a => (profile 0 a).toReal) ⬝ᵥ (Mtg G).mulVec (fun b => (profile 1 b).toReal) := by
  simp only [UniformActionNormalFormGame.toMixedGame, dotProduct, Matrix.mulVec, Mtg,
    Finset.mul_sum]
  rw [tsum_fintype, ← Equiv.sum_comp (piFinTwoEquiv (fun _ => A)).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp only [piFinTwoEquiv, Equiv.coe_fn_symm_mk]
  rw [show (Fin.cons a (Fin.cons b finZeroElim) : Fin 2 → A) = ![a, b] from rfl,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- For a zero-sum game, player 1's mixed payoff is the negation of player 0's. -/
theorem payoff1_eq (hzs : ∀ actions, G.payoff 0 actions = - G.payoff 1 actions)
    (profile : Fin 2 → PMF A) :
    G.toMixedGame.payoff 1 profile = - G.toMixedGame.payoff 0 profile := by
  simp only [UniformActionNormalFormGame.toMixedGame]
  rw [← tsum_neg]
  refine tsum_congr (fun prof => ?_)
  have h := hzs prof
  rw [h]; ring

/-- The coordinates of (the real form of) a `PMF` over a fintype sum to `1`. -/
theorem pmf_sum_toReal (σ : PMF A) : ∑ a, (σ a).toReal = 1 := by
  have h : (∑ a, σ a) = 1 := (tsum_fintype (σ ·)).symm.trans (PMF.tsum_coe σ)
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top σ a), h, ENNReal.toReal_one]

theorem pmf_pure_toReal (b a : A) : ((PMF.pure b) a).toReal = if a = b then 1 else 0 := by
  simp [PMF.pure_apply, apply_ite ENNReal.toReal]

/-- **Step B.** In any mixed Nash equilibrium of a zero-sum game whose payoff matrix is
antisymmetric, both players' strategies `x` satisfy `M.mulVec x ≤ 0`. -/
theorem mixedNash_mulVec_nonpos
    (hzs : ∀ actions, G.payoff 0 actions = - G.payoff 1 actions)
    (hanti : ∀ a b, (Mtg G) a b = - (Mtg G) b a)
    (profile : Fin 2 → PMF A)
    (hNash : G.toMixedGame.IsNashEquilibrium profile) :
    (∀ a, (Mtg G).mulVec (fun b => (profile 1 b).toReal) a ≤ 0) ∧
    (∀ a, (Mtg G).mulVec (fun b => (profile 0 b).toReal) a ≤ 0) := by
  set M := Mtg G
  set xv := fun a => (profile 0 a).toReal with hxv
  set yv := fun a => (profile 1 a).toReal with hyv
  -- payoff of profiles obtained by deviation
  have pu0 : ∀ a' : PMF A, G.toMixedGame.payoff 0 (Function.update profile 0 a')
      = (fun a => (a' a).toReal) ⬝ᵥ M.mulVec yv := by
    intro a'
    rw [payoff0_eq]
    have e0 : Function.update profile 0 a' 0 = a' := by simp
    have e1 : Function.update profile 0 a' 1 = profile 1 := by
      rw [Function.update_of_ne (by decide)]
    rw [e0, e1]
  have pu1 : ∀ a' : PMF A, G.toMixedGame.payoff 0 (Function.update profile 1 a')
      = xv ⬝ᵥ M.mulVec (fun b => (a' b).toReal) := by
    intro a'
    rw [payoff0_eq]
    have e0 : Function.update profile 1 a' 0 = profile 0 := by
      rw [Function.update_of_ne (by decide)]
    have e1 : Function.update profile 1 a' 1 = a' := by simp
    rw [e0, e1]
  -- the bilinear value
  have hval0 := payoff0_eq G profile
  set Val := xv ⬝ᵥ M.mulVec yv with hVal
  -- Nash conditions, specialised
  have N0 : ∀ a' : PMF A, (fun a => (a' a).toReal) ⬝ᵥ M.mulVec yv ≤ Val := by
    intro a'
    have := hNash 0 a'
    rw [pu0 a', hval0] at this
    exact this
  have N1 : ∀ a' : PMF A, Val ≤ xv ⬝ᵥ M.mulVec (fun b => (a' b).toReal) := by
    intro a'
    have := hNash 1 a'
    rw [payoff1_eq G hzs, payoff1_eq G hzs, pu1 a', hval0] at this
    linarith
  -- value is 0
  have hyMy : yv ⬝ᵥ M.mulVec yv = 0 := by
    have := dotProduct_mulVec_antisymm M hanti yv yv; linarith
  have hxMx : xv ⬝ᵥ M.mulVec xv = 0 := by
    have := dotProduct_mulVec_antisymm M hanti xv xv; linarith
  have hge : 0 ≤ Val := by have := N0 (profile 1); rw [← hyv] at this; linarith [hyMy]
  have hle : Val ≤ 0 := by have := N1 (profile 0); rw [← hxv] at this; linarith [hxMx]
  have hVal0 : Val = 0 := le_antisymm hle hge
  -- indicator helpers
  have hdotInd : ∀ (z : A → ℝ) (b : A), (fun a => if a = b then (1:ℝ) else 0) ⬝ᵥ z = z b := by
    intro z b
    simp [dotProduct, Finset.sum_ite_eq']
  have hmulInd : ∀ b : A, M.mulVec (fun a => if a = b then (1:ℝ) else 0) = fun c => M c b := by
    intro b
    funext c
    simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · -- M.mulVec yv a ≤ 0
    have := N0 (PMF.pure a)
    simp only [pmf_pure_toReal] at this
    rw [hdotInd] at this
    linarith [hVal0]
  · -- M.mulVec xv a ≤ 0
    have := N1 (PMF.pure a)
    simp only [pmf_pure_toReal] at this
    rw [hmulInd] at this
    -- this : Val ≤ xv ⬝ᵥ (fun c => M c a)
    have hcol : xv ⬝ᵥ (fun c => M c a) = - M.mulVec xv a := by
      simp only [dotProduct, Matrix.mulVec]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hanti c a]; ring
    rw [hcol] at this
    linarith [hVal0]

/-- **Uniqueness of the mixed Nash equilibrium** for a symmetric zero-sum game whose payoff
matrix is an (antisymmetric, `±1` off-diagonal) tournament matrix. -/
theorem subsingleton_mixedNash
    (hzs : ∀ actions, G.payoff 0 actions = - G.payoff 1 actions)
    (hanti : ∀ a b, (Mtg G) a b = - (Mtg G) b a)
    (hoff : ∀ a b, a ≠ b → (Mtg G) a b = 1 ∨ (Mtg G) a b = -1)
    (p q : Fin 2 → PMF A)
    (hp : G.IsMixedNashEquilibrium p) (hq : G.IsMixedNashEquilibrium q) :
    p = q := by
  have pmf_ext : ∀ (σ τ : PMF A),
      (fun a => (σ a).toReal) = (fun a => (τ a).toReal) → σ = τ := by
    intro σ τ h
    refine PMF.ext (fun a => ?_)
    exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top σ a) (PMF.apply_ne_top τ a)).mp
      (congrFun h a)
  obtain ⟨hp1, hp0⟩ := mixedNash_mulVec_nonpos G hzs hanti p hp
  obtain ⟨hq1, hq0⟩ := mixedNash_mulVec_nonpos G hzs hanti q hq
  have h0 : (fun a => (p 0 a).toReal) = (fun a => (q 0 a).toReal) :=
    tournament_optimal_unique (Mtg G) hanti hoff _ _
      (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
      (pmf_sum_toReal (p 0)) (pmf_sum_toReal (q 0)) hp0 hq0
  have h1 : (fun a => (p 1 a).toReal) = (fun a => (q 1 a).toReal) :=
    tournament_optimal_unique (Mtg G) hanti hoff _ _
      (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
      (pmf_sum_toReal (p 1)) (pmf_sum_toReal (q 1)) hp1 hq1
  funext i
  fin_cases i
  · exact pmf_ext _ _ h0
  · exact pmf_ext _ _ h1

end Game

/--
**A tournament game has at most one mixed-strategy Nash equilibrium.**

This is the uniqueness ("at most one MSNE") half of `TournamentGame.hasUniqueNashEquilibrium`,
formalising the argument of <https://mathoverflow.net/questions/506372>: in any equilibrium each
player's strategy `x` (as a real probability vector) is *optimal*, i.e. satisfies `M x ≤ 0` for the
payoff matrix `M`; and a tournament matrix admits at most one such `x`, because `x - y` would lie
in the kernel of `M` augmented by the all-ones row, which is nonsingular (it is so already mod 2).

NOTE. The current `TournamentGame` structure only encodes the zero-sum condition (`symmetric`) and
the `±1`-off-diagonal condition (`payoff_ne`). It does *not* encode invariance under swapping the
two players, which is part of the definition of a tournament game and is what makes the payoff
matrix antisymmetric (and the diagonal zero). That missing property is supplied here as the
hypothesis `hswap`.
-/
theorem TournamentGame.subsingleton_mixedNashEquilibrium
    {A : Type} [Fintype A] [DecidableEq A] (G : TournamentGame A)
    (hswap : ∀ a b : A, G.payoff 0 ![a, b] = G.payoff 1 ![b, a])
    (p q : Fin 2 → PMF A)
    (hp : G.toUniformActionNormalFormGame.IsMixedNashEquilibrium p)
    (hq : G.toUniformActionNormalFormGame.IsMixedNashEquilibrium q) :
    p = q := by
  refine subsingleton_mixedNash G.toUniformActionNormalFormGame G.symmetric ?_ ?_ p q hp hq
  · intro a b
    change G.payoff 0 ![a, b] = - G.payoff 0 ![b, a]
    rw [hswap a b]
    have := G.symmetric ![b, a]
    linarith
  · intro a b hab
    change G.payoff 0 ![a, b] = 1 ∨ G.payoff 0 ![a, b] = -1
    exact G.payoff_ne 0 ![a, b] (by simpa using hab)
