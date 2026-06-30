
import VCVio.OracleComp.ProbComp

/-!

# Probabilistically evaluables

This file contains the definition for a monad-like type transformation `ProbEval`
which encapsulates probabilistic computations (defined using VCVio's `ProbComp`)
that return the same value more than half of the time.

The concept of this structure
is that it's useful as an encapsulation for actions that arise in probabilistic tests.

Here are some examples of uses of this structure:

* The Miller-Rabin test can be written as a `ℕ → ProbComp Bool`
  that returns `true` if the number is probably prime and `false` if it is composite
  with soundness bound 75%.
* The Schwartz-Zippel test can be written as a `Polynomial → Polynomial → ProbComp Bool`
  that returns `true` if the two polynomials are probably equal and `false` if they are not.
* A `ProbComp Cell` could be written that returns the best cell to reveal in a minesweeper board,
  by statistically upper or lower bounding the equity of each other cell.

-/


/--
Probabilistic evaluables
-/
structure ProbEval (α : Type) where
  /-- The value associated with the evaluation
  (TODO: should this be included, or does this ruin the computational properties) -/
  val : α
  /-- A probabilistic computation we can run to obtain val -/
  comp : ProbComp α
  /-- A bound on the probability of correct evalaution -/
  bound_correct : NNRat
  /-- The bound must be at least 1/2 to guarantee ability to boost -/
  bound_correct_le : 1/2 < bound_correct
  /-- The soundness condition:
  the probability that `comp` does not return `val` is at most `bound`. -/
  soundness : bound_correct ≤ Pr[= val | comp]


/--
A probabilistic computation that involves repeating a
ProbEval some number of times and taking the plurality value.

This allows us to produce a new ProbEval with a much smaller error bound.
-/
def ProbEval.repeat {α} (p : ProbEval α) (repetitions : Nat) : ProbComp α :=
  sorry

/--
A probabilistic computation that involves repeating a
ProbEval some number of times and taking the plurality value.

We choose the number of repetitions to guarantee that the error bound is reduced to the given bound.

This allows us to produce a new ProbEval with a much smaller error bound.
-/
def ProbEval.boost {α} (p : ProbEval α) (bound : NNRat) : ProbComp α :=
  sorry

/--
The pure constructor for ProbEval, which just returns a fixed value with probability 1.
-/
def ProbEval.pure {α} (x : α) : ProbEval α := sorry

/--
The bind constructor for ProbEval, which composes two ProbEvals together.

Note that this is **not** constructed using the monadic bind of `ProbComp`,
because then the soundness would be the product of the individual soundness bounds,
which is not good enough to guarantee that the result is above 1/2.

Instead, we must first boost the ProbEvals before composing.

Note that unfortunately, this seems to mean that monad laws won't hold.

Can we fix this somehow?

On another level,
really what we want to do is do the whole computation
and then best decide how to boost parts of it

(perhaps by making a soundness budget that parts of the computation
for example,
we could let the first call take 1/2 the budget,
then the next 2 calls take the next 1/4, then the next 4 cals take 1/8, etc.
so that we can guarantee the final soundness is at most the given bound
and amortized each call takes about the polynomial buudget fraction in the number of calls.
)
-/
def ProbEval.bind {α β} (p : ProbEval α) (f : α → ProbEval β) : ProbEval β :=
  sorry
