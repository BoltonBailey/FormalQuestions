import Mathlib
import FormalQuestions.StrategicSettings.Basic

open Finset

/--
A [tournament](<https://en.wikipedia.org/wiki/Tournament_(graph_theory)>) is a directed graph
where any two distinct vertices have exactly one directed edge joining them
(so named, presumably, because this is the graph we obtain from a round-robin tournament
in which each player plays each other once,
and we draw an edge from the winner to the loser of each game).

Given a tournament, we can consider the symmetric, two-player, zero-sum, normal form game
where the action sets are the sets of vertices of the tournament,
and where, if the players moves are distinct,
then a player receives +1 payoff iff the edge joining the moves originates on their chosen vertex.
We'll call such a game a _tournament game_.
-/
structure TournamentGame (ActionMenu : Type)
    extends UniformActionNormalFormGame (Fin 2) ActionMenu where
  symmetric : ∀ (actions : (p : Fin 2) → ActionMenu), payoff 0 actions = -payoff 1 actions
  payoff_ne : ∀ (p) (actions : (p' : Fin 2) → ActionMenu),
    actions 0 ≠ actions 1 → payoff p actions = 1 ∨ payoff p actions = -1


/--
A tournament game has a unique Nash equilibrium.
https://mathoverflow.net/questions/506372/can-a-tournament-game-have-multiple-msne
-/
theorem TournamentGame.hasUniqueNashEquilibrium
    {ActionMenu : Type} (G : TournamentGame ActionMenu) :
    ∃! (profile : (Fin 2) → PMF (ActionMenu)),
      G.toUniformActionNormalFormGame.IsMixedNashEquilibrium profile := by
  sorry

noncomputable def TournamentGame.UniqueNashEquilibrium
    {ActionMenu : Type} (G : TournamentGame ActionMenu) :
    ((Fin 2) → PMF (ActionMenu)) :=
  Classical.choice (Exists.nonempty (hasUniqueNashEquilibrium G))


/--
The cyclic tournament game on `2n + 1` actions,
where actions beat those that are at most `n` steps ahead of them,
and lose to those that are at most `n` steps behind them.
-/
def TournamentGame.Cyclic (n : ℕ) : TournamentGame (Fin (2 * n + 1)) where
  payoff p actions :=
    if actions 0 = actions 1 then 0
    else if (actions 1 - actions 0) % (2 * n + 1) ≤ n then 1
    else -1
  symmetric := by
    intro actions
    sorry
  payoff_ne p actions h := by
    sorry

theorem TournamentGame.cyclic_UniqueNashEquilibrium (n : ℕ) (p : Fin 2) :
    TournamentGame.UniqueNashEquilibrium (TournamentGame.Cyclic n) p =
    PMF.uniformOfFinset (α := Fin (2 * n + 1)) (.univ) (univ_nonempty) := by
  sorry

def TournamentGame.multiphase
    {ActionMenu : Type} {ActionMenu' : (a : ActionMenu) → Type}
    [DecidableEq ActionMenu]
    [(a : ActionMenu) → DecidableEq (ActionMenu' a)]
    (G : TournamentGame ActionMenu)
    (G' : (a : ActionMenu) → TournamentGame (ActionMenu' a)) :
    TournamentGame (Σ a : ActionMenu, ActionMenu' a) where
  payoff p actions :=
    if h : ((actions 0).1 = (actions 1).1)
    then (G' (actions 0).1).payoff p
      (fun p' => if p' = 0 then (actions 0).2 else h ▸ (actions 1).2)
    else G.payoff p (fun p' => (actions p').1)
  symmetric := by
    intro actions
    sorry
  payoff_ne p actions h := by
    sorry
