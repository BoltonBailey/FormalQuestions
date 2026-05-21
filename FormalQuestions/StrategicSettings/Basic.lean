
import Mathlib

structure StrategicSetting (Players : Type) (States : Type) where
  /- For any player, the type of information states available to that player -/
  (InformationState : Players → Type)
  /- For any information state, the type of actions available in that state -/
  (ActionMenu : (p : Players) → InformationState p → Type)
  /- Initial state -/
  (initial_state : States)
  /- For any game state, the information state of each player -/
  (InformationState_of : States → (p : Players) → InformationState p)
  /- For any game state, and profile of actions taken by each player,
  a probability distribution over the next game state (or option to terminate game) -/
  (transition :
    (s : States) →
    (actions : (p : Players) → ActionMenu p (InformationState_of s p)) →
    PMF (Option States))
  /- For any sequence of game states and any player,
  a payoff function that gives the payoff of that player,
  given the sequence of game states. -/
  (payoff : Players -> (Stream' States) -> ℝ)

structure NormalFormGame (Players : Type) where
  ActionMenu : Players → Type
  payoff : (p : Players) → (actions : (p' : Players) → ActionMenu p') → ℝ

structure TwoPlayerZeroSumGame extends NormalFormGame (Fin 2) where
  payoff_zero_sum : ∀ (actions : (p : Fin 2) → ActionMenu p), payoff 0 actions = -payoff 1 actions

def NormalFormGame.IsNashEquilibrium {Players : Type} [DecidableEq Players] (G : NormalFormGame Players)
    (profile : (p : Players) → G.ActionMenu p) : Prop :=
  ∀ (p : Players) (a' : G.ActionMenu p),
    G.payoff p profile ≥ G.payoff p (Function.update profile p a')

noncomputable def NormalFormGame.toMixedGame {Players : Type} [FinEnum Players] [DecidableEq Players]
    (G : NormalFormGame Players) :
    NormalFormGame Players where
  ActionMenu p := PMF (G.ActionMenu p)
  payoff p actions :=
    ∑' profile : (p' : Players) → G.ActionMenu p',
      G.payoff p profile * ∏ p' : Players, (actions p' (profile p')).toReal

def NormalFormGame.IsMixedNashEquilibrium {Players : Type} [FinEnum Players] [DecidableEq Players]
    (G : NormalFormGame Players)
    (profile : (p : Players) → PMF (G.ActionMenu p)) : Prop :=
  G.toMixedGame.IsNashEquilibrium profile


section UniformActionNormalFormGame

structure UniformActionNormalFormGame (Players : Type) (ActionMenu : Type) where
  payoff : (p : Players) → (actions : (p' : Players) → ActionMenu) → ℝ

def UniformActionNormalFormGame.IsNashEquilibrium {Players ActionMenu : Type} [DecidableEq Players]
    (G : UniformActionNormalFormGame Players ActionMenu)
    (profile : (p : Players) → ActionMenu) : Prop :=
  ∀ (p : Players) (a' : ActionMenu),
    G.payoff p profile ≥ G.payoff p (Function.update profile p a')

noncomputable def UniformActionNormalFormGame.toMixedGame {Players ActionMenu : Type} [FinEnum Players] [DecidableEq Players]
    (G : UniformActionNormalFormGame Players ActionMenu) :
    UniformActionNormalFormGame Players (PMF ActionMenu) where
  payoff p actions :=
    ∑' profile : (p' : Players) → ActionMenu,
      G.payoff p profile * ∏ p' : Players, (actions p' (profile p')).toReal

def UniformActionNormalFormGame.IsMixedNashEquilibrium {Players ActionMenu : Type} [FinEnum Players] [DecidableEq Players]
    (G : UniformActionNormalFormGame Players ActionMenu)
    (profile : (p : Players) → PMF (ActionMenu)) : Prop :=
  G.toMixedGame.IsNashEquilibrium profile

end UniformActionNormalFormGame
