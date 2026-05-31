
import Mathlib


/-- A strategy profile for the Braess-with-tolls game.

The four nodes are `N`, `W`, `S`, `E`; drivers travel from `W` to `E`.
There are five roads (the two-letter toll names indicate the road's endpoints):

* `W → N`, congested: travel time equals the proportion of drivers using it.
  Its toll is `NWToll`.
* `N → E`, constant travel time `1`. Its toll is `NEToll`.
* `W → S`, constant travel time `1`. Its toll is `SWToll`.
* `S → E`, congested: travel time equals the proportion of drivers using it.
  Its toll is `SEToll`.
* `N → S` (the interchange), travel time `0`. Its toll is `InterchangeToll`.

There are three routes from `W` to `E`:

* `NorthRoute`: `W → N → E`.
* `SouthRoute`: `W → S → E`.
* `Interchange`: `W → N → S → E`, using the interchange.
-/
structure BraessGameProfile where
  NorthRouteDriverProportion : ℝ
  SouthRouteDriverProportion : ℝ
  InterchangeDriverProportion : ℝ
  NEToll : ℝ
  SEToll : ℝ
  NWToll : ℝ
  SWToll : ℝ
  InterchangeToll : ℝ

namespace BraessGameProfile

/-- A profile is valid when the driver proportions form a probability distribution
over the three routes. -/
def valid (p : BraessGameProfile) : Prop :=
  p.NorthRouteDriverProportion + p.SouthRouteDriverProportion + p.InterchangeDriverProportion = 1 ∧
  0 ≤ p.NorthRouteDriverProportion ∧
  0 ≤ p.SouthRouteDriverProportion ∧
  0 ≤ p.InterchangeDriverProportion

/-! ## Road usage

For each of the five roads, the proportion of drivers using it equals the sum of the proportions
on the routes that traverse that road. -/

/-- Proportion of drivers using the `W → N` road (North + interchange routes). -/
def WtoNUsage (p : BraessGameProfile) : ℝ :=
  p.NorthRouteDriverProportion + p.InterchangeDriverProportion

/-- Proportion of drivers using the `N → E` road (North route only). -/
def NtoEUsage (p : BraessGameProfile) : ℝ :=
  p.NorthRouteDriverProportion

/-- Proportion of drivers using the `W → S` road (South route only). -/
def WtoSUsage (p : BraessGameProfile) : ℝ :=
  p.SouthRouteDriverProportion

/-- Proportion of drivers using the `S → E` road (South + interchange routes). -/
def StoEUsage (p : BraessGameProfile) : ℝ :=
  p.SouthRouteDriverProportion + p.InterchangeDriverProportion

/-- Proportion of drivers using the interchange road `N → S`. -/
def InterchangeUsage (p : BraessGameProfile) : ℝ :=
  p.InterchangeDriverProportion

/-! ## Driver payoffs

A driver's payoff on a given route is the negative of the sum of tolls and travel times
along that route. Travel time on a congested road equals its usage; constant roads take
time `1`; the interchange takes time `0`. -/

/-- Payoff to a driver who takes the North route `W → N → E`. -/
def NorthRoutePayoff (p : BraessGameProfile) : ℝ :=
  - p.NWToll - p.NEToll - p.WtoNUsage - 1

/-- Payoff to a driver who takes the South route `W → S → E`. -/
def SouthRoutePayoff (p : BraessGameProfile) : ℝ :=
  - p.SWToll - p.SEToll - 1 - p.StoEUsage

/-- Payoff to a driver who takes the interchange route `W → N → S → E`. -/
def InterchangePayoff (p : BraessGameProfile) : ℝ :=
  - p.NWToll - p.InterchangeToll - p.SEToll - p.WtoNUsage - p.StoEUsage

/-! ## Toll-company payoffs

Each toll company's payoff equals its toll multiplied by the proportion of drivers on its road. -/

/-- Payoff to the company holding the `W → N` road. -/
def NWTollPayoff (p : BraessGameProfile) : ℝ :=
  p.NWToll * p.WtoNUsage

/-- Payoff to the company holding the `N → E` road. -/
def NETollPayoff (p : BraessGameProfile) : ℝ :=
  p.NEToll * p.NtoEUsage

/-- Payoff to the company holding the `W → S` road. -/
def SWTollPayoff (p : BraessGameProfile) : ℝ :=
  p.SWToll * p.WtoSUsage

/-- Payoff to the company holding the `S → E` road. -/
def SETollPayoff (p : BraessGameProfile) : ℝ :=
  p.SEToll * p.StoEUsage

/-- Payoff to the company holding the interchange. -/
def InterchangeTollPayoff (p : BraessGameProfile) : ℝ :=
  p.InterchangeToll * p.InterchangeUsage

/-- A profile is a Nash equilibrium iff:

* it is valid (driver proportions form a probability distribution);
* for the drivers: every route used by a positive proportion of drivers achieves the maximum
  driver payoff (so no individual driver can strictly improve by switching routes); and
* for each of the five toll companies: no other choice of toll (with everything else fixed)
  yields a strictly higher payoff.

TODO unfortunately, this is not what we want,
because if the toll companies can increase toll without drivers responding,
then they will always have incentive to do so.

We need some kind of equilibrium for the drivers themselves.
-/
def isNashEquilibrium (p : BraessGameProfile) : Prop :=
  p.valid ∧
  (0 < p.NorthRouteDriverProportion →
    p.SouthRoutePayoff ≤ p.NorthRoutePayoff ∧ p.InterchangePayoff ≤ p.NorthRoutePayoff) ∧
  (0 < p.SouthRouteDriverProportion →
    p.NorthRoutePayoff ≤ p.SouthRoutePayoff ∧ p.InterchangePayoff ≤ p.SouthRoutePayoff) ∧
  (0 < p.InterchangeDriverProportion →
    p.NorthRoutePayoff ≤ p.InterchangePayoff ∧ p.SouthRoutePayoff ≤ p.InterchangePayoff) ∧
  (∀ t : ℝ, ({p with NWToll := t} : BraessGameProfile).NWTollPayoff ≤ p.NWTollPayoff) ∧
  (∀ t : ℝ, ({p with NEToll := t} : BraessGameProfile).NETollPayoff ≤ p.NETollPayoff) ∧
  (∀ t : ℝ, ({p with SWToll := t} : BraessGameProfile).SWTollPayoff ≤ p.SWTollPayoff) ∧
  (∀ t : ℝ, ({p with SEToll := t} : BraessGameProfile).SETollPayoff ≤ p.SETollPayoff) ∧
  (∀ t : ℝ, ({p with InterchangeToll := t} : BraessGameProfile).InterchangeTollPayoff
    ≤ p.InterchangeTollPayoff)

/-! ## Questions

Formal counterparts of the questions raised in the introduction. -/

/-- The total travel time experienced by all drivers in a profile, weighted by the proportion
taking each route. Tolls are transfers between players and are not counted as social cost. -/
def totalTravelTime (p : BraessGameProfile) : ℝ :=
  p.NorthRouteDriverProportion * (p.WtoNUsage + 1)
  + p.SouthRouteDriverProportion * (p.StoEUsage + 1)
  + p.InterchangeDriverProportion * (p.WtoNUsage + p.StoEUsage)

/-- The infimum of total travel time over valid driver profiles (toll values do not affect
travel time, so this is the toll-free network optimum). -/
noncomputable def optimalTotalTravelTime : ℝ :=
  sInf (totalTravelTime '' { p : BraessGameProfile | p.valid })

/-- The supremum of total travel time over Nash equilibria. -/
noncomputable def worstNashTotalTravelTime : ℝ :=
  sSup (totalTravelTime '' { p : BraessGameProfile | p.isNashEquilibrium })

/-- Question (PoA): the Price of Anarchy, defined as the ratio of the worst Nash-equilibrium
total travel time to the optimal total travel time. -/
noncomputable def priceOfAnarchy : ℝ :=
  worstNashTotalTravelTime / optimalTotalTravelTime

/-- Question (existence): does a Nash equilibrium exist? -/
def NashEquilibriumExists : ∃ p : BraessGameProfile, p.isNashEquilibrium :=
  by
  sorry

/-- Does there exist a unique Nash equilibrium? -/
def UniqueNashEquilibrium : ∃! p : BraessGameProfile, p.isNashEquilibrium :=
  by
  sorry

/--
Is the set of possible total tolls paid by drivers in Nash equilibria bounded?
-/
def NashEquilibriumTollBounded : Prop :=
  ∃ M : ℝ, ∀ p : BraessGameProfile, p.isNashEquilibrium → p.NWToll + p.NEToll + p.SWToll + p.SEToll + p.InterchangeToll ≤ M

end BraessGameProfile
