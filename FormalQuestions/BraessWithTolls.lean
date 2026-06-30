
import Mathlib


/-! # Braess's paradox with tolls

The four nodes are `N`, `W`, `S`, `E`; drivers travel from `W` to `E`.
There are five roads (the two-letter toll names indicate the road's endpoints):

* `W → N`, congested: travel time equals the proportion of drivers using it. Its toll is `NWToll`.
* `N → E`, constant travel time `1`. Its toll is `NEToll`.
* `W → S`, constant travel time `1`. Its toll is `SWToll`.
* `S → E`, congested: travel time equals the proportion of drivers using it. Its toll is `SEToll`.
* `N → S` (the interchange), travel time `0`. Its toll is `InterchangeToll`.

There are three routes from `W` to `E`:

* `NorthRoute`: `W → N → E`.
* `SouthRoute`: `W → S → E`.
* `Interchange`: `W → N → S → E`, using the interchange.

We model the situation as **two coupled games**:

* the **driver game** (`DriverProfile.isEquilibrium`): for a *fixed* toll profile, the drivers
  choose which route to take and equilibrate so that no individual driver can lower their cost by
  switching routes (a Wardrop/Nash equilibrium of the routing game); and
* the **toll game** (`isTollEquilibrium`): the five toll companies set their tolls. Crucially,
  when a company changes its toll the drivers *respond* by re-equilibrating in the driver game.
  A company that raises its toll may therefore drive traffic off its road, which is exactly what
  stops the companies from raising tolls without bound.

This bilevel (Stackelberg-style) structure replaces the earlier single-profile model, in which a
toll company could deviate while the driver proportions were frozen — and so always had an
incentive to raise its toll.
-/

namespace Braess

/-- A choice of toll for each of the five roads. -/
structure TollProfile where
  NWToll : ℝ
  NEToll : ℝ
  SWToll : ℝ
  SEToll : ℝ
  InterchangeToll : ℝ

/-- A choice of what proportion of drivers takes each of the three routes. -/
structure DriverProfile where
  NorthRouteDriverProportion : ℝ
  SouthRouteDriverProportion : ℝ
  InterchangeDriverProportion : ℝ

namespace DriverProfile

/-- A driver profile is valid when the proportions form a probability distribution over the
three routes. -/
def valid (d : DriverProfile) : Prop :=
  d.NorthRouteDriverProportion + d.SouthRouteDriverProportion + d.InterchangeDriverProportion = 1 ∧
  0 ≤ d.NorthRouteDriverProportion ∧
  0 ≤ d.SouthRouteDriverProportion ∧
  0 ≤ d.InterchangeDriverProportion

/-! ## Road usage

For each of the five roads, the proportion of drivers using it equals the sum of the proportions
on the routes that traverse that road. These depend only on the driver profile. -/

/-- Proportion of drivers using the `W → N` road (North + interchange routes). -/
def WtoNUsage (d : DriverProfile) : ℝ :=
  d.NorthRouteDriverProportion + d.InterchangeDriverProportion

/-- Proportion of drivers using the `N → E` road (North route only). -/
def NtoEUsage (d : DriverProfile) : ℝ :=
  d.NorthRouteDriverProportion

/-- Proportion of drivers using the `W → S` road (South route only). -/
def WtoSUsage (d : DriverProfile) : ℝ :=
  d.SouthRouteDriverProportion

/-- Proportion of drivers using the `S → E` road (South + interchange routes). -/
def StoEUsage (d : DriverProfile) : ℝ :=
  d.SouthRouteDriverProportion + d.InterchangeDriverProportion

/-- Proportion of drivers using the interchange road `N → S`. -/
def InterchangeUsage (d : DriverProfile) : ℝ :=
  d.InterchangeDriverProportion

/-! ## Driver payoffs

A driver's payoff on a given route is the negative of the sum of tolls and travel times along that
route. Travel time on a congested road equals its usage; constant roads take time `1`; the
interchange takes time `0`. Payoffs depend on both the toll profile `t` and the driver profile `d`
(through congestion). -/

/-- Payoff to a driver who takes the North route `W → N → E`. -/
def NorthRoutePayoff (d : DriverProfile) (t : TollProfile) : ℝ :=
  - t.NWToll - t.NEToll - d.WtoNUsage - 1

/-- Payoff to a driver who takes the South route `W → S → E`. -/
def SouthRoutePayoff (d : DriverProfile) (t : TollProfile) : ℝ :=
  - t.SWToll - t.SEToll - 1 - d.StoEUsage

/-- Payoff to a driver who takes the interchange route `W → N → S → E`. -/
def InterchangePayoff (d : DriverProfile) (t : TollProfile) : ℝ :=
  - t.NWToll - t.InterchangeToll - t.SEToll - d.WtoNUsage - d.StoEUsage

/-! ## The driver game

For a fixed toll profile `t`, the drivers play a routing game: each driver picks a route, and the
proportions equilibrate. -/

/-- The driver game equilibrium for a fixed toll profile `t`: the driver profile `d` is valid, and
every route used by a positive proportion of drivers attains the maximum driver payoff (so no
individual driver can strictly improve by switching routes). -/
def isEquilibrium (t : TollProfile) (d : DriverProfile) : Prop :=
  d.valid ∧
  (0 < d.NorthRouteDriverProportion →
    d.SouthRoutePayoff t ≤ d.NorthRoutePayoff t ∧ d.InterchangePayoff t ≤ d.NorthRoutePayoff t) ∧
  (0 < d.SouthRouteDriverProportion →
    d.NorthRoutePayoff t ≤ d.SouthRoutePayoff t ∧ d.InterchangePayoff t ≤ d.SouthRoutePayoff t) ∧
  (0 < d.InterchangeDriverProportion →
    d.NorthRoutePayoff t ≤ d.InterchangePayoff t ∧ d.SouthRoutePayoff t ≤ d.InterchangePayoff t)

end DriverProfile

namespace TollProfile

/-! ## Toll-company payoffs

Each toll company's payoff equals its toll multiplied by the proportion of drivers on its road.
These depend on both the toll profile `t` and the driver profile `d`. -/

/-- Payoff to the company holding the `W → N` road. -/
def NWTollPayoff (t : TollProfile) (d : DriverProfile) : ℝ :=
  t.NWToll * d.WtoNUsage

/-- Payoff to the company holding the `N → E` road. -/
def NETollPayoff (t : TollProfile) (d : DriverProfile) : ℝ :=
  t.NEToll * d.NtoEUsage

/-- Payoff to the company holding the `W → S` road. -/
def SWTollPayoff (t : TollProfile) (d : DriverProfile) : ℝ :=
  t.SWToll * d.WtoSUsage

/-- Payoff to the company holding the `S → E` road. -/
def SETollPayoff (t : TollProfile) (d : DriverProfile) : ℝ :=
  t.SEToll * d.StoEUsage

/-- Payoff to the company holding the interchange. -/
def InterchangeTollPayoff (t : TollProfile) (d : DriverProfile) : ℝ :=
  t.InterchangeToll * d.InterchangeUsage

end TollProfile

/-! ## The toll game

The five toll companies are the leaders; the drivers are the followers. When a company changes its
toll, the drivers respond by re-equilibrating in the driver game. We therefore evaluate a company's
deviation against *every* driver equilibrium that the deviated toll profile admits: a configuration
`(t, d)` is a toll equilibrium when no company can pick an alternative toll for which *some*
resulting driver equilibrium yields it a strictly higher payoff.

Equivalently (the form used below): for every company, every alternative toll `s`, and every driver
equilibrium `d'` of the deviated toll profile, the company's deviated payoff does not exceed its
current payoff. This is the bilevel fix for the earlier model: raising a toll changes `d'`, so a
company can no longer profit by raising its toll while the drivers stay put. -/

/-- The toll game equilibrium, with drivers responding as followers.

A configuration `(t, d)` is a toll equilibrium when:

* `d` is a driver-game equilibrium for the toll profile `t` (drivers best-respond to the tolls and
  to each other); and
* no toll company can deviate to some alternative toll `s` such that, for the resulting toll
  profile, there is a driver equilibrium `d'` giving that company a strictly higher payoff.

Because the drivers re-equilibrate after a deviation (`d'` ranges over equilibria of the *deviated*
toll profile), a company that raises its toll can lose the traffic that made the toll worth
charging — so tolls are no longer trivially unbounded. -/
def isTollEquilibrium (t : TollProfile) (d : DriverProfile) : Prop :=
  DriverProfile.isEquilibrium t d ∧
  (∀ (s : ℝ) (d' : DriverProfile), DriverProfile.isEquilibrium {t with NWToll := s} d' →
    ({t with NWToll := s} : TollProfile).NWTollPayoff d' ≤ t.NWTollPayoff d) ∧
  (∀ (s : ℝ) (d' : DriverProfile), DriverProfile.isEquilibrium {t with NEToll := s} d' →
    ({t with NEToll := s} : TollProfile).NETollPayoff d' ≤ t.NETollPayoff d) ∧
  (∀ (s : ℝ) (d' : DriverProfile), DriverProfile.isEquilibrium {t with SWToll := s} d' →
    ({t with SWToll := s} : TollProfile).SWTollPayoff d' ≤ t.SWTollPayoff d) ∧
  (∀ (s : ℝ) (d' : DriverProfile), DriverProfile.isEquilibrium {t with SEToll := s} d' →
    ({t with SEToll := s} : TollProfile).SETollPayoff d' ≤ t.SETollPayoff d) ∧
  (∀ (s : ℝ) (d' : DriverProfile), DriverProfile.isEquilibrium {t with InterchangeToll := s} d' →
    ({t with InterchangeToll := s} : TollProfile).InterchangeTollPayoff d'
      ≤ t.InterchangeTollPayoff d)

/-! ## Questions

Formal counterparts of the questions raised in the introduction. -/

namespace DriverProfile

/-- The total travel time experienced by all drivers in a profile, weighted by the proportion
taking each route. Tolls are transfers between players and are not counted as social cost; the
total travel time therefore depends only on the driver profile. -/
def totalTravelTime (d : DriverProfile) : ℝ :=
  d.NorthRouteDriverProportion * (d.WtoNUsage + 1)
  + d.SouthRouteDriverProportion * (d.StoEUsage + 1)
  + d.InterchangeDriverProportion * (d.WtoNUsage + d.StoEUsage)

end DriverProfile

/-- The infimum of total travel time over valid driver profiles (toll values do not affect travel
time, so this is the toll-free network optimum). -/
noncomputable def optimalTotalTravelTime : ℝ :=
  sInf (DriverProfile.totalTravelTime '' { d : DriverProfile | d.valid })

/-- The supremum of total travel time over the driver profiles arising in toll-game equilibria. -/
noncomputable def worstNashTotalTravelTime : ℝ :=
  sSup (DriverProfile.totalTravelTime ''
    { d : DriverProfile | ∃ t : TollProfile, isTollEquilibrium t d })

/-- Question (PoA): the Price of Anarchy, defined as the ratio of the worst equilibrium total
travel time to the optimal total travel time. -/
noncomputable def priceOfAnarchy : ℝ :=
  worstNashTotalTravelTime / optimalTotalTravelTime

/-- Question (existence): does a toll-game equilibrium exist? -/
def NashEquilibriumExists : ∃ (t : TollProfile) (d : DriverProfile), isTollEquilibrium t d :=
  by
  sorry

/-- Does there exist a unique toll-game equilibrium? -/
def UniqueNashEquilibrium :
    ∃! p : TollProfile × DriverProfile, isTollEquilibrium p.1 p.2 :=
  by
  sorry

/--
Is the set of possible total tolls paid by drivers in toll-game equilibria bounded?
-/
def NashEquilibriumTollBounded : Prop :=
  ∃ M : ℝ, ∀ (t : TollProfile) (d : DriverProfile), isTollEquilibrium t d →
    t.NWToll + t.NEToll + t.SWToll + t.SEToll + t.InterchangeToll ≤ M

end Braess
