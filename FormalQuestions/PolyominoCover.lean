import Mathlib

/-! # Rationality of the minimal piercing density of a polyomino

We work on the planar integer grid `ℤ × ℤ`. A **polyomino** is a finite, nonempty, edge-connected
set of grid cells. A subset `S ⊆ ℤ × ℤ` **pierces** (or *touches*, *stabs*) every translate of a
polyomino `P` when `S` meets `P + v` for every translation vector `v`; such an `S` is called a
*transversal*. Among all transversals one looks for the one of smallest **density** — the limiting
proportion of grid points it occupies.

The claim formalized here (left as `sorry`) is:

> For every polyomino in the plane, the minimal density of a subset of the integer grid that
> touches every translation of that polyomino is rational.

This is the discrete analogue of a covering/piercing problem; the rationality reflects the fact that
an optimal transversal can be taken to be periodic.
-/

namespace PolyominoCover

/-! ## Polyominoes -/

/-- Two grid cells are *edge-adjacent* when they differ by exactly one in a single coordinate
(rook adjacency for a single step). -/
def Adjacent (a b : ℤ × ℤ) : Prop :=
  (a.1 - b.1).natAbs + (a.2 - b.2).natAbs = 1

/-- A set of cells is *connected* when any two of its cells are joined by a path of edge-adjacent
cells that stays inside the set. -/
def IsConnected (P : Set (ℤ × ℤ)) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, Relation.ReflTransGen (fun x y => x ∈ P ∧ y ∈ P ∧ Adjacent x y) a b

/-- A polyomino: a finite, nonempty, edge-connected set of cells in the planar integer grid. -/
structure Polyomino where
  /-- The cells making up the polyomino. -/
  cells : Set (ℤ × ℤ)
  finite : cells.Finite
  nonempty : cells.Nonempty
  connected : IsConnected cells

/-! ## Translations and transversals -/

/-- The translate of a cell set `P` by a vector `v`. -/
def translate (P : Set (ℤ × ℤ)) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  (· + v) '' P

/-- `S` is a *transversal* of `P` when it meets every translate of `P`, i.e. it touches every
translation of the polyomino. -/
def IsTransversal (P : Set (ℤ × ℤ)) (S : Set (ℤ × ℤ)) : Prop :=
  ∀ v : ℤ × ℤ, (S ∩ translate P v).Nonempty

/-! ## Density

The density of a subset of the grid is measured against axis-aligned square boxes centred at the
origin, taking the limit superior of the occupied proportion as the boxes grow. -/

/-- The `(2n+1) × (2n+1)` axis-aligned box of grid cells centred at the origin. -/
noncomputable def boxFinset (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))

open Classical in
/-- The number of cells of `S` lying in the box of radius `n`. -/
noncomputable def boxCount (S : Set (ℤ × ℤ)) (n : ℕ) : ℕ :=
  ((boxFinset n).filter (· ∈ S)).card

/-- The (upper) density of a subset of the grid: the limit superior, as the box grows, of the
proportion of box cells occupied by `S`. -/
noncomputable def upperDensity (S : Set (ℤ × ℤ)) : ℝ :=
  Filter.limsup (fun n : ℕ => (boxCount S n : ℝ) / ((boxFinset n).card : ℝ)) Filter.atTop

/-- The minimal density of a transversal of `P`: the infimum of the densities of subsets of the
grid that touch every translation of `P`. -/
noncomputable def minimalDensity (P : Set (ℤ × ℤ)) : ℝ :=
  sInf (upperDensity '' { S | IsTransversal P S })

/-! ## The claim -/

/-- For any polyomino in the plane, the minimal density of a subset of the integer grid that touches
every translation of that polyomino is rational.

TODO: proof unknown for now, I should add formalconjectures to the dep list so I can use the answer() scheme.
-/
theorem minimalDensity_rational (P : Polyomino) :
    ∃ q : ℚ, minimalDensity P.cells = (q : ℝ) := by
  sorry

end PolyominoCover
