
-- import Mathlib

namespace Minesweeper

/-- A disposition records mine presence at each cell. -/
abbrev Disposition (h w : Nat) := Vector (Vector Bool w) h

/-- Counts the number of mines in the given disposition. -/
def Disposition.mineCount {h w : Nat} (d : Disposition h w) : Nat :=
  d.foldl (fun acc row => acc + row.foldl (fun acc' cell => if cell then acc' + 1 else acc') 0) 0

/-- Convert a natural number (bitmask) to a disposition. -/
private def natToDisposition (h w : Nat) (bits : Nat) : Disposition h w :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    (bits / (2 ^ (i.val * w + j.val))) % 2 == 1

/-- All possible mine dispositions for a board of size `h × w`. -/
private def allDispositions (h w : Nat) : List (Disposition h w) :=
  (List.range (2 ^ (h * w))).map (natToDisposition h w)

/-- Count mines adjacent to cell `(ci, cj)` in a disposition grid. -/
private def adjacentMineCount {h w : Nat} (grid : Disposition h w) (ci cj : Nat) : Nat :=
  (List.finRange h).foldl (fun acc r =>
    (List.finRange w).foldl (fun acc' c =>
      if r.val ≤ ci + 1 ∧ ci ≤ r.val + 1 ∧ c.val ≤ cj + 1 ∧ cj ≤ c.val + 1 ∧ (r.val ≠ ci ∨ c.val ≠ cj) then
        if grid[r][c] then acc' + 1 else acc'
      else acc'
    ) acc
  ) 0


/--
A Minesweeper board with `h` rows and `w` columns.
Contains exactly the information a player would be provided by the game
(if they played without using flags or a timer)
-/
structure Board (h w : Nat) where
  /-- Each cell optionally contains a natural number representing the count of adjacent mines. -/
  revealed : Vector (Vector (Option Nat) w) h
  mineCount : Nat

/-- A board with no revealed cells for the given height, width, and total mine count. -/
def Board.starting (h w : Nat) (mineCount : Nat) : Board h w :=
  { revealed := Vector.ofFn fun _ => Vector.ofFn fun _ => none
    mineCount := mineCount }

/-- All revealed cells together with their revealed counts. -/
def Board.revealedCells (board : Board h w) : List ((Fin h × Fin w) × Nat) :=
  (List.finRange h).foldl (fun acc i =>
    (List.finRange w).foldl (fun acc' j =>
      match board.revealed[i][j] with
      | some k => ((i, j), k) :: acc'
      | none => acc'
    ) acc
  ) []

/-- All cells that have not yet been revealed. -/
def Board.unrevealedCells (board : Board h w) : List (Fin h × Fin w) :=
  (List.finRange h).foldl (fun acc i =>
    (List.finRange w).foldl (fun acc' j =>
      match board.revealed[i][j] with
      | some _ => acc'
      | none => (i, j) :: acc'
    ) acc
  ) []

/-- Count the number of revealed cells on the board. -/
def Board.revealedCount (board : Board h w) : Nat :=
  board.revealedCells.length

/-- Count the number of unrevealed cells on the board. -/
def Board.unrevealedCount (board : Board h w) : Nat :=
  board.unrevealedCells.length

/-- Check if a disposition is consistent with a board -/
private def Board.isConsistentWith {h w : Nat} (board : Board h w) (d : Disposition h w)  : Bool :=
  d.mineCount == board.mineCount &&
  board.revealedCells.all fun
    | ((i, j), k) => !d[i][j] && adjacentMineCount d i.val j.val == k

/--
A count of the number of possible mine dispositions that are consistent with the given `board`.
-/
def Board.countConsistentDispositions (board : Board h w) : Nat :=
  (allDispositions h w).foldl (fun acc d =>
    if board.isConsistentWith d then acc + 1 else acc
  ) 0

/--
A count of the number of possible mine dispositions that are consistent with the given `board`.
With a mine at i,j
-/
def Board.countConsistentDispositionsWithMine (board : Board h w) (i : Fin h) (j : Fin w) : Nat :=
  (allDispositions h w).foldl (fun acc d =>
    if board.isConsistentWith d  && d[i][j] then acc + 1 else acc
  ) 0

/-- Reveal the cell `(i, j)` with adjacent-mine count `k`. -/
private def Board.writeCell (board : Board h w) (i : Fin h) (j : Fin w) (k : Nat) : Board h w :=
  { revealed := Vector.ofFn fun r => Vector.ofFn fun c =>
      if r = i ∧ c = j then some k else board.revealed[r][c]
    mineCount := board.mineCount }

/-- Returns `true` when every starting cell is flaggable/forced to be a mine. -/
private def Board.isWon (board : Board h w) : Bool :=
  board.unrevealedCells.length == board.mineCount

/--
Returns the probability of a mine being present in the cell at position `(i, j)` on the given `board`.
Or None if invalid
-/
def Board.MineProbability (board : Board h w) (i : Fin h) (j : Fin w) : Option Rat :=
  let total := board.countConsistentDispositions
  if total = 0 then
    none
  else
    let with_mine := board.countConsistentDispositionsWithMine i j
    some (mkRat with_mine total)

/--
Probability of seeing the count `k` when revealing the unopened cell `(i, j)`.

This is a naive algorithm meant to give the correct answer in the simplest way possible,
optimized implementations can be introduced later.
-/
private def Board.openingOutcomeProbability (board : Board h w) (i : Fin h) (j : Fin w) (k : Nat) : Rat :=
  if 8 < k then
    0
  else
    if (i, j) ∈ board.unrevealedCells then
      let total := board.countConsistentDispositions
      if total = 0 then
        0
      else
        let nextBoard := board.writeCell i j k
        mkRat nextBoard.countConsistentDispositions total
    else
      0

/-- Prefer guaranteed-safe openings when any are available; otherwise consider all openings. -/
private def Board.preferredOpenings (board : Board h w) : List (Fin h × Fin w) :=
  let safeOpenings :=
    board.unrevealedCells.filter fun (i, j) =>
      board.countConsistentDispositionsWithMine i j = 0
  if safeOpenings.isEmpty then
    board.unrevealedCells
  else
    safeOpenings

/--
Calculates the expected equity of the board with optimal play.
Returns None if the board is invalid.

This is a naive algorithm meant to give the correct answer in the simplest way possible,
optimized implementations can be introduced later.
-/
partial def Board.equity (board : Board h w) : Option Rat :=
  -- If there are no consistent dispositions,
  -- the board is invalid, we return None to indicate this.
  if board.countConsistentDispositions = 0 then
    none
  -- If every starting cell is forced to be a mine, then the position is already won.
  else if board.isWon then
    some 1
  -- Otherwise, we must recurse.
  else
    let best :=
      board.unrevealedCells.filterMap (fun (i, j) =>
          let expected :=
            (List.range 9).filterMap (fun k =>
              let nextBoard := board.writeCell i j k
              let probability := board.openingOutcomeProbability i j k
              nextBoard.equity.map (· * probability)
            ) |>.sum
          some expected
      ) |>.max?
    match best with
    | some value => some value
    | none => some 0
-- termination_by
--   board.unrevealedCount
-- decreasing_by


/--
Calculates the expected equity of the board with optimal play, checking guaranteed-safe openings first.
Returns None if the board is invalid.

This is a naive algorithm meant to give the correct answer in the simplest way possible,
optimized implementations can be introduced later.
-/
partial def Board.fastEquity (board : Board h w) : Option Rat :=
  if board.countConsistentDispositions = 0 then
    none
  else if board.isWon then
    some 1
  else
    let best :=
      board.preferredOpenings.filterMap (fun (i, j) =>
          let expected :=
            (List.range 9).filterMap (fun k =>
              let nextBoard := board.writeCell i j k
              let probability := board.openingOutcomeProbability i j k
              nextBoard.fastEquity.map (· * probability)
            ) |>.sum
          some expected
      ) |>.max?
    match best with
    | some value => some value
    | none => some 0


#eval (Board.starting (h := 1) (w := 2) 0).fastEquity == some 1
#eval (Board.starting (h := 1) (w := 2) 1).fastEquity == some (1 / 2)
#eval (Board.starting (h := 1) (w := 2) 2).fastEquity == some 1

#eval (Board.starting (h := 1) (w := 3) 0).fastEquity == some 1
#eval (Board.starting (h := 1) (w := 3) 1).fastEquity == some (2 / 3)
#eval (Board.starting (h := 1) (w := 3) 2).fastEquity == some (1 / 3)
#eval (Board.starting (h := 1) (w := 3) 3).fastEquity == some 1

#eval (Board.starting (h := 2) (w := 2) 0).fastEquity == some 1
#eval (Board.starting (h := 2) (w := 2) 1).fastEquity == some (1 / 4)
#eval (Board.starting (h := 2) (w := 2) 2).fastEquity == some (1 / 6)
#eval (Board.starting (h := 2) (w := 2) 3).fastEquity == some (1 / 4)
#eval (Board.starting (h := 2) (w := 2) 4).fastEquity == some 1

#eval (Board.starting (h := 2) (w := 3) 1).fastEquity


theorem beginner_minesweeper_equity_eq : (Board.starting (h := 9) (w := 9) 10).fastEquity = sorry := by sorry
theorem intermediate_minesweeper_equity_eq : (Board.starting (h := 16) (w := 16) 40).fastEquity = sorry := by sorry
theorem expert_minesweeper_equity_eq : (Board.starting (h := 16) (w := 30) 99).fastEquity = sorry := by sorry

end Minesweeper
