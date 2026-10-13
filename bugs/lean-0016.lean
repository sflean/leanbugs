/-
Needs Batteries. On Batteries v4.32.2 the compiled `Vector.scanr` returns `[5, 3, 0, 0]` for the
suffix sums of `[1, 2, 3]`, while the definition the kernel sees gives `[6, 5, 3, 0]`;
`native_decide` trusts the compiled code, and the two together prove `False`. On v4.33.0 and
later `#eval` prints `[6, 5, 3, 0]` and `native_says` fails.
From the issue.
-/

import Batteries.Data.Vector.Basic
import Batteries.Data.Vector.Lemmas
import Batteries.Data.List.Scan

def mkV (l : List Nat) : Vector Nat l.length := ⟨l.toArray, by simp⟩

-- Runs the compiled `scanrMFast`.
#eval (Vector.scanr (· + ·) 0 (mkV [1, 2, 3])).toList

-- `native_decide` runs the same compiled code.
theorem native_says : (Vector.scanr (· + ·) 0 (mkV [1, 2, 3])).toList = [5, 3, 0, 0] := by
  native_decide

-- The kernel, through Batteries' own `Vector.toList_scanr`, gets the correct answer.
theorem kernel_says : (Vector.scanr (· + ·) 0 (mkV [1, 2, 3])).toList = [6, 5, 3, 0] := by
  rw [Vector.toList_scanr]; decide

theorem boom : False := by
  have h : ([5, 3, 0, 0] : List Nat) = [6, 5, 3, 0] := native_says ▸ kernel_says
  exact absurd h (by decide)

#print axioms boom
