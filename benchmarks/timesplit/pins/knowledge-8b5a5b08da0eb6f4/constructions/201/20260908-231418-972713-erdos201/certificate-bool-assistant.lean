-- PROVENANCE: written by the assistant AFTER the harness run to validate the Bool-reflection certificate style;
-- it certifies the object the harness's construct stage found (A has Roth number ≤ 7; W ⊆ {0..13} is an 8-element 3-AP-free set).
-- Compiled in 239 s (lake env lean, Mathlib v4.32.0-rc1). NOT an autonomous harness certificate; the run itself was 'uncertified'.
import Mathlib.Tactic

set_option maxHeartbeats 4000000
set_option autoImplicit false

-- Erdős #201 construct object found by the harness: A (14 elements) has Roth number 7 while R_3(14) = 8.
def A : List ℕ := [0, 4, 6, 8, 10, 12, 13, 14, 16, 18, 20, 22, 24, 26]
def W : List ℕ := [0, 1, 3, 4, 9, 10, 12, 13]

def hasAP (t : List ℕ) : Bool :=
  t.any fun a => t.any fun b => t.any fun c => decide (a < b ∧ b < c ∧ a + c = b + b)

/-- every 8-element sublist of A contains a 3-AP (so roth(A) ≤ 7) -/
def allEightSubsetsHaveAP : Bool :=
  (A.sublists.filter (fun t => t.length == 8)).all hasAP

/-- W ⊆ {0,…,13}, |W| = 8, W is 3-AP-free (so R_3(14) ≥ 8) -/
def wOK : Bool := (W.all (fun x => x < 14)) && (W.length == 8) && (!hasAP W)

theorem construct_cert : allEightSubsetsHaveAP = true ∧ wOK = true := by
  constructor <;> decide +kernel
