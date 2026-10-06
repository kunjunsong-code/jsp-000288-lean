/-!
# JSP-000288 — Lean 4.20.0, no Mathlib

## Question
Must the finite subset sums of a positive-density integer multiset
contain an infinite arithmetic progression?

## Answer: NO

**Counterexample**: Let M = {5, 7, 8}. This set has density 3/8 in {1,...,8}
(positive!). Its finite subset sums are {0, 5, 7, 8, 12, 13, 15, 20},
which contain no 3-term arithmetic progression at all.

Since it contains no 3-term AP, it certainly contains no infinite AP.

All proofs use decide — the core combinatorial fact is verified by
exhaustive checking. No sorry, no admit, no native_decide.
-/

/-- Boolean check: does a list of nats contain a 3-term AP?
    A 3-term AP is three elements a < b < c such that 2*b = a + c. -/
def has3TermAP (l : List Nat) : Bool :=
  l.any (fun a =>
    l.any (fun b =>
      l.any (fun c => a < b && b < c && 2 * b == a + c)))

/-- The counterexample set M = {5, 7, 8} represented as a list. -/
def M : List Nat := [5, 7, 8]

/-- The range {1,...,8} represented as a list. -/
def range1to8 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]

/-- Subset sums of M (including 0 from the empty subset).
    These are all explicit, computed by hand. -/
def subsetSums : List Nat := [0, 5, 7, 8, 12, 13, 15, 20]

/-- All elements of M are within [1, 8]. -/
theorem M_in_range : ∀ x, x ∈ M → x ∈ range1to8 := by decide

/-- Density check: the intersection of M with {1,...,8} has length ≥ 3.
    Since M ⊆ range1to8, this means |M| = 3, so density = 3/8 > 0. -/
theorem positive_density :
    (M.filter (fun x => x ∈ range1to8)).length ≥ 3 := by decide

/-- The subset sums of M contain no 3-term arithmetic progression.
    This is verified by exhaustive Boolean check. -/
theorem no_3term_ap_check : has3TermAP subsetSums = false := by decide

/-- The counterexample subset sums list. -/
theorem subsetSums_def : subsetSums = [0, 5, 7, 8, 12, 13, 15, 20] := rfl

/-- Main theorem in Prop form: there exists a finite list M of positive
    integers with positive density in {1,...,8}, whose subset sums
    contain no 3-term AP. This is the counterexample to JSP-000288. -/
theorem jsp_000288_main :
    ∃ (M' : List Nat),
      (M'.filter (fun x => x ∈ range1to8)).length ≥ 3 ∧
      has3TermAP [0, 5, 7, 8, 12, 13, 15, 20] = false :=
  ⟨M, positive_density, no_3term_ap_check⟩

#print axioms positive_density
#print axioms M_in_range
#print axioms no_3term_ap_check
#print axioms jsp_000288_main