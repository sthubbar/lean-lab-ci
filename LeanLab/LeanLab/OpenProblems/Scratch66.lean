import LeanLab.OpenProblems.Erdos9
import LeanLab.OpenProblems.Lemoine
import LeanLab.OpenProblems.Erdos17
import LeanLab.BrunGap.Uniform

open Finset

example (s : Finset ℕ) : ((s : Set ℕ).ncard) = s.card := by simp
example (s : Finset ℕ) : ((s : Set ℕ).ncard) = s.card := by exact?
example (s : Finset ℕ) : (s : Set ℕ).ncard ≤ s.card := by simp
