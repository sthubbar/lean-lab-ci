/-
P0032 Riesel-Vaughan 1983, the 18-prime Theorem with three of the four values of (2.30) and
(2.31) discharged. Unit U-6715, CLOUD 20261020T1816Z-cloud48, track T1. AI-written Lean code,
Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

CONDITIONAL, counted apart:
* `theorem_LS2`: every even number is a sum of at most eighteen primes, CONDITIONAL ON Lemma 5
  at five rows, Lemma 6 (i) and (ii), `T(99989) ≤ 80096031` and Rosser-Schoenfeld (3.3) only.
  `T(79) ≤ 328.5614`, `s(79) = 21` and `s(99989) = 9590` are PROVED in Table230Small.lean.
* `corollary19_LS2`: the nineteen prime form under the same inputs.
KNOWN mathematics.
-/
import LeanLab.RieselVaughan1983.Section9LS
import LeanLab.RieselVaughan1983.Table230Small

namespace LeanLab.RieselVaughan1983.Section9LS2

open LeanLab.RieselVaughan1983 LeanLab.RieselVaughan1983.Section9LS
  LeanLab.RieselVaughan1983.Table230Small

/-- **The Theorem**, CONDITIONAL ON Lemma 5 at five rows, Lemma 6 (i) and (ii),
`Table230Big` and `RS33`. -/
theorem theorem_LS2 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hT : Table230Big) (hRS : RS33) :
    Theorem :=
  theorem_LS h24 h42 h278 h396 h5 h6 h6' (table230_of_big hT) hRS

/-- The nineteen prime form under the same inputs. -/
theorem corollary19_LS2 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hT : Table230Big) (hRS : RS33) :
    Corollary19 :=
  corollary19_LS h24 h42 h278 h396 h5 h6 h6' (table230_of_big hT) hRS

end LeanLab.RieselVaughan1983.Section9LS2
