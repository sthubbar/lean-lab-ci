import Mathlib

/-!
# PROGRAM SEARCH certificate shape: placements of segments for finite additive 2-bases

Unit U-1604, run 20261102T0813Z-2382, track ORIGINAL, PROGRAM SEARCH. AI wrote the Lean code.
Binary Goldbach is OPEN; this file is about the neighbouring record below, not about Goldbach.

Plain math twin. Fix `t >= 1` and the segments `V = [0, t]`, `H = {0, t, ..., t^2 - t}`,
`S = {0, t + 1, ..., t^2 - 1}`. For finite sets `I, J, K` of naturals put
`A = (V + t^2 I) ∪ (H + t^2 J) ∪ (S + t^2 K)`. Say block `b` is covered if `b` is in `I + J` or
`I + K`, or if both `b` and `b - 1` are in `J + K`. If blocks `0, ..., m - 1` are covered then
`A + A` contains `[0, m t^2 - 1]`, and `|A| <= (|I| + |J| + |K|) t + |I|`. So with
`l = |I| + |J| + |K|`, the extremal range satisfies `liminf n(k) / k^2 >= m / l^2`.

Source: J. Kohonen, An improved lower bound for finite additive 2-bases, J. Number Theory 174,
2017, pages 518-524, DOI 10.1016/j.jnt.2016.11.011, arXiv:1606.04770. Facts 1 to 3 and Theorem 1
at arXiv pages 2 to 5 give the construction and the placement with `l = 42`, `m = 510`, hence the
record `85/294`. The paper checks that placement case by case and states no general criterion;
`sumset_of_covers` below is such a criterion, with the triangle split of the parallelogram
`H + S` made explicit. Known mathematics. The same bound reads
`g(n)^2 <= (3.4588... + o(1)) n` for Erdos Problem 791, https://www.erdosproblems.com/791, an open
problem on the exact asymptotic of `g`.

* `sumset_of_covers`: the criterion above, for any placement. PROVED.
* `card_basis_le`: the size bound. PROVED.
* `certificate_of_covers`: both together; this is the theorem every candidate plugs into. PROVED.
* `kohonen_covers`, `kohonen_certificate`: Kohonen's placement, by kernel computation. PROVED.
* `RecordBeaten`: the OPEN target, a placement with `m / l^2 > 85 / 294`. Not proved. A search
  winner closes it by one `decide +kernel` of `coversB`, see `recordBeaten_of_certificate`.

Vacuity: `kohonen_covers` shows the hypothesis is met, `kohonen_not_511` and `small_not_covers`
show `coversB` is not constantly true, `kohonen_not_beats` shows the strict record is not met by
the baseline itself.

Not done here: the passage from the family in `t` to the `liminf` statement for every `k`.
That step is routine monotonicity in `k` and does not depend on the placement.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

open Finset

/-- The vertical segment `[0, t]`. -/
def V (t : ℕ) : Finset ℕ := range (t + 1)

/-- The horizontal segment `{0, t, ..., t^2 - t}`. -/
def H (t : ℕ) : Finset ℕ := (range t).image (· * t)

/-- The slanted segment `{0, t + 1, ..., t^2 - 1}`. -/
def S (t : ℕ) : Finset ℕ := (range t).image (· * (t + 1))

/-- The translate of a segment by the blocks in a list, block unit `t^2`. -/
def place (t : ℕ) (seg : Finset ℕ) (B : List ℕ) : Finset ℕ :=
  B.toFinset.biUnion fun b => seg.image (· + t ^ 2 * b)

/-- The basis of a placement. -/
def basis (t : ℕ) (I J K : List ℕ) : Finset ℕ :=
  place t (V t) I ∪ place t (H t) J ∪ place t (S t) K

/-- `b` is a sum of an element of `P` and an element of `Q`. -/
def sumHits (P Q : List ℕ) (b : ℕ) : Bool := P.any fun p => Q.any fun q => p + q == b

/-- The coverage rule for one block; the `b - 1` part is guarded so that block `0` needs `I`. -/
def blockOK (I J K : List ℕ) (b : ℕ) : Bool :=
  sumHits I J b || sumHits I K b ||
    (sumHits J K b && (b != 0 && sumHits J K (b - 1)))

/-- All blocks below `m` are covered. This is the finite check of a certificate. -/
def coversB (I J K : List ℕ) (m : ℕ) : Bool := (List.range m).all (blockOK I J K)

lemma sumHits_spec {P Q : List ℕ} {b : ℕ} (h : sumHits P Q b = true) :
    ∃ p ∈ P, ∃ q ∈ Q, p + q = b := by
  simpa [sumHits] using h

lemma vh {t x : ℕ} (ht : 0 < t) (hx : x < t ^ 2) : ∃ v ∈ V t, ∃ h ∈ H t, v + h = x := by
  refine ⟨x % t, ?_, x / t * t, ?_, ?_⟩
  · have := Nat.mod_lt x ht
    simp only [V, mem_range]; omega
  · refine mem_image.2 ⟨x / t, mem_range.2 ?_, rfl⟩
    exact Nat.div_lt_of_lt_mul (by nlinarith)
  · exact Nat.mod_add_div' x t

lemma vs {t x : ℕ} (hx : x < t ^ 2) : ∃ v ∈ V t, ∃ s ∈ S t, v + s = x := by
  refine ⟨x % (t + 1), ?_, x / (t + 1) * (t + 1), ?_, ?_⟩
  · have := Nat.mod_lt x (Nat.succ_pos t)
    simp only [V, mem_range]; omega
  · refine mem_image.2 ⟨x / (t + 1), mem_range.2 ?_, rfl⟩
    exact Nat.div_lt_of_lt_mul (by nlinarith)
  · exact Nat.mod_add_div' x (t + 1)

/-- Lower triangle of the parallelogram `H + S`. -/
lemma hs_lower {t x : ℕ} (ht : 0 < t) (hx : x < t ^ 2) (hrs : x % t ≤ x / t) :
    ∃ h ∈ H t, ∃ s ∈ S t, h + s = x := by
  have hd : x / t < t := Nat.div_lt_of_lt_mul (by nlinarith)
  have hr := Nat.mod_lt x ht
  have hx' : x % t + x / t * t = x := Nat.mod_add_div' x t
  generalize x / t = q at *
  generalize x % t = r at *
  refine ⟨(q - r) * t, mem_image.2 ⟨_, mem_range.2 (by omega), rfl⟩,
    r * (t + 1), mem_image.2 ⟨_, mem_range.2 hr, rfl⟩, ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  rw [Nat.add_sub_cancel_left, ← hx']
  ring

/-- Upper triangle of the parallelogram `H + S`, sitting one block higher. -/
lemma hs_upper {t x : ℕ} (ht : 0 < t) (hrs : x / t < x % t) :
    ∃ h ∈ H t, ∃ s ∈ S t, h + s = x + t ^ 2 := by
  have hr := Nat.mod_lt x ht
  have hx' : x % t + x / t * t = x := Nat.mod_add_div' x t
  generalize x / t = q at *
  generalize x % t = r at *
  refine ⟨(t + q - r) * t, mem_image.2 ⟨_, mem_range.2 (by omega), rfl⟩,
    r * (t + 1), mem_image.2 ⟨_, mem_range.2 hr, rfl⟩, ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr.le
  have : r + d + q - r = d + q := by omega
  rw [this, ← hx']
  ring

lemma mem_place {t : ℕ} {seg : Finset ℕ} {B : List ℕ} {x b : ℕ} (hx : x ∈ seg) (hb : b ∈ B) :
    x + t ^ 2 * b ∈ place t seg B :=
  mem_biUnion.2 ⟨b, List.mem_toFinset.2 hb, mem_image.2 ⟨x, hx, rfl⟩⟩

/-- **Coverage criterion.** Every covered block is a full interval of `A + A`. -/
theorem sumset_of_covers {t : ℕ} (ht : 0 < t) {I J K : List ℕ} {m : ℕ}
    (hc : coversB I J K m = true) :
    ∀ n < m * t ^ 2, ∃ a ∈ basis t I J K, ∃ b ∈ basis t I J K, a + b = n := by
  intro n hn
  have ht2 : 0 < t ^ 2 := by positivity
  have hx : n % t ^ 2 < t ^ 2 := Nat.mod_lt n ht2
  have hnx : n = n % t ^ 2 + t ^ 2 * (n / t ^ 2) := (Nat.mod_add_div n (t ^ 2)).symm
  have hbm : n / t ^ 2 < m := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hn)
  generalize n / t ^ 2 = b at *
  generalize n % t ^ 2 = x at *
  have hbk : blockOK I J K b = true := by
    have := (List.all_eq_true.1 hc) b (List.mem_range.2 hbm)
    exact this
  have inV : ∀ {y c}, y ∈ V t → c ∈ I → y + t ^ 2 * c ∈ basis t I J K := fun hy hc' => by
    simp only [basis, mem_union]; exact Or.inl (Or.inl (mem_place hy hc'))
  have inH : ∀ {y c}, y ∈ H t → c ∈ J → y + t ^ 2 * c ∈ basis t I J K := fun hy hc' => by
    simp only [basis, mem_union]; exact Or.inl (Or.inr (mem_place hy hc'))
  have inS : ∀ {y c}, y ∈ S t → c ∈ K → y + t ^ 2 * c ∈ basis t I J K := fun hy hc' => by
    simp only [basis, mem_union]; exact Or.inr (mem_place hy hc')
  simp only [blockOK, Bool.or_eq_true, Bool.and_eq_true] at hbk
  rcases hbk with (hij | hik) | ⟨hjk, hb0, hjk'⟩
  · obtain ⟨i, hi, j, hj, hij⟩ := sumHits_spec hij
    obtain ⟨v, hv, h, hh, hvh⟩ := vh ht hx
    refine ⟨_, inV hv hi, _, inH hh hj, ?_⟩
    rw [hnx, ← hij, ← hvh]; ring
  · obtain ⟨i, hi, k, hk, hik⟩ := sumHits_spec hik
    obtain ⟨v, hv, s, hs, hvs⟩ := vs hx
    refine ⟨_, inV hv hi, _, inS hs hk, ?_⟩
    rw [hnx, ← hik, ← hvs]; ring
  · by_cases hrs : x % t ≤ x / t
    · obtain ⟨j, hj, k, hk, hjk⟩ := sumHits_spec hjk
      obtain ⟨h, hh, s, hs, hhs⟩ := hs_lower ht hx hrs
      refine ⟨_, inH hh hj, _, inS hs hk, ?_⟩
      rw [hnx, ← hjk, ← hhs]; ring
    · obtain ⟨j, hj, k, hk, hjk⟩ := sumHits_spec hjk'
      obtain ⟨h, hh, s, hs, hhs⟩ := hs_upper ht (not_le.1 hrs)
      refine ⟨_, inH hh hj, _, inS hs hk, ?_⟩
      have hb1 : b ≠ 0 := by simpa using hb0
      have hb2 : b = j + k + 1 := by omega
      rw [hnx, hb2]
      have : h + t ^ 2 * j + (s + t ^ 2 * k) = (h + s) + t ^ 2 * (j + k) := by ring
      rw [this, hhs]; ring

lemma card_place_le (t : ℕ) (seg : Finset ℕ) (B : List ℕ) :
    (place t seg B).card ≤ B.length * seg.card := by
  refine (card_biUnion_le_card_mul _ _ seg.card fun b _ => card_image_le).trans ?_
  exact Nat.mul_le_mul_right _ (List.toFinset_card_le B)

/-- **Size bound.** -/
theorem card_basis_le (t : ℕ) (I J K : List ℕ) :
    (basis t I J K).card ≤ (I.length + J.length + K.length) * t + I.length := by
  have h1 := card_place_le t (V t) I
  have h2 := card_place_le t (H t) J
  have h3 := card_place_le t (S t) K
  have hV : (V t).card = t + 1 := by simp [V]
  have hH : (H t).card ≤ t := card_image_le.trans (by simp)
  have hS : (S t).card ≤ t := card_image_le.trans (by simp)
  have h12 := card_union_le (place t (V t) I ∪ place t (H t) J) (place t (S t) K)
  have h4 := card_union_le (place t (V t) I) (place t (H t) J)
  have hJ := Nat.mul_le_mul_left J.length hH
  have hK := Nat.mul_le_mul_left K.length hS
  rw [hV] at h1
  simp only [basis]
  nlinarith

/-- **The certificate theorem.** A placement passing `coversB` gives, for every `t`, a set of size
at most `l t + |I|` whose sumset contains `[0, m t^2 - 1]`. -/
theorem certificate_of_covers {I J K : List ℕ} {m : ℕ} (hc : coversB I J K m = true) (t : ℕ)
    (ht : 0 < t) :
    ∃ A : Finset ℕ, A.card ≤ (I.length + J.length + K.length) * t + I.length ∧
      ∀ n < m * t ^ 2, ∃ a ∈ A, ∃ b ∈ A, a + b = n :=
  ⟨basis t I J K, card_basis_le t I J K, sumset_of_covers ht hc⟩

/-- A placement of `l` segments covering `m` blocks strictly beats the record `85/294`. -/
def Beats (I J K : List ℕ) (m : ℕ) : Prop :=
  85 * (I.length + J.length + K.length) ^ 2 < 294 * m

/-- **OPEN target.** Some placement strictly beats Kohonen's `85/294`. Not proved; a true instance
would be a new lower bound only after the literature search required by TARGETS.md. -/
def RecordBeaten : Prop := ∃ (I J K : List ℕ) (m : ℕ), coversB I J K m = true ∧ Beats I J K m

/-- How a search winner closes the target. -/
theorem recordBeaten_of_certificate {I J K : List ℕ} {m : ℕ} (hc : coversB I J K m = true)
    (hb : Beats I J K m) : RecordBeaten := ⟨I, J, K, m, hc, hb⟩

/-! ## The baseline, Kohonen's placement, arXiv:1606.04770, Theorem 1. -/

/-- `I = {0, 5} ∪ [112, (5), 137]`, 8 blocks. -/
def kI : List ℕ := [0, 5, 112, 117, 122, 127, 132, 137]

/-- `J = [10, (6), 106]`, 17 blocks. -/
def kJ : List ℕ := (List.range 17).map fun i => 10 + 6 * i

/-- `K = [0, 4] ∪ [224, 229] ∪ [367, 372]`, 17 blocks. -/
def kK : List ℕ :=
  [0, 1, 2, 3, 4, 224, 225, 226, 227, 228, 229, 367, 368, 369, 370, 371, 372]

theorem kohonen_covers : coversB kI kJ kK 510 = true := by decide +kernel

/-- **Kohonen's family.** The arXiv text prints `k = 42 t + 7`; this file proves `42 t + 8`. The
difference of one does not change the ratio `510 / 42^2`. -/
theorem kohonen_certificate (t : ℕ) (ht : 0 < t) :
    ∃ A : Finset ℕ, A.card ≤ 42 * t + 8 ∧ ∀ n < 510 * t ^ 2, ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  simpa [kI, kJ, kK] using certificate_of_covers kohonen_covers t ht

/-! ## Vacuity. -/

/-- The block count `510` is exact for this rule, so `coversB` is not constantly true. -/
theorem kohonen_not_511 : coversB kI kJ kK 511 = false := by decide +kernel

/-- A small placement that fails. -/
theorem small_not_covers : coversB [0] [0] [] 2 = false := by decide +kernel

/-- The baseline ties the record and does not beat it. -/
theorem kohonen_not_beats : ¬ Beats kI kJ kK 510 := by
  unfold Beats
  decide +kernel

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.sumset_of_covers
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.certificate_of_covers
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_covers
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_certificate
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_not_511
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.recordBeaten_of_certificate
