import LeanLab.LiuWang2002.RatioScan352

/-!
Bounded checkpoint transfers for Schoenfeld page 356, display 5.1 star.
The certificates use the integer base of Task352 and retain all rounding.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368
open Task352

/-- Product of the prime factors introduced in a bounded integer interval.
Derived executable data for page 356, display 5.1 star. -/
def segmentProduct : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, n => segmentProduct k n *
    (if 2 ≤ n + k + 1 ∧ Nat.minFac (n + k + 1) = n + k + 1 then n + k + 1 else 1)

/-- The bounded product updates the exact primorial.
Derived transfer for page 356, display 5.1 star. -/
theorem primorial_segment (k n : ℕ) :
    primorial (n + k) = primorial n * segmentProduct k n := by
  induction k with
  | zero => simp [segmentProduct]
  | succ k ih =>
    rw [Nat.add_succ, primorial_next, ih, segmentProduct]
    simp only [Nat.add_assoc, mul_assoc]

/-- An integer certificate remains valid with a fixed product when its
exponent increases. Derived transfer for page 356, display 5.1 star. -/
theorem certificate_exponent (p a t : ℕ) (h : p * 25 ^ a < 68 ^ a) :
    p * 25 ^ (a + t) < 68 ^ (a + t) := by
  rw [pow_add, pow_add, ← mul_assoc]
  exact (Nat.mul_lt_mul_of_pos_right h (by positivity : 0 < 25 ^ t)).trans_le
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 25 ≤ 68) t))

/-- A checkpoint upper bound supplies every integer strictly after n
through n plus k. Only the new interval product is evaluated.
Derived transfer for page 356, display 5.1 star. -/
theorem checkpoint_range (k n r S : ℕ)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : r * segmentProduct k n * 25 < S * 68) :
    ∀ m : ℕ, n < m → m ≤ n + k → primorial m * 25 ^ m < 68 ^ m := by
  have hbase : primorial (n + k) * 25 ^ (n + 1) < 68 ^ (n + 1) := by
    have hh : primorial (n + k) * 25 ^ (n + 1) * S < S * 68 ^ (n + 1) := by
      calc
        _ = (primorial n * 25 ^ n * S) * (segmentProduct k n * 25) := by
          rw [primorial_segment, pow_succ]; ring
        _ ≤ (r * 68 ^ n) * (segmentProduct k n * 25) := Nat.mul_le_mul_right _ hi
        _ = (r * segmentProduct k n * 25) * 68 ^ n := by ring
        _ < (S * 68) * 68 ^ n := Nat.mul_lt_mul_of_pos_right hc (by positivity)
        _ = S * 68 ^ (n + 1) := by rw [pow_succ]; ring
    rw [Nat.mul_comm S] at hh
    exact Nat.lt_of_mul_lt_mul_right hh
  intro m hm hm'
  have hmono : primorial m * 25 ^ (n + 1) < 68 ^ (n + 1) :=
    (Nat.mul_le_mul_right _ (primorial_mono hm')).trans_lt hbase
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show n + 1 ≤ m by omega)
  subst m
  exact certificate_exponent _ _ _ hmono

/-- The terminal integer bound is handed to the next checkpoint.
Derived transfer for page 356, display 5.1 star. -/
theorem checkpoint_next (k n r s S : ℕ)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : r * segmentProduct k n * 25 ^ k ≤ s * 68 ^ k) :
    primorial (n + k) * 25 ^ (n + k) * S ≤ s * 68 ^ (n + k) := by
  calc
    _ = (primorial n * 25 ^ n * S) * (segmentProduct k n * 25 ^ k) := by
      rw [primorial_segment, pow_add]; ring
    _ ≤ (r * 68 ^ n) * (segmentProduct k n * 25 ^ k) := Nat.mul_le_mul_right _ hi
    _ = (r * segmentProduct k n * 25 ^ k) * 68 ^ n := by ring
    _ ≤ (s * 68 ^ k) * 68 ^ n := Nat.mul_le_mul_right _ hc
    _ = s * 68 ^ (n + k) := by rw [pow_add]; ring

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_segment
#print axioms LeanLab.LiuWang2002.Task368.certificate_exponent
#print axioms LeanLab.LiuWang2002.Task368.checkpoint_range
#print axioms LeanLab.LiuWang2002.Task368.checkpoint_next

namespace LeanLab.LiuWang2002.Task368

/-- The scale for the bounded certificates. This is derived integer data
for Schoenfeld page 356, display 5.1 star. -/
def checkpointScale : ℕ := 2 ^ 4096

/-- Check each bounded interval from explicit terminal states. No state
is computed by unfolding an earlier checkpoint.
Derived executable data for page 356, display 5.1 star. -/
def checkpointCheck (S n r : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | (k, s) :: rest =>
    decide (r * segmentProduct k n * 25 < S * 68) &&
    decide (r * segmentProduct k n * 25 ^ k ≤ s * 68 ^ k) &&
    checkpointCheck S (n + k) s rest

/-- Soundness of a list of independently bounded checkpoints.
Derived transfer for page 356, display 5.1 star. -/
theorem checkpointCheck_sound (cs : List (ℕ × ℕ)) (S n r : ℕ)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : checkpointCheck S n r cs = true) :
    ∀ m : ℕ, n < m → m ≤ n + (cs.map Prod.fst).sum →
      primorial m * 25 ^ m < 68 ^ m := by
  induction cs generalizing n r with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.add_zero]; omega
  | cons c cs ih =>
    obtain ⟨k, s⟩ := c
    simp only [checkpointCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    intro m hm hm'
    by_cases hk : m ≤ n + k
    · exact checkpoint_range k n r S hi hc.1.1 m hm hk
    · apply ih (n + k) s (checkpoint_next k n r s S hi hc.1.2) hc.2 m (by omega)
      simp only [List.map_cons, List.sum_cons] at hm'
      omega

/-- The last checkpoint retains an exact invariant for a later file.
Derived transfer for page 356, display 5.1 star. -/
theorem checkpointCheck_terminal (cs : List (ℕ × ℕ)) (S n r : ℕ)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : checkpointCheck S n r cs = true) :
    primorial (n + (cs.map Prod.fst).sum) * 25 ^ (n + (cs.map Prod.fst).sum) * S ≤
      (cs.getLast?.getD (0, r)).2 * 68 ^ (n + (cs.map Prod.fst).sum) := by
  induction cs generalizing n r with
  | nil => simpa using hi
  | cons c cs ih =>
    obtain ⟨k, s⟩ := c
    simp only [checkpointCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hh := ih (n + k) s (checkpoint_next k n r s S hi hc.1.2) hc.2
    cases cs with
    | nil => simpa using hh
    | cons c cs => simpa [Nat.add_assoc, List.getLast?_cons] using hh

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.checkpointCheck_sound
#print axioms LeanLab.LiuWang2002.Task368.checkpointCheck_terminal

namespace LeanLab.LiuWang2002.Task368
/-- A nonempty checkpoint instance certifies integer 2 and keeps a
positive terminal invariant. Derived instance for page 356,
display 5.1 star. -/
theorem checkpoint_instance :
    primorial 1 * 25 ^ 1 * 100 ≤ 37 * 68 ^ 1 ∧
    checkpointCheck 100 1 37 [(1, 28)] = true ∧
    primorial 2 * 25 ^ 2 < 68 ^ 2 ∧
    primorial 2 * 25 ^ 2 * 100 ≤ 28 * 68 ^ 2 := by
  decide +kernel
end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.checkpoint_instance
