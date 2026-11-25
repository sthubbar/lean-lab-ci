import LeanLab.ExceptionalSet.KarLemma1VinogradovSplit

/-!
Elementary leaf of the Vinogradov split: adding `t` unknowns on each side costs at most
`P^(2t)`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.Elementary

open LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit
open Classical

theorem ind_sum {γ : Type*} (V : Finset γ) (p q : γ) :
    (∑ v ∈ V, (if p = v then (1 : ℝ) else 0) * (if q = v then (1 : ℝ) else 0)) =
      if p ∈ V then (if q = p then 1 else 0) else 0 := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]

/-- Collision bound: `Σ [f a = g c] ≤ (Σ [f a = f a'] + Σ [g c = g c']) / 2`. -/
theorem collision_le {α γ : Type*} [Fintype α] (f g : α → γ) :
    (∑ a, ∑ c, (if f a = g c then (1 : ℝ) else 0)) ≤
      ((∑ a, ∑ a', (if f a = f a' then (1 : ℝ) else 0)) +
        (∑ c, ∑ c', (if g c = g c' then (1 : ℝ) else 0))) / 2 := by
  set V : Finset γ := Finset.univ.image f
  have hfV : ∀ a, f a ∈ V := fun a => Finset.mem_image_of_mem f (Finset.mem_univ a)
  let A : γ → ℝ := fun v => ∑ a, if f a = v then 1 else 0
  let B : γ → ℝ := fun v => ∑ c, if g c = v then 1 else 0
  have hAB : ∀ (F G : α → γ), (∑ v ∈ V, (∑ a, if F a = v then (1 : ℝ) else 0) *
      (∑ c, if G c = v then (1 : ℝ) else 0)) = ∑ c, ∑ a, ∑ v ∈ V,
        (if F a = v then (1 : ℝ) else 0) * (if G c = v then (1 : ℝ) else 0) := by
    intro F G
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    first
      | rfl
      | exact Finset.sum_comm
  have h1 : (∑ a, ∑ c, (if f a = g c then (1 : ℝ) else 0)) = ∑ v ∈ V, A v * B v := by
    rw [hAB f g, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [ind_sum]
    by_cases h : f y = g x <;> simp [h, eq_comm, hfV y] <;> rw [← h] <;> exact hfV y
  have h2 : (∑ v ∈ V, A v * A v) = ∑ a, ∑ a', (if f a = f a' then (1 : ℝ) else 0) := by
    rw [hAB f f, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [ind_sum]
    by_cases h : f y = f x <;> by_cases h' : f x = f y <;> simp_all [hfV y]
  have h3 : (∑ v ∈ V, B v * B v) ≤ ∑ c, ∑ c', (if g c = g c' then (1 : ℝ) else 0) := by
    rw [hAB g g]
    refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
    rw [ind_sum]
    by_cases hc : g c' ∈ V <;> by_cases h : g c = g c' <;> simp [hc, h, eq_comm] <;> split_ifs <;> norm_num
  have h4 : ∀ v, A v * B v ≤ (A v * A v + B v * B v) / 2 := fun v => by
    nlinarith [sq_nonneg (A v - B v)]
  calc (∑ a, ∑ c, (if f a = g c then (1 : ℝ) else 0)) = ∑ v ∈ V, A v * B v := h1
    _ ≤ ∑ v ∈ V, (A v * A v + B v * B v) / 2 := Finset.sum_le_sum fun v _ => h4 v
    _ = ((∑ v ∈ V, A v * A v) + ∑ v ∈ V, B v * B v) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by rw [h2]; linarith

/-- The vector of power sums of orders `1, ..., n` of a tuple. -/
noncomputable def pw (n P m : ℕ) (x : Fin m → Fin P) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)

theorem vJ_eq_pw (n m P : ℕ) :
    vJ n m P = ∑ x, ∑ y, (if pw n P m x = pw n P m y then (1 : ℝ) else 0) := by
  unfold vJ pw
  simp only [funext_iff]

theorem pw_append (n P s t : ℕ) (a : Fin s → Fin P) (b : Fin t → Fin P) :
    pw n P (s + t) (Fin.append a b) = pw n P s a + pw n P t b := by
  funext j
  simp [pw, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem inner_le (n P s t : ℕ) (b d : Fin t → Fin P) :
    (∑ a, ∑ c, (if pw n P s a + pw n P t b = pw n P s c + pw n P t d then (1 : ℝ) else 0))
      ≤ vJ n s P := by
  have h := collision_le (fun a => pw n P s a + pw n P t b) (fun c => pw n P s c + pw n P t d)
  simp only [add_left_inj] at h
  rw [vJ_eq_pw]
  convert h using 1
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by congr
  · rw [← two_mul, mul_div_cancel_left₀ _ two_ne_zero]

theorem leaf_extra_unknowns_proved :
    type_of% @LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.leaf_extra_unknowns := by
  intro n s t P
  rw [vJ_eq_pw n (s + t) P]
  rw [← (Fin.appendEquiv s t).sum_comp]
  simp_rw [← (Fin.appendEquiv s t).sum_comp]
  have hA : ∀ (x : Fin s → Fin P) (y : Fin t → Fin P),
      (Fin.appendEquiv s t) (x, y) = Fin.append x y := fun _ _ => rfl
  simp only [Fintype.sum_prod_type, hA, pw_append]
  set F : (Fin s → Fin P) → (Fin t → Fin P) → (Fin s → Fin P) → (Fin t → Fin P) → ℝ :=
    fun a b c d => if pw n P s a + pw n P t b = pw n P s c + pw n P t d then 1 else 0 with hF
  calc (∑ a, ∑ b, ∑ c, ∑ d, F a b c d)
        = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ d, ∑ c, F a b c d := Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ a, ∑ c, F a b c d := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ ≤ ∑ b : Fin t → Fin P, ∑ d : Fin t → Fin P, vJ n s P :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun d _ => inner_le n P s t b d
    _ = (P : ℝ) ^ (2 * t) * vJ n s P := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        ring

#print axioms leaf_extra_unknowns_proved

end LeanLab.ExceptionalSet.U1539.KaracubaSplit.VinogradovSplit.Elementary
