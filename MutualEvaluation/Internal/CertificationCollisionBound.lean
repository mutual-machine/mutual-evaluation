import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Internal birthday bound for independent uniform indices. The proof counts
injective index tables exactly, then bounds the missing mass by the pair count. -/

namespace MutualEvaluation.Certification.Internal

private lemma birthday_count_bound (m n : ℕ) :
    (m : ℝ) * ((m : ℝ)^n - (m.descFactorial n : ℝ)) ≤
      (n.choose 2 : ℝ) * (m : ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hd : (0 : ℝ) ≤ m.descFactorial n := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : (m.descFactorial n : ℝ) ≤ (m : ℝ)^n := by
      exact_mod_cast Nat.descFactorial_le_pow m n
    have hs : (m : ℝ) ≤ (m - n : ℕ) + (n : ℝ) := by
      exact_mod_cast (show m ≤ m - n + n by omega)
    have h1 := mul_le_mul_of_nonneg_right hs hd
    have h2 := mul_le_mul_of_nonneg_left hp hn
    have h3 := mul_le_mul_of_nonneg_left ih hm
    rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ,
      Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
    nlinarith

/-- Collision probability of `n` independent uniform `Fin m` indices. -/
lemma collision_sum_le (m n : ℕ) (hm : 0 < m) :
    (∑ u : Fin n → Fin m,
      if ¬Function.Injective u then ((m : ℝ)⁻¹)^n else 0) ≤
      (Nat.choose n 2 : ℝ) / (m : ℝ) := by
  classical
  let e : {u : Fin n → Fin m // Function.Injective u} ≃ (Fin n ↪ Fin m) :=
    { toFun := fun u => ⟨u.val, u.property⟩
      invFun := fun u => ⟨u.toFun, u.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Fintype.card {u : Fin n → Fin m // Function.Injective u} =
      m.descFactorial n := by
    simpa using Fintype.card_congr e
  have hb : Fintype.card {u : Fin n → Fin m // ¬Function.Injective u} =
      m^n - m.descFactorial n := by
    rw [Fintype.card_subtype_compl, hc]
    simp
  have hsum : (∑ u : Fin n → Fin m,
      if ¬Function.Injective u then ((m : ℝ)⁻¹)^n else 0) =
      ((m : ℝ)^n - (m.descFactorial n : ℝ)) * ((m : ℝ)⁻¹)^n := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype, hb,
      Nat.cast_sub (Nat.descFactorial_le_pow m n), Nat.cast_pow]
  rw [hsum]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hmR _) hmR]
  nlinarith [birthday_count_bound m n]

end MutualEvaluation.Certification.Internal
