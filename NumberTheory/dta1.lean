import Mathlib
import Paperproof

open Nat

example (x y m n : Nat) (h : m * x + n * y = x.gcd y) (h1 : m > 0) (h2 : x > 0) : Nat.Coprime m n := by
  by_contra h_neg
  let a := m.gcd n
  have a_not_one : a ≠ 1 := h_neg
  have a_not_zero : a ≠ 0 := by
    intro h_zero
    rw [Nat.gcd_eq_zero_iff] at h_zero
    exact (Nat.ne_zero_iff_zero_lt.2 h1) h_zero.1
  have a_ge_one : a ≥ 1 := Nat.gcd_pos_of_pos_left _ h1
  have g_gt_one : a > 1 := by
    apply Nat.lt_of_le_of_ne
    exact a_ge_one
    exact a_not_one.symm
  have a_divides_m : a ∣ m := Nat.gcd_dvd_left m n
  have a_divides_n : a ∣ n := Nat.gcd_dvd_right m n
  have ⟨q, h_q⟩ := exists_eq_mul_right_of_dvd (a_divides_m)
  have ⟨p, h_p⟩ := exists_eq_mul_right_of_dvd (a_divides_n)
  rw [h_q, h_p] at h
  simp only [Nat.mul_assoc, ← Nat.mul_add] at h
  have ⟨e, h_e⟩ := exists_eq_mul_right_of_dvd (Nat.gcd_dvd_left x y)
  have ⟨f, h_f⟩ := exists_eq_mul_right_of_dvd (Nat.gcd_dvd_right x y)
  rw (config := { occs := .pos [1]}) [h_e] at h
  rw (config := { occs := .pos [2]}) [h_f] at h
  repeat rw [← Nat.mul_assoc] at h
  rw (config := { occs := .pos [3]}) [Nat.mul_comm] at h
  rw (config := { occs := .pos [5]}) [Nat.mul_comm] at h
  simp only [Nat.mul_assoc, ← Nat.mul_add] at h
  rw [← Nat.mul_assoc] at h
  rw (config := { occs := .pos [2]}) [Nat.mul_comm] at h
  rw [Nat.mul_assoc] at h
  conv at h =>
    rhs
    rw [← Nat.mul_one (x.gcd y)]
  have h_cancel : a * (q * e + p * f) = 1 := by
    have x_not_zero : x ≠ 0 := Nat.ne_zero_iff_zero_lt.2 h2
    apply Nat.eq_of_mul_eq_mul_left
    apply Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left x_not_zero)
    exact y
    exact h
  have a_divides_one : a ∣ 1 := by
    rw [← h_cancel]
    apply Nat.dvd_mul_right
  have a_one : a = 1 := by
    exact Nat.eq_one_of_dvd_one a_divides_one
  exact a_not_one a_one


example (x y m n : Nat) (h : m * x + n * y = x.gcd y) (h2 : x > 0) : Nat.Coprime m n := by
  by_contra h_neg
  let a := m.gcd n
  have : a ∣ m := Nat.gcd_dvd_left m n
  obtain ⟨q, h_q⟩ := exists_eq_mul_right_of_dvd (this)
  have : a ∣ n := Nat.gcd_dvd_right m n
  obtain ⟨p, h_p⟩ := exists_eq_mul_right_of_dvd (this)
  obtain ⟨e, h_e⟩ := exists_eq_mul_right_of_dvd (Nat.gcd_dvd_left x y)
  obtain ⟨f, h_f⟩ := exists_eq_mul_right_of_dvd (Nat.gcd_dvd_right x y)
  suffices : a * (q * e + p * f) = 1
  . have : a = 1 := Nat.eq_one_of_mul_eq_one_right this
    contradiction
  . have : x ≠ 0 := Nat.ne_zero_iff_zero_lt.2 h2
    apply Nat.eq_of_mul_eq_mul_left
    apply Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left this)
    exact y
    rw [h_q, h_p] at h
    simp only [Nat.mul_assoc, ← Nat.mul_add] at h
    conv_lhs at h =>
      enter [2]; rw [h_e]
      arg 2; rw [h_f]
    repeat rw [← Nat.mul_assoc] at h
    conv_lhs at h =>
      enter [2]
      congr
      arg 1
      rw [Nat.mul_comm]
    conv_lhs at h =>
      enter [2]; enter [2]; arg 1; rw [Nat.mul_comm]
    simp only [Nat.mul_assoc, ← Nat.mul_add] at h
    rw [← Nat.mul_assoc] at h
    conv_lhs at h =>
      rw (config := { occs := .pos [2]}) [Nat.mul_comm]
    rw [Nat.mul_assoc] at h
    conv_rhs at h => rw [← Nat.mul_one (x.gcd y)]
    exact h


example (a b c : Nat) (h1 : Nat.Coprime a b) (h2 : c ∣ a): Nat.Coprime b c := by
  have ⟨k, h_k⟩ := exists_eq_mul_right_of_dvd (h2)
  rw [h_k] at h1
  apply Nat.coprime_iff_gcd_eq_one.2
  apply Nat.gcd_eq_iff.2
  simp
  intro n h_nb h_nc
  apply Nat.eq_one_of_dvd_coprimes
  exact h1
  conv =>
    lhs
    rw [← Nat.mul_one n]
  apply Nat.mul_dvd_mul
  exact h_nc
  apply Nat.one_dvd
  exact h_nb


example (a b : Nat) : ((a + b).gcd a = a.gcd b) := by
  simp [Nat.gcd_comm a b]
