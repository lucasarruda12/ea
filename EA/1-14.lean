import EA.«2-7»

class Field (F : Type) extends
  Ring F, Inv F
where
  one_neq_zero : 1 ≠ 0
  mul_inv_ne_zero : ∀ x : F, x ≠ 0 → x * x⁻¹ = 1
  inv_mul_ne_zero : ∀ x : F, x ≠ 0 → x⁻¹ * x = 1

/- Para qualquer n, Fin n é um Anel -/

instance (n : Nat) [NeZero n] : Ring (Fin n) where
  zero := 0
  one := 1
  add_zero a := by
    simp only [Fin.add_def]
    rw [Fin.val_zero, Nat.add_zero]
    ext; simp
    rw [Nat.mod_eq_of_lt a.is_lt]

  zero_add := by grind

  add_assoc a b c := by
    simp only [Fin.add_def]
    ext; simp
    rw [Nat.add_assoc]

  add_comm a b := by
    simp only [Fin.add_def]
    ext; simp
    rw [Nat.add_comm]

  add_neg a := by
    simp only [Fin.add_def, Fin.neg_def]
    ext
    show (↑a + (n - ↑a) % n) % n = 0
    cases (Classical.em (a.val = 0)) with
    | inl h =>
      rw [h, Nat.sub_zero, Nat.zero_add]
      rw [Nat.mod_self, Nat.zero_mod]
    | inr h =>
      have h := Nat.zero_lt_of_ne_zero h
      have hn := Nat.zero_lt_of_ne_zero (NeZero.ne n)
      have := Nat.sub_lt hn h
      rw [Nat.mod_eq_of_lt this]
      rw [Nat.add_sub_of_le]
      rw [Nat.mod_self]
      exact a.is_le'

  neg_add := by grind

  mul_assoc a b c := by
    simp only [Fin.mul_def]
    ext; simp
    rw [Nat.mul_assoc]

  one_mul a := by
    ext
    sorry

  mul_one a := by grind

  mul_add := sorry
  add_mul := sorry

/-
Mas Fin n só é um Corpo, quando n é primo.
Isso porque a tem inverso multiplicativo mod m sse (a, m) = 1.
Então, pra garantir que todo mundo tem inverso multiplicativo,
basta que m seja primo! (fmc1)
-/
