class Monoid (M : Type) : Type
  extends
    Mul M, One M
where
  mul_assoc (a b c : M) : a * b * c = a * (b * c)
  one_mul (a : M) : 1 * a = a
  mul_one (a : M) : a * 1 = a

class CommMonoid (M : Type) : Type
  extends
    Monoid M
where
  mul_comm (a b : M) : a * b = b * a

namespace ex4

/- Subtipos! -/
instance : CommMonoid {n : Nat // ∃k : Nat, n = 2 * k} where
  mul x y := ⟨x.val + y.val, by
    have ⟨x, k_x, x_par⟩ := x
    have ⟨y, k_y, y_par⟩ := y
    simp
    exists k_x + k_y
    rw [x_par, y_par, Nat.mul_add]
   ⟩

  one := ⟨0, by exists 0⟩

  mul_assoc a b c := by
    ext
    exact Nat.add_assoc a.val b.val c.val

  mul_one a := by
    ext
    exact Nat.add_zero a.val

  one_mul a := by
    ext
    exact Nat.zero_add a.val

  mul_comm a b := by
    ext
    exact Nat.add_comm a.val b.val

instance : CommMonoid {n : Nat // ∃k : Nat, n = 2 * k + 1} where
  mul x y := ⟨x.val * y.val, by
    have ⟨x, k_x, x_impar⟩ := x
    have ⟨y, k_y, y_impar⟩ := y
    simp
    exists 2*k_x*k_y + k_x + k_y
    grind
  ⟩

  one := ⟨1, by exists 0⟩

  mul_assoc a b c := by
    ext
    exact Nat.mul_assoc a.val b.val c.val

  mul_one a := by
    ext
    exact Nat.mul_one a.val

  one_mul a := by
    ext
    exact Nat.one_mul a.val

  mul_comm a b := by
    ext
    exact Nat.mul_comm a.val b.val

end ex4

namespace ex9

theorem inv_unic [Monoid M] (a b : M) (b_inv_a : a * b = 1 ∧ b * a = 1) :
  ∀ x, a * x = 1 ∧ x * a = 1 → x = b
:= by
  intro x x_inv_a
  rw [← Monoid.one_mul x]
  rw [← b_inv_a.right]
  rw [Monoid.mul_assoc]
  rw [x_inv_a.left]
  rw [Monoid.mul_one]

end ex9
