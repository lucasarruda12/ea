import EA.«1-10»

class SemiGroup (S : Type) extends
  Mul S
  where
    mul_assoc (a b c : S) : a * b * c = a * (b * c)

class UniqResSemiGroup (S : Type) extends
  SemiGroup S
  where
    a : S
    rr : S → S → S
    rl : S → S → S
    res_right : ∀ (a b : S), a * (rr a b) = b
    res_left : ∀ (a b : S), (rl a b) * a = b
    res_uniq_right : ∀ (a b x : S), a * x = b → x = rr a b
    res_uniq_left : ∀ (a b y : S), y * a = b → y = rl a b

namespace ex12.ida

variable {S : Type} [UniqResSemiGroup S]

open UniqResSemiGroup

theorem mul_one' : ∀ x : S, x * (rr a a) = x := by
    intro x
    calc
      x * rr a a
        = (rl a x * a) * rr a a
      := by rw [res_left]
      _ = rl a x * (a * rr a a)
      := by rw [SemiGroup.mul_assoc]
      _ = rl a x * a
      := by rw [res_right]
      _ = x
      := by rw [res_left]

theorem one_mul' : ∀ x : S, (rl a a) * x = x := by
  intro x
  calc
      rl a a * x
        = rl a a * (a * rr a x)
      := by rw [res_right]
      _ = rl a a * a * rr a x
      := by rw [SemiGroup.mul_assoc]
      _ = a * rr a x
      := by rw [res_left]
      _ = x
      := by rw [res_right]

theorem rr_uniq : ∀ x y : S, rr x x = rr y y := by
  intro x y
  apply res_uniq_right
  rw [← res_left x y]
  rw [SemiGroup.mul_assoc]
  rw [res_right]

theorem rl_uniq : ∀ x y : S, rl x x = rl y y := by
  intro x y
  apply res_uniq_left
  rw [← res_right x y]
  rw [← SemiGroup.mul_assoc]
  rw [res_left]

theorem rr_a_rl_a : rr (a : S) a = rl a a := by
  calc
    rr a a
      = rl a a * rr a a
    := by rw [one_mul']
    _ = rl a a
    := by rw [mul_one']

theorem rr_rl : ∀ x : S, rr x x = rl x x := by
  intro x
  rw [rr_uniq x a, rl_uniq x a]
  rw [rr_a_rl_a]

theorem inv_mul' : ∀ x : S, rl x (rr a a) * x = rr a a := by
  intro x
  rw [res_left]

theorem inv_uniq : ∀ x : S, rr x (rr a a) = rl x (rr a a) := by
  intro x
  calc
    rr x (rr a a)
      = (rl a a) * rr x (rr a a)
    := by rw [one_mul']
    _ = (rr a a) * rr x (rr a a)
    := by rw [rr_rl]
    _ = rl x (rr a a) * x * rr x (rr a a)
    := by rw [inv_mul']
    _ = rl x (rr a a) * (x * rr x (rr a a))
    := by simp [SemiGroup.mul_assoc]
    _ = rl x (rr a a) * rr a a
    := by rw [res_right]
    _ = rl x (rr a a)
    := by rw [mul_one']

instance : Group S where
  one := rr a a
  inv x := rr x (rr a a)
  mul_assoc := SemiGroup.mul_assoc

  mul_one x := by
    show x * (rr a a) = x
    exact (mul_one' x)
  one_mul x := by
    show (rr a a) * x = x
    rw [rr_a_rl_a, one_mul']

  mul_inv := by
    intro x
    rw [res_right]; rfl
  inv_mul := by
    intro x
    show rr x (rr a a) * x = rr a a
    rw [inv_uniq, inv_mul']

/-
A volta é mostrar resoluções únicas para grupos,
que foi feito em exercício anterior
-/
end ex12.ida

namespace ex12.volta

variable {G : Type} [Group G]

instance : UniqResSemiGroup G where
  mul_assoc := Group.mul_assoc
  a := 1
  rr a b := a⁻¹ * b
  rl a b := b * a⁻¹
  res_right := by
    intro a b
    rw [← Group.mul_assoc]
    rw [Group.mul_inv, Group.one_mul]

  res_left := by
    intro a b
    rw [Group.mul_assoc]
    rw [Group.inv_mul, Group.mul_one]

  res_uniq_right := by
    intro a b x h
    have := congrArg (a⁻¹*·) h
    rw [← Group.mul_assoc] at this
    rw [Group.inv_mul] at this
    rw [Group.one_mul] at this
    assumption

  res_uniq_left := by
    intro a b x h
    have := congrArg (· * a⁻¹) h
    rw [Group.mul_assoc] at this
    rw [Group.mul_inv] at this
    rw [Group.mul_one] at this
    assumption

end ex12.volta
