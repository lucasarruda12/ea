class Ring (R : Type) : Type
  extends
    Mul R, One R, Neg R, Add R, Zero R
where
  add_assoc (a b c : R) : a + b + c = a + (b + c)
  add_comm (a b : R) : a + b = b + a
  zero_add (a : R) : 0 + a = a
  add_zero (a : R) : a + 0 = a
  add_neg (a : R) : a + (-a) = 0
  neg_add (a : R) : (-a) + a = 0

  mul_assoc (a b c : R) : a * b * c = a * (b * c)
  one_mul (a : R) : 1 * a = a
  mul_one (a : R) : a * 1 = a

  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (b + c) * a = b * a + c * a


-- f deve ser um homomorfismo de grupos para a parte aditiva
-- e um homomorfismo de monoids para a parte multiplicativa.
structure ring_homm [Ring R] [Ring S] : Type where
  f : R → S
  f_add : f (x + y) = f x + f y
  f_mul : f (x * y) = f x * f y
  f_one : f 1 = 1
