inductive Index
  | zero : Index
  | one : Index

instance : Zero Index where
  zero := Index.zero

instance : One Index where
  one := Index.one

def Matrix_2x2 : Type := Index → Index → Int


def Matrix_2x2.add (A B : Matrix_2x2) : Matrix_2x2
  | x, y => A x y + B x y

instance : Add Matrix_2x2 where
  add := Matrix_2x2.add

def Matrix_2x2.mul (A B : Matrix_2x2) : Matrix_2x2
  | x, y => A x 0 * B 0 y + A x 1 * B 1 y

instance : Mul Matrix_2x2 where
  mul := Matrix_2x2.mul

def f (x : Int) : Matrix_2x2
  | 0, 0 => x
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => 0

theorem f_add (x y : Int) : f (x + y) = f x + f y := by
  funext i j
  match i, j with
  | 0,0 => rfl
  | 0,1 => rfl
  | 1,0 => rfl
  | 1,1 => rfl

theorem f_mul (x y : Int) : f (x * y) = (f x).mul (f y) := by
  funext i j
  match i, j with
  | 0,0 =>
    rw [f.eq_def]; simp
    rw [Matrix_2x2.mul]
    simp only [f.eq_def]
    simp

  | 0,1 =>
    rw [f.eq_def]; simp
    rw [Matrix_2x2.mul]
    simp only [f.eq_def]
    simp

  | 1,0 =>
    rw [f.eq_def]; simp
    rw [Matrix_2x2.mul]
    simp only [f.eq_def]
    simp

  | 1,1 =>
    rw [f.eq_def]; simp
    rw [Matrix_2x2.mul]
    simp only [f.eq_def]
    simp

#eval (f 1) 0 0 -- 1
#eval (f 1) 0 1 -- 0
#eval (f 1) 1 0 -- 0
#eval (f 1) 1 1 -- 0

/-
Como (f 1) 1 1 ≠ 1, f 1 ≠ 1.
Logo, f não é um homomorfismo de anéis unitários.

Apesar disso, como mostramos que f respeita a adição e a multiplicação,
podemos afirmar que f é um homomorfismo de anéis.
-/
